import E112055Data
namespace Snake9.Regrowth.E112055
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then false else decide (InPath q (0 : Vertex))) else (if i < 3 then decide (InPath q (1 : Vertex)) else decide (InPath q (2 : Vertex)))) else (if i < 6 then (if i < 5 then decide (InPath q (5 : Vertex)) else decide (InPath q (8 : Vertex))) else (if i < 7 then decide (InPath q (10 : Vertex)) else decide (InPath q (12 : Vertex))))) else (if i < 12 then (if i < 10 then (if i < 9 then decide (InPath q (14 : Vertex)) else decide (InPath q (15 : Vertex))) else (if i < 11 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex)))) else (if i < 14 then (if i < 13 then decide (InPath q (19 : Vertex)) else decide (InPath q (21 : Vertex))) else (if i < 15 then decide (InPath q (22 : Vertex)) else decide (InPath q (23 : Vertex)))))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then decide (InPath q (25 : Vertex)) else decide (InPath q (27 : Vertex))) else (if i < 19 then decide (InPath q (28 : Vertex)) else decide (InPath q (29 : Vertex)))) else (if i < 22 then (if i < 21 then decide (InPath q (31 : Vertex)) else decide (InPath q (67 : Vertex))) else (if i < 23 then decide (InPath q (68 : Vertex)) else decide (InPath q (69 : Vertex))))) else (if i < 28 then (if i < 26 then (if i < 25 then decide (InPath q (70 : Vertex)) else decide (InPath q (71 : Vertex))) else (if i < 27 then decide (InPath q (72 : Vertex)) else decide (InPath q (73 : Vertex)))) else (if i < 30 then (if i < 29 then decide (InPath q (75 : Vertex)) else decide (InPath q (79 : Vertex))) else (if i < 31 then decide (InPath q (80 : Vertex)) else decide (InPath q (82 : Vertex))))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then decide (InPath q (84 : Vertex)) else decide (InPath q (85 : Vertex))) else (if i < 35 then decide (InPath q (88 : Vertex)) else decide (InPath q (90 : Vertex)))) else (if i < 38 then (if i < 37 then decide (InPath q (92 : Vertex)) else decide (InPath q (94 : Vertex))) else (if i < 39 then decide (InPath q (131 : Vertex)) else decide (InPath q (132 : Vertex))))) else (if i < 44 then (if i < 42 then (if i < 41 then decide (InPath q (133 : Vertex)) else decide (InPath q (134 : Vertex))) else (if i < 43 then decide (InPath q (135 : Vertex)) else decide (InPath q (136 : Vertex)))) else (if i < 46 then (if i < 45 then decide (InPath q (137 : Vertex)) else decide (InPath q (138 : Vertex))) else (if i < 47 then decide (InPath q (139 : Vertex)) else decide (InPath q (141 : Vertex)))))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then decide (InPath q (144 : Vertex)) else decide (InPath q (148 : Vertex))) else (if i < 51 then decide (InPath q (149 : Vertex)) else decide (InPath q (150 : Vertex)))) else (if i < 54 then (if i < 53 then decide (InPath q (151 : Vertex)) else decide (InPath q (152 : Vertex))) else (if i < 55 then decide (InPath q (154 : Vertex)) else decide (InPath q (158 : Vertex))))) else (if i < 60 then (if i < 58 then (if i < 57 then decide (InPath q (192 : Vertex)) else decide (InPath q (193 : Vertex))) else (if i < 59 then decide (InPath q (194 : Vertex)) else decide (InPath q (197 : Vertex)))) else (if i < 62 then (if i < 61 then decide (InPath q (202 : Vertex)) else decide (InPath q (204 : Vertex))) else (if i < 63 then decide (InPath q (206 : Vertex)) else decide (InPath q (207 : Vertex)))))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then decide (InPath q (208 : Vertex)) else decide (InPath q (222 : Vertex))) else (if i < 67 then decide (InPath q (228 : Vertex)) else decide (InPath q (229 : Vertex)))) else (if i < 70 then (if i < 69 then decide (InPath q (245 : Vertex)) else decide (InPath q (259 : Vertex))) else (if i < 71 then decide (InPath q (260 : Vertex)) else decide (InPath q (261 : Vertex))))) else (if i < 76 then (if i < 74 then (if i < 73 then decide (InPath q (262 : Vertex)) else decide (InPath q (263 : Vertex))) else (if i < 75 then decide (InPath q (264 : Vertex)) else decide (InPath q (265 : Vertex)))) else (if i < 78 then (if i < 77 then decide (InPath q (267 : Vertex)) else decide (InPath q (268 : Vertex))) else (if i < 79 then decide (InPath q (269 : Vertex)) else decide (InPath q (271 : Vertex)))))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then decide (InPath q (272 : Vertex)) else decide (InPath q (274 : Vertex))) else (if i < 83 then decide (InPath q (276 : Vertex)) else decide (InPath q (277 : Vertex)))) else (if i < 86 then (if i < 85 then decide (InPath q (278 : Vertex)) else decide (InPath q (279 : Vertex))) else (if i < 87 then decide (InPath q (280 : Vertex)) else decide (InPath q (281 : Vertex))))) else (if i < 92 then (if i < 90 then (if i < 89 then decide (InPath q (282 : Vertex)) else decide (InPath q (283 : Vertex))) else (if i < 91 then decide (InPath q (284 : Vertex)) else decide (InPath q (287 : Vertex)))) else (if i < 94 then (if i < 93 then decide (InPath q (320 : Vertex)) else decide (InPath q (321 : Vertex))) else (if i < 95 then decide (InPath q (322 : Vertex)) else decide (InPath q (325 : Vertex))))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then decide (InPath q (330 : Vertex)) else decide (InPath q (332 : Vertex))) else (if i < 99 then decide (InPath q (333 : Vertex)) else decide (InPath q (334 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (336 : Vertex)) else decide (InPath q (337 : Vertex))) else (if i < 103 then decide (InPath q (342 : Vertex)) else decide (InPath q (343 : Vertex))))) else (if i < 108 then (if i < 106 then (if i < 105 then decide (InPath q (345 : Vertex)) else decide (InPath q (347 : Vertex))) else (if i < 107 then decide (InPath q (348 : Vertex)) else decide (InPath q (350 : Vertex)))) else (if i < 110 then (if i < 109 then decide (InPath q (351 : Vertex)) else decide (InPath q (384 : Vertex))) else (if i < 111 then decide (InPath q (385 : Vertex)) else decide (InPath q (386 : Vertex)))))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then decide (InPath q (389 : Vertex)) else decide (InPath q (394 : Vertex))) else (if i < 115 then decide (InPath q (396 : Vertex)) else decide (InPath q (397 : Vertex)))) else (if i < 118 then (if i < 117 then decide (InPath q (398 : Vertex)) else decide (InPath q (399 : Vertex))) else (if i < 119 then decide (InPath q (400 : Vertex)) else decide (InPath q (401 : Vertex))))) else (if i < 124 then (if i < 122 then (if i < 121 then decide (InPath q (403 : Vertex)) else decide (InPath q (406 : Vertex))) else (if i < 123 then decide (InPath q (407 : Vertex)) else decide (InPath q (409 : Vertex)))) else (if i < 126 then (if i < 125 then decide (InPath q (411 : Vertex)) else decide (InPath q (412 : Vertex))) else (if i < 127 then decide (InPath q (414 : Vertex)) else decide (InPath q (415 : Vertex))))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then decide (InPath q (485 : Vertex)) else decide (BallClauseLogic.Endpoint q (0 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (1 : Vertex)) else decide (BallClauseLogic.Endpoint q (2 : Vertex)))) else (if i < 134 then (if i < 133 then decide (BallClauseLogic.Endpoint q (5 : Vertex)) else decide (BallClauseLogic.Endpoint q (8 : Vertex))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else decide (BallClauseLogic.Endpoint q (12 : Vertex))))) else (if i < 140 then (if i < 138 then (if i < 137 then decide (BallClauseLogic.Endpoint q (14 : Vertex)) else decide (BallClauseLogic.Endpoint q (15 : Vertex))) else (if i < 139 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex)))) else (if i < 142 then (if i < 141 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else decide (BallClauseLogic.Endpoint q (21 : Vertex))) else (if i < 143 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (23 : Vertex)))))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then decide (BallClauseLogic.Endpoint q (25 : Vertex)) else decide (BallClauseLogic.Endpoint q (27 : Vertex))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (31 : Vertex)) else decide (BallClauseLogic.Endpoint q (67 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (68 : Vertex)) else decide (BallClauseLogic.Endpoint q (69 : Vertex))))) else (if i < 156 then (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (70 : Vertex)) else decide (BallClauseLogic.Endpoint q (71 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else decide (BallClauseLogic.Endpoint q (73 : Vertex)))) else (if i < 158 then (if i < 157 then decide (BallClauseLogic.Endpoint q (75 : Vertex)) else decide (BallClauseLogic.Endpoint q (79 : Vertex))) else (if i < 159 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else decide (BallClauseLogic.Endpoint q (82 : Vertex))))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (85 : Vertex))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (88 : Vertex)) else decide (BallClauseLogic.Endpoint q (90 : Vertex)))) else (if i < 166 then (if i < 165 then decide (BallClauseLogic.Endpoint q (92 : Vertex)) else decide (BallClauseLogic.Endpoint q (94 : Vertex))) else (if i < 167 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex))))) else (if i < 172 then (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else decide (BallClauseLogic.Endpoint q (136 : Vertex)))) else (if i < 174 then (if i < 173 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (138 : Vertex))) else (if i < 175 then decide (BallClauseLogic.Endpoint q (139 : Vertex)) else decide (BallClauseLogic.Endpoint q (141 : Vertex)))))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex))) else (if i < 179 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else decide (BallClauseLogic.Endpoint q (150 : Vertex)))) else (if i < 182 then (if i < 181 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (152 : Vertex))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else decide (BallClauseLogic.Endpoint q (158 : Vertex))))) else (if i < 188 then (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else decide (BallClauseLogic.Endpoint q (193 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (194 : Vertex)) else decide (BallClauseLogic.Endpoint q (197 : Vertex)))) else (if i < 190 then (if i < 189 then decide (BallClauseLogic.Endpoint q (202 : Vertex)) else decide (BallClauseLogic.Endpoint q (204 : Vertex))) else (if i < 191 then decide (BallClauseLogic.Endpoint q (206 : Vertex)) else decide (BallClauseLogic.Endpoint q (207 : Vertex)))))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then decide (BallClauseLogic.Endpoint q (208 : Vertex)) else decide (BallClauseLogic.Endpoint q (222 : Vertex))) else (if i < 195 then decide (BallClauseLogic.Endpoint q (228 : Vertex)) else decide (BallClauseLogic.Endpoint q (229 : Vertex)))) else (if i < 198 then (if i < 197 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else decide (BallClauseLogic.Endpoint q (259 : Vertex))) else (if i < 199 then decide (BallClauseLogic.Endpoint q (260 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex))))) else (if i < 204 then (if i < 202 then (if i < 201 then decide (BallClauseLogic.Endpoint q (262 : Vertex)) else decide (BallClauseLogic.Endpoint q (263 : Vertex))) else (if i < 203 then decide (BallClauseLogic.Endpoint q (264 : Vertex)) else decide (BallClauseLogic.Endpoint q (265 : Vertex)))) else (if i < 206 then (if i < 205 then decide (BallClauseLogic.Endpoint q (267 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex))) else (if i < 207 then decide (BallClauseLogic.Endpoint q (269 : Vertex)) else decide (BallClauseLogic.Endpoint q (271 : Vertex)))))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (274 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else decide (BallClauseLogic.Endpoint q (277 : Vertex)))) else (if i < 214 then (if i < 213 then decide (BallClauseLogic.Endpoint q (278 : Vertex)) else decide (BallClauseLogic.Endpoint q (279 : Vertex))) else (if i < 215 then decide (BallClauseLogic.Endpoint q (280 : Vertex)) else decide (BallClauseLogic.Endpoint q (281 : Vertex))))) else (if i < 220 then (if i < 218 then (if i < 217 then decide (BallClauseLogic.Endpoint q (282 : Vertex)) else decide (BallClauseLogic.Endpoint q (283 : Vertex))) else (if i < 219 then decide (BallClauseLogic.Endpoint q (284 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex)))) else (if i < 222 then (if i < 221 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else decide (BallClauseLogic.Endpoint q (321 : Vertex))) else (if i < 223 then decide (BallClauseLogic.Endpoint q (322 : Vertex)) else decide (BallClauseLogic.Endpoint q (325 : Vertex))))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then decide (BallClauseLogic.Endpoint q (330 : Vertex)) else decide (BallClauseLogic.Endpoint q (332 : Vertex))) else (if i < 227 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (334 : Vertex)))) else (if i < 230 then (if i < 229 then decide (BallClauseLogic.Endpoint q (336 : Vertex)) else decide (BallClauseLogic.Endpoint q (337 : Vertex))) else (if i < 231 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (343 : Vertex))))) else (if i < 236 then (if i < 234 then (if i < 233 then decide (BallClauseLogic.Endpoint q (345 : Vertex)) else decide (BallClauseLogic.Endpoint q (347 : Vertex))) else (if i < 235 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else decide (BallClauseLogic.Endpoint q (350 : Vertex)))) else (if i < 238 then (if i < 237 then decide (BallClauseLogic.Endpoint q (351 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 239 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (386 : Vertex)))))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then decide (BallClauseLogic.Endpoint q (389 : Vertex)) else decide (BallClauseLogic.Endpoint q (394 : Vertex))) else (if i < 243 then decide (BallClauseLogic.Endpoint q (396 : Vertex)) else decide (BallClauseLogic.Endpoint q (397 : Vertex)))) else (if i < 246 then (if i < 245 then decide (BallClauseLogic.Endpoint q (398 : Vertex)) else decide (BallClauseLogic.Endpoint q (399 : Vertex))) else (if i < 247 then decide (BallClauseLogic.Endpoint q (400 : Vertex)) else decide (BallClauseLogic.Endpoint q (401 : Vertex))))) else (if i < 252 then (if i < 250 then (if i < 249 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else decide (BallClauseLogic.Endpoint q (406 : Vertex))) else (if i < 251 then decide (BallClauseLogic.Endpoint q (407 : Vertex)) else decide (BallClauseLogic.Endpoint q (409 : Vertex)))) else (if i < 254 then (if i < 253 then decide (BallClauseLogic.Endpoint q (411 : Vertex)) else decide (BallClauseLogic.Endpoint q (412 : Vertex))) else (if i < 255 then decide (BallClauseLogic.Endpoint q (414 : Vertex)) else (if i < 256 then decide (BallClauseLogic.Endpoint q (415 : Vertex)) else decide (BallClauseLogic.Endpoint q (485 : Vertex)))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count257 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [129, 130, 131]
def count261 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139]
def count275 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142, 143]
def count283 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]
def count285 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count287 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147]
def count291 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149, 150, 151]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count301 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]
def count315 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]
def count317 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count319 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163]
def count323 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167]
def count331 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count333 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171]
def count337 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171, 172, 173, 174, 175]
def count345 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]
def count347 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count349 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count351 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179]
def count353 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183]
def count359 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count369 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count377 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count379 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count381 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count383 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count385 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195]
def count387 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count389 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count391 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199]
def count393 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199]
def count395 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203]
def count401 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count403 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [204, 205, 206, 207]
def count407 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203, 204, 205, 206, 207]
def count409 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
def count411 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count413 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count415 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211]
def count417 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count419 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count421 (b : Nat → Bool) : Nat := countLit b [212, 213, 214, 215]
def count423 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211, 212, 213, 214, 215]
def count425 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count427 (b : Nat → Bool) : Nat := countLit b [218, 219]
def count429 (b : Nat → Bool) : Nat := countLit b [216, 217, 218, 219]
def count431 (b : Nat → Bool) : Nat := countLit b [220, 221]
def count433 (b : Nat → Bool) : Nat := countLit b [222, 223]
def count435 (b : Nat → Bool) : Nat := countLit b [220, 221, 222, 223]
def count437 (b : Nat → Bool) : Nat := countLit b [216, 217, 218, 219, 220, 221, 222, 223]
def count439 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
def count441 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
def count443 (b : Nat → Bool) : Nat := countLit b [224, 225]
def count445 (b : Nat → Bool) : Nat := countLit b [226, 227]
def count447 (b : Nat → Bool) : Nat := countLit b [224, 225, 226, 227]
def count449 (b : Nat → Bool) : Nat := countLit b [228, 229]
def count451 (b : Nat → Bool) : Nat := countLit b [230, 231]
def count453 (b : Nat → Bool) : Nat := countLit b [228, 229, 230, 231]
def count455 (b : Nat → Bool) : Nat := countLit b [224, 225, 226, 227, 228, 229, 230, 231]
def count457 (b : Nat → Bool) : Nat := countLit b [232, 233]
def count459 (b : Nat → Bool) : Nat := countLit b [234, 235]
def count461 (b : Nat → Bool) : Nat := countLit b [232, 233, 234, 235]
def count463 (b : Nat → Bool) : Nat := countLit b [236, 237]
def count465 (b : Nat → Bool) : Nat := countLit b [238, 239]
def count467 (b : Nat → Bool) : Nat := countLit b [236, 237, 238, 239]
def count469 (b : Nat → Bool) : Nat := countLit b [232, 233, 234, 235, 236, 237, 238, 239]
def count471 (b : Nat → Bool) : Nat := countLit b [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239]
def count473 (b : Nat → Bool) : Nat := countLit b [240, 241]
def count475 (b : Nat → Bool) : Nat := countLit b [242, 243]
def count477 (b : Nat → Bool) : Nat := countLit b [240, 241, 242, 243]
def count479 (b : Nat → Bool) : Nat := countLit b [244, 245]
def count481 (b : Nat → Bool) : Nat := countLit b [246, 247]
def count483 (b : Nat → Bool) : Nat := countLit b [244, 245, 246, 247]
def count485 (b : Nat → Bool) : Nat := countLit b [240, 241, 242, 243, 244, 245, 246, 247]
def count487 (b : Nat → Bool) : Nat := countLit b [248, 249]
def count489 (b : Nat → Bool) : Nat := countLit b [250, 251]
def count491 (b : Nat → Bool) : Nat := countLit b [248, 249, 250, 251]
def count493 (b : Nat → Bool) : Nat := countLit b [252, 253]
def count495 (b : Nat → Bool) : Nat := countLit b [254, 255]
def count497 (b : Nat → Bool) : Nat := countLit b [252, 253, 254, 255]
def count499 (b : Nat → Bool) : Nat := countLit b [248, 249, 250, 251, 252, 253, 254, 255]
def count501 (b : Nat → Bool) : Nat := countLit b [240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
def count503 (b : Nat → Bool) : Nat := countLit b [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
def count505 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
def count507 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255]
def count509 (b : Nat → Bool) : Nat := countLit b [1, 4]
def count511 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count513 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7]
def count517 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count519 (b : Nat → Bool) : Nat := countLit b [11, 15]
def count521 (b : Nat → Bool) : Nat := countLit b [9, 10, 11, 15]
def count525 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 10, 11, 15]
def count533 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count535 (b : Nat → Bool) : Nat := countLit b [22, 25]
def count537 (b : Nat → Bool) : Nat := countLit b [17, 19, 22, 25]
def count541 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count543 (b : Nat → Bool) : Nat := countLit b [30, 33]
def count545 (b : Nat → Bool) : Nat := countLit b [26, 28, 30, 33]
def count549 (b : Nat → Bool) : Nat := countLit b [17, 19, 22, 25, 26, 28, 30, 33]
def count557 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 10, 11, 15, 17, 19, 22, 25, 26, 28, 30, 33]
def count573 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count575 (b : Nat → Bool) : Nat := countLit b [39, 42]
def count577 (b : Nat → Bool) : Nat := countLit b [35, 36, 39, 42]
def count581 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count583 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count585 (b : Nat → Bool) : Nat := countLit b [43, 46, 47, 48]
def count589 (b : Nat → Bool) : Nat := countLit b [35, 36, 39, 42, 43, 46, 47, 48]
def count597 (b : Nat → Bool) : Nat := countLit b [50, 51]
def count599 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count601 (b : Nat → Bool) : Nat := countLit b [50, 51, 54, 56]
def count605 (b : Nat → Bool) : Nat := countLit b [59, 60]
def count607 (b : Nat → Bool) : Nat := countLit b [61, 63]
def count609 (b : Nat → Bool) : Nat := countLit b [59, 60, 61, 63]
def count613 (b : Nat → Bool) : Nat := countLit b [50, 51, 54, 56, 59, 60, 61, 63]
def count621 (b : Nat → Bool) : Nat := countLit b [35, 36, 39, 42, 43, 46, 47, 48, 50, 51, 54, 56, 59, 60, 61, 63]
def count637 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 10, 11, 15, 17, 19, 22, 25, 26, 28, 30, 33, 35, 36, 39, 42, 43, 46, 47, 48, 50, 51, 54, 56, 59, 60, 61, 63]
def count669 (b : Nat → Bool) : Nat := countLit b [65, 66]
def count671 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count673 (b : Nat → Bool) : Nat := countLit b [65, 66, 68, 70]
def count677 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count679 (b : Nat → Bool) : Nat := countLit b [76, 78]
def count681 (b : Nat → Bool) : Nat := countLit b [73, 74, 76, 78]
def count685 (b : Nat → Bool) : Nat := countLit b [65, 66, 68, 70, 73, 74, 76, 78]
def count693 (b : Nat → Bool) : Nat := countLit b [80, 83]
def count695 (b : Nat → Bool) : Nat := countLit b [84, 87]
def count697 (b : Nat → Bool) : Nat := countLit b [80, 83, 84, 87]
def count701 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count703 (b : Nat → Bool) : Nat := countLit b [91, 92]
def count705 (b : Nat → Bool) : Nat := countLit b [88, 90, 91, 92]
def count709 (b : Nat → Bool) : Nat := countLit b [80, 83, 84, 87, 88, 90, 91, 92]
def count717 (b : Nat → Bool) : Nat := countLit b [65, 66, 68, 70, 73, 74, 76, 78, 80, 83, 84, 87, 88, 90, 91, 92]
def count733 (b : Nat → Bool) : Nat := countLit b [95, 96]
def count735 (b : Nat → Bool) : Nat := countLit b [97, 101]
def count737 (b : Nat → Bool) : Nat := countLit b [95, 96, 97, 101]
def count741 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count743 (b : Nat → Bool) : Nat := countLit b [107, 109]
def count745 (b : Nat → Bool) : Nat := countLit b [103, 105, 107, 109]
def count749 (b : Nat → Bool) : Nat := countLit b [95, 96, 97, 101, 103, 105, 107, 109]
def count757 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count759 (b : Nat → Bool) : Nat := countLit b [114, 117]
def count761 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 117]
def count765 (b : Nat → Bool) : Nat := countLit b [119, 122]
def count767 (b : Nat → Bool) : Nat := countLit b [126, 128]
def count769 (b : Nat → Bool) : Nat := countLit b [124, 126, 128]
def count772 (b : Nat → Bool) : Nat := countLit b [119, 122, 124, 126, 128]
def count777 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 117, 119, 122, 124, 126, 128]
def count786 (b : Nat → Bool) : Nat := countLit b [95, 96, 97, 101, 103, 105, 107, 109, 112, 113, 114, 117, 119, 122, 124, 126, 128]
def count803 (b : Nat → Bool) : Nat := countLit b [65, 66, 68, 70, 73, 74, 76, 78, 80, 83, 84, 87, 88, 90, 91, 92, 95, 96, 97, 101, 103, 105, 107, 109, 112, 113, 114, 117, 119, 122, 124, 126, 128]
def count836 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 10, 11, 15, 17, 19, 22, 25, 26, 28, 30, 33, 35, 36, 39, 42, 43, 46, 47, 48, 50, 51, 54, 56, 59, 60, 61, 63, 65, 66, 68, 70, 73, 74, 76, 78, 80, 83, 84, 87, 88, 90, 91, 92, 95, 96, 97, 101, 103, 105, 107, 109, 112, 113, 114, 117, 119, 122, 124, 126, 128]
def count878 (b : Nat → Bool) : Nat := countLit b [-1, -4]
def count880 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count882 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7]
def count886 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count888 (b : Nat → Bool) : Nat := countLit b [-11, -15]
def count890 (b : Nat → Bool) : Nat := countLit b [-9, -10, -11, -15]
def count894 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -10, -11, -15]
def count902 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count904 (b : Nat → Bool) : Nat := countLit b [-22, -25]
def count906 (b : Nat → Bool) : Nat := countLit b [-17, -19, -22, -25]
def count910 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count912 (b : Nat → Bool) : Nat := countLit b [-30, -33]
def count914 (b : Nat → Bool) : Nat := countLit b [-26, -28, -30, -33]
def count918 (b : Nat → Bool) : Nat := countLit b [-17, -19, -22, -25, -26, -28, -30, -33]
def count926 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]
def count942 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count944 (b : Nat → Bool) : Nat := countLit b [-39, -42]
def count946 (b : Nat → Bool) : Nat := countLit b [-35, -36, -39, -42]
def count950 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count952 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count954 (b : Nat → Bool) : Nat := countLit b [-43, -46, -47, -48]
def count958 (b : Nat → Bool) : Nat := countLit b [-35, -36, -39, -42, -43, -46, -47, -48]
def count966 (b : Nat → Bool) : Nat := countLit b [-50, -51]
def count968 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count970 (b : Nat → Bool) : Nat := countLit b [-50, -51, -54, -56]
def count974 (b : Nat → Bool) : Nat := countLit b [-59, -60]
def count976 (b : Nat → Bool) : Nat := countLit b [-61, -63]
def count978 (b : Nat → Bool) : Nat := countLit b [-59, -60, -61, -63]
def count982 (b : Nat → Bool) : Nat := countLit b [-50, -51, -54, -56, -59, -60, -61, -63]
def count990 (b : Nat → Bool) : Nat := countLit b [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -63]
def count1006 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -63]
def count1031 (b : Nat → Bool) : Nat := countLit b [-65, -66]
def count1033 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count1035 (b : Nat → Bool) : Nat := countLit b [-65, -66, -68, -70]
def count1039 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count1041 (b : Nat → Bool) : Nat := countLit b [-76, -78]
def count1043 (b : Nat → Bool) : Nat := countLit b [-73, -74, -76, -78]
def count1047 (b : Nat → Bool) : Nat := countLit b [-65, -66, -68, -70, -73, -74, -76, -78]
def count1055 (b : Nat → Bool) : Nat := countLit b [-80, -83]
def count1057 (b : Nat → Bool) : Nat := countLit b [-84, -87]
def count1059 (b : Nat → Bool) : Nat := countLit b [-80, -83, -84, -87]
def count1063 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count1065 (b : Nat → Bool) : Nat := countLit b [-91, -92]
def count1067 (b : Nat → Bool) : Nat := countLit b [-88, -90, -91, -92]
def count1071 (b : Nat → Bool) : Nat := countLit b [-80, -83, -84, -87, -88, -90, -91, -92]
def count1079 (b : Nat → Bool) : Nat := countLit b [-65, -66, -68, -70, -73, -74, -76, -78, -80, -83, -84, -87, -88, -90, -91, -92]
def count1095 (b : Nat → Bool) : Nat := countLit b [-95, -96]
def count1097 (b : Nat → Bool) : Nat := countLit b [-97, -101]
def count1099 (b : Nat → Bool) : Nat := countLit b [-95, -96, -97, -101]
def count1103 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count1105 (b : Nat → Bool) : Nat := countLit b [-107, -109]
def count1107 (b : Nat → Bool) : Nat := countLit b [-103, -105, -107, -109]
def count1111 (b : Nat → Bool) : Nat := countLit b [-95, -96, -97, -101, -103, -105, -107, -109]
def count1119 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1121 (b : Nat → Bool) : Nat := countLit b [-114, -117]
def count1123 (b : Nat → Bool) : Nat := countLit b [-112, -113, -114, -117]
def count1127 (b : Nat → Bool) : Nat := countLit b [-119, -122]
def count1129 (b : Nat → Bool) : Nat := countLit b [-126, -128]
def count1131 (b : Nat → Bool) : Nat := countLit b [-124, -126, -128]
def count1134 (b : Nat → Bool) : Nat := countLit b [-119, -122, -124, -126, -128]
def count1139 (b : Nat → Bool) : Nat := countLit b [-112, -113, -114, -117, -119, -122, -124, -126, -128]
def count1148 (b : Nat → Bool) : Nat := countLit b [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -117, -119, -122, -124, -126, -128]
def count1165 (b : Nat → Bool) : Nat := countLit b [-65, -66, -68, -70, -73, -74, -76, -78, -80, -83, -84, -87, -88, -90, -91, -92, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -117, -119, -122, -124, -126, -128]
def count1190 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -63, -65, -66, -68, -70, -73, -74, -76, -78, -80, -83, -84, -87, -88, -90, -91, -92, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -117, -119, -122, -124, -126, -128]
def count1215 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count1217 (b : Nat → Bool) : Nat := countLit b [2, 3, 5]
def count1220 (b : Nat → Bool) : Nat := countLit b [8, 12]
def count1222 (b : Nat → Bool) : Nat := countLit b [13, 14]
def count1224 (b : Nat → Bool) : Nat := countLit b [8, 12, 13, 14]
def count1228 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 12, 13, 14]
def count1235 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count1237 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count1239 (b : Nat → Bool) : Nat := countLit b [16, 18, 20, 21]
def count1243 (b : Nat → Bool) : Nat := countLit b [23, 24]
def count1245 (b : Nat → Bool) : Nat := countLit b [27, 29]
def count1247 (b : Nat → Bool) : Nat := countLit b [23, 24, 27, 29]
def count1251 (b : Nat → Bool) : Nat := countLit b [16, 18, 20, 21, 23, 24, 27, 29]
def count1259 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 12, 13, 14, 16, 18, 20, 21, 23, 24, 27, 29]
def count1274 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count1276 (b : Nat → Bool) : Nat := countLit b [34, 37]
def count1278 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37]
def count1282 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count1284 (b : Nat → Bool) : Nat := countLit b [41, 44]
def count1286 (b : Nat → Bool) : Nat := countLit b [38, 40, 41, 44]
def count1290 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37, 38, 40, 41, 44]
def count1298 (b : Nat → Bool) : Nat := countLit b [45, 49]
def count1300 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count1302 (b : Nat → Bool) : Nat := countLit b [45, 49, 52, 53]
def count1306 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count1308 (b : Nat → Bool) : Nat := countLit b [58, 62]
def count1310 (b : Nat → Bool) : Nat := countLit b [55, 57, 58, 62]
def count1314 (b : Nat → Bool) : Nat := countLit b [45, 49, 52, 53, 55, 57, 58, 62]
def count1322 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37, 38, 40, 41, 44, 45, 49, 52, 53, 55, 57, 58, 62]
def count1338 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 12, 13, 14, 16, 18, 20, 21, 23, 24, 27, 29, 31, 32, 34, 37, 38, 40, 41, 44, 45, 49, 52, 53, 55, 57, 58, 62]
def count1369 (b : Nat → Bool) : Nat := countLit b [64, 67]
def count1371 (b : Nat → Bool) : Nat := countLit b [69, 71]
def count1373 (b : Nat → Bool) : Nat := countLit b [64, 67, 69, 71]
def count1377 (b : Nat → Bool) : Nat := countLit b [72, 75]
def count1379 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count1381 (b : Nat → Bool) : Nat := countLit b [72, 75, 77, 79]
def count1385 (b : Nat → Bool) : Nat := countLit b [64, 67, 69, 71, 72, 75, 77, 79]
def count1393 (b : Nat → Bool) : Nat := countLit b [81, 82]
def count1395 (b : Nat → Bool) : Nat := countLit b [85, 86]
def count1397 (b : Nat → Bool) : Nat := countLit b [81, 82, 85, 86]
def count1401 (b : Nat → Bool) : Nat := countLit b [89, 93]
def count1403 (b : Nat → Bool) : Nat := countLit b [94, 98]
def count1405 (b : Nat → Bool) : Nat := countLit b [89, 93, 94, 98]
def count1409 (b : Nat → Bool) : Nat := countLit b [81, 82, 85, 86, 89, 93, 94, 98]
def count1417 (b : Nat → Bool) : Nat := countLit b [64, 67, 69, 71, 72, 75, 77, 79, 81, 82, 85, 86, 89, 93, 94, 98]
def count1433 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count1435 (b : Nat → Bool) : Nat := countLit b [102, 104]
def count1437 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 104]
def count1441 (b : Nat → Bool) : Nat := countLit b [106, 108]
def count1443 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count1445 (b : Nat → Bool) : Nat := countLit b [106, 108, 110, 111]
def count1449 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 104, 106, 108, 110, 111]
def count1457 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count1459 (b : Nat → Bool) : Nat := countLit b [118, 120]
def count1461 (b : Nat → Bool) : Nat := countLit b [115, 116, 118, 120]
def count1465 (b : Nat → Bool) : Nat := countLit b [121, 123]
def count1467 (b : Nat → Bool) : Nat := countLit b [125, 127]
def count1469 (b : Nat → Bool) : Nat := countLit b [121, 123, 125, 127]
def count1473 (b : Nat → Bool) : Nat := countLit b [115, 116, 118, 120, 121, 123, 125, 127]
def count1481 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 104, 106, 108, 110, 111, 115, 116, 118, 120, 121, 123, 125, 127]
def count1497 (b : Nat → Bool) : Nat := countLit b [64, 67, 69, 71, 72, 75, 77, 79, 81, 82, 85, 86, 89, 93, 94, 98, 99, 100, 102, 104, 106, 108, 110, 111, 115, 116, 118, 120, 121, 123, 125, 127]
def count1529 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 12, 13, 14, 16, 18, 20, 21, 23, 24, 27, 29, 31, 32, 34, 37, 38, 40, 41, 44, 45, 49, 52, 53, 55, 57, 58, 62, 64, 67, 69, 71, 72, 75, 77, 79, 81, 82, 85, 86, 89, 93, 94, 98, 99, 100, 102, 104, 106, 108, 110, 111, 115, 116, 118, 120, 121, 123, 125, 127]
def count1571 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count1573 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5]
def count1576 (b : Nat → Bool) : Nat := countLit b [-8, -12]
def count1578 (b : Nat → Bool) : Nat := countLit b [-13, -14]
def count1580 (b : Nat → Bool) : Nat := countLit b [-8, -12, -13, -14]
def count1584 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -12, -13, -14]
def count1591 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1593 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count1595 (b : Nat → Bool) : Nat := countLit b [-16, -18, -20, -21]
def count1599 (b : Nat → Bool) : Nat := countLit b [-23, -24]
def count1601 (b : Nat → Bool) : Nat := countLit b [-27, -29]
def count1603 (b : Nat → Bool) : Nat := countLit b [-23, -24, -27, -29]
def count1607 (b : Nat → Bool) : Nat := countLit b [-16, -18, -20, -21, -23, -24, -27, -29]
def count1615 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]
def count1630 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count1632 (b : Nat → Bool) : Nat := countLit b [-34, -37]
def count1634 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37]
def count1638 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1640 (b : Nat → Bool) : Nat := countLit b [-41, -44]
def count1642 (b : Nat → Bool) : Nat := countLit b [-38, -40, -41, -44]
def count1646 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37, -38, -40, -41, -44]
def count1654 (b : Nat → Bool) : Nat := countLit b [-45, -49]
def count1656 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count1658 (b : Nat → Bool) : Nat := countLit b [-45, -49, -52, -53]
def count1662 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count1664 (b : Nat → Bool) : Nat := countLit b [-58, -62]
def count1666 (b : Nat → Bool) : Nat := countLit b [-55, -57, -58, -62]
def count1670 (b : Nat → Bool) : Nat := countLit b [-45, -49, -52, -53, -55, -57, -58, -62]
def count1678 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]
def count1694 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]
def count1717 (b : Nat → Bool) : Nat := countLit b [-64, -67]
def count1719 (b : Nat → Bool) : Nat := countLit b [-69, -71]
def count1721 (b : Nat → Bool) : Nat := countLit b [-64, -67, -69, -71]
def count1725 (b : Nat → Bool) : Nat := countLit b [-72, -75]
def count1727 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count1729 (b : Nat → Bool) : Nat := countLit b [-72, -75, -77, -79]
def count1733 (b : Nat → Bool) : Nat := countLit b [-64, -67, -69, -71, -72, -75, -77, -79]
def count1741 (b : Nat → Bool) : Nat := countLit b [-81, -82]
def count1743 (b : Nat → Bool) : Nat := countLit b [-85, -86]
def count1745 (b : Nat → Bool) : Nat := countLit b [-81, -82, -85, -86]
def count1749 (b : Nat → Bool) : Nat := countLit b [-89, -93]
def count1751 (b : Nat → Bool) : Nat := countLit b [-94, -98]
def count1753 (b : Nat → Bool) : Nat := countLit b [-89, -93, -94, -98]
def count1757 (b : Nat → Bool) : Nat := countLit b [-81, -82, -85, -86, -89, -93, -94, -98]
def count1765 (b : Nat → Bool) : Nat := countLit b [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98]
def count1781 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1783 (b : Nat → Bool) : Nat := countLit b [-102, -104]
def count1785 (b : Nat → Bool) : Nat := countLit b [-99, -100, -102, -104]
def count1789 (b : Nat → Bool) : Nat := countLit b [-106, -108]
def count1791 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count1793 (b : Nat → Bool) : Nat := countLit b [-106, -108, -110, -111]
def count1797 (b : Nat → Bool) : Nat := countLit b [-99, -100, -102, -104, -106, -108, -110, -111]
def count1805 (b : Nat → Bool) : Nat := countLit b [-115, -116]
def count1807 (b : Nat → Bool) : Nat := countLit b [-118, -120]
def count1809 (b : Nat → Bool) : Nat := countLit b [-115, -116, -118, -120]
def count1813 (b : Nat → Bool) : Nat := countLit b [-121, -123]
def count1815 (b : Nat → Bool) : Nat := countLit b [-125, -127]
def count1817 (b : Nat → Bool) : Nat := countLit b [-121, -123, -125, -127]
def count1821 (b : Nat → Bool) : Nat := countLit b [-115, -116, -118, -120, -121, -123, -125, -127]
def count1829 (b : Nat → Bool) : Nat := countLit b [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]
def count1845 (b : Nat → Bool) : Nat := countLit b [-64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]
def count1868 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62, -64, -67, -69, -71, -72, -75, -77, -79, -81, -82, -85, -86, -89, -93, -94, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -123, -125, -127]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 945 then (if i < 472 then (if i < 236 then (if i < 118 then (if i < 59 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 25 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else b 24)) else (if i < 27 then (if i < 26 then b 25 else b 26) else (if i < 28 then b 27 else b 28))))) else (if i < 44 then (if i < 36 then (if i < 32 then (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)) else (if i < 34 then (if i < 33 then b 32 else b 33) else (if i < 35 then b 34 else b 35))) else (if i < 40 then (if i < 38 then (if i < 37 then b 36 else b 37) else (if i < 39 then b 38 else b 39)) else (if i < 42 then (if i < 41 then b 40 else b 41) else (if i < 43 then b 42 else b 43)))) else (if i < 51 then (if i < 47 then (if i < 45 then b 44 else (if i < 46 then b 45 else b 46)) else (if i < 49 then (if i < 48 then b 47 else b 48) else (if i < 50 then b 49 else b 50))) else (if i < 55 then (if i < 53 then (if i < 52 then b 51 else b 52) else (if i < 54 then b 53 else b 54)) else (if i < 57 then (if i < 56 then b 55 else b 56) else (if i < 58 then b 57 else b 58)))))) else (if i < 88 then (if i < 73 then (if i < 66 then (if i < 62 then (if i < 60 then b 59 else (if i < 61 then b 60 else b 61)) else (if i < 64 then (if i < 63 then b 62 else b 63) else (if i < 65 then b 64 else b 65))) else (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 71 then (if i < 70 then b 69 else b 70) else (if i < 72 then b 71 else b 72)))) else (if i < 80 then (if i < 76 then (if i < 74 then b 73 else (if i < 75 then b 74 else b 75)) else (if i < 78 then (if i < 77 then b 76 else b 77) else (if i < 79 then b 78 else b 79))) else (if i < 84 then (if i < 82 then (if i < 81 then b 80 else b 81) else (if i < 83 then b 82 else b 83)) else (if i < 86 then (if i < 85 then b 84 else b 85) else (if i < 87 then b 86 else b 87))))) else (if i < 103 then (if i < 95 then (if i < 91 then (if i < 89 then b 88 else (if i < 90 then b 89 else b 90)) else (if i < 93 then (if i < 92 then b 91 else b 92) else (if i < 94 then b 93 else b 94))) else (if i < 99 then (if i < 97 then (if i < 96 then b 95 else b 96) else (if i < 98 then b 97 else b 98)) else (if i < 101 then (if i < 100 then b 99 else b 100) else (if i < 102 then b 101 else b 102)))) else (if i < 110 then (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 108 then (if i < 107 then b 106 else b 107) else (if i < 109 then b 108 else b 109))) else (if i < 114 then (if i < 112 then (if i < 111 then b 110 else b 111) else (if i < 113 then b 112 else b 113)) else (if i < 116 then (if i < 115 then b 114 else b 115) else (if i < 117 then b 116 else b 117))))))) else (if i < 177 then (if i < 147 then (if i < 132 then (if i < 125 then (if i < 121 then (if i < 119 then b 118 else (if i < 120 then b 119 else b 120)) else (if i < 123 then (if i < 122 then b 121 else b 122) else (if i < 124 then b 123 else b 124))) else (if i < 128 then (if i < 126 then b 125 else (if i < 127 then b 126 else b 127)) else (if i < 130 then (if i < 129 then b 128 else b 129) else (if i < 131 then b 130 else b 131)))) else (if i < 139 then (if i < 135 then (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)) else (if i < 137 then (if i < 136 then b 135 else b 136) else (if i < 138 then b 137 else b 138))) else (if i < 143 then (if i < 141 then (if i < 140 then b 139 else b 140) else (if i < 142 then b 141 else b 142)) else (if i < 145 then (if i < 144 then b 143 else b 144) else (if i < 146 then b 145 else b 146))))) else (if i < 162 then (if i < 154 then (if i < 150 then (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)) else (if i < 152 then (if i < 151 then b 150 else b 151) else (if i < 153 then b 152 else b 153))) else (if i < 158 then (if i < 156 then (if i < 155 then b 154 else b 155) else (if i < 157 then b 156 else b 157)) else (if i < 160 then (if i < 159 then b 158 else b 159) else (if i < 161 then b 160 else b 161)))) else (if i < 169 then (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 167 then (if i < 166 then b 165 else b 166) else (if i < 168 then b 167 else b 168))) else (if i < 173 then (if i < 171 then (if i < 170 then b 169 else b 170) else (if i < 172 then b 171 else b 172)) else (if i < 175 then (if i < 174 then b 173 else b 174) else (if i < 176 then b 175 else b 176)))))) else (if i < 206 then (if i < 191 then (if i < 184 then (if i < 180 then (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)) else (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else b 183))) else (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 189 then (if i < 188 then b 187 else b 188) else (if i < 190 then b 189 else b 190)))) else (if i < 198 then (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else b 197))) else (if i < 202 then (if i < 200 then (if i < 199 then b 198 else b 199) else (if i < 201 then b 200 else b 201)) else (if i < 204 then (if i < 203 then b 202 else b 203) else (if i < 205 then b 204 else b 205))))) else (if i < 221 then (if i < 213 then (if i < 209 then (if i < 207 then b 206 else (if i < 208 then b 207 else b 208)) else (if i < 211 then (if i < 210 then b 209 else b 210) else (if i < 212 then b 211 else b 212))) else (if i < 217 then (if i < 215 then (if i < 214 then b 213 else b 214) else (if i < 216 then b 215 else b 216)) else (if i < 219 then (if i < 218 then b 217 else b 218) else (if i < 220 then b 219 else b 220)))) else (if i < 228 then (if i < 224 then (if i < 222 then b 221 else (if i < 223 then b 222 else b 223)) else (if i < 226 then (if i < 225 then b 224 else b 225) else (if i < 227 then b 226 else b 227))) else (if i < 232 then (if i < 230 then (if i < 229 then b 228 else b 229) else (if i < 231 then b 230 else b 231)) else (if i < 234 then (if i < 233 then b 232 else b 233) else (if i < 235 then b 234 else b 235)))))))) else (if i < 354 then (if i < 295 then (if i < 265 then (if i < 250 then (if i < 243 then (if i < 239 then (if i < 237 then b 236 else (if i < 238 then b 237 else b 238)) else (if i < 241 then (if i < 240 then b 239 else b 240) else (if i < 242 then b 241 else b 242))) else (if i < 246 then (if i < 244 then b 243 else (if i < 245 then b 244 else b 245)) else (if i < 248 then (if i < 247 then b 246 else b 247) else (if i < 249 then b 248 else b 249)))) else (if i < 257 then (if i < 253 then (if i < 251 then b 250 else (if i < 252 then b 251 else b 252)) else (if i < 255 then (if i < 254 then b 253 else b 254) else (if i < 256 then b 255 else b 256))) else (if i < 261 then (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 263 then (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b)) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)))))) else (if i < 280 then (if i < 272 then (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 270 then (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)))) else (if i < 276 then (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 278 then (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))))) else (if i < 287 then (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))) else (if i < 291 then (if i < 289 then (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))) else (if i < 293 then (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b))))))) else (if i < 324 then (if i < 309 then (if i < 302 then (if i < 298 then (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))) else (if i < 300 then (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b)) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))) else (if i < 305 then (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))) else (if i < 307 then (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))))) else (if i < 316 then (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 314 then (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)))) else (if i < 320 then (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b))) else (if i < 322 then (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b)) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)))))) else (if i < 339 then (if i < 331 then (if i < 327 then (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))) else (if i < 329 then (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)))) else (if i < 335 then (if i < 333 then (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 337 then (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))))) else (if i < 346 then (if i < 342 then (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b))) else (if i < 344 then (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b)) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b)))) else (if i < 350 then (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))))))) else (if i < 413 then (if i < 383 then (if i < 368 then (if i < 361 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 359 then (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))) else (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 366 then (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))))) else (if i < 375 then (if i < 371 then (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))) else (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)))) else (if i < 379 then (if i < 377 then (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b))) else (if i < 381 then (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b)) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))))) else (if i < 398 then (if i < 390 then (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 388 then (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b)))) else (if i < 394 then (if i < 392 then (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b)) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 396 then (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b)) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))))) else (if i < 405 then (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 403 then (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b)) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b)))) else (if i < 409 then (if i < 407 then (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b)) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))) else (if i < 411 then (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))))))) else (if i < 442 then (if i < 427 then (if i < 420 then (if i < 416 then (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b))) else (if i < 418 then (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)) else (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)))) else (if i < 423 then (if i < 421 then decide (2 ≤ count419 b) else (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b))) else (if i < 425 then (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b)) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b))))) else (if i < 434 then (if i < 430 then (if i < 428 then decide (1 ≤ count427 b) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b))) else (if i < 432 then (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b)))) else (if i < 438 then (if i < 436 then (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b)) else (if i < 437 then decide (2 ≤ count435 b) else decide (1 ≤ count437 b))) else (if i < 440 then (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b)) else (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)))))) else (if i < 457 then (if i < 449 then (if i < 445 then (if i < 443 then decide (2 ≤ count441 b) else (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b))) else (if i < 447 then (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b)) else (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b)))) else (if i < 453 then (if i < 451 then (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b))) else (if i < 455 then (if i < 454 then decide (1 ≤ count453 b) else decide (2 ≤ count453 b)) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b))))) else (if i < 464 then (if i < 460 then (if i < 458 then decide (1 ≤ count457 b) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b))) else (if i < 462 then (if i < 461 then decide (2 ≤ count459 b) else decide (1 ≤ count461 b)) else (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b)))) else (if i < 468 then (if i < 466 then (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b)) else (if i < 467 then decide (2 ≤ count465 b) else decide (1 ≤ count467 b))) else (if i < 470 then (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b)) else (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b)))))))))) else (if i < 708 then (if i < 590 then (if i < 531 then (if i < 501 then (if i < 486 then (if i < 479 then (if i < 475 then (if i < 473 then decide (2 ≤ count471 b) else (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b))) else (if i < 477 then (if i < 476 then decide (1 ≤ count475 b) else decide (2 ≤ count475 b)) else (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b)))) else (if i < 482 then (if i < 480 then decide (1 ≤ count479 b) else (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b))) else (if i < 484 then (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b)) else (if i < 485 then decide (2 ≤ count483 b) else decide (1 ≤ count485 b))))) else (if i < 493 then (if i < 489 then (if i < 487 then decide (2 ≤ count485 b) else (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b))) else (if i < 491 then (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b)) else (if i < 492 then decide (1 ≤ count491 b) else decide (2 ≤ count491 b)))) else (if i < 497 then (if i < 495 then (if i < 494 then decide (1 ≤ count493 b) else decide (2 ≤ count493 b)) else (if i < 496 then decide (1 ≤ count495 b) else decide (2 ≤ count495 b))) else (if i < 499 then (if i < 498 then decide (1 ≤ count497 b) else decide (2 ≤ count497 b)) else (if i < 500 then decide (1 ≤ count499 b) else decide (2 ≤ count499 b)))))) else (if i < 516 then (if i < 508 then (if i < 504 then (if i < 502 then decide (1 ≤ count501 b) else (if i < 503 then decide (2 ≤ count501 b) else decide (1 ≤ count503 b))) else (if i < 506 then (if i < 505 then decide (2 ≤ count503 b) else decide (1 ≤ count505 b)) else (if i < 507 then decide (2 ≤ count505 b) else decide (1 ≤ count507 b)))) else (if i < 512 then (if i < 510 then (if i < 509 then decide (2 ≤ count507 b) else decide (1 ≤ count509 b)) else (if i < 511 then decide (2 ≤ count509 b) else decide (1 ≤ count511 b))) else (if i < 514 then (if i < 513 then decide (2 ≤ count511 b) else decide (1 ≤ count513 b)) else (if i < 515 then decide (2 ≤ count513 b) else decide (3 ≤ count513 b))))) else (if i < 523 then (if i < 519 then (if i < 517 then decide (4 ≤ count513 b) else (if i < 518 then decide (1 ≤ count517 b) else decide (2 ≤ count517 b))) else (if i < 521 then (if i < 520 then decide (1 ≤ count519 b) else decide (2 ≤ count519 b)) else (if i < 522 then decide (1 ≤ count521 b) else decide (2 ≤ count521 b)))) else (if i < 527 then (if i < 525 then (if i < 524 then decide (3 ≤ count521 b) else decide (4 ≤ count521 b)) else (if i < 526 then decide (1 ≤ count525 b) else decide (2 ≤ count525 b))) else (if i < 529 then (if i < 528 then decide (3 ≤ count525 b) else decide (4 ≤ count525 b)) else (if i < 530 then decide (5 ≤ count525 b) else decide (6 ≤ count525 b))))))) else (if i < 560 then (if i < 545 then (if i < 538 then (if i < 534 then (if i < 532 then decide (7 ≤ count525 b) else (if i < 533 then decide (8 ≤ count525 b) else decide (1 ≤ count533 b))) else (if i < 536 then (if i < 535 then decide (2 ≤ count533 b) else decide (1 ≤ count535 b)) else (if i < 537 then decide (2 ≤ count535 b) else decide (1 ≤ count537 b)))) else (if i < 541 then (if i < 539 then decide (2 ≤ count537 b) else (if i < 540 then decide (3 ≤ count537 b) else decide (4 ≤ count537 b))) else (if i < 543 then (if i < 542 then decide (1 ≤ count541 b) else decide (2 ≤ count541 b)) else (if i < 544 then decide (1 ≤ count543 b) else decide (2 ≤ count543 b))))) else (if i < 552 then (if i < 548 then (if i < 546 then decide (1 ≤ count545 b) else (if i < 547 then decide (2 ≤ count545 b) else decide (3 ≤ count545 b))) else (if i < 550 then (if i < 549 then decide (4 ≤ count545 b) else decide (1 ≤ count549 b)) else (if i < 551 then decide (2 ≤ count549 b) else decide (3 ≤ count549 b)))) else (if i < 556 then (if i < 554 then (if i < 553 then decide (4 ≤ count549 b) else decide (5 ≤ count549 b)) else (if i < 555 then decide (6 ≤ count549 b) else decide (7 ≤ count549 b))) else (if i < 558 then (if i < 557 then decide (8 ≤ count549 b) else decide (1 ≤ count557 b)) else (if i < 559 then decide (2 ≤ count557 b) else decide (3 ≤ count557 b)))))) else (if i < 575 then (if i < 567 then (if i < 563 then (if i < 561 then decide (4 ≤ count557 b) else (if i < 562 then decide (5 ≤ count557 b) else decide (6 ≤ count557 b))) else (if i < 565 then (if i < 564 then decide (7 ≤ count557 b) else decide (8 ≤ count557 b)) else (if i < 566 then decide (9 ≤ count557 b) else decide (10 ≤ count557 b)))) else (if i < 571 then (if i < 569 then (if i < 568 then decide (11 ≤ count557 b) else decide (12 ≤ count557 b)) else (if i < 570 then decide (13 ≤ count557 b) else decide (14 ≤ count557 b))) else (if i < 573 then (if i < 572 then decide (15 ≤ count557 b) else decide (16 ≤ count557 b)) else (if i < 574 then decide (1 ≤ count573 b) else decide (2 ≤ count573 b))))) else (if i < 582 then (if i < 578 then (if i < 576 then decide (1 ≤ count575 b) else (if i < 577 then decide (2 ≤ count575 b) else decide (1 ≤ count577 b))) else (if i < 580 then (if i < 579 then decide (2 ≤ count577 b) else decide (3 ≤ count577 b)) else (if i < 581 then decide (4 ≤ count577 b) else decide (1 ≤ count581 b)))) else (if i < 586 then (if i < 584 then (if i < 583 then decide (2 ≤ count581 b) else decide (1 ≤ count583 b)) else (if i < 585 then decide (2 ≤ count583 b) else decide (1 ≤ count585 b))) else (if i < 588 then (if i < 587 then decide (2 ≤ count585 b) else decide (3 ≤ count585 b)) else (if i < 589 then decide (4 ≤ count585 b) else decide (1 ≤ count589 b)))))))) else (if i < 649 then (if i < 619 then (if i < 604 then (if i < 597 then (if i < 593 then (if i < 591 then decide (2 ≤ count589 b) else (if i < 592 then decide (3 ≤ count589 b) else decide (4 ≤ count589 b))) else (if i < 595 then (if i < 594 then decide (5 ≤ count589 b) else decide (6 ≤ count589 b)) else (if i < 596 then decide (7 ≤ count589 b) else decide (8 ≤ count589 b)))) else (if i < 600 then (if i < 598 then decide (1 ≤ count597 b) else (if i < 599 then decide (2 ≤ count597 b) else decide (1 ≤ count599 b))) else (if i < 602 then (if i < 601 then decide (2 ≤ count599 b) else decide (1 ≤ count601 b)) else (if i < 603 then decide (2 ≤ count601 b) else decide (3 ≤ count601 b))))) else (if i < 611 then (if i < 607 then (if i < 605 then decide (4 ≤ count601 b) else (if i < 606 then decide (1 ≤ count605 b) else decide (2 ≤ count605 b))) else (if i < 609 then (if i < 608 then decide (1 ≤ count607 b) else decide (2 ≤ count607 b)) else (if i < 610 then decide (1 ≤ count609 b) else decide (2 ≤ count609 b)))) else (if i < 615 then (if i < 613 then (if i < 612 then decide (3 ≤ count609 b) else decide (4 ≤ count609 b)) else (if i < 614 then decide (1 ≤ count613 b) else decide (2 ≤ count613 b))) else (if i < 617 then (if i < 616 then decide (3 ≤ count613 b) else decide (4 ≤ count613 b)) else (if i < 618 then decide (5 ≤ count613 b) else decide (6 ≤ count613 b)))))) else (if i < 634 then (if i < 626 then (if i < 622 then (if i < 620 then decide (7 ≤ count613 b) else (if i < 621 then decide (8 ≤ count613 b) else decide (1 ≤ count621 b))) else (if i < 624 then (if i < 623 then decide (2 ≤ count621 b) else decide (3 ≤ count621 b)) else (if i < 625 then decide (4 ≤ count621 b) else decide (5 ≤ count621 b)))) else (if i < 630 then (if i < 628 then (if i < 627 then decide (6 ≤ count621 b) else decide (7 ≤ count621 b)) else (if i < 629 then decide (8 ≤ count621 b) else decide (9 ≤ count621 b))) else (if i < 632 then (if i < 631 then decide (10 ≤ count621 b) else decide (11 ≤ count621 b)) else (if i < 633 then decide (12 ≤ count621 b) else decide (13 ≤ count621 b))))) else (if i < 641 then (if i < 637 then (if i < 635 then decide (14 ≤ count621 b) else (if i < 636 then decide (15 ≤ count621 b) else decide (16 ≤ count621 b))) else (if i < 639 then (if i < 638 then decide (1 ≤ count637 b) else decide (2 ≤ count637 b)) else (if i < 640 then decide (3 ≤ count637 b) else decide (4 ≤ count637 b)))) else (if i < 645 then (if i < 643 then (if i < 642 then decide (5 ≤ count637 b) else decide (6 ≤ count637 b)) else (if i < 644 then decide (7 ≤ count637 b) else decide (8 ≤ count637 b))) else (if i < 647 then (if i < 646 then decide (9 ≤ count637 b) else decide (10 ≤ count637 b)) else (if i < 648 then decide (11 ≤ count637 b) else decide (12 ≤ count637 b))))))) else (if i < 678 then (if i < 663 then (if i < 656 then (if i < 652 then (if i < 650 then decide (13 ≤ count637 b) else (if i < 651 then decide (14 ≤ count637 b) else decide (15 ≤ count637 b))) else (if i < 654 then (if i < 653 then decide (16 ≤ count637 b) else decide (17 ≤ count637 b)) else (if i < 655 then decide (18 ≤ count637 b) else decide (19 ≤ count637 b)))) else (if i < 659 then (if i < 657 then decide (20 ≤ count637 b) else (if i < 658 then decide (21 ≤ count637 b) else decide (22 ≤ count637 b))) else (if i < 661 then (if i < 660 then decide (23 ≤ count637 b) else decide (24 ≤ count637 b)) else (if i < 662 then decide (25 ≤ count637 b) else decide (26 ≤ count637 b))))) else (if i < 670 then (if i < 666 then (if i < 664 then decide (27 ≤ count637 b) else (if i < 665 then decide (28 ≤ count637 b) else decide (29 ≤ count637 b))) else (if i < 668 then (if i < 667 then decide (30 ≤ count637 b) else decide (31 ≤ count637 b)) else (if i < 669 then decide (32 ≤ count637 b) else decide (1 ≤ count669 b)))) else (if i < 674 then (if i < 672 then (if i < 671 then decide (2 ≤ count669 b) else decide (1 ≤ count671 b)) else (if i < 673 then decide (2 ≤ count671 b) else decide (1 ≤ count673 b))) else (if i < 676 then (if i < 675 then decide (2 ≤ count673 b) else decide (3 ≤ count673 b)) else (if i < 677 then decide (4 ≤ count673 b) else decide (1 ≤ count677 b)))))) else (if i < 693 then (if i < 685 then (if i < 681 then (if i < 679 then decide (2 ≤ count677 b) else (if i < 680 then decide (1 ≤ count679 b) else decide (2 ≤ count679 b))) else (if i < 683 then (if i < 682 then decide (1 ≤ count681 b) else decide (2 ≤ count681 b)) else (if i < 684 then decide (3 ≤ count681 b) else decide (4 ≤ count681 b)))) else (if i < 689 then (if i < 687 then (if i < 686 then decide (1 ≤ count685 b) else decide (2 ≤ count685 b)) else (if i < 688 then decide (3 ≤ count685 b) else decide (4 ≤ count685 b))) else (if i < 691 then (if i < 690 then decide (5 ≤ count685 b) else decide (6 ≤ count685 b)) else (if i < 692 then decide (7 ≤ count685 b) else decide (8 ≤ count685 b))))) else (if i < 700 then (if i < 696 then (if i < 694 then decide (1 ≤ count693 b) else (if i < 695 then decide (2 ≤ count693 b) else decide (1 ≤ count695 b))) else (if i < 698 then (if i < 697 then decide (2 ≤ count695 b) else decide (1 ≤ count697 b)) else (if i < 699 then decide (2 ≤ count697 b) else decide (3 ≤ count697 b)))) else (if i < 704 then (if i < 702 then (if i < 701 then decide (4 ≤ count697 b) else decide (1 ≤ count701 b)) else (if i < 703 then decide (2 ≤ count701 b) else decide (1 ≤ count703 b))) else (if i < 706 then (if i < 705 then decide (2 ≤ count703 b) else decide (1 ≤ count705 b)) else (if i < 707 then decide (2 ≤ count705 b) else decide (3 ≤ count705 b))))))))) else (if i < 826 then (if i < 767 then (if i < 737 then (if i < 722 then (if i < 715 then (if i < 711 then (if i < 709 then decide (4 ≤ count705 b) else (if i < 710 then decide (1 ≤ count709 b) else decide (2 ≤ count709 b))) else (if i < 713 then (if i < 712 then decide (3 ≤ count709 b) else decide (4 ≤ count709 b)) else (if i < 714 then decide (5 ≤ count709 b) else decide (6 ≤ count709 b)))) else (if i < 718 then (if i < 716 then decide (7 ≤ count709 b) else (if i < 717 then decide (8 ≤ count709 b) else decide (1 ≤ count717 b))) else (if i < 720 then (if i < 719 then decide (2 ≤ count717 b) else decide (3 ≤ count717 b)) else (if i < 721 then decide (4 ≤ count717 b) else decide (5 ≤ count717 b))))) else (if i < 729 then (if i < 725 then (if i < 723 then decide (6 ≤ count717 b) else (if i < 724 then decide (7 ≤ count717 b) else decide (8 ≤ count717 b))) else (if i < 727 then (if i < 726 then decide (9 ≤ count717 b) else decide (10 ≤ count717 b)) else (if i < 728 then decide (11 ≤ count717 b) else decide (12 ≤ count717 b)))) else (if i < 733 then (if i < 731 then (if i < 730 then decide (13 ≤ count717 b) else decide (14 ≤ count717 b)) else (if i < 732 then decide (15 ≤ count717 b) else decide (16 ≤ count717 b))) else (if i < 735 then (if i < 734 then decide (1 ≤ count733 b) else decide (2 ≤ count733 b)) else (if i < 736 then decide (1 ≤ count735 b) else decide (2 ≤ count735 b)))))) else (if i < 752 then (if i < 744 then (if i < 740 then (if i < 738 then decide (1 ≤ count737 b) else (if i < 739 then decide (2 ≤ count737 b) else decide (3 ≤ count737 b))) else (if i < 742 then (if i < 741 then decide (4 ≤ count737 b) else decide (1 ≤ count741 b)) else (if i < 743 then decide (2 ≤ count741 b) else decide (1 ≤ count743 b)))) else (if i < 748 then (if i < 746 then (if i < 745 then decide (2 ≤ count743 b) else decide (1 ≤ count745 b)) else (if i < 747 then decide (2 ≤ count745 b) else decide (3 ≤ count745 b))) else (if i < 750 then (if i < 749 then decide (4 ≤ count745 b) else decide (1 ≤ count749 b)) else (if i < 751 then decide (2 ≤ count749 b) else decide (3 ≤ count749 b))))) else (if i < 759 then (if i < 755 then (if i < 753 then decide (4 ≤ count749 b) else (if i < 754 then decide (5 ≤ count749 b) else decide (6 ≤ count749 b))) else (if i < 757 then (if i < 756 then decide (7 ≤ count749 b) else decide (8 ≤ count749 b)) else (if i < 758 then decide (1 ≤ count757 b) else decide (2 ≤ count757 b)))) else (if i < 763 then (if i < 761 then (if i < 760 then decide (1 ≤ count759 b) else decide (2 ≤ count759 b)) else (if i < 762 then decide (1 ≤ count761 b) else decide (2 ≤ count761 b))) else (if i < 765 then (if i < 764 then decide (3 ≤ count761 b) else decide (4 ≤ count761 b)) else (if i < 766 then decide (1 ≤ count765 b) else decide (2 ≤ count765 b))))))) else (if i < 796 then (if i < 781 then (if i < 774 then (if i < 770 then (if i < 768 then decide (1 ≤ count767 b) else (if i < 769 then decide (2 ≤ count767 b) else decide (1 ≤ count769 b))) else (if i < 772 then (if i < 771 then decide (2 ≤ count769 b) else decide (3 ≤ count769 b)) else (if i < 773 then decide (1 ≤ count772 b) else decide (2 ≤ count772 b)))) else (if i < 777 then (if i < 775 then decide (3 ≤ count772 b) else (if i < 776 then decide (4 ≤ count772 b) else decide (5 ≤ count772 b))) else (if i < 779 then (if i < 778 then decide (1 ≤ count777 b) else decide (2 ≤ count777 b)) else (if i < 780 then decide (3 ≤ count777 b) else decide (4 ≤ count777 b))))) else (if i < 788 then (if i < 784 then (if i < 782 then decide (5 ≤ count777 b) else (if i < 783 then decide (6 ≤ count777 b) else decide (7 ≤ count777 b))) else (if i < 786 then (if i < 785 then decide (8 ≤ count777 b) else decide (9 ≤ count777 b)) else (if i < 787 then decide (1 ≤ count786 b) else decide (2 ≤ count786 b)))) else (if i < 792 then (if i < 790 then (if i < 789 then decide (3 ≤ count786 b) else decide (4 ≤ count786 b)) else (if i < 791 then decide (5 ≤ count786 b) else decide (6 ≤ count786 b))) else (if i < 794 then (if i < 793 then decide (7 ≤ count786 b) else decide (8 ≤ count786 b)) else (if i < 795 then decide (9 ≤ count786 b) else decide (10 ≤ count786 b)))))) else (if i < 811 then (if i < 803 then (if i < 799 then (if i < 797 then decide (11 ≤ count786 b) else (if i < 798 then decide (12 ≤ count786 b) else decide (13 ≤ count786 b))) else (if i < 801 then (if i < 800 then decide (14 ≤ count786 b) else decide (15 ≤ count786 b)) else (if i < 802 then decide (16 ≤ count786 b) else decide (17 ≤ count786 b)))) else (if i < 807 then (if i < 805 then (if i < 804 then decide (1 ≤ count803 b) else decide (2 ≤ count803 b)) else (if i < 806 then decide (3 ≤ count803 b) else decide (4 ≤ count803 b))) else (if i < 809 then (if i < 808 then decide (5 ≤ count803 b) else decide (6 ≤ count803 b)) else (if i < 810 then decide (7 ≤ count803 b) else decide (8 ≤ count803 b))))) else (if i < 818 then (if i < 814 then (if i < 812 then decide (9 ≤ count803 b) else (if i < 813 then decide (10 ≤ count803 b) else decide (11 ≤ count803 b))) else (if i < 816 then (if i < 815 then decide (12 ≤ count803 b) else decide (13 ≤ count803 b)) else (if i < 817 then decide (14 ≤ count803 b) else decide (15 ≤ count803 b)))) else (if i < 822 then (if i < 820 then (if i < 819 then decide (16 ≤ count803 b) else decide (17 ≤ count803 b)) else (if i < 821 then decide (18 ≤ count803 b) else decide (19 ≤ count803 b))) else (if i < 824 then (if i < 823 then decide (20 ≤ count803 b) else decide (21 ≤ count803 b)) else (if i < 825 then decide (22 ≤ count803 b) else decide (23 ≤ count803 b)))))))) else (if i < 885 then (if i < 855 then (if i < 840 then (if i < 833 then (if i < 829 then (if i < 827 then decide (24 ≤ count803 b) else (if i < 828 then decide (25 ≤ count803 b) else decide (26 ≤ count803 b))) else (if i < 831 then (if i < 830 then decide (27 ≤ count803 b) else decide (28 ≤ count803 b)) else (if i < 832 then decide (29 ≤ count803 b) else decide (30 ≤ count803 b)))) else (if i < 836 then (if i < 834 then decide (31 ≤ count803 b) else (if i < 835 then decide (32 ≤ count803 b) else decide (33 ≤ count803 b))) else (if i < 838 then (if i < 837 then decide (1 ≤ count836 b) else decide (2 ≤ count836 b)) else (if i < 839 then decide (3 ≤ count836 b) else decide (4 ≤ count836 b))))) else (if i < 847 then (if i < 843 then (if i < 841 then decide (5 ≤ count836 b) else (if i < 842 then decide (6 ≤ count836 b) else decide (7 ≤ count836 b))) else (if i < 845 then (if i < 844 then decide (8 ≤ count836 b) else decide (9 ≤ count836 b)) else (if i < 846 then decide (10 ≤ count836 b) else decide (11 ≤ count836 b)))) else (if i < 851 then (if i < 849 then (if i < 848 then decide (12 ≤ count836 b) else decide (13 ≤ count836 b)) else (if i < 850 then decide (14 ≤ count836 b) else decide (15 ≤ count836 b))) else (if i < 853 then (if i < 852 then decide (16 ≤ count836 b) else decide (17 ≤ count836 b)) else (if i < 854 then decide (18 ≤ count836 b) else decide (19 ≤ count836 b)))))) else (if i < 870 then (if i < 862 then (if i < 858 then (if i < 856 then decide (20 ≤ count836 b) else (if i < 857 then decide (21 ≤ count836 b) else decide (22 ≤ count836 b))) else (if i < 860 then (if i < 859 then decide (23 ≤ count836 b) else decide (24 ≤ count836 b)) else (if i < 861 then decide (25 ≤ count836 b) else decide (26 ≤ count836 b)))) else (if i < 866 then (if i < 864 then (if i < 863 then decide (27 ≤ count836 b) else decide (28 ≤ count836 b)) else (if i < 865 then decide (29 ≤ count836 b) else decide (30 ≤ count836 b))) else (if i < 868 then (if i < 867 then decide (31 ≤ count836 b) else decide (32 ≤ count836 b)) else (if i < 869 then decide (33 ≤ count836 b) else decide (34 ≤ count836 b))))) else (if i < 877 then (if i < 873 then (if i < 871 then decide (35 ≤ count836 b) else (if i < 872 then decide (36 ≤ count836 b) else decide (37 ≤ count836 b))) else (if i < 875 then (if i < 874 then decide (38 ≤ count836 b) else decide (39 ≤ count836 b)) else (if i < 876 then decide (40 ≤ count836 b) else decide (41 ≤ count836 b)))) else (if i < 881 then (if i < 879 then (if i < 878 then decide (42 ≤ count836 b) else decide (1 ≤ count878 b)) else (if i < 880 then decide (2 ≤ count878 b) else decide (1 ≤ count880 b))) else (if i < 883 then (if i < 882 then decide (2 ≤ count880 b) else decide (1 ≤ count882 b)) else (if i < 884 then decide (2 ≤ count882 b) else decide (3 ≤ count882 b))))))) else (if i < 915 then (if i < 900 then (if i < 892 then (if i < 888 then (if i < 886 then decide (4 ≤ count882 b) else (if i < 887 then decide (1 ≤ count886 b) else decide (2 ≤ count886 b))) else (if i < 890 then (if i < 889 then decide (1 ≤ count888 b) else decide (2 ≤ count888 b)) else (if i < 891 then decide (1 ≤ count890 b) else decide (2 ≤ count890 b)))) else (if i < 896 then (if i < 894 then (if i < 893 then decide (3 ≤ count890 b) else decide (4 ≤ count890 b)) else (if i < 895 then decide (1 ≤ count894 b) else decide (2 ≤ count894 b))) else (if i < 898 then (if i < 897 then decide (3 ≤ count894 b) else decide (4 ≤ count894 b)) else (if i < 899 then decide (5 ≤ count894 b) else decide (6 ≤ count894 b))))) else (if i < 907 then (if i < 903 then (if i < 901 then decide (7 ≤ count894 b) else (if i < 902 then decide (8 ≤ count894 b) else decide (1 ≤ count902 b))) else (if i < 905 then (if i < 904 then decide (2 ≤ count902 b) else decide (1 ≤ count904 b)) else (if i < 906 then decide (2 ≤ count904 b) else decide (1 ≤ count906 b)))) else (if i < 911 then (if i < 909 then (if i < 908 then decide (2 ≤ count906 b) else decide (3 ≤ count906 b)) else (if i < 910 then decide (4 ≤ count906 b) else decide (1 ≤ count910 b))) else (if i < 913 then (if i < 912 then decide (2 ≤ count910 b) else decide (1 ≤ count912 b)) else (if i < 914 then decide (2 ≤ count912 b) else decide (1 ≤ count914 b)))))) else (if i < 930 then (if i < 922 then (if i < 918 then (if i < 916 then decide (2 ≤ count914 b) else (if i < 917 then decide (3 ≤ count914 b) else decide (4 ≤ count914 b))) else (if i < 920 then (if i < 919 then decide (1 ≤ count918 b) else decide (2 ≤ count918 b)) else (if i < 921 then decide (3 ≤ count918 b) else decide (4 ≤ count918 b)))) else (if i < 926 then (if i < 924 then (if i < 923 then decide (5 ≤ count918 b) else decide (6 ≤ count918 b)) else (if i < 925 then decide (7 ≤ count918 b) else decide (8 ≤ count918 b))) else (if i < 928 then (if i < 927 then decide (1 ≤ count926 b) else decide (2 ≤ count926 b)) else (if i < 929 then decide (3 ≤ count926 b) else decide (4 ≤ count926 b))))) else (if i < 937 then (if i < 933 then (if i < 931 then decide (5 ≤ count926 b) else (if i < 932 then decide (6 ≤ count926 b) else decide (7 ≤ count926 b))) else (if i < 935 then (if i < 934 then decide (8 ≤ count926 b) else decide (9 ≤ count926 b)) else (if i < 936 then decide (10 ≤ count926 b) else decide (11 ≤ count926 b)))) else (if i < 941 then (if i < 939 then (if i < 938 then decide (12 ≤ count926 b) else decide (13 ≤ count926 b)) else (if i < 940 then decide (14 ≤ count926 b) else decide (15 ≤ count926 b))) else (if i < 943 then (if i < 942 then decide (16 ≤ count926 b) else decide (1 ≤ count942 b)) else (if i < 944 then decide (2 ≤ count942 b) else decide (1 ≤ count944 b))))))))))) else (if i < 1418 then (if i < 1181 then (if i < 1063 then (if i < 1004 then (if i < 974 then (if i < 959 then (if i < 952 then (if i < 948 then (if i < 946 then decide (2 ≤ count944 b) else (if i < 947 then decide (1 ≤ count946 b) else decide (2 ≤ count946 b))) else (if i < 950 then (if i < 949 then decide (3 ≤ count946 b) else decide (4 ≤ count946 b)) else (if i < 951 then decide (1 ≤ count950 b) else decide (2 ≤ count950 b)))) else (if i < 955 then (if i < 953 then decide (1 ≤ count952 b) else (if i < 954 then decide (2 ≤ count952 b) else decide (1 ≤ count954 b))) else (if i < 957 then (if i < 956 then decide (2 ≤ count954 b) else decide (3 ≤ count954 b)) else (if i < 958 then decide (4 ≤ count954 b) else decide (1 ≤ count958 b))))) else (if i < 966 then (if i < 962 then (if i < 960 then decide (2 ≤ count958 b) else (if i < 961 then decide (3 ≤ count958 b) else decide (4 ≤ count958 b))) else (if i < 964 then (if i < 963 then decide (5 ≤ count958 b) else decide (6 ≤ count958 b)) else (if i < 965 then decide (7 ≤ count958 b) else decide (8 ≤ count958 b)))) else (if i < 970 then (if i < 968 then (if i < 967 then decide (1 ≤ count966 b) else decide (2 ≤ count966 b)) else (if i < 969 then decide (1 ≤ count968 b) else decide (2 ≤ count968 b))) else (if i < 972 then (if i < 971 then decide (1 ≤ count970 b) else decide (2 ≤ count970 b)) else (if i < 973 then decide (3 ≤ count970 b) else decide (4 ≤ count970 b)))))) else (if i < 989 then (if i < 981 then (if i < 977 then (if i < 975 then decide (1 ≤ count974 b) else (if i < 976 then decide (2 ≤ count974 b) else decide (1 ≤ count976 b))) else (if i < 979 then (if i < 978 then decide (2 ≤ count976 b) else decide (1 ≤ count978 b)) else (if i < 980 then decide (2 ≤ count978 b) else decide (3 ≤ count978 b)))) else (if i < 985 then (if i < 983 then (if i < 982 then decide (4 ≤ count978 b) else decide (1 ≤ count982 b)) else (if i < 984 then decide (2 ≤ count982 b) else decide (3 ≤ count982 b))) else (if i < 987 then (if i < 986 then decide (4 ≤ count982 b) else decide (5 ≤ count982 b)) else (if i < 988 then decide (6 ≤ count982 b) else decide (7 ≤ count982 b))))) else (if i < 996 then (if i < 992 then (if i < 990 then decide (8 ≤ count982 b) else (if i < 991 then decide (1 ≤ count990 b) else decide (2 ≤ count990 b))) else (if i < 994 then (if i < 993 then decide (3 ≤ count990 b) else decide (4 ≤ count990 b)) else (if i < 995 then decide (5 ≤ count990 b) else decide (6 ≤ count990 b)))) else (if i < 1000 then (if i < 998 then (if i < 997 then decide (7 ≤ count990 b) else decide (8 ≤ count990 b)) else (if i < 999 then decide (9 ≤ count990 b) else decide (10 ≤ count990 b))) else (if i < 1002 then (if i < 1001 then decide (11 ≤ count990 b) else decide (12 ≤ count990 b)) else (if i < 1003 then decide (13 ≤ count990 b) else decide (14 ≤ count990 b))))))) else (if i < 1033 then (if i < 1018 then (if i < 1011 then (if i < 1007 then (if i < 1005 then decide (15 ≤ count990 b) else (if i < 1006 then decide (16 ≤ count990 b) else decide (1 ≤ count1006 b))) else (if i < 1009 then (if i < 1008 then decide (2 ≤ count1006 b) else decide (3 ≤ count1006 b)) else (if i < 1010 then decide (4 ≤ count1006 b) else decide (5 ≤ count1006 b)))) else (if i < 1014 then (if i < 1012 then decide (6 ≤ count1006 b) else (if i < 1013 then decide (7 ≤ count1006 b) else decide (8 ≤ count1006 b))) else (if i < 1016 then (if i < 1015 then decide (9 ≤ count1006 b) else decide (10 ≤ count1006 b)) else (if i < 1017 then decide (11 ≤ count1006 b) else decide (12 ≤ count1006 b))))) else (if i < 1025 then (if i < 1021 then (if i < 1019 then decide (13 ≤ count1006 b) else (if i < 1020 then decide (14 ≤ count1006 b) else decide (15 ≤ count1006 b))) else (if i < 1023 then (if i < 1022 then decide (16 ≤ count1006 b) else decide (17 ≤ count1006 b)) else (if i < 1024 then decide (18 ≤ count1006 b) else decide (19 ≤ count1006 b)))) else (if i < 1029 then (if i < 1027 then (if i < 1026 then decide (20 ≤ count1006 b) else decide (21 ≤ count1006 b)) else (if i < 1028 then decide (22 ≤ count1006 b) else decide (23 ≤ count1006 b))) else (if i < 1031 then (if i < 1030 then decide (24 ≤ count1006 b) else decide (25 ≤ count1006 b)) else (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b)))))) else (if i < 1048 then (if i < 1040 then (if i < 1036 then (if i < 1034 then decide (1 ≤ count1033 b) else (if i < 1035 then decide (2 ≤ count1033 b) else decide (1 ≤ count1035 b))) else (if i < 1038 then (if i < 1037 then decide (2 ≤ count1035 b) else decide (3 ≤ count1035 b)) else (if i < 1039 then decide (4 ≤ count1035 b) else decide (1 ≤ count1039 b)))) else (if i < 1044 then (if i < 1042 then (if i < 1041 then decide (2 ≤ count1039 b) else decide (1 ≤ count1041 b)) else (if i < 1043 then decide (2 ≤ count1041 b) else decide (1 ≤ count1043 b))) else (if i < 1046 then (if i < 1045 then decide (2 ≤ count1043 b) else decide (3 ≤ count1043 b)) else (if i < 1047 then decide (4 ≤ count1043 b) else decide (1 ≤ count1047 b))))) else (if i < 1055 then (if i < 1051 then (if i < 1049 then decide (2 ≤ count1047 b) else (if i < 1050 then decide (3 ≤ count1047 b) else decide (4 ≤ count1047 b))) else (if i < 1053 then (if i < 1052 then decide (5 ≤ count1047 b) else decide (6 ≤ count1047 b)) else (if i < 1054 then decide (7 ≤ count1047 b) else decide (8 ≤ count1047 b)))) else (if i < 1059 then (if i < 1057 then (if i < 1056 then decide (1 ≤ count1055 b) else decide (2 ≤ count1055 b)) else (if i < 1058 then decide (1 ≤ count1057 b) else decide (2 ≤ count1057 b))) else (if i < 1061 then (if i < 1060 then decide (1 ≤ count1059 b) else decide (2 ≤ count1059 b)) else (if i < 1062 then decide (3 ≤ count1059 b) else decide (4 ≤ count1059 b)))))))) else (if i < 1122 then (if i < 1092 then (if i < 1077 then (if i < 1070 then (if i < 1066 then (if i < 1064 then decide (1 ≤ count1063 b) else (if i < 1065 then decide (2 ≤ count1063 b) else decide (1 ≤ count1065 b))) else (if i < 1068 then (if i < 1067 then decide (2 ≤ count1065 b) else decide (1 ≤ count1067 b)) else (if i < 1069 then decide (2 ≤ count1067 b) else decide (3 ≤ count1067 b)))) else (if i < 1073 then (if i < 1071 then decide (4 ≤ count1067 b) else (if i < 1072 then decide (1 ≤ count1071 b) else decide (2 ≤ count1071 b))) else (if i < 1075 then (if i < 1074 then decide (3 ≤ count1071 b) else decide (4 ≤ count1071 b)) else (if i < 1076 then decide (5 ≤ count1071 b) else decide (6 ≤ count1071 b))))) else (if i < 1084 then (if i < 1080 then (if i < 1078 then decide (7 ≤ count1071 b) else (if i < 1079 then decide (8 ≤ count1071 b) else decide (1 ≤ count1079 b))) else (if i < 1082 then (if i < 1081 then decide (2 ≤ count1079 b) else decide (3 ≤ count1079 b)) else (if i < 1083 then decide (4 ≤ count1079 b) else decide (5 ≤ count1079 b)))) else (if i < 1088 then (if i < 1086 then (if i < 1085 then decide (6 ≤ count1079 b) else decide (7 ≤ count1079 b)) else (if i < 1087 then decide (8 ≤ count1079 b) else decide (9 ≤ count1079 b))) else (if i < 1090 then (if i < 1089 then decide (10 ≤ count1079 b) else decide (11 ≤ count1079 b)) else (if i < 1091 then decide (12 ≤ count1079 b) else decide (13 ≤ count1079 b)))))) else (if i < 1107 then (if i < 1099 then (if i < 1095 then (if i < 1093 then decide (14 ≤ count1079 b) else (if i < 1094 then decide (15 ≤ count1079 b) else decide (16 ≤ count1079 b))) else (if i < 1097 then (if i < 1096 then decide (1 ≤ count1095 b) else decide (2 ≤ count1095 b)) else (if i < 1098 then decide (1 ≤ count1097 b) else decide (2 ≤ count1097 b)))) else (if i < 1103 then (if i < 1101 then (if i < 1100 then decide (1 ≤ count1099 b) else decide (2 ≤ count1099 b)) else (if i < 1102 then decide (3 ≤ count1099 b) else decide (4 ≤ count1099 b))) else (if i < 1105 then (if i < 1104 then decide (1 ≤ count1103 b) else decide (2 ≤ count1103 b)) else (if i < 1106 then decide (1 ≤ count1105 b) else decide (2 ≤ count1105 b))))) else (if i < 1114 then (if i < 1110 then (if i < 1108 then decide (1 ≤ count1107 b) else (if i < 1109 then decide (2 ≤ count1107 b) else decide (3 ≤ count1107 b))) else (if i < 1112 then (if i < 1111 then decide (4 ≤ count1107 b) else decide (1 ≤ count1111 b)) else (if i < 1113 then decide (2 ≤ count1111 b) else decide (3 ≤ count1111 b)))) else (if i < 1118 then (if i < 1116 then (if i < 1115 then decide (4 ≤ count1111 b) else decide (5 ≤ count1111 b)) else (if i < 1117 then decide (6 ≤ count1111 b) else decide (7 ≤ count1111 b))) else (if i < 1120 then (if i < 1119 then decide (8 ≤ count1111 b) else decide (1 ≤ count1119 b)) else (if i < 1121 then decide (2 ≤ count1119 b) else decide (1 ≤ count1121 b))))))) else (if i < 1151 then (if i < 1136 then (if i < 1129 then (if i < 1125 then (if i < 1123 then decide (2 ≤ count1121 b) else (if i < 1124 then decide (1 ≤ count1123 b) else decide (2 ≤ count1123 b))) else (if i < 1127 then (if i < 1126 then decide (3 ≤ count1123 b) else decide (4 ≤ count1123 b)) else (if i < 1128 then decide (1 ≤ count1127 b) else decide (2 ≤ count1127 b)))) else (if i < 1132 then (if i < 1130 then decide (1 ≤ count1129 b) else (if i < 1131 then decide (2 ≤ count1129 b) else decide (1 ≤ count1131 b))) else (if i < 1134 then (if i < 1133 then decide (2 ≤ count1131 b) else decide (3 ≤ count1131 b)) else (if i < 1135 then decide (1 ≤ count1134 b) else decide (2 ≤ count1134 b))))) else (if i < 1143 then (if i < 1139 then (if i < 1137 then decide (3 ≤ count1134 b) else (if i < 1138 then decide (4 ≤ count1134 b) else decide (5 ≤ count1134 b))) else (if i < 1141 then (if i < 1140 then decide (1 ≤ count1139 b) else decide (2 ≤ count1139 b)) else (if i < 1142 then decide (3 ≤ count1139 b) else decide (4 ≤ count1139 b)))) else (if i < 1147 then (if i < 1145 then (if i < 1144 then decide (5 ≤ count1139 b) else decide (6 ≤ count1139 b)) else (if i < 1146 then decide (7 ≤ count1139 b) else decide (8 ≤ count1139 b))) else (if i < 1149 then (if i < 1148 then decide (9 ≤ count1139 b) else decide (1 ≤ count1148 b)) else (if i < 1150 then decide (2 ≤ count1148 b) else decide (3 ≤ count1148 b)))))) else (if i < 1166 then (if i < 1158 then (if i < 1154 then (if i < 1152 then decide (4 ≤ count1148 b) else (if i < 1153 then decide (5 ≤ count1148 b) else decide (6 ≤ count1148 b))) else (if i < 1156 then (if i < 1155 then decide (7 ≤ count1148 b) else decide (8 ≤ count1148 b)) else (if i < 1157 then decide (9 ≤ count1148 b) else decide (10 ≤ count1148 b)))) else (if i < 1162 then (if i < 1160 then (if i < 1159 then decide (11 ≤ count1148 b) else decide (12 ≤ count1148 b)) else (if i < 1161 then decide (13 ≤ count1148 b) else decide (14 ≤ count1148 b))) else (if i < 1164 then (if i < 1163 then decide (15 ≤ count1148 b) else decide (16 ≤ count1148 b)) else (if i < 1165 then decide (17 ≤ count1148 b) else decide (1 ≤ count1165 b))))) else (if i < 1173 then (if i < 1169 then (if i < 1167 then decide (2 ≤ count1165 b) else (if i < 1168 then decide (3 ≤ count1165 b) else decide (4 ≤ count1165 b))) else (if i < 1171 then (if i < 1170 then decide (5 ≤ count1165 b) else decide (6 ≤ count1165 b)) else (if i < 1172 then decide (7 ≤ count1165 b) else decide (8 ≤ count1165 b)))) else (if i < 1177 then (if i < 1175 then (if i < 1174 then decide (9 ≤ count1165 b) else decide (10 ≤ count1165 b)) else (if i < 1176 then decide (11 ≤ count1165 b) else decide (12 ≤ count1165 b))) else (if i < 1179 then (if i < 1178 then decide (13 ≤ count1165 b) else decide (14 ≤ count1165 b)) else (if i < 1180 then decide (15 ≤ count1165 b) else decide (16 ≤ count1165 b))))))))) else (if i < 1299 then (if i < 1240 then (if i < 1210 then (if i < 1195 then (if i < 1188 then (if i < 1184 then (if i < 1182 then decide (17 ≤ count1165 b) else (if i < 1183 then decide (18 ≤ count1165 b) else decide (19 ≤ count1165 b))) else (if i < 1186 then (if i < 1185 then decide (20 ≤ count1165 b) else decide (21 ≤ count1165 b)) else (if i < 1187 then decide (22 ≤ count1165 b) else decide (23 ≤ count1165 b)))) else (if i < 1191 then (if i < 1189 then decide (24 ≤ count1165 b) else (if i < 1190 then decide (25 ≤ count1165 b) else decide (1 ≤ count1190 b))) else (if i < 1193 then (if i < 1192 then decide (2 ≤ count1190 b) else decide (3 ≤ count1190 b)) else (if i < 1194 then decide (4 ≤ count1190 b) else decide (5 ≤ count1190 b))))) else (if i < 1202 then (if i < 1198 then (if i < 1196 then decide (6 ≤ count1190 b) else (if i < 1197 then decide (7 ≤ count1190 b) else decide (8 ≤ count1190 b))) else (if i < 1200 then (if i < 1199 then decide (9 ≤ count1190 b) else decide (10 ≤ count1190 b)) else (if i < 1201 then decide (11 ≤ count1190 b) else decide (12 ≤ count1190 b)))) else (if i < 1206 then (if i < 1204 then (if i < 1203 then decide (13 ≤ count1190 b) else decide (14 ≤ count1190 b)) else (if i < 1205 then decide (15 ≤ count1190 b) else decide (16 ≤ count1190 b))) else (if i < 1208 then (if i < 1207 then decide (17 ≤ count1190 b) else decide (18 ≤ count1190 b)) else (if i < 1209 then decide (19 ≤ count1190 b) else decide (20 ≤ count1190 b)))))) else (if i < 1225 then (if i < 1217 then (if i < 1213 then (if i < 1211 then decide (21 ≤ count1190 b) else (if i < 1212 then decide (22 ≤ count1190 b) else decide (23 ≤ count1190 b))) else (if i < 1215 then (if i < 1214 then decide (24 ≤ count1190 b) else decide (25 ≤ count1190 b)) else (if i < 1216 then decide (1 ≤ count1215 b) else decide (2 ≤ count1215 b)))) else (if i < 1221 then (if i < 1219 then (if i < 1218 then decide (1 ≤ count1217 b) else decide (2 ≤ count1217 b)) else (if i < 1220 then decide (3 ≤ count1217 b) else decide (1 ≤ count1220 b))) else (if i < 1223 then (if i < 1222 then decide (2 ≤ count1220 b) else decide (1 ≤ count1222 b)) else (if i < 1224 then decide (2 ≤ count1222 b) else decide (1 ≤ count1224 b))))) else (if i < 1232 then (if i < 1228 then (if i < 1226 then decide (2 ≤ count1224 b) else (if i < 1227 then decide (3 ≤ count1224 b) else decide (4 ≤ count1224 b))) else (if i < 1230 then (if i < 1229 then decide (1 ≤ count1228 b) else decide (2 ≤ count1228 b)) else (if i < 1231 then decide (3 ≤ count1228 b) else decide (4 ≤ count1228 b)))) else (if i < 1236 then (if i < 1234 then (if i < 1233 then decide (5 ≤ count1228 b) else decide (6 ≤ count1228 b)) else (if i < 1235 then decide (7 ≤ count1228 b) else decide (1 ≤ count1235 b))) else (if i < 1238 then (if i < 1237 then decide (2 ≤ count1235 b) else decide (1 ≤ count1237 b)) else (if i < 1239 then decide (2 ≤ count1237 b) else decide (1 ≤ count1239 b))))))) else (if i < 1269 then (if i < 1254 then (if i < 1247 then (if i < 1243 then (if i < 1241 then decide (2 ≤ count1239 b) else (if i < 1242 then decide (3 ≤ count1239 b) else decide (4 ≤ count1239 b))) else (if i < 1245 then (if i < 1244 then decide (1 ≤ count1243 b) else decide (2 ≤ count1243 b)) else (if i < 1246 then decide (1 ≤ count1245 b) else decide (2 ≤ count1245 b)))) else (if i < 1250 then (if i < 1248 then decide (1 ≤ count1247 b) else (if i < 1249 then decide (2 ≤ count1247 b) else decide (3 ≤ count1247 b))) else (if i < 1252 then (if i < 1251 then decide (4 ≤ count1247 b) else decide (1 ≤ count1251 b)) else (if i < 1253 then decide (2 ≤ count1251 b) else decide (3 ≤ count1251 b))))) else (if i < 1261 then (if i < 1257 then (if i < 1255 then decide (4 ≤ count1251 b) else (if i < 1256 then decide (5 ≤ count1251 b) else decide (6 ≤ count1251 b))) else (if i < 1259 then (if i < 1258 then decide (7 ≤ count1251 b) else decide (8 ≤ count1251 b)) else (if i < 1260 then decide (1 ≤ count1259 b) else decide (2 ≤ count1259 b)))) else (if i < 1265 then (if i < 1263 then (if i < 1262 then decide (3 ≤ count1259 b) else decide (4 ≤ count1259 b)) else (if i < 1264 then decide (5 ≤ count1259 b) else decide (6 ≤ count1259 b))) else (if i < 1267 then (if i < 1266 then decide (7 ≤ count1259 b) else decide (8 ≤ count1259 b)) else (if i < 1268 then decide (9 ≤ count1259 b) else decide (10 ≤ count1259 b)))))) else (if i < 1284 then (if i < 1276 then (if i < 1272 then (if i < 1270 then decide (11 ≤ count1259 b) else (if i < 1271 then decide (12 ≤ count1259 b) else decide (13 ≤ count1259 b))) else (if i < 1274 then (if i < 1273 then decide (14 ≤ count1259 b) else decide (15 ≤ count1259 b)) else (if i < 1275 then decide (1 ≤ count1274 b) else decide (2 ≤ count1274 b)))) else (if i < 1280 then (if i < 1278 then (if i < 1277 then decide (1 ≤ count1276 b) else decide (2 ≤ count1276 b)) else (if i < 1279 then decide (1 ≤ count1278 b) else decide (2 ≤ count1278 b))) else (if i < 1282 then (if i < 1281 then decide (3 ≤ count1278 b) else decide (4 ≤ count1278 b)) else (if i < 1283 then decide (1 ≤ count1282 b) else decide (2 ≤ count1282 b))))) else (if i < 1291 then (if i < 1287 then (if i < 1285 then decide (1 ≤ count1284 b) else (if i < 1286 then decide (2 ≤ count1284 b) else decide (1 ≤ count1286 b))) else (if i < 1289 then (if i < 1288 then decide (2 ≤ count1286 b) else decide (3 ≤ count1286 b)) else (if i < 1290 then decide (4 ≤ count1286 b) else decide (1 ≤ count1290 b)))) else (if i < 1295 then (if i < 1293 then (if i < 1292 then decide (2 ≤ count1290 b) else decide (3 ≤ count1290 b)) else (if i < 1294 then decide (4 ≤ count1290 b) else decide (5 ≤ count1290 b))) else (if i < 1297 then (if i < 1296 then decide (6 ≤ count1290 b) else decide (7 ≤ count1290 b)) else (if i < 1298 then decide (8 ≤ count1290 b) else decide (1 ≤ count1298 b)))))))) else (if i < 1358 then (if i < 1328 then (if i < 1313 then (if i < 1306 then (if i < 1302 then (if i < 1300 then decide (2 ≤ count1298 b) else (if i < 1301 then decide (1 ≤ count1300 b) else decide (2 ≤ count1300 b))) else (if i < 1304 then (if i < 1303 then decide (1 ≤ count1302 b) else decide (2 ≤ count1302 b)) else (if i < 1305 then decide (3 ≤ count1302 b) else decide (4 ≤ count1302 b)))) else (if i < 1309 then (if i < 1307 then decide (1 ≤ count1306 b) else (if i < 1308 then decide (2 ≤ count1306 b) else decide (1 ≤ count1308 b))) else (if i < 1311 then (if i < 1310 then decide (2 ≤ count1308 b) else decide (1 ≤ count1310 b)) else (if i < 1312 then decide (2 ≤ count1310 b) else decide (3 ≤ count1310 b))))) else (if i < 1320 then (if i < 1316 then (if i < 1314 then decide (4 ≤ count1310 b) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b))) else (if i < 1318 then (if i < 1317 then decide (3 ≤ count1314 b) else decide (4 ≤ count1314 b)) else (if i < 1319 then decide (5 ≤ count1314 b) else decide (6 ≤ count1314 b)))) else (if i < 1324 then (if i < 1322 then (if i < 1321 then decide (7 ≤ count1314 b) else decide (8 ≤ count1314 b)) else (if i < 1323 then decide (1 ≤ count1322 b) else decide (2 ≤ count1322 b))) else (if i < 1326 then (if i < 1325 then decide (3 ≤ count1322 b) else decide (4 ≤ count1322 b)) else (if i < 1327 then decide (5 ≤ count1322 b) else decide (6 ≤ count1322 b)))))) else (if i < 1343 then (if i < 1335 then (if i < 1331 then (if i < 1329 then decide (7 ≤ count1322 b) else (if i < 1330 then decide (8 ≤ count1322 b) else decide (9 ≤ count1322 b))) else (if i < 1333 then (if i < 1332 then decide (10 ≤ count1322 b) else decide (11 ≤ count1322 b)) else (if i < 1334 then decide (12 ≤ count1322 b) else decide (13 ≤ count1322 b)))) else (if i < 1339 then (if i < 1337 then (if i < 1336 then decide (14 ≤ count1322 b) else decide (15 ≤ count1322 b)) else (if i < 1338 then decide (16 ≤ count1322 b) else decide (1 ≤ count1338 b))) else (if i < 1341 then (if i < 1340 then decide (2 ≤ count1338 b) else decide (3 ≤ count1338 b)) else (if i < 1342 then decide (4 ≤ count1338 b) else decide (5 ≤ count1338 b))))) else (if i < 1350 then (if i < 1346 then (if i < 1344 then decide (6 ≤ count1338 b) else (if i < 1345 then decide (7 ≤ count1338 b) else decide (8 ≤ count1338 b))) else (if i < 1348 then (if i < 1347 then decide (9 ≤ count1338 b) else decide (10 ≤ count1338 b)) else (if i < 1349 then decide (11 ≤ count1338 b) else decide (12 ≤ count1338 b)))) else (if i < 1354 then (if i < 1352 then (if i < 1351 then decide (13 ≤ count1338 b) else decide (14 ≤ count1338 b)) else (if i < 1353 then decide (15 ≤ count1338 b) else decide (16 ≤ count1338 b))) else (if i < 1356 then (if i < 1355 then decide (17 ≤ count1338 b) else decide (18 ≤ count1338 b)) else (if i < 1357 then decide (19 ≤ count1338 b) else decide (20 ≤ count1338 b))))))) else (if i < 1388 then (if i < 1373 then (if i < 1365 then (if i < 1361 then (if i < 1359 then decide (21 ≤ count1338 b) else (if i < 1360 then decide (22 ≤ count1338 b) else decide (23 ≤ count1338 b))) else (if i < 1363 then (if i < 1362 then decide (24 ≤ count1338 b) else decide (25 ≤ count1338 b)) else (if i < 1364 then decide (26 ≤ count1338 b) else decide (27 ≤ count1338 b)))) else (if i < 1369 then (if i < 1367 then (if i < 1366 then decide (28 ≤ count1338 b) else decide (29 ≤ count1338 b)) else (if i < 1368 then decide (30 ≤ count1338 b) else decide (31 ≤ count1338 b))) else (if i < 1371 then (if i < 1370 then decide (1 ≤ count1369 b) else decide (2 ≤ count1369 b)) else (if i < 1372 then decide (1 ≤ count1371 b) else decide (2 ≤ count1371 b))))) else (if i < 1380 then (if i < 1376 then (if i < 1374 then decide (1 ≤ count1373 b) else (if i < 1375 then decide (2 ≤ count1373 b) else decide (3 ≤ count1373 b))) else (if i < 1378 then (if i < 1377 then decide (4 ≤ count1373 b) else decide (1 ≤ count1377 b)) else (if i < 1379 then decide (2 ≤ count1377 b) else decide (1 ≤ count1379 b)))) else (if i < 1384 then (if i < 1382 then (if i < 1381 then decide (2 ≤ count1379 b) else decide (1 ≤ count1381 b)) else (if i < 1383 then decide (2 ≤ count1381 b) else decide (3 ≤ count1381 b))) else (if i < 1386 then (if i < 1385 then decide (4 ≤ count1381 b) else decide (1 ≤ count1385 b)) else (if i < 1387 then decide (2 ≤ count1385 b) else decide (3 ≤ count1385 b)))))) else (if i < 1403 then (if i < 1395 then (if i < 1391 then (if i < 1389 then decide (4 ≤ count1385 b) else (if i < 1390 then decide (5 ≤ count1385 b) else decide (6 ≤ count1385 b))) else (if i < 1393 then (if i < 1392 then decide (7 ≤ count1385 b) else decide (8 ≤ count1385 b)) else (if i < 1394 then decide (1 ≤ count1393 b) else decide (2 ≤ count1393 b)))) else (if i < 1399 then (if i < 1397 then (if i < 1396 then decide (1 ≤ count1395 b) else decide (2 ≤ count1395 b)) else (if i < 1398 then decide (1 ≤ count1397 b) else decide (2 ≤ count1397 b))) else (if i < 1401 then (if i < 1400 then decide (3 ≤ count1397 b) else decide (4 ≤ count1397 b)) else (if i < 1402 then decide (1 ≤ count1401 b) else decide (2 ≤ count1401 b))))) else (if i < 1410 then (if i < 1406 then (if i < 1404 then decide (1 ≤ count1403 b) else (if i < 1405 then decide (2 ≤ count1403 b) else decide (1 ≤ count1405 b))) else (if i < 1408 then (if i < 1407 then decide (2 ≤ count1405 b) else decide (3 ≤ count1405 b)) else (if i < 1409 then decide (4 ≤ count1405 b) else decide (1 ≤ count1409 b)))) else (if i < 1414 then (if i < 1412 then (if i < 1411 then decide (2 ≤ count1409 b) else decide (3 ≤ count1409 b)) else (if i < 1413 then decide (4 ≤ count1409 b) else decide (5 ≤ count1409 b))) else (if i < 1416 then (if i < 1415 then decide (6 ≤ count1409 b) else decide (7 ≤ count1409 b)) else (if i < 1417 then decide (8 ≤ count1409 b) else decide (1 ≤ count1417 b)))))))))) else (if i < 1654 then (if i < 1536 then (if i < 1477 then (if i < 1447 then (if i < 1432 then (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (2 ≤ count1417 b) else (if i < 1420 then decide (3 ≤ count1417 b) else decide (4 ≤ count1417 b))) else (if i < 1423 then (if i < 1422 then decide (5 ≤ count1417 b) else decide (6 ≤ count1417 b)) else (if i < 1424 then decide (7 ≤ count1417 b) else decide (8 ≤ count1417 b)))) else (if i < 1428 then (if i < 1426 then decide (9 ≤ count1417 b) else (if i < 1427 then decide (10 ≤ count1417 b) else decide (11 ≤ count1417 b))) else (if i < 1430 then (if i < 1429 then decide (12 ≤ count1417 b) else decide (13 ≤ count1417 b)) else (if i < 1431 then decide (14 ≤ count1417 b) else decide (15 ≤ count1417 b))))) else (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (16 ≤ count1417 b) else (if i < 1434 then decide (1 ≤ count1433 b) else decide (2 ≤ count1433 b))) else (if i < 1437 then (if i < 1436 then decide (1 ≤ count1435 b) else decide (2 ≤ count1435 b)) else (if i < 1438 then decide (1 ≤ count1437 b) else decide (2 ≤ count1437 b)))) else (if i < 1443 then (if i < 1441 then (if i < 1440 then decide (3 ≤ count1437 b) else decide (4 ≤ count1437 b)) else (if i < 1442 then decide (1 ≤ count1441 b) else decide (2 ≤ count1441 b))) else (if i < 1445 then (if i < 1444 then decide (1 ≤ count1443 b) else decide (2 ≤ count1443 b)) else (if i < 1446 then decide (1 ≤ count1445 b) else decide (2 ≤ count1445 b)))))) else (if i < 1462 then (if i < 1454 then (if i < 1450 then (if i < 1448 then decide (3 ≤ count1445 b) else (if i < 1449 then decide (4 ≤ count1445 b) else decide (1 ≤ count1449 b))) else (if i < 1452 then (if i < 1451 then decide (2 ≤ count1449 b) else decide (3 ≤ count1449 b)) else (if i < 1453 then decide (4 ≤ count1449 b) else decide (5 ≤ count1449 b)))) else (if i < 1458 then (if i < 1456 then (if i < 1455 then decide (6 ≤ count1449 b) else decide (7 ≤ count1449 b)) else (if i < 1457 then decide (8 ≤ count1449 b) else decide (1 ≤ count1457 b))) else (if i < 1460 then (if i < 1459 then decide (2 ≤ count1457 b) else decide (1 ≤ count1459 b)) else (if i < 1461 then decide (2 ≤ count1459 b) else decide (1 ≤ count1461 b))))) else (if i < 1469 then (if i < 1465 then (if i < 1463 then decide (2 ≤ count1461 b) else (if i < 1464 then decide (3 ≤ count1461 b) else decide (4 ≤ count1461 b))) else (if i < 1467 then (if i < 1466 then decide (1 ≤ count1465 b) else decide (2 ≤ count1465 b)) else (if i < 1468 then decide (1 ≤ count1467 b) else decide (2 ≤ count1467 b)))) else (if i < 1473 then (if i < 1471 then (if i < 1470 then decide (1 ≤ count1469 b) else decide (2 ≤ count1469 b)) else (if i < 1472 then decide (3 ≤ count1469 b) else decide (4 ≤ count1469 b))) else (if i < 1475 then (if i < 1474 then decide (1 ≤ count1473 b) else decide (2 ≤ count1473 b)) else (if i < 1476 then decide (3 ≤ count1473 b) else decide (4 ≤ count1473 b))))))) else (if i < 1506 then (if i < 1491 then (if i < 1484 then (if i < 1480 then (if i < 1478 then decide (5 ≤ count1473 b) else (if i < 1479 then decide (6 ≤ count1473 b) else decide (7 ≤ count1473 b))) else (if i < 1482 then (if i < 1481 then decide (8 ≤ count1473 b) else decide (1 ≤ count1481 b)) else (if i < 1483 then decide (2 ≤ count1481 b) else decide (3 ≤ count1481 b)))) else (if i < 1487 then (if i < 1485 then decide (4 ≤ count1481 b) else (if i < 1486 then decide (5 ≤ count1481 b) else decide (6 ≤ count1481 b))) else (if i < 1489 then (if i < 1488 then decide (7 ≤ count1481 b) else decide (8 ≤ count1481 b)) else (if i < 1490 then decide (9 ≤ count1481 b) else decide (10 ≤ count1481 b))))) else (if i < 1498 then (if i < 1494 then (if i < 1492 then decide (11 ≤ count1481 b) else (if i < 1493 then decide (12 ≤ count1481 b) else decide (13 ≤ count1481 b))) else (if i < 1496 then (if i < 1495 then decide (14 ≤ count1481 b) else decide (15 ≤ count1481 b)) else (if i < 1497 then decide (16 ≤ count1481 b) else decide (1 ≤ count1497 b)))) else (if i < 1502 then (if i < 1500 then (if i < 1499 then decide (2 ≤ count1497 b) else decide (3 ≤ count1497 b)) else (if i < 1501 then decide (4 ≤ count1497 b) else decide (5 ≤ count1497 b))) else (if i < 1504 then (if i < 1503 then decide (6 ≤ count1497 b) else decide (7 ≤ count1497 b)) else (if i < 1505 then decide (8 ≤ count1497 b) else decide (9 ≤ count1497 b)))))) else (if i < 1521 then (if i < 1513 then (if i < 1509 then (if i < 1507 then decide (10 ≤ count1497 b) else (if i < 1508 then decide (11 ≤ count1497 b) else decide (12 ≤ count1497 b))) else (if i < 1511 then (if i < 1510 then decide (13 ≤ count1497 b) else decide (14 ≤ count1497 b)) else (if i < 1512 then decide (15 ≤ count1497 b) else decide (16 ≤ count1497 b)))) else (if i < 1517 then (if i < 1515 then (if i < 1514 then decide (17 ≤ count1497 b) else decide (18 ≤ count1497 b)) else (if i < 1516 then decide (19 ≤ count1497 b) else decide (20 ≤ count1497 b))) else (if i < 1519 then (if i < 1518 then decide (21 ≤ count1497 b) else decide (22 ≤ count1497 b)) else (if i < 1520 then decide (23 ≤ count1497 b) else decide (24 ≤ count1497 b))))) else (if i < 1528 then (if i < 1524 then (if i < 1522 then decide (25 ≤ count1497 b) else (if i < 1523 then decide (26 ≤ count1497 b) else decide (27 ≤ count1497 b))) else (if i < 1526 then (if i < 1525 then decide (28 ≤ count1497 b) else decide (29 ≤ count1497 b)) else (if i < 1527 then decide (30 ≤ count1497 b) else decide (31 ≤ count1497 b)))) else (if i < 1532 then (if i < 1530 then (if i < 1529 then decide (32 ≤ count1497 b) else decide (1 ≤ count1529 b)) else (if i < 1531 then decide (2 ≤ count1529 b) else decide (3 ≤ count1529 b))) else (if i < 1534 then (if i < 1533 then decide (4 ≤ count1529 b) else decide (5 ≤ count1529 b)) else (if i < 1535 then decide (6 ≤ count1529 b) else decide (7 ≤ count1529 b)))))))) else (if i < 1595 then (if i < 1565 then (if i < 1550 then (if i < 1543 then (if i < 1539 then (if i < 1537 then decide (8 ≤ count1529 b) else (if i < 1538 then decide (9 ≤ count1529 b) else decide (10 ≤ count1529 b))) else (if i < 1541 then (if i < 1540 then decide (11 ≤ count1529 b) else decide (12 ≤ count1529 b)) else (if i < 1542 then decide (13 ≤ count1529 b) else decide (14 ≤ count1529 b)))) else (if i < 1546 then (if i < 1544 then decide (15 ≤ count1529 b) else (if i < 1545 then decide (16 ≤ count1529 b) else decide (17 ≤ count1529 b))) else (if i < 1548 then (if i < 1547 then decide (18 ≤ count1529 b) else decide (19 ≤ count1529 b)) else (if i < 1549 then decide (20 ≤ count1529 b) else decide (21 ≤ count1529 b))))) else (if i < 1557 then (if i < 1553 then (if i < 1551 then decide (22 ≤ count1529 b) else (if i < 1552 then decide (23 ≤ count1529 b) else decide (24 ≤ count1529 b))) else (if i < 1555 then (if i < 1554 then decide (25 ≤ count1529 b) else decide (26 ≤ count1529 b)) else (if i < 1556 then decide (27 ≤ count1529 b) else decide (28 ≤ count1529 b)))) else (if i < 1561 then (if i < 1559 then (if i < 1558 then decide (29 ≤ count1529 b) else decide (30 ≤ count1529 b)) else (if i < 1560 then decide (31 ≤ count1529 b) else decide (32 ≤ count1529 b))) else (if i < 1563 then (if i < 1562 then decide (33 ≤ count1529 b) else decide (34 ≤ count1529 b)) else (if i < 1564 then decide (35 ≤ count1529 b) else decide (36 ≤ count1529 b)))))) else (if i < 1580 then (if i < 1572 then (if i < 1568 then (if i < 1566 then decide (37 ≤ count1529 b) else (if i < 1567 then decide (38 ≤ count1529 b) else decide (39 ≤ count1529 b))) else (if i < 1570 then (if i < 1569 then decide (40 ≤ count1529 b) else decide (41 ≤ count1529 b)) else (if i < 1571 then decide (42 ≤ count1529 b) else decide (1 ≤ count1571 b)))) else (if i < 1576 then (if i < 1574 then (if i < 1573 then decide (2 ≤ count1571 b) else decide (1 ≤ count1573 b)) else (if i < 1575 then decide (2 ≤ count1573 b) else decide (3 ≤ count1573 b))) else (if i < 1578 then (if i < 1577 then decide (1 ≤ count1576 b) else decide (2 ≤ count1576 b)) else (if i < 1579 then decide (1 ≤ count1578 b) else decide (2 ≤ count1578 b))))) else (if i < 1587 then (if i < 1583 then (if i < 1581 then decide (1 ≤ count1580 b) else (if i < 1582 then decide (2 ≤ count1580 b) else decide (3 ≤ count1580 b))) else (if i < 1585 then (if i < 1584 then decide (4 ≤ count1580 b) else decide (1 ≤ count1584 b)) else (if i < 1586 then decide (2 ≤ count1584 b) else decide (3 ≤ count1584 b)))) else (if i < 1591 then (if i < 1589 then (if i < 1588 then decide (4 ≤ count1584 b) else decide (5 ≤ count1584 b)) else (if i < 1590 then decide (6 ≤ count1584 b) else decide (7 ≤ count1584 b))) else (if i < 1593 then (if i < 1592 then decide (1 ≤ count1591 b) else decide (2 ≤ count1591 b)) else (if i < 1594 then decide (1 ≤ count1593 b) else decide (2 ≤ count1593 b))))))) else (if i < 1624 then (if i < 1609 then (if i < 1602 then (if i < 1598 then (if i < 1596 then decide (1 ≤ count1595 b) else (if i < 1597 then decide (2 ≤ count1595 b) else decide (3 ≤ count1595 b))) else (if i < 1600 then (if i < 1599 then decide (4 ≤ count1595 b) else decide (1 ≤ count1599 b)) else (if i < 1601 then decide (2 ≤ count1599 b) else decide (1 ≤ count1601 b)))) else (if i < 1605 then (if i < 1603 then decide (2 ≤ count1601 b) else (if i < 1604 then decide (1 ≤ count1603 b) else decide (2 ≤ count1603 b))) else (if i < 1607 then (if i < 1606 then decide (3 ≤ count1603 b) else decide (4 ≤ count1603 b)) else (if i < 1608 then decide (1 ≤ count1607 b) else decide (2 ≤ count1607 b))))) else (if i < 1616 then (if i < 1612 then (if i < 1610 then decide (3 ≤ count1607 b) else (if i < 1611 then decide (4 ≤ count1607 b) else decide (5 ≤ count1607 b))) else (if i < 1614 then (if i < 1613 then decide (6 ≤ count1607 b) else decide (7 ≤ count1607 b)) else (if i < 1615 then decide (8 ≤ count1607 b) else decide (1 ≤ count1615 b)))) else (if i < 1620 then (if i < 1618 then (if i < 1617 then decide (2 ≤ count1615 b) else decide (3 ≤ count1615 b)) else (if i < 1619 then decide (4 ≤ count1615 b) else decide (5 ≤ count1615 b))) else (if i < 1622 then (if i < 1621 then decide (6 ≤ count1615 b) else decide (7 ≤ count1615 b)) else (if i < 1623 then decide (8 ≤ count1615 b) else decide (9 ≤ count1615 b)))))) else (if i < 1639 then (if i < 1631 then (if i < 1627 then (if i < 1625 then decide (10 ≤ count1615 b) else (if i < 1626 then decide (11 ≤ count1615 b) else decide (12 ≤ count1615 b))) else (if i < 1629 then (if i < 1628 then decide (13 ≤ count1615 b) else decide (14 ≤ count1615 b)) else (if i < 1630 then decide (15 ≤ count1615 b) else decide (1 ≤ count1630 b)))) else (if i < 1635 then (if i < 1633 then (if i < 1632 then decide (2 ≤ count1630 b) else decide (1 ≤ count1632 b)) else (if i < 1634 then decide (2 ≤ count1632 b) else decide (1 ≤ count1634 b))) else (if i < 1637 then (if i < 1636 then decide (2 ≤ count1634 b) else decide (3 ≤ count1634 b)) else (if i < 1638 then decide (4 ≤ count1634 b) else decide (1 ≤ count1638 b))))) else (if i < 1646 then (if i < 1642 then (if i < 1640 then decide (2 ≤ count1638 b) else (if i < 1641 then decide (1 ≤ count1640 b) else decide (2 ≤ count1640 b))) else (if i < 1644 then (if i < 1643 then decide (1 ≤ count1642 b) else decide (2 ≤ count1642 b)) else (if i < 1645 then decide (3 ≤ count1642 b) else decide (4 ≤ count1642 b)))) else (if i < 1650 then (if i < 1648 then (if i < 1647 then decide (1 ≤ count1646 b) else decide (2 ≤ count1646 b)) else (if i < 1649 then decide (3 ≤ count1646 b) else decide (4 ≤ count1646 b))) else (if i < 1652 then (if i < 1651 then decide (5 ≤ count1646 b) else decide (6 ≤ count1646 b)) else (if i < 1653 then decide (7 ≤ count1646 b) else decide (8 ≤ count1646 b))))))))) else (if i < 1772 then (if i < 1713 then (if i < 1683 then (if i < 1668 then (if i < 1661 then (if i < 1657 then (if i < 1655 then decide (1 ≤ count1654 b) else (if i < 1656 then decide (2 ≤ count1654 b) else decide (1 ≤ count1656 b))) else (if i < 1659 then (if i < 1658 then decide (2 ≤ count1656 b) else decide (1 ≤ count1658 b)) else (if i < 1660 then decide (2 ≤ count1658 b) else decide (3 ≤ count1658 b)))) else (if i < 1664 then (if i < 1662 then decide (4 ≤ count1658 b) else (if i < 1663 then decide (1 ≤ count1662 b) else decide (2 ≤ count1662 b))) else (if i < 1666 then (if i < 1665 then decide (1 ≤ count1664 b) else decide (2 ≤ count1664 b)) else (if i < 1667 then decide (1 ≤ count1666 b) else decide (2 ≤ count1666 b))))) else (if i < 1675 then (if i < 1671 then (if i < 1669 then decide (3 ≤ count1666 b) else (if i < 1670 then decide (4 ≤ count1666 b) else decide (1 ≤ count1670 b))) else (if i < 1673 then (if i < 1672 then decide (2 ≤ count1670 b) else decide (3 ≤ count1670 b)) else (if i < 1674 then decide (4 ≤ count1670 b) else decide (5 ≤ count1670 b)))) else (if i < 1679 then (if i < 1677 then (if i < 1676 then decide (6 ≤ count1670 b) else decide (7 ≤ count1670 b)) else (if i < 1678 then decide (8 ≤ count1670 b) else decide (1 ≤ count1678 b))) else (if i < 1681 then (if i < 1680 then decide (2 ≤ count1678 b) else decide (3 ≤ count1678 b)) else (if i < 1682 then decide (4 ≤ count1678 b) else decide (5 ≤ count1678 b)))))) else (if i < 1698 then (if i < 1690 then (if i < 1686 then (if i < 1684 then decide (6 ≤ count1678 b) else (if i < 1685 then decide (7 ≤ count1678 b) else decide (8 ≤ count1678 b))) else (if i < 1688 then (if i < 1687 then decide (9 ≤ count1678 b) else decide (10 ≤ count1678 b)) else (if i < 1689 then decide (11 ≤ count1678 b) else decide (12 ≤ count1678 b)))) else (if i < 1694 then (if i < 1692 then (if i < 1691 then decide (13 ≤ count1678 b) else decide (14 ≤ count1678 b)) else (if i < 1693 then decide (15 ≤ count1678 b) else decide (16 ≤ count1678 b))) else (if i < 1696 then (if i < 1695 then decide (1 ≤ count1694 b) else decide (2 ≤ count1694 b)) else (if i < 1697 then decide (3 ≤ count1694 b) else decide (4 ≤ count1694 b))))) else (if i < 1705 then (if i < 1701 then (if i < 1699 then decide (5 ≤ count1694 b) else (if i < 1700 then decide (6 ≤ count1694 b) else decide (7 ≤ count1694 b))) else (if i < 1703 then (if i < 1702 then decide (8 ≤ count1694 b) else decide (9 ≤ count1694 b)) else (if i < 1704 then decide (10 ≤ count1694 b) else decide (11 ≤ count1694 b)))) else (if i < 1709 then (if i < 1707 then (if i < 1706 then decide (12 ≤ count1694 b) else decide (13 ≤ count1694 b)) else (if i < 1708 then decide (14 ≤ count1694 b) else decide (15 ≤ count1694 b))) else (if i < 1711 then (if i < 1710 then decide (16 ≤ count1694 b) else decide (17 ≤ count1694 b)) else (if i < 1712 then decide (18 ≤ count1694 b) else decide (19 ≤ count1694 b))))))) else (if i < 1742 then (if i < 1727 then (if i < 1720 then (if i < 1716 then (if i < 1714 then decide (20 ≤ count1694 b) else (if i < 1715 then decide (21 ≤ count1694 b) else decide (22 ≤ count1694 b))) else (if i < 1718 then (if i < 1717 then decide (23 ≤ count1694 b) else decide (1 ≤ count1717 b)) else (if i < 1719 then decide (2 ≤ count1717 b) else decide (1 ≤ count1719 b)))) else (if i < 1723 then (if i < 1721 then decide (2 ≤ count1719 b) else (if i < 1722 then decide (1 ≤ count1721 b) else decide (2 ≤ count1721 b))) else (if i < 1725 then (if i < 1724 then decide (3 ≤ count1721 b) else decide (4 ≤ count1721 b)) else (if i < 1726 then decide (1 ≤ count1725 b) else decide (2 ≤ count1725 b))))) else (if i < 1734 then (if i < 1730 then (if i < 1728 then decide (1 ≤ count1727 b) else (if i < 1729 then decide (2 ≤ count1727 b) else decide (1 ≤ count1729 b))) else (if i < 1732 then (if i < 1731 then decide (2 ≤ count1729 b) else decide (3 ≤ count1729 b)) else (if i < 1733 then decide (4 ≤ count1729 b) else decide (1 ≤ count1733 b)))) else (if i < 1738 then (if i < 1736 then (if i < 1735 then decide (2 ≤ count1733 b) else decide (3 ≤ count1733 b)) else (if i < 1737 then decide (4 ≤ count1733 b) else decide (5 ≤ count1733 b))) else (if i < 1740 then (if i < 1739 then decide (6 ≤ count1733 b) else decide (7 ≤ count1733 b)) else (if i < 1741 then decide (8 ≤ count1733 b) else decide (1 ≤ count1741 b)))))) else (if i < 1757 then (if i < 1749 then (if i < 1745 then (if i < 1743 then decide (2 ≤ count1741 b) else (if i < 1744 then decide (1 ≤ count1743 b) else decide (2 ≤ count1743 b))) else (if i < 1747 then (if i < 1746 then decide (1 ≤ count1745 b) else decide (2 ≤ count1745 b)) else (if i < 1748 then decide (3 ≤ count1745 b) else decide (4 ≤ count1745 b)))) else (if i < 1753 then (if i < 1751 then (if i < 1750 then decide (1 ≤ count1749 b) else decide (2 ≤ count1749 b)) else (if i < 1752 then decide (1 ≤ count1751 b) else decide (2 ≤ count1751 b))) else (if i < 1755 then (if i < 1754 then decide (1 ≤ count1753 b) else decide (2 ≤ count1753 b)) else (if i < 1756 then decide (3 ≤ count1753 b) else decide (4 ≤ count1753 b))))) else (if i < 1764 then (if i < 1760 then (if i < 1758 then decide (1 ≤ count1757 b) else (if i < 1759 then decide (2 ≤ count1757 b) else decide (3 ≤ count1757 b))) else (if i < 1762 then (if i < 1761 then decide (4 ≤ count1757 b) else decide (5 ≤ count1757 b)) else (if i < 1763 then decide (6 ≤ count1757 b) else decide (7 ≤ count1757 b)))) else (if i < 1768 then (if i < 1766 then (if i < 1765 then decide (8 ≤ count1757 b) else decide (1 ≤ count1765 b)) else (if i < 1767 then decide (2 ≤ count1765 b) else decide (3 ≤ count1765 b))) else (if i < 1770 then (if i < 1769 then decide (4 ≤ count1765 b) else decide (5 ≤ count1765 b)) else (if i < 1771 then decide (6 ≤ count1765 b) else decide (7 ≤ count1765 b)))))))) else (if i < 1831 then (if i < 1801 then (if i < 1786 then (if i < 1779 then (if i < 1775 then (if i < 1773 then decide (8 ≤ count1765 b) else (if i < 1774 then decide (9 ≤ count1765 b) else decide (10 ≤ count1765 b))) else (if i < 1777 then (if i < 1776 then decide (11 ≤ count1765 b) else decide (12 ≤ count1765 b)) else (if i < 1778 then decide (13 ≤ count1765 b) else decide (14 ≤ count1765 b)))) else (if i < 1782 then (if i < 1780 then decide (15 ≤ count1765 b) else (if i < 1781 then decide (16 ≤ count1765 b) else decide (1 ≤ count1781 b))) else (if i < 1784 then (if i < 1783 then decide (2 ≤ count1781 b) else decide (1 ≤ count1783 b)) else (if i < 1785 then decide (2 ≤ count1783 b) else decide (1 ≤ count1785 b))))) else (if i < 1793 then (if i < 1789 then (if i < 1787 then decide (2 ≤ count1785 b) else (if i < 1788 then decide (3 ≤ count1785 b) else decide (4 ≤ count1785 b))) else (if i < 1791 then (if i < 1790 then decide (1 ≤ count1789 b) else decide (2 ≤ count1789 b)) else (if i < 1792 then decide (1 ≤ count1791 b) else decide (2 ≤ count1791 b)))) else (if i < 1797 then (if i < 1795 then (if i < 1794 then decide (1 ≤ count1793 b) else decide (2 ≤ count1793 b)) else (if i < 1796 then decide (3 ≤ count1793 b) else decide (4 ≤ count1793 b))) else (if i < 1799 then (if i < 1798 then decide (1 ≤ count1797 b) else decide (2 ≤ count1797 b)) else (if i < 1800 then decide (3 ≤ count1797 b) else decide (4 ≤ count1797 b)))))) else (if i < 1816 then (if i < 1808 then (if i < 1804 then (if i < 1802 then decide (5 ≤ count1797 b) else (if i < 1803 then decide (6 ≤ count1797 b) else decide (7 ≤ count1797 b))) else (if i < 1806 then (if i < 1805 then decide (8 ≤ count1797 b) else decide (1 ≤ count1805 b)) else (if i < 1807 then decide (2 ≤ count1805 b) else decide (1 ≤ count1807 b)))) else (if i < 1812 then (if i < 1810 then (if i < 1809 then decide (2 ≤ count1807 b) else decide (1 ≤ count1809 b)) else (if i < 1811 then decide (2 ≤ count1809 b) else decide (3 ≤ count1809 b))) else (if i < 1814 then (if i < 1813 then decide (4 ≤ count1809 b) else decide (1 ≤ count1813 b)) else (if i < 1815 then decide (2 ≤ count1813 b) else decide (1 ≤ count1815 b))))) else (if i < 1823 then (if i < 1819 then (if i < 1817 then decide (2 ≤ count1815 b) else (if i < 1818 then decide (1 ≤ count1817 b) else decide (2 ≤ count1817 b))) else (if i < 1821 then (if i < 1820 then decide (3 ≤ count1817 b) else decide (4 ≤ count1817 b)) else (if i < 1822 then decide (1 ≤ count1821 b) else decide (2 ≤ count1821 b)))) else (if i < 1827 then (if i < 1825 then (if i < 1824 then decide (3 ≤ count1821 b) else decide (4 ≤ count1821 b)) else (if i < 1826 then decide (5 ≤ count1821 b) else decide (6 ≤ count1821 b))) else (if i < 1829 then (if i < 1828 then decide (7 ≤ count1821 b) else decide (8 ≤ count1821 b)) else (if i < 1830 then decide (1 ≤ count1829 b) else decide (2 ≤ count1829 b))))))) else (if i < 1861 then (if i < 1846 then (if i < 1838 then (if i < 1834 then (if i < 1832 then decide (3 ≤ count1829 b) else (if i < 1833 then decide (4 ≤ count1829 b) else decide (5 ≤ count1829 b))) else (if i < 1836 then (if i < 1835 then decide (6 ≤ count1829 b) else decide (7 ≤ count1829 b)) else (if i < 1837 then decide (8 ≤ count1829 b) else decide (9 ≤ count1829 b)))) else (if i < 1842 then (if i < 1840 then (if i < 1839 then decide (10 ≤ count1829 b) else decide (11 ≤ count1829 b)) else (if i < 1841 then decide (12 ≤ count1829 b) else decide (13 ≤ count1829 b))) else (if i < 1844 then (if i < 1843 then decide (14 ≤ count1829 b) else decide (15 ≤ count1829 b)) else (if i < 1845 then decide (16 ≤ count1829 b) else decide (1 ≤ count1845 b))))) else (if i < 1853 then (if i < 1849 then (if i < 1847 then decide (2 ≤ count1845 b) else (if i < 1848 then decide (3 ≤ count1845 b) else decide (4 ≤ count1845 b))) else (if i < 1851 then (if i < 1850 then decide (5 ≤ count1845 b) else decide (6 ≤ count1845 b)) else (if i < 1852 then decide (7 ≤ count1845 b) else decide (8 ≤ count1845 b)))) else (if i < 1857 then (if i < 1855 then (if i < 1854 then decide (9 ≤ count1845 b) else decide (10 ≤ count1845 b)) else (if i < 1856 then decide (11 ≤ count1845 b) else decide (12 ≤ count1845 b))) else (if i < 1859 then (if i < 1858 then decide (13 ≤ count1845 b) else decide (14 ≤ count1845 b)) else (if i < 1860 then decide (15 ≤ count1845 b) else decide (16 ≤ count1845 b)))))) else (if i < 1876 then (if i < 1868 then (if i < 1864 then (if i < 1862 then decide (17 ≤ count1845 b) else (if i < 1863 then decide (18 ≤ count1845 b) else decide (19 ≤ count1845 b))) else (if i < 1866 then (if i < 1865 then decide (20 ≤ count1845 b) else decide (21 ≤ count1845 b)) else (if i < 1867 then decide (22 ≤ count1845 b) else decide (23 ≤ count1845 b)))) else (if i < 1872 then (if i < 1870 then (if i < 1869 then decide (1 ≤ count1868 b) else decide (2 ≤ count1868 b)) else (if i < 1871 then decide (3 ≤ count1868 b) else decide (4 ≤ count1868 b))) else (if i < 1874 then (if i < 1873 then decide (5 ≤ count1868 b) else decide (6 ≤ count1868 b)) else (if i < 1875 then decide (7 ≤ count1868 b) else decide (8 ≤ count1868 b))))) else (if i < 1883 then (if i < 1879 then (if i < 1877 then decide (9 ≤ count1868 b) else (if i < 1878 then decide (10 ≤ count1868 b) else decide (11 ≤ count1868 b))) else (if i < 1881 then (if i < 1880 then decide (12 ≤ count1868 b) else decide (13 ≤ count1868 b)) else (if i < 1882 then decide (14 ≤ count1868 b) else decide (15 ≤ count1868 b)))) else (if i < 1887 then (if i < 1885 then (if i < 1884 then decide (16 ≤ count1868 b) else decide (17 ≤ count1868 b)) else (if i < 1886 then decide (18 ≤ count1868 b) else decide (19 ≤ count1868 b))) else (if i < 1889 then (if i < 1888 then decide (20 ≤ count1868 b) else decide (21 ≤ count1868 b)) else (if i < 1890 then decide (22 ≤ count1868 b) else decide (23 ≤ count1868 b))))))))))))
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
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (207 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (208 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (222 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (228 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (229 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (245 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (259 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (260 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (261 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (262 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (263 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (264 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (265 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (267 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (268 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (269 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (271 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (272 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (274 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (276 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (277 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (278 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (279 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (280 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (281 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (282 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (283 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (284 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (287 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (320 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (321 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (322 : Vertex)) := rfl
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
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (399 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (400 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (401 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (403 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (406 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (407 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (409 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (411 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (InPath q (412 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (InPath q (414 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (InPath q (415 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (InPath q (485 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (2 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (5 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (12 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (21 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (23 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (27 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (31 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (67 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (68 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (70 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (71 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (72 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (75 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (80 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (82 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (85 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (88 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (90 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (92 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (136 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (141 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (150 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (154 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (158 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (194 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (197 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (202 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (204 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (206 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (208 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (228 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (260 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (262 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (263 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (269 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (271 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (274 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (278 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (282 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (284 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (322 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (325 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (330 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (334 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (336 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (343 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (347 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (351 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (389 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (394 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (396 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (398 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (400 : Vertex)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value250 (q : Snake 81) : valuation q 250 = decide (BallClauseLogic.Endpoint q (407 : Vertex)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (BallClauseLogic.Endpoint q (411 : Vertex)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (BallClauseLogic.Endpoint q (415 : Vertex)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value260 (q : Snake 81) : valuation q 260 = decide (2 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value268 (q : Snake 81) : valuation q 268 = decide (2 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value284 (q : Snake 81) : valuation q 284 = decide (2 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value298 (q : Snake 81) : valuation q 298 = decide (2 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value316 (q : Snake 81) : valuation q 316 = decide (2 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value330 (q : Snake 81) : valuation q 330 = decide (2 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value366 (q : Snake 81) : valuation q 366 = decide (2 ≤ count365 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value380 (q : Snake 81) : valuation q 380 = decide (2 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value408 (q : Snake 81) : valuation q 408 = decide (2 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value424 (q : Snake 81) : valuation q 424 = decide (2 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value440 (q : Snake 81) : valuation q 440 = decide (2 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value442 (q : Snake 81) : valuation q 442 = decide (2 ≤ count441 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value446 (q : Snake 81) : valuation q 446 = decide (2 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value448 (q : Snake 81) : valuation q 448 = decide (2 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value454 (q : Snake 81) : valuation q 454 = decide (2 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value456 (q : Snake 81) : valuation q 456 = decide (2 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value462 (q : Snake 81) : valuation q 462 = decide (2 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value466 (q : Snake 81) : valuation q 466 = decide (2 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value468 (q : Snake 81) : valuation q 468 = decide (2 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value470 (q : Snake 81) : valuation q 470 = decide (2 ≤ count469 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value472 (q : Snake 81) : valuation q 472 = decide (2 ≤ count471 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value479 (q : Snake 81) : valuation q 479 = decide (1 ≤ count479 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value485 (q : Snake 81) : valuation q 485 = decide (1 ≤ count485 (baseVal q)) := rfl
theorem value486 (q : Snake 81) : valuation q 486 = decide (2 ≤ count485 (baseVal q)) := rfl
theorem value487 (q : Snake 81) : valuation q 487 = decide (1 ≤ count487 (baseVal q)) := rfl
theorem value488 (q : Snake 81) : valuation q 488 = decide (2 ≤ count487 (baseVal q)) := rfl
theorem value489 (q : Snake 81) : valuation q 489 = decide (1 ≤ count489 (baseVal q)) := rfl
theorem value491 (q : Snake 81) : valuation q 491 = decide (1 ≤ count491 (baseVal q)) := rfl
theorem value492 (q : Snake 81) : valuation q 492 = decide (2 ≤ count491 (baseVal q)) := rfl
theorem value493 (q : Snake 81) : valuation q 493 = decide (1 ≤ count493 (baseVal q)) := rfl
theorem value495 (q : Snake 81) : valuation q 495 = decide (1 ≤ count495 (baseVal q)) := rfl
theorem value497 (q : Snake 81) : valuation q 497 = decide (1 ≤ count497 (baseVal q)) := rfl
theorem value498 (q : Snake 81) : valuation q 498 = decide (2 ≤ count497 (baseVal q)) := rfl
theorem value499 (q : Snake 81) : valuation q 499 = decide (1 ≤ count499 (baseVal q)) := rfl
theorem value500 (q : Snake 81) : valuation q 500 = decide (2 ≤ count499 (baseVal q)) := rfl
theorem value501 (q : Snake 81) : valuation q 501 = decide (1 ≤ count501 (baseVal q)) := rfl
theorem value502 (q : Snake 81) : valuation q 502 = decide (2 ≤ count501 (baseVal q)) := rfl
theorem value503 (q : Snake 81) : valuation q 503 = decide (1 ≤ count503 (baseVal q)) := rfl
theorem value504 (q : Snake 81) : valuation q 504 = decide (2 ≤ count503 (baseVal q)) := rfl
theorem value505 (q : Snake 81) : valuation q 505 = decide (1 ≤ count505 (baseVal q)) := rfl
theorem value506 (q : Snake 81) : valuation q 506 = decide (2 ≤ count505 (baseVal q)) := rfl
theorem value508 (q : Snake 81) : valuation q 508 = decide (2 ≤ count507 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (1 ≤ count1571 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (2 ≤ count1571 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (1 ≤ count1573 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (2 ≤ count1573 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (3 ≤ count1573 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (1 ≤ count1576 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (2 ≤ count1576 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (1 ≤ count1578 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (2 ≤ count1578 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (1 ≤ count1580 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (3 ≤ count1580 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (4 ≤ count1580 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (1 ≤ count1584 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (2 ≤ count1584 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (3 ≤ count1584 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (4 ≤ count1584 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (5 ≤ count1584 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (1 ≤ count1591 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (2 ≤ count1591 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (1 ≤ count1593 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (2 ≤ count1593 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (1 ≤ count1595 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (2 ≤ count1595 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (3 ≤ count1595 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (4 ≤ count1595 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (1 ≤ count1599 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (2 ≤ count1599 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (1 ≤ count1601 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (2 ≤ count1601 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (1 ≤ count1603 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (2 ≤ count1603 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (3 ≤ count1603 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (4 ≤ count1603 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (1 ≤ count1607 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (2 ≤ count1607 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (3 ≤ count1607 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (4 ≤ count1607 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (5 ≤ count1607 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (2 ≤ count1615 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (3 ≤ count1615 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (4 ≤ count1615 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (5 ≤ count1615 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (6 ≤ count1615 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (7 ≤ count1615 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (8 ≤ count1615 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (9 ≤ count1615 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (1 ≤ count1630 (baseVal q)) := rfl
theorem value1631 (q : Snake 81) : valuation q 1631 = decide (2 ≤ count1630 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (1 ≤ count1632 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (2 ≤ count1632 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (1 ≤ count1634 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (2 ≤ count1634 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (3 ≤ count1634 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (4 ≤ count1634 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (1 ≤ count1638 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (2 ≤ count1638 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (1 ≤ count1640 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (2 ≤ count1640 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (1 ≤ count1642 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (2 ≤ count1642 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (3 ≤ count1642 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (4 ≤ count1642 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (1 ≤ count1646 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (2 ≤ count1646 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (3 ≤ count1646 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (4 ≤ count1646 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (5 ≤ count1646 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (6 ≤ count1646 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (1 ≤ count1654 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (2 ≤ count1654 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (1 ≤ count1656 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (2 ≤ count1656 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (1 ≤ count1658 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (2 ≤ count1658 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (3 ≤ count1658 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (1 ≤ count1662 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (2 ≤ count1662 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (1 ≤ count1664 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (2 ≤ count1664 (baseVal q)) := rfl
theorem value1666 (q : Snake 81) : valuation q 1666 = decide (1 ≤ count1666 (baseVal q)) := rfl
theorem value1667 (q : Snake 81) : valuation q 1667 = decide (2 ≤ count1666 (baseVal q)) := rfl
theorem value1668 (q : Snake 81) : valuation q 1668 = decide (3 ≤ count1666 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (1 ≤ count1670 (baseVal q)) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (2 ≤ count1670 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (3 ≤ count1670 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (4 ≤ count1670 (baseVal q)) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (5 ≤ count1670 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (3 ≤ count1678 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (4 ≤ count1678 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (5 ≤ count1678 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (6 ≤ count1678 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (7 ≤ count1678 (baseVal q)) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (8 ≤ count1678 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (9 ≤ count1678 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (10 ≤ count1678 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (7 ≤ count1694 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (8 ≤ count1694 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (9 ≤ count1694 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (10 ≤ count1694 (baseVal q)) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (11 ≤ count1694 (baseVal q)) := rfl
theorem value1705 (q : Snake 81) : valuation q 1705 = decide (12 ≤ count1694 (baseVal q)) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (13 ≤ count1694 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (14 ≤ count1694 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (1 ≤ count1717 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (1 ≤ count1719 (baseVal q)) := rfl
theorem value1720 (q : Snake 81) : valuation q 1720 = decide (2 ≤ count1719 (baseVal q)) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (1 ≤ count1721 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (2 ≤ count1721 (baseVal q)) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (3 ≤ count1721 (baseVal q)) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (1 ≤ count1725 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (2 ≤ count1725 (baseVal q)) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (1 ≤ count1727 (baseVal q)) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (2 ≤ count1727 (baseVal q)) := rfl
theorem value1729 (q : Snake 81) : valuation q 1729 = decide (1 ≤ count1729 (baseVal q)) := rfl
theorem value1730 (q : Snake 81) : valuation q 1730 = decide (2 ≤ count1729 (baseVal q)) := rfl
theorem value1731 (q : Snake 81) : valuation q 1731 = decide (3 ≤ count1729 (baseVal q)) := rfl
theorem value1732 (q : Snake 81) : valuation q 1732 = decide (4 ≤ count1729 (baseVal q)) := rfl
theorem value1733 (q : Snake 81) : valuation q 1733 = decide (1 ≤ count1733 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (2 ≤ count1733 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (3 ≤ count1733 (baseVal q)) := rfl
theorem value1736 (q : Snake 81) : valuation q 1736 = decide (4 ≤ count1733 (baseVal q)) := rfl
theorem value1737 (q : Snake 81) : valuation q 1737 = decide (5 ≤ count1733 (baseVal q)) := rfl
theorem value1738 (q : Snake 81) : valuation q 1738 = decide (6 ≤ count1733 (baseVal q)) := rfl
theorem value1739 (q : Snake 81) : valuation q 1739 = decide (7 ≤ count1733 (baseVal q)) := rfl
theorem value1741 (q : Snake 81) : valuation q 1741 = decide (1 ≤ count1741 (baseVal q)) := rfl
theorem value1742 (q : Snake 81) : valuation q 1742 = decide (2 ≤ count1741 (baseVal q)) := rfl
theorem value1743 (q : Snake 81) : valuation q 1743 = decide (1 ≤ count1743 (baseVal q)) := rfl
theorem value1744 (q : Snake 81) : valuation q 1744 = decide (2 ≤ count1743 (baseVal q)) := rfl
theorem value1745 (q : Snake 81) : valuation q 1745 = decide (1 ≤ count1745 (baseVal q)) := rfl
theorem value1746 (q : Snake 81) : valuation q 1746 = decide (2 ≤ count1745 (baseVal q)) := rfl
theorem value1747 (q : Snake 81) : valuation q 1747 = decide (3 ≤ count1745 (baseVal q)) := rfl
theorem value1748 (q : Snake 81) : valuation q 1748 = decide (4 ≤ count1745 (baseVal q)) := rfl
theorem value1749 (q : Snake 81) : valuation q 1749 = decide (1 ≤ count1749 (baseVal q)) := rfl
theorem value1750 (q : Snake 81) : valuation q 1750 = decide (2 ≤ count1749 (baseVal q)) := rfl
theorem value1751 (q : Snake 81) : valuation q 1751 = decide (1 ≤ count1751 (baseVal q)) := rfl
theorem value1752 (q : Snake 81) : valuation q 1752 = decide (2 ≤ count1751 (baseVal q)) := rfl
theorem value1753 (q : Snake 81) : valuation q 1753 = decide (1 ≤ count1753 (baseVal q)) := rfl
theorem value1754 (q : Snake 81) : valuation q 1754 = decide (2 ≤ count1753 (baseVal q)) := rfl
theorem value1755 (q : Snake 81) : valuation q 1755 = decide (3 ≤ count1753 (baseVal q)) := rfl
theorem value1756 (q : Snake 81) : valuation q 1756 = decide (4 ≤ count1753 (baseVal q)) := rfl
theorem value1757 (q : Snake 81) : valuation q 1757 = decide (1 ≤ count1757 (baseVal q)) := rfl
theorem value1758 (q : Snake 81) : valuation q 1758 = decide (2 ≤ count1757 (baseVal q)) := rfl
theorem value1759 (q : Snake 81) : valuation q 1759 = decide (3 ≤ count1757 (baseVal q)) := rfl
theorem value1760 (q : Snake 81) : valuation q 1760 = decide (4 ≤ count1757 (baseVal q)) := rfl
theorem value1761 (q : Snake 81) : valuation q 1761 = decide (5 ≤ count1757 (baseVal q)) := rfl
theorem value1762 (q : Snake 81) : valuation q 1762 = decide (6 ≤ count1757 (baseVal q)) := rfl
theorem value1763 (q : Snake 81) : valuation q 1763 = decide (7 ≤ count1757 (baseVal q)) := rfl
theorem value1764 (q : Snake 81) : valuation q 1764 = decide (8 ≤ count1757 (baseVal q)) := rfl
theorem value1767 (q : Snake 81) : valuation q 1767 = decide (3 ≤ count1765 (baseVal q)) := rfl
theorem value1768 (q : Snake 81) : valuation q 1768 = decide (4 ≤ count1765 (baseVal q)) := rfl
theorem value1769 (q : Snake 81) : valuation q 1769 = decide (5 ≤ count1765 (baseVal q)) := rfl
theorem value1770 (q : Snake 81) : valuation q 1770 = decide (6 ≤ count1765 (baseVal q)) := rfl
theorem value1771 (q : Snake 81) : valuation q 1771 = decide (7 ≤ count1765 (baseVal q)) := rfl
theorem value1772 (q : Snake 81) : valuation q 1772 = decide (8 ≤ count1765 (baseVal q)) := rfl
theorem value1773 (q : Snake 81) : valuation q 1773 = decide (9 ≤ count1765 (baseVal q)) := rfl
theorem value1774 (q : Snake 81) : valuation q 1774 = decide (10 ≤ count1765 (baseVal q)) := rfl
theorem value1775 (q : Snake 81) : valuation q 1775 = decide (11 ≤ count1765 (baseVal q)) := rfl
theorem value1776 (q : Snake 81) : valuation q 1776 = decide (12 ≤ count1765 (baseVal q)) := rfl
theorem value1781 (q : Snake 81) : valuation q 1781 = decide (1 ≤ count1781 (baseVal q)) := rfl
theorem value1782 (q : Snake 81) : valuation q 1782 = decide (2 ≤ count1781 (baseVal q)) := rfl
theorem value1783 (q : Snake 81) : valuation q 1783 = decide (1 ≤ count1783 (baseVal q)) := rfl
theorem value1784 (q : Snake 81) : valuation q 1784 = decide (2 ≤ count1783 (baseVal q)) := rfl
theorem value1785 (q : Snake 81) : valuation q 1785 = decide (1 ≤ count1785 (baseVal q)) := rfl
theorem value1786 (q : Snake 81) : valuation q 1786 = decide (2 ≤ count1785 (baseVal q)) := rfl
theorem value1787 (q : Snake 81) : valuation q 1787 = decide (3 ≤ count1785 (baseVal q)) := rfl
theorem value1788 (q : Snake 81) : valuation q 1788 = decide (4 ≤ count1785 (baseVal q)) := rfl
theorem value1789 (q : Snake 81) : valuation q 1789 = decide (1 ≤ count1789 (baseVal q)) := rfl
theorem value1790 (q : Snake 81) : valuation q 1790 = decide (2 ≤ count1789 (baseVal q)) := rfl
theorem value1791 (q : Snake 81) : valuation q 1791 = decide (1 ≤ count1791 (baseVal q)) := rfl
theorem value1792 (q : Snake 81) : valuation q 1792 = decide (2 ≤ count1791 (baseVal q)) := rfl
theorem value1793 (q : Snake 81) : valuation q 1793 = decide (1 ≤ count1793 (baseVal q)) := rfl
theorem value1794 (q : Snake 81) : valuation q 1794 = decide (2 ≤ count1793 (baseVal q)) := rfl
theorem value1795 (q : Snake 81) : valuation q 1795 = decide (3 ≤ count1793 (baseVal q)) := rfl
theorem value1796 (q : Snake 81) : valuation q 1796 = decide (4 ≤ count1793 (baseVal q)) := rfl
theorem value1797 (q : Snake 81) : valuation q 1797 = decide (1 ≤ count1797 (baseVal q)) := rfl
theorem value1798 (q : Snake 81) : valuation q 1798 = decide (2 ≤ count1797 (baseVal q)) := rfl
theorem value1799 (q : Snake 81) : valuation q 1799 = decide (3 ≤ count1797 (baseVal q)) := rfl
theorem value1800 (q : Snake 81) : valuation q 1800 = decide (4 ≤ count1797 (baseVal q)) := rfl
theorem value1801 (q : Snake 81) : valuation q 1801 = decide (5 ≤ count1797 (baseVal q)) := rfl
theorem value1802 (q : Snake 81) : valuation q 1802 = decide (6 ≤ count1797 (baseVal q)) := rfl
theorem value1805 (q : Snake 81) : valuation q 1805 = decide (1 ≤ count1805 (baseVal q)) := rfl
theorem value1806 (q : Snake 81) : valuation q 1806 = decide (2 ≤ count1805 (baseVal q)) := rfl
theorem value1807 (q : Snake 81) : valuation q 1807 = decide (1 ≤ count1807 (baseVal q)) := rfl
theorem value1808 (q : Snake 81) : valuation q 1808 = decide (2 ≤ count1807 (baseVal q)) := rfl
theorem value1809 (q : Snake 81) : valuation q 1809 = decide (1 ≤ count1809 (baseVal q)) := rfl
theorem value1810 (q : Snake 81) : valuation q 1810 = decide (2 ≤ count1809 (baseVal q)) := rfl
theorem value1811 (q : Snake 81) : valuation q 1811 = decide (3 ≤ count1809 (baseVal q)) := rfl
theorem value1812 (q : Snake 81) : valuation q 1812 = decide (4 ≤ count1809 (baseVal q)) := rfl
theorem value1813 (q : Snake 81) : valuation q 1813 = decide (1 ≤ count1813 (baseVal q)) := rfl
theorem value1814 (q : Snake 81) : valuation q 1814 = decide (2 ≤ count1813 (baseVal q)) := rfl
theorem value1815 (q : Snake 81) : valuation q 1815 = decide (1 ≤ count1815 (baseVal q)) := rfl
theorem value1816 (q : Snake 81) : valuation q 1816 = decide (2 ≤ count1815 (baseVal q)) := rfl
theorem value1817 (q : Snake 81) : valuation q 1817 = decide (1 ≤ count1817 (baseVal q)) := rfl
theorem value1818 (q : Snake 81) : valuation q 1818 = decide (2 ≤ count1817 (baseVal q)) := rfl
theorem value1819 (q : Snake 81) : valuation q 1819 = decide (3 ≤ count1817 (baseVal q)) := rfl
theorem value1820 (q : Snake 81) : valuation q 1820 = decide (4 ≤ count1817 (baseVal q)) := rfl
theorem value1821 (q : Snake 81) : valuation q 1821 = decide (1 ≤ count1821 (baseVal q)) := rfl
theorem value1822 (q : Snake 81) : valuation q 1822 = decide (2 ≤ count1821 (baseVal q)) := rfl
theorem value1823 (q : Snake 81) : valuation q 1823 = decide (3 ≤ count1821 (baseVal q)) := rfl
theorem value1824 (q : Snake 81) : valuation q 1824 = decide (4 ≤ count1821 (baseVal q)) := rfl
theorem value1825 (q : Snake 81) : valuation q 1825 = decide (5 ≤ count1821 (baseVal q)) := rfl
theorem value1826 (q : Snake 81) : valuation q 1826 = decide (6 ≤ count1821 (baseVal q)) := rfl
theorem value1830 (q : Snake 81) : valuation q 1830 = decide (2 ≤ count1829 (baseVal q)) := rfl
theorem value1831 (q : Snake 81) : valuation q 1831 = decide (3 ≤ count1829 (baseVal q)) := rfl
theorem value1832 (q : Snake 81) : valuation q 1832 = decide (4 ≤ count1829 (baseVal q)) := rfl
theorem value1833 (q : Snake 81) : valuation q 1833 = decide (5 ≤ count1829 (baseVal q)) := rfl
theorem value1834 (q : Snake 81) : valuation q 1834 = decide (6 ≤ count1829 (baseVal q)) := rfl
theorem value1835 (q : Snake 81) : valuation q 1835 = decide (7 ≤ count1829 (baseVal q)) := rfl
theorem value1836 (q : Snake 81) : valuation q 1836 = decide (8 ≤ count1829 (baseVal q)) := rfl
theorem value1837 (q : Snake 81) : valuation q 1837 = decide (9 ≤ count1829 (baseVal q)) := rfl
theorem value1838 (q : Snake 81) : valuation q 1838 = decide (10 ≤ count1829 (baseVal q)) := rfl
theorem value1853 (q : Snake 81) : valuation q 1853 = decide (9 ≤ count1845 (baseVal q)) := rfl
theorem value1854 (q : Snake 81) : valuation q 1854 = decide (10 ≤ count1845 (baseVal q)) := rfl
theorem value1855 (q : Snake 81) : valuation q 1855 = decide (11 ≤ count1845 (baseVal q)) := rfl
theorem value1856 (q : Snake 81) : valuation q 1856 = decide (12 ≤ count1845 (baseVal q)) := rfl
theorem value1857 (q : Snake 81) : valuation q 1857 = decide (13 ≤ count1845 (baseVal q)) := rfl
theorem value1858 (q : Snake 81) : valuation q 1858 = decide (14 ≤ count1845 (baseVal q)) := rfl
theorem value1859 (q : Snake 81) : valuation q 1859 = decide (15 ≤ count1845 (baseVal q)) := rfl
theorem value1860 (q : Snake 81) : valuation q 1860 = decide (16 ≤ count1845 (baseVal q)) := rfl
theorem value1890 (q : Snake 81) : valuation q 1890 = decide (23 ≤ count1868 (baseVal q)) := rfl
theorem meaningNeg127 (b : Nat → Bool) : literal (valuationOf b) (-127) = decide (1 ≤ countLit b [-127]) := by
  change literal b (-127) = decide (1 ≤ countLit b [-127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-127) <;> decide
theorem meaningNeg125 (b : Nat → Bool) : literal (valuationOf b) (-125) = decide (1 ≤ countLit b [-125]) := by
  change literal b (-125) = decide (1 ≤ countLit b [-125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-125) <;> decide
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
theorem meaningNeg79 (b : Nat → Bool) : literal (valuationOf b) (-79) = decide (1 ≤ countLit b [-79]) := by
  change literal b (-79) = decide (1 ≤ countLit b [-79])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-79) <;> decide
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
theorem meaningNeg64 (b : Nat → Bool) : literal (valuationOf b) (-64) = decide (1 ≤ countLit b [-64]) := by
  change literal b (-64) = decide (1 ≤ countLit b [-64])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-64) <;> decide
theorem meaningNeg62 (b : Nat → Bool) : literal (valuationOf b) (-62) = decide (1 ≤ countLit b [-62]) := by
  change literal b (-62) = decide (1 ≤ countLit b [-62])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-62) <;> decide
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
theorem meaningNeg40 (b : Nat → Bool) : literal (valuationOf b) (-40) = decide (1 ≤ countLit b [-40]) := by
  change literal b (-40) = decide (1 ≤ countLit b [-40])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-40) <;> decide
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
theorem meaningNeg12 (b : Nat → Bool) : literal (valuationOf b) (-12) = decide (1 ≤ countLit b [-12]) := by
  change literal b (-12) = decide (1 ≤ countLit b [-12])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-12) <;> decide
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
theorem meaning136 (b : Nat → Bool) : literal (valuationOf b) (136) = decide (1 ≤ countLit b [136]) := by
  change literal b (136) = decide (1 ≤ countLit b [136])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (136) <;> decide
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
theorem meaning165 (b : Nat → Bool) : literal (valuationOf b) (165) = decide (1 ≤ countLit b [165]) := by
  change literal b (165) = decide (1 ≤ countLit b [165])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (165) <;> decide
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
theorem meaning177 (b : Nat → Bool) : literal (valuationOf b) (177) = decide (1 ≤ countLit b [177]) := by
  change literal b (177) = decide (1 ≤ countLit b [177])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (177) <;> decide
theorem meaning180 (b : Nat → Bool) : literal (valuationOf b) (180) = decide (1 ≤ countLit b [180]) := by
  change literal b (180) = decide (1 ≤ countLit b [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (180) <;> decide
theorem meaning181 (b : Nat → Bool) : literal (valuationOf b) (181) = decide (1 ≤ countLit b [181]) := by
  change literal b (181) = decide (1 ≤ countLit b [181])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (181) <;> decide
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
theorem meaning192 (b : Nat → Bool) : literal (valuationOf b) (192) = decide (1 ≤ countLit b [192]) := by
  change literal b (192) = decide (1 ≤ countLit b [192])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (192) <;> decide
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
theorem meaning199 (b : Nat → Bool) : literal (valuationOf b) (199) = decide (1 ≤ countLit b [199]) := by
  change literal b (199) = decide (1 ≤ countLit b [199])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (199) <;> decide
theorem meaning200 (b : Nat → Bool) : literal (valuationOf b) (200) = decide (1 ≤ countLit b [200]) := by
  change literal b (200) = decide (1 ≤ countLit b [200])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (200) <;> decide
theorem meaning203 (b : Nat → Bool) : literal (valuationOf b) (203) = decide (1 ≤ countLit b [203]) := by
  change literal b (203) = decide (1 ≤ countLit b [203])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (203) <;> decide
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
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) (213) = decide (1 ≤ countLit b [213]) := by
  change literal b (213) = decide (1 ≤ countLit b [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (213) <;> decide
theorem meaning214 (b : Nat → Bool) : literal (valuationOf b) (214) = decide (1 ≤ countLit b [214]) := by
  change literal b (214) = decide (1 ≤ countLit b [214])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (214) <;> decide
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) (217) = decide (1 ≤ countLit b [217]) := by
  change literal b (217) = decide (1 ≤ countLit b [217])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (217) <;> decide
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
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) (232) = decide (1 ≤ countLit b [232]) := by
  change literal b (232) = decide (1 ≤ countLit b [232])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (232) <;> decide
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
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) (238) = decide (1 ≤ countLit b [238]) := by
  change literal b (238) = decide (1 ≤ countLit b [238])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (238) <;> decide
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) (239) = decide (1 ≤ countLit b [239]) := by
  change literal b (239) = decide (1 ≤ countLit b [239])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (239) <;> decide
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
theorem meaning248 (b : Nat → Bool) : literal (valuationOf b) (248) = decide (1 ≤ countLit b [248]) := by
  change literal b (248) = decide (1 ≤ countLit b [248])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (248) <;> decide
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
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) (255) = decide (1 ≤ countLit b [255]) := by
  change literal b (255) = decide (1 ≤ countLit b [255])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (255) <;> decide
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning260 (b : Nat → Bool) : literal (valuationOf b) 260 = decide (2 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning268 (b : Nat → Bool) : literal (valuationOf b) 268 = decide (2 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning284 (b : Nat → Bool) : literal (valuationOf b) 284 = decide (2 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning298 (b : Nat → Bool) : literal (valuationOf b) 298 = decide (2 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning316 (b : Nat → Bool) : literal (valuationOf b) 316 = decide (2 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning330 (b : Nat → Bool) : literal (valuationOf b) 330 = decide (2 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning366 (b : Nat → Bool) : literal (valuationOf b) 366 = decide (2 ≤ count365 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning380 (b : Nat → Bool) : literal (valuationOf b) 380 = decide (2 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning408 (b : Nat → Bool) : literal (valuationOf b) 408 = decide (2 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning424 (b : Nat → Bool) : literal (valuationOf b) 424 = decide (2 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning440 (b : Nat → Bool) : literal (valuationOf b) 440 = decide (2 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning442 (b : Nat → Bool) : literal (valuationOf b) 442 = decide (2 ≤ count441 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning446 (b : Nat → Bool) : literal (valuationOf b) 446 = decide (2 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning448 (b : Nat → Bool) : literal (valuationOf b) 448 = decide (2 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning454 (b : Nat → Bool) : literal (valuationOf b) 454 = decide (2 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning456 (b : Nat → Bool) : literal (valuationOf b) 456 = decide (2 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning462 (b : Nat → Bool) : literal (valuationOf b) 462 = decide (2 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning466 (b : Nat → Bool) : literal (valuationOf b) 466 = decide (2 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning468 (b : Nat → Bool) : literal (valuationOf b) 468 = decide (2 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning470 (b : Nat → Bool) : literal (valuationOf b) 470 = decide (2 ≤ count469 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning472 (b : Nat → Bool) : literal (valuationOf b) 472 = decide (2 ≤ count471 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning479 (b : Nat → Bool) : literal (valuationOf b) 479 = decide (1 ≤ count479 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning485 (b : Nat → Bool) : literal (valuationOf b) 485 = decide (1 ≤ count485 b) := rfl
theorem meaning486 (b : Nat → Bool) : literal (valuationOf b) 486 = decide (2 ≤ count485 b) := rfl
theorem meaning487 (b : Nat → Bool) : literal (valuationOf b) 487 = decide (1 ≤ count487 b) := rfl
theorem meaning488 (b : Nat → Bool) : literal (valuationOf b) 488 = decide (2 ≤ count487 b) := rfl
theorem meaning489 (b : Nat → Bool) : literal (valuationOf b) 489 = decide (1 ≤ count489 b) := rfl
theorem meaning491 (b : Nat → Bool) : literal (valuationOf b) 491 = decide (1 ≤ count491 b) := rfl
theorem meaning492 (b : Nat → Bool) : literal (valuationOf b) 492 = decide (2 ≤ count491 b) := rfl
theorem meaning493 (b : Nat → Bool) : literal (valuationOf b) 493 = decide (1 ≤ count493 b) := rfl
theorem meaning495 (b : Nat → Bool) : literal (valuationOf b) 495 = decide (1 ≤ count495 b) := rfl
theorem meaning497 (b : Nat → Bool) : literal (valuationOf b) 497 = decide (1 ≤ count497 b) := rfl
theorem meaning498 (b : Nat → Bool) : literal (valuationOf b) 498 = decide (2 ≤ count497 b) := rfl
theorem meaning499 (b : Nat → Bool) : literal (valuationOf b) 499 = decide (1 ≤ count499 b) := rfl
theorem meaning500 (b : Nat → Bool) : literal (valuationOf b) 500 = decide (2 ≤ count499 b) := rfl
theorem meaning501 (b : Nat → Bool) : literal (valuationOf b) 501 = decide (1 ≤ count501 b) := rfl
theorem meaning502 (b : Nat → Bool) : literal (valuationOf b) 502 = decide (2 ≤ count501 b) := rfl
theorem meaning503 (b : Nat → Bool) : literal (valuationOf b) 503 = decide (1 ≤ count503 b) := rfl
theorem meaning504 (b : Nat → Bool) : literal (valuationOf b) 504 = decide (2 ≤ count503 b) := rfl
theorem meaning505 (b : Nat → Bool) : literal (valuationOf b) 505 = decide (1 ≤ count505 b) := rfl
theorem meaning506 (b : Nat → Bool) : literal (valuationOf b) 506 = decide (2 ≤ count505 b) := rfl
theorem meaning508 (b : Nat → Bool) : literal (valuationOf b) 508 = decide (2 ≤ count507 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (1 ≤ count1571 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (2 ≤ count1571 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (1 ≤ count1573 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (2 ≤ count1573 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (3 ≤ count1573 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (1 ≤ count1576 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (2 ≤ count1576 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (1 ≤ count1578 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (2 ≤ count1578 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (1 ≤ count1580 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (3 ≤ count1580 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (4 ≤ count1580 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (1 ≤ count1584 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (2 ≤ count1584 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (3 ≤ count1584 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (4 ≤ count1584 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (5 ≤ count1584 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (1 ≤ count1591 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (2 ≤ count1591 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (1 ≤ count1593 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (2 ≤ count1593 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (1 ≤ count1595 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (2 ≤ count1595 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (3 ≤ count1595 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (4 ≤ count1595 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (1 ≤ count1599 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (2 ≤ count1599 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (1 ≤ count1601 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (2 ≤ count1601 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (1 ≤ count1603 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (2 ≤ count1603 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (3 ≤ count1603 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (4 ≤ count1603 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (1 ≤ count1607 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (2 ≤ count1607 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (3 ≤ count1607 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (4 ≤ count1607 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (5 ≤ count1607 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (2 ≤ count1615 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (3 ≤ count1615 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (4 ≤ count1615 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (5 ≤ count1615 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (6 ≤ count1615 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (7 ≤ count1615 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (8 ≤ count1615 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (9 ≤ count1615 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (1 ≤ count1630 b) := rfl
theorem meaning1631 (b : Nat → Bool) : literal (valuationOf b) 1631 = decide (2 ≤ count1630 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (1 ≤ count1632 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (2 ≤ count1632 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (1 ≤ count1634 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (2 ≤ count1634 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (3 ≤ count1634 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (4 ≤ count1634 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (1 ≤ count1638 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (2 ≤ count1638 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (1 ≤ count1640 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (2 ≤ count1640 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (1 ≤ count1642 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (2 ≤ count1642 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (3 ≤ count1642 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (4 ≤ count1642 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (1 ≤ count1646 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (2 ≤ count1646 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (3 ≤ count1646 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (4 ≤ count1646 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (5 ≤ count1646 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (6 ≤ count1646 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (1 ≤ count1654 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (2 ≤ count1654 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (1 ≤ count1656 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (2 ≤ count1656 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (1 ≤ count1658 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (2 ≤ count1658 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (3 ≤ count1658 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (1 ≤ count1662 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (2 ≤ count1662 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (1 ≤ count1664 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (2 ≤ count1664 b) := rfl
theorem meaning1666 (b : Nat → Bool) : literal (valuationOf b) 1666 = decide (1 ≤ count1666 b) := rfl
theorem meaning1667 (b : Nat → Bool) : literal (valuationOf b) 1667 = decide (2 ≤ count1666 b) := rfl
theorem meaning1668 (b : Nat → Bool) : literal (valuationOf b) 1668 = decide (3 ≤ count1666 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (1 ≤ count1670 b) := rfl
theorem meaning1671 (b : Nat → Bool) : literal (valuationOf b) 1671 = decide (2 ≤ count1670 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (3 ≤ count1670 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (4 ≤ count1670 b) := rfl
theorem meaning1674 (b : Nat → Bool) : literal (valuationOf b) 1674 = decide (5 ≤ count1670 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (3 ≤ count1678 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (4 ≤ count1678 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (5 ≤ count1678 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (6 ≤ count1678 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (7 ≤ count1678 b) := rfl
theorem meaning1685 (b : Nat → Bool) : literal (valuationOf b) 1685 = decide (8 ≤ count1678 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (9 ≤ count1678 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (10 ≤ count1678 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (7 ≤ count1694 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (8 ≤ count1694 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (9 ≤ count1694 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (10 ≤ count1694 b) := rfl
theorem meaning1704 (b : Nat → Bool) : literal (valuationOf b) 1704 = decide (11 ≤ count1694 b) := rfl
theorem meaning1705 (b : Nat → Bool) : literal (valuationOf b) 1705 = decide (12 ≤ count1694 b) := rfl
theorem meaning1706 (b : Nat → Bool) : literal (valuationOf b) 1706 = decide (13 ≤ count1694 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (14 ≤ count1694 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (1 ≤ count1717 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (1 ≤ count1719 b) := rfl
theorem meaning1720 (b : Nat → Bool) : literal (valuationOf b) 1720 = decide (2 ≤ count1719 b) := rfl
theorem meaning1721 (b : Nat → Bool) : literal (valuationOf b) 1721 = decide (1 ≤ count1721 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (2 ≤ count1721 b) := rfl
theorem meaning1723 (b : Nat → Bool) : literal (valuationOf b) 1723 = decide (3 ≤ count1721 b) := rfl
theorem meaning1725 (b : Nat → Bool) : literal (valuationOf b) 1725 = decide (1 ≤ count1725 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (2 ≤ count1725 b) := rfl
theorem meaning1727 (b : Nat → Bool) : literal (valuationOf b) 1727 = decide (1 ≤ count1727 b) := rfl
theorem meaning1728 (b : Nat → Bool) : literal (valuationOf b) 1728 = decide (2 ≤ count1727 b) := rfl
theorem meaning1729 (b : Nat → Bool) : literal (valuationOf b) 1729 = decide (1 ≤ count1729 b) := rfl
theorem meaning1730 (b : Nat → Bool) : literal (valuationOf b) 1730 = decide (2 ≤ count1729 b) := rfl
theorem meaning1731 (b : Nat → Bool) : literal (valuationOf b) 1731 = decide (3 ≤ count1729 b) := rfl
theorem meaning1732 (b : Nat → Bool) : literal (valuationOf b) 1732 = decide (4 ≤ count1729 b) := rfl
theorem meaning1733 (b : Nat → Bool) : literal (valuationOf b) 1733 = decide (1 ≤ count1733 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (2 ≤ count1733 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (3 ≤ count1733 b) := rfl
theorem meaning1736 (b : Nat → Bool) : literal (valuationOf b) 1736 = decide (4 ≤ count1733 b) := rfl
theorem meaning1737 (b : Nat → Bool) : literal (valuationOf b) 1737 = decide (5 ≤ count1733 b) := rfl
theorem meaning1738 (b : Nat → Bool) : literal (valuationOf b) 1738 = decide (6 ≤ count1733 b) := rfl
theorem meaning1739 (b : Nat → Bool) : literal (valuationOf b) 1739 = decide (7 ≤ count1733 b) := rfl
theorem meaning1741 (b : Nat → Bool) : literal (valuationOf b) 1741 = decide (1 ≤ count1741 b) := rfl
theorem meaning1742 (b : Nat → Bool) : literal (valuationOf b) 1742 = decide (2 ≤ count1741 b) := rfl
theorem meaning1743 (b : Nat → Bool) : literal (valuationOf b) 1743 = decide (1 ≤ count1743 b) := rfl
theorem meaning1744 (b : Nat → Bool) : literal (valuationOf b) 1744 = decide (2 ≤ count1743 b) := rfl
theorem meaning1745 (b : Nat → Bool) : literal (valuationOf b) 1745 = decide (1 ≤ count1745 b) := rfl
theorem meaning1746 (b : Nat → Bool) : literal (valuationOf b) 1746 = decide (2 ≤ count1745 b) := rfl
theorem meaning1747 (b : Nat → Bool) : literal (valuationOf b) 1747 = decide (3 ≤ count1745 b) := rfl
theorem meaning1748 (b : Nat → Bool) : literal (valuationOf b) 1748 = decide (4 ≤ count1745 b) := rfl
theorem meaning1749 (b : Nat → Bool) : literal (valuationOf b) 1749 = decide (1 ≤ count1749 b) := rfl
theorem meaning1750 (b : Nat → Bool) : literal (valuationOf b) 1750 = decide (2 ≤ count1749 b) := rfl
theorem meaning1751 (b : Nat → Bool) : literal (valuationOf b) 1751 = decide (1 ≤ count1751 b) := rfl
theorem meaning1752 (b : Nat → Bool) : literal (valuationOf b) 1752 = decide (2 ≤ count1751 b) := rfl
theorem meaning1753 (b : Nat → Bool) : literal (valuationOf b) 1753 = decide (1 ≤ count1753 b) := rfl
theorem meaning1754 (b : Nat → Bool) : literal (valuationOf b) 1754 = decide (2 ≤ count1753 b) := rfl
theorem meaning1755 (b : Nat → Bool) : literal (valuationOf b) 1755 = decide (3 ≤ count1753 b) := rfl
theorem meaning1756 (b : Nat → Bool) : literal (valuationOf b) 1756 = decide (4 ≤ count1753 b) := rfl
theorem meaning1757 (b : Nat → Bool) : literal (valuationOf b) 1757 = decide (1 ≤ count1757 b) := rfl
theorem meaning1758 (b : Nat → Bool) : literal (valuationOf b) 1758 = decide (2 ≤ count1757 b) := rfl
theorem meaning1759 (b : Nat → Bool) : literal (valuationOf b) 1759 = decide (3 ≤ count1757 b) := rfl
theorem meaning1760 (b : Nat → Bool) : literal (valuationOf b) 1760 = decide (4 ≤ count1757 b) := rfl
theorem meaning1761 (b : Nat → Bool) : literal (valuationOf b) 1761 = decide (5 ≤ count1757 b) := rfl
theorem meaning1762 (b : Nat → Bool) : literal (valuationOf b) 1762 = decide (6 ≤ count1757 b) := rfl
theorem meaning1763 (b : Nat → Bool) : literal (valuationOf b) 1763 = decide (7 ≤ count1757 b) := rfl
theorem meaning1764 (b : Nat → Bool) : literal (valuationOf b) 1764 = decide (8 ≤ count1757 b) := rfl
theorem meaning1767 (b : Nat → Bool) : literal (valuationOf b) 1767 = decide (3 ≤ count1765 b) := rfl
theorem meaning1768 (b : Nat → Bool) : literal (valuationOf b) 1768 = decide (4 ≤ count1765 b) := rfl
theorem meaning1769 (b : Nat → Bool) : literal (valuationOf b) 1769 = decide (5 ≤ count1765 b) := rfl
theorem meaning1770 (b : Nat → Bool) : literal (valuationOf b) 1770 = decide (6 ≤ count1765 b) := rfl
theorem meaning1771 (b : Nat → Bool) : literal (valuationOf b) 1771 = decide (7 ≤ count1765 b) := rfl
theorem meaning1772 (b : Nat → Bool) : literal (valuationOf b) 1772 = decide (8 ≤ count1765 b) := rfl
theorem meaning1773 (b : Nat → Bool) : literal (valuationOf b) 1773 = decide (9 ≤ count1765 b) := rfl
theorem meaning1774 (b : Nat → Bool) : literal (valuationOf b) 1774 = decide (10 ≤ count1765 b) := rfl
theorem meaning1775 (b : Nat → Bool) : literal (valuationOf b) 1775 = decide (11 ≤ count1765 b) := rfl
theorem meaning1776 (b : Nat → Bool) : literal (valuationOf b) 1776 = decide (12 ≤ count1765 b) := rfl
theorem meaning1781 (b : Nat → Bool) : literal (valuationOf b) 1781 = decide (1 ≤ count1781 b) := rfl
theorem meaning1782 (b : Nat → Bool) : literal (valuationOf b) 1782 = decide (2 ≤ count1781 b) := rfl
theorem meaning1783 (b : Nat → Bool) : literal (valuationOf b) 1783 = decide (1 ≤ count1783 b) := rfl
theorem meaning1784 (b : Nat → Bool) : literal (valuationOf b) 1784 = decide (2 ≤ count1783 b) := rfl
theorem meaning1785 (b : Nat → Bool) : literal (valuationOf b) 1785 = decide (1 ≤ count1785 b) := rfl
theorem meaning1786 (b : Nat → Bool) : literal (valuationOf b) 1786 = decide (2 ≤ count1785 b) := rfl
theorem meaning1787 (b : Nat → Bool) : literal (valuationOf b) 1787 = decide (3 ≤ count1785 b) := rfl
theorem meaning1788 (b : Nat → Bool) : literal (valuationOf b) 1788 = decide (4 ≤ count1785 b) := rfl
theorem meaning1789 (b : Nat → Bool) : literal (valuationOf b) 1789 = decide (1 ≤ count1789 b) := rfl
theorem meaning1790 (b : Nat → Bool) : literal (valuationOf b) 1790 = decide (2 ≤ count1789 b) := rfl
theorem meaning1791 (b : Nat → Bool) : literal (valuationOf b) 1791 = decide (1 ≤ count1791 b) := rfl
theorem meaning1792 (b : Nat → Bool) : literal (valuationOf b) 1792 = decide (2 ≤ count1791 b) := rfl
theorem meaning1793 (b : Nat → Bool) : literal (valuationOf b) 1793 = decide (1 ≤ count1793 b) := rfl
theorem meaning1794 (b : Nat → Bool) : literal (valuationOf b) 1794 = decide (2 ≤ count1793 b) := rfl
theorem meaning1795 (b : Nat → Bool) : literal (valuationOf b) 1795 = decide (3 ≤ count1793 b) := rfl
theorem meaning1796 (b : Nat → Bool) : literal (valuationOf b) 1796 = decide (4 ≤ count1793 b) := rfl
theorem meaning1797 (b : Nat → Bool) : literal (valuationOf b) 1797 = decide (1 ≤ count1797 b) := rfl
theorem meaning1798 (b : Nat → Bool) : literal (valuationOf b) 1798 = decide (2 ≤ count1797 b) := rfl
theorem meaning1799 (b : Nat → Bool) : literal (valuationOf b) 1799 = decide (3 ≤ count1797 b) := rfl
theorem meaning1800 (b : Nat → Bool) : literal (valuationOf b) 1800 = decide (4 ≤ count1797 b) := rfl
theorem meaning1801 (b : Nat → Bool) : literal (valuationOf b) 1801 = decide (5 ≤ count1797 b) := rfl
theorem meaning1802 (b : Nat → Bool) : literal (valuationOf b) 1802 = decide (6 ≤ count1797 b) := rfl
theorem meaning1805 (b : Nat → Bool) : literal (valuationOf b) 1805 = decide (1 ≤ count1805 b) := rfl
theorem meaning1806 (b : Nat → Bool) : literal (valuationOf b) 1806 = decide (2 ≤ count1805 b) := rfl
theorem meaning1807 (b : Nat → Bool) : literal (valuationOf b) 1807 = decide (1 ≤ count1807 b) := rfl
theorem meaning1808 (b : Nat → Bool) : literal (valuationOf b) 1808 = decide (2 ≤ count1807 b) := rfl
theorem meaning1809 (b : Nat → Bool) : literal (valuationOf b) 1809 = decide (1 ≤ count1809 b) := rfl
theorem meaning1810 (b : Nat → Bool) : literal (valuationOf b) 1810 = decide (2 ≤ count1809 b) := rfl
theorem meaning1811 (b : Nat → Bool) : literal (valuationOf b) 1811 = decide (3 ≤ count1809 b) := rfl
theorem meaning1812 (b : Nat → Bool) : literal (valuationOf b) 1812 = decide (4 ≤ count1809 b) := rfl
theorem meaning1813 (b : Nat → Bool) : literal (valuationOf b) 1813 = decide (1 ≤ count1813 b) := rfl
theorem meaning1814 (b : Nat → Bool) : literal (valuationOf b) 1814 = decide (2 ≤ count1813 b) := rfl
theorem meaning1815 (b : Nat → Bool) : literal (valuationOf b) 1815 = decide (1 ≤ count1815 b) := rfl
theorem meaning1816 (b : Nat → Bool) : literal (valuationOf b) 1816 = decide (2 ≤ count1815 b) := rfl
theorem meaning1817 (b : Nat → Bool) : literal (valuationOf b) 1817 = decide (1 ≤ count1817 b) := rfl
theorem meaning1818 (b : Nat → Bool) : literal (valuationOf b) 1818 = decide (2 ≤ count1817 b) := rfl
theorem meaning1819 (b : Nat → Bool) : literal (valuationOf b) 1819 = decide (3 ≤ count1817 b) := rfl
theorem meaning1820 (b : Nat → Bool) : literal (valuationOf b) 1820 = decide (4 ≤ count1817 b) := rfl
theorem meaning1821 (b : Nat → Bool) : literal (valuationOf b) 1821 = decide (1 ≤ count1821 b) := rfl
theorem meaning1822 (b : Nat → Bool) : literal (valuationOf b) 1822 = decide (2 ≤ count1821 b) := rfl
theorem meaning1823 (b : Nat → Bool) : literal (valuationOf b) 1823 = decide (3 ≤ count1821 b) := rfl
theorem meaning1824 (b : Nat → Bool) : literal (valuationOf b) 1824 = decide (4 ≤ count1821 b) := rfl
theorem meaning1825 (b : Nat → Bool) : literal (valuationOf b) 1825 = decide (5 ≤ count1821 b) := rfl
theorem meaning1826 (b : Nat → Bool) : literal (valuationOf b) 1826 = decide (6 ≤ count1821 b) := rfl
theorem meaning1830 (b : Nat → Bool) : literal (valuationOf b) 1830 = decide (2 ≤ count1829 b) := rfl
theorem meaning1831 (b : Nat → Bool) : literal (valuationOf b) 1831 = decide (3 ≤ count1829 b) := rfl
theorem meaning1832 (b : Nat → Bool) : literal (valuationOf b) 1832 = decide (4 ≤ count1829 b) := rfl
theorem meaning1833 (b : Nat → Bool) : literal (valuationOf b) 1833 = decide (5 ≤ count1829 b) := rfl
theorem meaning1834 (b : Nat → Bool) : literal (valuationOf b) 1834 = decide (6 ≤ count1829 b) := rfl
theorem meaning1835 (b : Nat → Bool) : literal (valuationOf b) 1835 = decide (7 ≤ count1829 b) := rfl
theorem meaning1836 (b : Nat → Bool) : literal (valuationOf b) 1836 = decide (8 ≤ count1829 b) := rfl
theorem meaning1837 (b : Nat → Bool) : literal (valuationOf b) 1837 = decide (9 ≤ count1829 b) := rfl
theorem meaning1838 (b : Nat → Bool) : literal (valuationOf b) 1838 = decide (10 ≤ count1829 b) := rfl
theorem meaning1853 (b : Nat → Bool) : literal (valuationOf b) 1853 = decide (9 ≤ count1845 b) := rfl
theorem meaning1854 (b : Nat → Bool) : literal (valuationOf b) 1854 = decide (10 ≤ count1845 b) := rfl
theorem meaning1855 (b : Nat → Bool) : literal (valuationOf b) 1855 = decide (11 ≤ count1845 b) := rfl
theorem meaning1856 (b : Nat → Bool) : literal (valuationOf b) 1856 = decide (12 ≤ count1845 b) := rfl
theorem meaning1857 (b : Nat → Bool) : literal (valuationOf b) 1857 = decide (13 ≤ count1845 b) := rfl
theorem meaning1858 (b : Nat → Bool) : literal (valuationOf b) 1858 = decide (14 ≤ count1845 b) := rfl
theorem meaning1859 (b : Nat → Bool) : literal (valuationOf b) 1859 = decide (15 ≤ count1845 b) := rfl
theorem meaning1860 (b : Nat → Bool) : literal (valuationOf b) 1860 = decide (16 ≤ count1845 b) := rfl
theorem meaning1890 (b : Nat → Bool) : literal (valuationOf b) 1890 = decide (23 ≤ count1868 b) := rfl
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
end Snake9.Regrowth.E112055
