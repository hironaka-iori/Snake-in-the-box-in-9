import E112089Data
namespace Snake9.Regrowth.E112089
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 124 then (if i < 62 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (3 : Vertex)) else decide (InPath q (5 : Vertex))) else (if i < 6 then decide (InPath q (7 : Vertex)) else decide (InPath q (9 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (10 : Vertex)) else decide (InPath q (11 : Vertex))) else (if i < 10 then decide (InPath q (13 : Vertex)) else decide (InPath q (14 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (16 : Vertex)) else decide (InPath q (18 : Vertex))) else (if i < 14 then decide (InPath q (19 : Vertex)) else decide (InPath q (22 : Vertex)))))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then decide (InPath q (28 : Vertex)) else decide (InPath q (29 : Vertex))) else (if i < 18 then decide (InPath q (30 : Vertex)) else decide (InPath q (64 : Vertex)))) else (if i < 21 then (if i < 20 then decide (InPath q (65 : Vertex)) else decide (InPath q (66 : Vertex))) else (if i < 22 then decide (InPath q (68 : Vertex)) else decide (InPath q (70 : Vertex))))) else (if i < 27 then (if i < 25 then (if i < 24 then decide (InPath q (72 : Vertex)) else decide (InPath q (73 : Vertex))) else (if i < 26 then decide (InPath q (76 : Vertex)) else decide (InPath q (78 : Vertex)))) else (if i < 29 then (if i < 28 then decide (InPath q (79 : Vertex)) else decide (InPath q (83 : Vertex))) else (if i < 30 then decide (InPath q (84 : Vertex)) else decide (InPath q (85 : Vertex))))))) else (if i < 46 then (if i < 38 then (if i < 34 then (if i < 32 then decide (InPath q (87 : Vertex)) else (if i < 33 then decide (InPath q (88 : Vertex)) else decide (InPath q (90 : Vertex)))) else (if i < 36 then (if i < 35 then decide (InPath q (91 : Vertex)) else decide (InPath q (95 : Vertex))) else (if i < 37 then decide (InPath q (129 : Vertex)) else decide (InPath q (130 : Vertex))))) else (if i < 42 then (if i < 40 then (if i < 39 then decide (InPath q (132 : Vertex)) else decide (InPath q (134 : Vertex))) else (if i < 41 then decide (InPath q (136 : Vertex)) else decide (InPath q (137 : Vertex)))) else (if i < 44 then (if i < 43 then decide (InPath q (138 : Vertex)) else decide (InPath q (139 : Vertex))) else (if i < 45 then decide (InPath q (140 : Vertex)) else decide (InPath q (143 : Vertex)))))) else (if i < 54 then (if i < 50 then (if i < 48 then (if i < 47 then decide (InPath q (145 : Vertex)) else decide (InPath q (148 : Vertex))) else (if i < 49 then decide (InPath q (149 : Vertex)) else decide (InPath q (150 : Vertex)))) else (if i < 52 then (if i < 51 then decide (InPath q (151 : Vertex)) else decide (InPath q (152 : Vertex))) else (if i < 53 then decide (InPath q (153 : Vertex)) else decide (InPath q (154 : Vertex))))) else (if i < 58 then (if i < 56 then (if i < 55 then decide (InPath q (155 : Vertex)) else decide (InPath q (159 : Vertex))) else (if i < 57 then decide (InPath q (193 : Vertex)) else decide (InPath q (194 : Vertex)))) else (if i < 60 then (if i < 59 then decide (InPath q (195 : Vertex)) else decide (InPath q (197 : Vertex))) else (if i < 61 then decide (InPath q (198 : Vertex)) else decide (InPath q (199 : Vertex)))))))) else (if i < 93 then (if i < 77 then (if i < 69 then (if i < 65 then (if i < 63 then decide (InPath q (200 : Vertex)) else (if i < 64 then decide (InPath q (201 : Vertex)) else decide (InPath q (203 : Vertex)))) else (if i < 67 then (if i < 66 then decide (InPath q (204 : Vertex)) else decide (InPath q (205 : Vertex))) else (if i < 68 then decide (InPath q (206 : Vertex)) else decide (InPath q (207 : Vertex))))) else (if i < 73 then (if i < 71 then (if i < 70 then decide (InPath q (208 : Vertex)) else decide (InPath q (209 : Vertex))) else (if i < 72 then decide (InPath q (210 : Vertex)) else decide (InPath q (211 : Vertex)))) else (if i < 75 then (if i < 74 then decide (InPath q (214 : Vertex)) else decide (InPath q (216 : Vertex))) else (if i < 76 then decide (InPath q (218 : Vertex)) else decide (InPath q (220 : Vertex)))))) else (if i < 85 then (if i < 81 then (if i < 79 then (if i < 78 then decide (InPath q (221 : Vertex)) else decide (InPath q (222 : Vertex))) else (if i < 80 then decide (InPath q (259 : Vertex)) else decide (InPath q (264 : Vertex)))) else (if i < 83 then (if i < 82 then decide (InPath q (266 : Vertex)) else decide (InPath q (282 : Vertex))) else (if i < 84 then decide (InPath q (323 : Vertex)) else decide (InPath q (325 : Vertex))))) else (if i < 89 then (if i < 87 then (if i < 86 then decide (InPath q (327 : Vertex)) else decide (InPath q (330 : Vertex))) else (if i < 88 then decide (InPath q (331 : Vertex)) else decide (InPath q (332 : Vertex)))) else (if i < 91 then (if i < 90 then decide (InPath q (333 : Vertex)) else decide (InPath q (384 : Vertex))) else (if i < 92 then decide (InPath q (386 : Vertex)) else decide (InPath q (387 : Vertex))))))) else (if i < 108 then (if i < 100 then (if i < 96 then (if i < 94 then decide (InPath q (389 : Vertex)) else (if i < 95 then decide (InPath q (391 : Vertex)) else decide (InPath q (394 : Vertex)))) else (if i < 98 then (if i < 97 then decide (InPath q (395 : Vertex)) else decide (InPath q (396 : Vertex))) else (if i < 99 then decide (InPath q (397 : Vertex)) else decide (InPath q (400 : Vertex))))) else (if i < 104 then (if i < 102 then (if i < 101 then decide (InPath q (401 : Vertex)) else decide (InPath q (402 : Vertex))) else (if i < 103 then decide (InPath q (403 : Vertex)) else decide (InPath q (406 : Vertex)))) else (if i < 106 then (if i < 105 then decide (InPath q (412 : Vertex)) else decide (InPath q (413 : Vertex))) else (if i < 107 then decide (InPath q (414 : Vertex)) else decide (InPath q (448 : Vertex)))))) else (if i < 116 then (if i < 112 then (if i < 110 then (if i < 109 then decide (InPath q (449 : Vertex)) else decide (InPath q (450 : Vertex))) else (if i < 111 then decide (InPath q (452 : Vertex)) else decide (InPath q (454 : Vertex)))) else (if i < 114 then (if i < 113 then decide (InPath q (456 : Vertex)) else decide (InPath q (457 : Vertex))) else (if i < 115 then decide (InPath q (462 : Vertex)) else decide (InPath q (463 : Vertex))))) else (if i < 120 then (if i < 118 then (if i < 117 then decide (InPath q (467 : Vertex)) else decide (InPath q (468 : Vertex))) else (if i < 119 then decide (InPath q (469 : Vertex)) else decide (InPath q (471 : Vertex)))) else (if i < 122 then (if i < 121 then decide (InPath q (472 : Vertex)) else decide (InPath q (474 : Vertex))) else (if i < 123 then decide (InPath q (475 : Vertex)) else decide (InPath q (477 : Vertex))))))))) else (if i < 186 then (if i < 155 then (if i < 139 then (if i < 131 then (if i < 127 then (if i < 125 then decide (InPath q (479 : Vertex)) else (if i < 126 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 129 then (if i < 128 then decide (BallClauseLogic.Endpoint q (3 : Vertex)) else decide (BallClauseLogic.Endpoint q (5 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (7 : Vertex)) else decide (BallClauseLogic.Endpoint q (9 : Vertex))))) else (if i < 135 then (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else decide (BallClauseLogic.Endpoint q (11 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (13 : Vertex)) else decide (BallClauseLogic.Endpoint q (14 : Vertex)))) else (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (16 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else decide (BallClauseLogic.Endpoint q (22 : Vertex)))))) else (if i < 147 then (if i < 143 then (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (30 : Vertex)) else decide (BallClauseLogic.Endpoint q (64 : Vertex)))) else (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (65 : Vertex)) else decide (BallClauseLogic.Endpoint q (66 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (68 : Vertex)) else decide (BallClauseLogic.Endpoint q (70 : Vertex))))) else (if i < 151 then (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else decide (BallClauseLogic.Endpoint q (73 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (76 : Vertex)) else decide (BallClauseLogic.Endpoint q (78 : Vertex)))) else (if i < 153 then (if i < 152 then decide (BallClauseLogic.Endpoint q (79 : Vertex)) else decide (BallClauseLogic.Endpoint q (83 : Vertex))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (85 : Vertex))))))) else (if i < 170 then (if i < 162 then (if i < 158 then (if i < 156 then decide (BallClauseLogic.Endpoint q (87 : Vertex)) else (if i < 157 then decide (BallClauseLogic.Endpoint q (88 : Vertex)) else decide (BallClauseLogic.Endpoint q (90 : Vertex)))) else (if i < 160 then (if i < 159 then decide (BallClauseLogic.Endpoint q (91 : Vertex)) else decide (BallClauseLogic.Endpoint q (95 : Vertex))) else (if i < 161 then decide (BallClauseLogic.Endpoint q (129 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex))))) else (if i < 166 then (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (136 : Vertex)) else decide (BallClauseLogic.Endpoint q (137 : Vertex)))) else (if i < 168 then (if i < 167 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex))) else (if i < 169 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else decide (BallClauseLogic.Endpoint q (143 : Vertex)))))) else (if i < 178 then (if i < 174 then (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (145 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else decide (BallClauseLogic.Endpoint q (150 : Vertex)))) else (if i < 176 then (if i < 175 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (152 : Vertex))) else (if i < 177 then decide (BallClauseLogic.Endpoint q (153 : Vertex)) else decide (BallClauseLogic.Endpoint q (154 : Vertex))))) else (if i < 182 then (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (155 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else decide (BallClauseLogic.Endpoint q (194 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (195 : Vertex)) else decide (BallClauseLogic.Endpoint q (197 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else decide (BallClauseLogic.Endpoint q (199 : Vertex)))))))) else (if i < 217 then (if i < 201 then (if i < 193 then (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (200 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (201 : Vertex)) else decide (BallClauseLogic.Endpoint q (203 : Vertex)))) else (if i < 191 then (if i < 190 then decide (BallClauseLogic.Endpoint q (204 : Vertex)) else decide (BallClauseLogic.Endpoint q (205 : Vertex))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (206 : Vertex)) else decide (BallClauseLogic.Endpoint q (207 : Vertex))))) else (if i < 197 then (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (208 : Vertex)) else decide (BallClauseLogic.Endpoint q (209 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (210 : Vertex)) else decide (BallClauseLogic.Endpoint q (211 : Vertex)))) else (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else decide (BallClauseLogic.Endpoint q (216 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (220 : Vertex)))))) else (if i < 209 then (if i < 205 then (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else decide (BallClauseLogic.Endpoint q (222 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (259 : Vertex)) else decide (BallClauseLogic.Endpoint q (264 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (282 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (323 : Vertex)) else decide (BallClauseLogic.Endpoint q (325 : Vertex))))) else (if i < 213 then (if i < 211 then (if i < 210 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (330 : Vertex))) else (if i < 212 then decide (BallClauseLogic.Endpoint q (331 : Vertex)) else decide (BallClauseLogic.Endpoint q (332 : Vertex)))) else (if i < 215 then (if i < 214 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 216 then decide (BallClauseLogic.Endpoint q (386 : Vertex)) else decide (BallClauseLogic.Endpoint q (387 : Vertex))))))) else (if i < 233 then (if i < 225 then (if i < 221 then (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (389 : Vertex)) else decide (BallClauseLogic.Endpoint q (391 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (394 : Vertex)) else decide (BallClauseLogic.Endpoint q (395 : Vertex)))) else (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (396 : Vertex)) else decide (BallClauseLogic.Endpoint q (397 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (400 : Vertex)) else decide (BallClauseLogic.Endpoint q (401 : Vertex))))) else (if i < 229 then (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (402 : Vertex)) else decide (BallClauseLogic.Endpoint q (403 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else decide (BallClauseLogic.Endpoint q (412 : Vertex)))) else (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (413 : Vertex)) else decide (BallClauseLogic.Endpoint q (414 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (448 : Vertex)) else decide (BallClauseLogic.Endpoint q (449 : Vertex)))))) else (if i < 241 then (if i < 237 then (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (450 : Vertex)) else decide (BallClauseLogic.Endpoint q (452 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (454 : Vertex)) else decide (BallClauseLogic.Endpoint q (456 : Vertex)))) else (if i < 239 then (if i < 238 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else decide (BallClauseLogic.Endpoint q (462 : Vertex))) else (if i < 240 then decide (BallClauseLogic.Endpoint q (463 : Vertex)) else decide (BallClauseLogic.Endpoint q (467 : Vertex))))) else (if i < 245 then (if i < 243 then (if i < 242 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else decide (BallClauseLogic.Endpoint q (469 : Vertex))) else (if i < 244 then decide (BallClauseLogic.Endpoint q (471 : Vertex)) else decide (BallClauseLogic.Endpoint q (472 : Vertex)))) else (if i < 247 then (if i < 246 then decide (BallClauseLogic.Endpoint q (474 : Vertex)) else decide (BallClauseLogic.Endpoint q (475 : Vertex))) else (if i < 248 then decide (BallClauseLogic.Endpoint q (477 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count249 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131]
def count261 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count271 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138, 139]
def count275 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
def count277 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [140, 141, 142]
def count281 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146]
def count287 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143, 144, 145, 146]
def count289 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count299 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150, 151, 152, 153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]
def count305 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]
def count307 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [155, 156, 157]
def count311 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 159, 160, 161]
def count319 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count329 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165, 166, 167, 168, 169]
def count333 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]
def count335 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count337 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173]
def count341 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175, 176, 177]
def count349 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count351 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count367 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count369 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count371 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count373 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192]
def count379 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192]
def count381 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count383 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196]
def count387 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200]
def count395 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]
def count397 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count399 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count403 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count405 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208]
def count409 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204, 205, 206, 207, 208]
def count411 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count413 (b : Nat → Bool) : Nat := countLit b [211, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count419 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count421 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217]
def count423 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 213, 214, 215, 216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]
def count427 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217]
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
def count489 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count491 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count493 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count495 (b : Nat → Bool) : Nat := countLit b [1, 3, 4]
def count498 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count500 (b : Nat → Bool) : Nat := countLit b [12, 16]
def count502 (b : Nat → Bool) : Nat := countLit b [6, 7, 12, 16]
def count506 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 12, 16]
def count513 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count515 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count517 (b : Nat → Bool) : Nat := countLit b [17, 19, 20, 21]
def count521 (b : Nat → Bool) : Nat := countLit b [23, 26]
def count523 (b : Nat → Bool) : Nat := countLit b [28, 30]
def count525 (b : Nat → Bool) : Nat := countLit b [23, 26, 28, 30]
def count529 (b : Nat → Bool) : Nat := countLit b [17, 19, 20, 21, 23, 26, 28, 30]
def count537 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 12, 16, 17, 19, 20, 21, 23, 26, 28, 30]
def count552 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count554 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count556 (b : Nat → Bool) : Nat := countLit b [33, 35, 36, 37]
def count560 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count562 (b : Nat → Bool) : Nat := countLit b [43, 48]
def count564 (b : Nat → Bool) : Nat := countLit b [38, 40, 43, 48]
def count568 (b : Nat → Bool) : Nat := countLit b [33, 35, 36, 37, 38, 40, 43, 48]
def count576 (b : Nat → Bool) : Nat := countLit b [49, 52]
def count578 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count580 (b : Nat → Bool) : Nat := countLit b [49, 52, 53, 55]
def count584 (b : Nat → Bool) : Nat := countLit b [58, 59]
def count586 (b : Nat → Bool) : Nat := countLit b [60, 63]
def count588 (b : Nat → Bool) : Nat := countLit b [58, 59, 60, 63]
def count592 (b : Nat → Bool) : Nat := countLit b [49, 52, 53, 55, 58, 59, 60, 63]
def count600 (b : Nat → Bool) : Nat := countLit b [33, 35, 36, 37, 38, 40, 43, 48, 49, 52, 53, 55, 58, 59, 60, 63]
def count616 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 12, 16, 17, 19, 20, 21, 23, 26, 28, 30, 33, 35, 36, 37, 38, 40, 43, 48, 49, 52, 53, 55, 58, 59, 60, 63]
def count647 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count649 (b : Nat → Bool) : Nat := countLit b [65, 68, 70]
def count652 (b : Nat → Bool) : Nat := countLit b [71, 74]
def count654 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count656 (b : Nat → Bool) : Nat := countLit b [71, 74, 77, 78]
def count660 (b : Nat → Bool) : Nat := countLit b [65, 68, 70, 71, 74, 77, 78]
def count667 (b : Nat → Bool) : Nat := countLit b [80, 82]
def count669 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count671 (b : Nat → Bool) : Nat := countLit b [80, 82, 83, 84]
def count675 (b : Nat → Bool) : Nat := countLit b [86, 88]
def count677 (b : Nat → Bool) : Nat := countLit b [90, 92]
def count679 (b : Nat → Bool) : Nat := countLit b [86, 88, 90, 92]
def count683 (b : Nat → Bool) : Nat := countLit b [80, 82, 83, 84, 86, 88, 90, 92]
def count691 (b : Nat → Bool) : Nat := countLit b [65, 68, 70, 71, 74, 77, 78, 80, 82, 83, 84, 86, 88, 90, 92]
def count706 (b : Nat → Bool) : Nat := countLit b [93, 95]
def count708 (b : Nat → Bool) : Nat := countLit b [97, 100]
def count710 (b : Nat → Bool) : Nat := countLit b [93, 95, 97, 100]
def count714 (b : Nat → Bool) : Nat := countLit b [101, 105]
def count716 (b : Nat → Bool) : Nat := countLit b [106, 108]
def count718 (b : Nat → Bool) : Nat := countLit b [101, 105, 106, 108]
def count722 (b : Nat → Bool) : Nat := countLit b [93, 95, 97, 100, 101, 105, 106, 108]
def count730 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count732 (b : Nat → Bool) : Nat := countLit b [112, 114]
def count734 (b : Nat → Bool) : Nat := countLit b [109, 110, 112, 114]
def count738 (b : Nat → Bool) : Nat := countLit b [116, 118]
def count740 (b : Nat → Bool) : Nat := countLit b [121, 124]
def count742 (b : Nat → Bool) : Nat := countLit b [116, 118, 121, 124]
def count746 (b : Nat → Bool) : Nat := countLit b [109, 110, 112, 114, 116, 118, 121, 124]
def count754 (b : Nat → Bool) : Nat := countLit b [93, 95, 97, 100, 101, 105, 106, 108, 109, 110, 112, 114, 116, 118, 121, 124]
def count770 (b : Nat → Bool) : Nat := countLit b [65, 68, 70, 71, 74, 77, 78, 80, 82, 83, 84, 86, 88, 90, 92, 93, 95, 97, 100, 101, 105, 106, 108, 109, 110, 112, 114, 116, 118, 121, 124]
def count801 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 12, 16, 17, 19, 20, 21, 23, 26, 28, 30, 33, 35, 36, 37, 38, 40, 43, 48, 49, 52, 53, 55, 58, 59, 60, 63, 65, 68, 70, 71, 74, 77, 78, 80, 82, 83, 84, 86, 88, 90, 92, 93, 95, 97, 100, 101, 105, 106, 108, 109, 110, 112, 114, 116, 118, 121, 124]
def count843 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count845 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4]
def count848 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count850 (b : Nat → Bool) : Nat := countLit b [-12, -16]
def count852 (b : Nat → Bool) : Nat := countLit b [-6, -7, -12, -16]
def count856 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -12, -16]
def count863 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count865 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count867 (b : Nat → Bool) : Nat := countLit b [-17, -19, -20, -21]
def count871 (b : Nat → Bool) : Nat := countLit b [-23, -26]
def count873 (b : Nat → Bool) : Nat := countLit b [-28, -30]
def count875 (b : Nat → Bool) : Nat := countLit b [-23, -26, -28, -30]
def count879 (b : Nat → Bool) : Nat := countLit b [-17, -19, -20, -21, -23, -26, -28, -30]
def count887 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -12, -16, -17, -19, -20, -21, -23, -26, -28, -30]
def count902 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count904 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count906 (b : Nat → Bool) : Nat := countLit b [-33, -35, -36, -37]
def count910 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count912 (b : Nat → Bool) : Nat := countLit b [-43, -48]
def count914 (b : Nat → Bool) : Nat := countLit b [-38, -40, -43, -48]
def count918 (b : Nat → Bool) : Nat := countLit b [-33, -35, -36, -37, -38, -40, -43, -48]
def count926 (b : Nat → Bool) : Nat := countLit b [-49, -52]
def count928 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count930 (b : Nat → Bool) : Nat := countLit b [-49, -52, -53, -55]
def count934 (b : Nat → Bool) : Nat := countLit b [-58, -59]
def count936 (b : Nat → Bool) : Nat := countLit b [-60, -63]
def count938 (b : Nat → Bool) : Nat := countLit b [-58, -59, -60, -63]
def count942 (b : Nat → Bool) : Nat := countLit b [-49, -52, -53, -55, -58, -59, -60, -63]
def count950 (b : Nat → Bool) : Nat := countLit b [-33, -35, -36, -37, -38, -40, -43, -48, -49, -52, -53, -55, -58, -59, -60, -63]
def count966 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -12, -16, -17, -19, -20, -21, -23, -26, -28, -30, -33, -35, -36, -37, -38, -40, -43, -48, -49, -52, -53, -55, -58, -59, -60, -63]
def count988 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count990 (b : Nat → Bool) : Nat := countLit b [-65, -68, -70]
def count993 (b : Nat → Bool) : Nat := countLit b [-71, -74]
def count995 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count997 (b : Nat → Bool) : Nat := countLit b [-71, -74, -77, -78]
def count1001 (b : Nat → Bool) : Nat := countLit b [-65, -68, -70, -71, -74, -77, -78]
def count1008 (b : Nat → Bool) : Nat := countLit b [-80, -82]
def count1010 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count1012 (b : Nat → Bool) : Nat := countLit b [-80, -82, -83, -84]
def count1016 (b : Nat → Bool) : Nat := countLit b [-86, -88]
def count1018 (b : Nat → Bool) : Nat := countLit b [-90, -92]
def count1020 (b : Nat → Bool) : Nat := countLit b [-86, -88, -90, -92]
def count1024 (b : Nat → Bool) : Nat := countLit b [-80, -82, -83, -84, -86, -88, -90, -92]
def count1032 (b : Nat → Bool) : Nat := countLit b [-65, -68, -70, -71, -74, -77, -78, -80, -82, -83, -84, -86, -88, -90, -92]
def count1047 (b : Nat → Bool) : Nat := countLit b [-93, -95]
def count1049 (b : Nat → Bool) : Nat := countLit b [-97, -100]
def count1051 (b : Nat → Bool) : Nat := countLit b [-93, -95, -97, -100]
def count1055 (b : Nat → Bool) : Nat := countLit b [-101, -105]
def count1057 (b : Nat → Bool) : Nat := countLit b [-106, -108]
def count1059 (b : Nat → Bool) : Nat := countLit b [-101, -105, -106, -108]
def count1063 (b : Nat → Bool) : Nat := countLit b [-93, -95, -97, -100, -101, -105, -106, -108]
def count1071 (b : Nat → Bool) : Nat := countLit b [-109, -110]
def count1073 (b : Nat → Bool) : Nat := countLit b [-112, -114]
def count1075 (b : Nat → Bool) : Nat := countLit b [-109, -110, -112, -114]
def count1079 (b : Nat → Bool) : Nat := countLit b [-116, -118]
def count1081 (b : Nat → Bool) : Nat := countLit b [-121, -124]
def count1083 (b : Nat → Bool) : Nat := countLit b [-116, -118, -121, -124]
def count1087 (b : Nat → Bool) : Nat := countLit b [-109, -110, -112, -114, -116, -118, -121, -124]
def count1095 (b : Nat → Bool) : Nat := countLit b [-93, -95, -97, -100, -101, -105, -106, -108, -109, -110, -112, -114, -116, -118, -121, -124]
def count1111 (b : Nat → Bool) : Nat := countLit b [-65, -68, -70, -71, -74, -77, -78, -80, -82, -83, -84, -86, -88, -90, -92, -93, -95, -97, -100, -101, -105, -106, -108, -109, -110, -112, -114, -116, -118, -121, -124]
def count1133 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -12, -16, -17, -19, -20, -21, -23, -26, -28, -30, -33, -35, -36, -37, -38, -40, -43, -48, -49, -52, -53, -55, -58, -59, -60, -63, -65, -68, -70, -71, -74, -77, -78, -80, -82, -83, -84, -86, -88, -90, -92, -93, -95, -97, -100, -101, -105, -106, -108, -109, -110, -112, -114, -116, -118, -121, -124]
def count1155 (b : Nat → Bool) : Nat := countLit b [5, 8]
def count1157 (b : Nat → Bool) : Nat := countLit b [2, 5, 8]
def count1160 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count1162 (b : Nat → Bool) : Nat := countLit b [11, 13]
def count1164 (b : Nat → Bool) : Nat := countLit b [9, 10, 11, 13]
def count1168 (b : Nat → Bool) : Nat := countLit b [2, 5, 8, 9, 10, 11, 13]
def count1175 (b : Nat → Bool) : Nat := countLit b [14, 15]
def count1177 (b : Nat → Bool) : Nat := countLit b [18, 22]
def count1179 (b : Nat → Bool) : Nat := countLit b [14, 15, 18, 22]
def count1183 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count1185 (b : Nat → Bool) : Nat := countLit b [27, 29]
def count1187 (b : Nat → Bool) : Nat := countLit b [24, 25, 27, 29]
def count1191 (b : Nat → Bool) : Nat := countLit b [14, 15, 18, 22, 24, 25, 27, 29]
def count1199 (b : Nat → Bool) : Nat := countLit b [2, 5, 8, 9, 10, 11, 13, 14, 15, 18, 22, 24, 25, 27, 29]
def count1214 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count1216 (b : Nat → Bool) : Nat := countLit b [34, 39]
def count1218 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 39]
def count1222 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count1224 (b : Nat → Bool) : Nat := countLit b [44, 45]
def count1226 (b : Nat → Bool) : Nat := countLit b [41, 42, 44, 45]
def count1230 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 39, 41, 42, 44, 45]
def count1238 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count1240 (b : Nat → Bool) : Nat := countLit b [50, 51]
def count1242 (b : Nat → Bool) : Nat := countLit b [46, 47, 50, 51]
def count1246 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count1248 (b : Nat → Bool) : Nat := countLit b [57, 61]
def count1250 (b : Nat → Bool) : Nat := countLit b [54, 56, 57, 61]
def count1254 (b : Nat → Bool) : Nat := countLit b [46, 47, 50, 51, 54, 56, 57, 61]
def count1262 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 39, 41, 42, 44, 45, 46, 47, 50, 51, 54, 56, 57, 61]
def count1278 (b : Nat → Bool) : Nat := countLit b [2, 5, 8, 9, 10, 11, 13, 14, 15, 18, 22, 24, 25, 27, 29, 31, 32, 34, 39, 41, 42, 44, 45, 46, 47, 50, 51, 54, 56, 57, 61]
def count1309 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count1311 (b : Nat → Bool) : Nat := countLit b [62, 64, 66]
def count1314 (b : Nat → Bool) : Nat := countLit b [67, 69]
def count1316 (b : Nat → Bool) : Nat := countLit b [72, 73]
def count1318 (b : Nat → Bool) : Nat := countLit b [67, 69, 72, 73]
def count1322 (b : Nat → Bool) : Nat := countLit b [62, 64, 66, 67, 69, 72, 73]
def count1329 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count1331 (b : Nat → Bool) : Nat := countLit b [79, 81]
def count1333 (b : Nat → Bool) : Nat := countLit b [75, 76, 79, 81]
def count1337 (b : Nat → Bool) : Nat := countLit b [85, 87]
def count1339 (b : Nat → Bool) : Nat := countLit b [89, 91]
def count1341 (b : Nat → Bool) : Nat := countLit b [85, 87, 89, 91]
def count1345 (b : Nat → Bool) : Nat := countLit b [75, 76, 79, 81, 85, 87, 89, 91]
def count1353 (b : Nat → Bool) : Nat := countLit b [62, 64, 66, 67, 69, 72, 73, 75, 76, 79, 81, 85, 87, 89, 91]
def count1368 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count1370 (b : Nat → Bool) : Nat := countLit b [98, 99]
def count1372 (b : Nat → Bool) : Nat := countLit b [94, 96, 98, 99]
def count1376 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count1378 (b : Nat → Bool) : Nat := countLit b [104, 107]
def count1380 (b : Nat → Bool) : Nat := countLit b [102, 103, 104, 107]
def count1384 (b : Nat → Bool) : Nat := countLit b [94, 96, 98, 99, 102, 103, 104, 107]
def count1392 (b : Nat → Bool) : Nat := countLit b [111, 113]
def count1394 (b : Nat → Bool) : Nat := countLit b [115, 117]
def count1396 (b : Nat → Bool) : Nat := countLit b [111, 113, 115, 117]
def count1400 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count1402 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count1404 (b : Nat → Bool) : Nat := countLit b [119, 120, 122, 123]
def count1408 (b : Nat → Bool) : Nat := countLit b [111, 113, 115, 117, 119, 120, 122, 123]
def count1416 (b : Nat → Bool) : Nat := countLit b [94, 96, 98, 99, 102, 103, 104, 107, 111, 113, 115, 117, 119, 120, 122, 123]
def count1432 (b : Nat → Bool) : Nat := countLit b [62, 64, 66, 67, 69, 72, 73, 75, 76, 79, 81, 85, 87, 89, 91, 94, 96, 98, 99, 102, 103, 104, 107, 111, 113, 115, 117, 119, 120, 122, 123]
def count1463 (b : Nat → Bool) : Nat := countLit b [2, 5, 8, 9, 10, 11, 13, 14, 15, 18, 22, 24, 25, 27, 29, 31, 32, 34, 39, 41, 42, 44, 45, 46, 47, 50, 51, 54, 56, 57, 61, 62, 64, 66, 67, 69, 72, 73, 75, 76, 79, 81, 85, 87, 89, 91, 94, 96, 98, 99, 102, 103, 104, 107, 111, 113, 115, 117, 119, 120, 122, 123]
def count1505 (b : Nat → Bool) : Nat := countLit b [-5, -8]
def count1507 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8]
def count1510 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count1512 (b : Nat → Bool) : Nat := countLit b [-11, -13]
def count1514 (b : Nat → Bool) : Nat := countLit b [-9, -10, -11, -13]
def count1518 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8, -9, -10, -11, -13]
def count1525 (b : Nat → Bool) : Nat := countLit b [-14, -15]
def count1527 (b : Nat → Bool) : Nat := countLit b [-18, -22]
def count1529 (b : Nat → Bool) : Nat := countLit b [-14, -15, -18, -22]
def count1533 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count1535 (b : Nat → Bool) : Nat := countLit b [-27, -29]
def count1537 (b : Nat → Bool) : Nat := countLit b [-24, -25, -27, -29]
def count1541 (b : Nat → Bool) : Nat := countLit b [-14, -15, -18, -22, -24, -25, -27, -29]
def count1549 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]
def count1564 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count1566 (b : Nat → Bool) : Nat := countLit b [-34, -39]
def count1568 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -39]
def count1572 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count1574 (b : Nat → Bool) : Nat := countLit b [-44, -45]
def count1576 (b : Nat → Bool) : Nat := countLit b [-41, -42, -44, -45]
def count1580 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -39, -41, -42, -44, -45]
def count1588 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count1590 (b : Nat → Bool) : Nat := countLit b [-50, -51]
def count1592 (b : Nat → Bool) : Nat := countLit b [-46, -47, -50, -51]
def count1596 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count1598 (b : Nat → Bool) : Nat := countLit b [-57, -61]
def count1600 (b : Nat → Bool) : Nat := countLit b [-54, -56, -57, -61]
def count1604 (b : Nat → Bool) : Nat := countLit b [-46, -47, -50, -51, -54, -56, -57, -61]
def count1612 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]
def count1628 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]
def count1650 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count1652 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66]
def count1655 (b : Nat → Bool) : Nat := countLit b [-67, -69]
def count1657 (b : Nat → Bool) : Nat := countLit b [-72, -73]
def count1659 (b : Nat → Bool) : Nat := countLit b [-67, -69, -72, -73]
def count1663 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66, -67, -69, -72, -73]
def count1670 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count1672 (b : Nat → Bool) : Nat := countLit b [-79, -81]
def count1674 (b : Nat → Bool) : Nat := countLit b [-75, -76, -79, -81]
def count1678 (b : Nat → Bool) : Nat := countLit b [-85, -87]
def count1680 (b : Nat → Bool) : Nat := countLit b [-89, -91]
def count1682 (b : Nat → Bool) : Nat := countLit b [-85, -87, -89, -91]
def count1686 (b : Nat → Bool) : Nat := countLit b [-75, -76, -79, -81, -85, -87, -89, -91]
def count1694 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]
def count1709 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1711 (b : Nat → Bool) : Nat := countLit b [-98, -99]
def count1713 (b : Nat → Bool) : Nat := countLit b [-94, -96, -98, -99]
def count1717 (b : Nat → Bool) : Nat := countLit b [-102, -103]
def count1719 (b : Nat → Bool) : Nat := countLit b [-104, -107]
def count1721 (b : Nat → Bool) : Nat := countLit b [-102, -103, -104, -107]
def count1725 (b : Nat → Bool) : Nat := countLit b [-94, -96, -98, -99, -102, -103, -104, -107]
def count1733 (b : Nat → Bool) : Nat := countLit b [-111, -113]
def count1735 (b : Nat → Bool) : Nat := countLit b [-115, -117]
def count1737 (b : Nat → Bool) : Nat := countLit b [-111, -113, -115, -117]
def count1741 (b : Nat → Bool) : Nat := countLit b [-119, -120]
def count1743 (b : Nat → Bool) : Nat := countLit b [-122, -123]
def count1745 (b : Nat → Bool) : Nat := countLit b [-119, -120, -122, -123]
def count1749 (b : Nat → Bool) : Nat := countLit b [-111, -113, -115, -117, -119, -120, -122, -123]
def count1757 (b : Nat → Bool) : Nat := countLit b [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]
def count1773 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]
def count1795 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61, -62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 908 then (if i < 454 then (if i < 227 then (if i < 113 then (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 24 then (if i < 22 then b 21 else (if i < 23 then b 22 else b 23)) else (if i < 26 then (if i < 25 then b 24 else b 25) else (if i < 27 then b 26 else b 27))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)) else (if i < 33 then (if i < 32 then b 31 else b 32) else (if i < 34 then b 33 else b 34))) else (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 40 then (if i < 39 then b 38 else b 39) else (if i < 41 then b 40 else b 41)))) else (if i < 49 then (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else b 48))) else (if i < 52 then (if i < 50 then b 49 else (if i < 51 then b 50 else b 51)) else (if i < 54 then (if i < 53 then b 52 else b 53) else (if i < 55 then b 54 else b 55)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then b 56 else (if i < 58 then b 57 else b 58)) else (if i < 61 then (if i < 60 then b 59 else b 60) else (if i < 62 then b 61 else b 62))) else (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 68 then (if i < 67 then b 66 else b 67) else (if i < 69 then b 68 else b 69)))) else (if i < 77 then (if i < 73 then (if i < 71 then b 70 else (if i < 72 then b 71 else b 72)) else (if i < 75 then (if i < 74 then b 73 else b 74) else (if i < 76 then b 75 else b 76))) else (if i < 80 then (if i < 78 then b 77 else (if i < 79 then b 78 else b 79)) else (if i < 82 then (if i < 81 then b 80 else b 81) else (if i < 83 then b 82 else b 83))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else b 90))) else (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else b 97)))) else (if i < 105 then (if i < 101 then (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)) else (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else b 104))) else (if i < 109 then (if i < 107 then (if i < 106 then b 105 else b 106) else (if i < 108 then b 107 else b 108)) else (if i < 111 then (if i < 110 then b 109 else b 110) else (if i < 112 then b 111 else b 112))))))) else (if i < 170 then (if i < 141 then (if i < 127 then (if i < 120 then (if i < 116 then (if i < 114 then b 113 else (if i < 115 then b 114 else b 115)) else (if i < 118 then (if i < 117 then b 116 else b 117) else (if i < 119 then b 118 else b 119))) else (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 125 then (if i < 124 then b 123 else b 124) else (if i < 126 then b 125 else b 126)))) else (if i < 134 then (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 132 then (if i < 131 then b 130 else b 131) else (if i < 133 then b 132 else b 133))) else (if i < 137 then (if i < 135 then b 134 else (if i < 136 then b 135 else b 136)) else (if i < 139 then (if i < 138 then b 137 else b 138) else (if i < 140 then b 139 else b 140))))) else (if i < 155 then (if i < 148 then (if i < 144 then (if i < 142 then b 141 else (if i < 143 then b 142 else b 143)) else (if i < 146 then (if i < 145 then b 144 else b 145) else (if i < 147 then b 146 else b 147))) else (if i < 151 then (if i < 149 then b 148 else (if i < 150 then b 149 else b 150)) else (if i < 153 then (if i < 152 then b 151 else b 152) else (if i < 154 then b 153 else b 154)))) else (if i < 162 then (if i < 158 then (if i < 156 then b 155 else (if i < 157 then b 156 else b 157)) else (if i < 160 then (if i < 159 then b 158 else b 159) else (if i < 161 then b 160 else b 161))) else (if i < 166 then (if i < 164 then (if i < 163 then b 162 else b 163) else (if i < 165 then b 164 else b 165)) else (if i < 168 then (if i < 167 then b 166 else b 167) else (if i < 169 then b 168 else b 169)))))) else (if i < 198 then (if i < 184 then (if i < 177 then (if i < 173 then (if i < 171 then b 170 else (if i < 172 then b 171 else b 172)) else (if i < 175 then (if i < 174 then b 173 else b 174) else (if i < 176 then b 175 else b 176))) else (if i < 180 then (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)) else (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else b 183)))) else (if i < 191 then (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 189 then (if i < 188 then b 187 else b 188) else (if i < 190 then b 189 else b 190))) else (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else b 197))))) else (if i < 212 then (if i < 205 then (if i < 201 then (if i < 199 then b 198 else (if i < 200 then b 199 else b 200)) else (if i < 203 then (if i < 202 then b 201 else b 202) else (if i < 204 then b 203 else b 204))) else (if i < 208 then (if i < 206 then b 205 else (if i < 207 then b 206 else b 207)) else (if i < 210 then (if i < 209 then b 208 else b 209) else (if i < 211 then b 210 else b 211)))) else (if i < 219 then (if i < 215 then (if i < 213 then b 212 else (if i < 214 then b 213 else b 214)) else (if i < 217 then (if i < 216 then b 215 else b 216) else (if i < 218 then b 217 else b 218))) else (if i < 223 then (if i < 221 then (if i < 220 then b 219 else b 220) else (if i < 222 then b 221 else b 222)) else (if i < 225 then (if i < 224 then b 223 else b 224) else (if i < 226 then b 225 else b 226)))))))) else (if i < 340 then (if i < 283 then (if i < 255 then (if i < 241 then (if i < 234 then (if i < 230 then (if i < 228 then b 227 else (if i < 229 then b 228 else b 229)) else (if i < 232 then (if i < 231 then b 230 else b 231) else (if i < 233 then b 232 else b 233))) else (if i < 237 then (if i < 235 then b 234 else (if i < 236 then b 235 else b 236)) else (if i < 239 then (if i < 238 then b 237 else b 238) else (if i < 240 then b 239 else b 240)))) else (if i < 248 then (if i < 244 then (if i < 242 then b 241 else (if i < 243 then b 242 else b 243)) else (if i < 246 then (if i < 245 then b 244 else b 245) else (if i < 247 then b 246 else b 247))) else (if i < 251 then (if i < 249 then b 248 else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 253 then (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b)))))) else (if i < 269 then (if i < 262 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 260 then (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b)) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))) else (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 267 then (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b))))) else (if i < 276 then (if i < 272 then (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))) else (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)))) else (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 281 then (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))))))) else (if i < 311 then (if i < 297 then (if i < 290 then (if i < 286 then (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b))) else (if i < 288 then (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b)) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)))) else (if i < 293 then (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))) else (if i < 295 then (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b))))) else (if i < 304 then (if i < 300 then (if i < 298 then decide (1 ≤ count297 b) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))) else (if i < 302 then (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)))) else (if i < 307 then (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))) else (if i < 309 then (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)))))) else (if i < 325 then (if i < 318 then (if i < 314 then (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b))) else (if i < 316 then (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)))) else (if i < 321 then (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))) else (if i < 323 then (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))))) else (if i < 332 then (if i < 328 then (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b))) else (if i < 330 then (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)))) else (if i < 336 then (if i < 334 then (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 338 then (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)))))))) else (if i < 397 then (if i < 368 then (if i < 354 then (if i < 347 then (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)))) else (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))))) else (if i < 361 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 359 then (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))) else (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 366 then (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)))))) else (if i < 382 then (if i < 375 then (if i < 371 then (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))) else (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)))) else (if i < 378 then (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))) else (if i < 380 then (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b)) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))))) else (if i < 389 then (if i < 385 then (if i < 383 then decide (2 ≤ count381 b) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))) else (if i < 387 then (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 393 then (if i < 391 then (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))) else (if i < 395 then (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))))))) else (if i < 425 then (if i < 411 then (if i < 404 then (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)))) else (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 409 then (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))))) else (if i < 418 then (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 416 then (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)))) else (if i < 421 then (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))) else (if i < 423 then (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b)) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b)))))) else (if i < 439 then (if i < 432 then (if i < 428 then (if i < 426 then decide (1 ≤ count425 b) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b))) else (if i < 430 then (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b)) else (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)))) else (if i < 435 then (if i < 433 then decide (2 ≤ count431 b) else (if i < 434 then decide (1 ≤ count433 b) else decide (2 ≤ count433 b))) else (if i < 437 then (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)) else (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b))))) else (if i < 446 then (if i < 442 then (if i < 440 then decide (1 ≤ count439 b) else (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b))) else (if i < 444 then (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)) else (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)))) else (if i < 450 then (if i < 448 then (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b)) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b))) else (if i < 452 then (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b)) else (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b)))))))))) else (if i < 681 then (if i < 567 then (if i < 510 then (if i < 482 then (if i < 468 then (if i < 461 then (if i < 457 then (if i < 455 then decide (2 ≤ count453 b) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b))) else (if i < 459 then (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)) else (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)))) else (if i < 464 then (if i < 462 then decide (1 ≤ count461 b) else (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b))) else (if i < 466 then (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b)) else (if i < 467 then decide (2 ≤ count465 b) else decide (1 ≤ count467 b))))) else (if i < 475 then (if i < 471 then (if i < 469 then decide (2 ≤ count467 b) else (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b))) else (if i < 473 then (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b)) else (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)))) else (if i < 478 then (if i < 476 then decide (1 ≤ count475 b) else (if i < 477 then decide (2 ≤ count475 b) else decide (1 ≤ count477 b))) else (if i < 480 then (if i < 479 then decide (2 ≤ count477 b) else decide (1 ≤ count479 b)) else (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b)))))) else (if i < 496 then (if i < 489 then (if i < 485 then (if i < 483 then decide (2 ≤ count481 b) else (if i < 484 then decide (1 ≤ count483 b) else decide (2 ≤ count483 b))) else (if i < 487 then (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b)) else (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b)))) else (if i < 492 then (if i < 490 then decide (1 ≤ count489 b) else (if i < 491 then decide (2 ≤ count489 b) else decide (1 ≤ count491 b))) else (if i < 494 then (if i < 493 then decide (2 ≤ count491 b) else decide (1 ≤ count493 b)) else (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b))))) else (if i < 503 then (if i < 499 then (if i < 497 then decide (2 ≤ count495 b) else (if i < 498 then decide (3 ≤ count495 b) else decide (1 ≤ count498 b))) else (if i < 501 then (if i < 500 then decide (2 ≤ count498 b) else decide (1 ≤ count500 b)) else (if i < 502 then decide (2 ≤ count500 b) else decide (1 ≤ count502 b)))) else (if i < 506 then (if i < 504 then decide (2 ≤ count502 b) else (if i < 505 then decide (3 ≤ count502 b) else decide (4 ≤ count502 b))) else (if i < 508 then (if i < 507 then decide (1 ≤ count506 b) else decide (2 ≤ count506 b)) else (if i < 509 then decide (3 ≤ count506 b) else decide (4 ≤ count506 b))))))) else (if i < 538 then (if i < 524 then (if i < 517 then (if i < 513 then (if i < 511 then decide (5 ≤ count506 b) else (if i < 512 then decide (6 ≤ count506 b) else decide (7 ≤ count506 b))) else (if i < 515 then (if i < 514 then decide (1 ≤ count513 b) else decide (2 ≤ count513 b)) else (if i < 516 then decide (1 ≤ count515 b) else decide (2 ≤ count515 b)))) else (if i < 520 then (if i < 518 then decide (1 ≤ count517 b) else (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b))) else (if i < 522 then (if i < 521 then decide (4 ≤ count517 b) else decide (1 ≤ count521 b)) else (if i < 523 then decide (2 ≤ count521 b) else decide (1 ≤ count523 b))))) else (if i < 531 then (if i < 527 then (if i < 525 then decide (2 ≤ count523 b) else (if i < 526 then decide (1 ≤ count525 b) else decide (2 ≤ count525 b))) else (if i < 529 then (if i < 528 then decide (3 ≤ count525 b) else decide (4 ≤ count525 b)) else (if i < 530 then decide (1 ≤ count529 b) else decide (2 ≤ count529 b)))) else (if i < 534 then (if i < 532 then decide (3 ≤ count529 b) else (if i < 533 then decide (4 ≤ count529 b) else decide (5 ≤ count529 b))) else (if i < 536 then (if i < 535 then decide (6 ≤ count529 b) else decide (7 ≤ count529 b)) else (if i < 537 then decide (8 ≤ count529 b) else decide (1 ≤ count537 b)))))) else (if i < 552 then (if i < 545 then (if i < 541 then (if i < 539 then decide (2 ≤ count537 b) else (if i < 540 then decide (3 ≤ count537 b) else decide (4 ≤ count537 b))) else (if i < 543 then (if i < 542 then decide (5 ≤ count537 b) else decide (6 ≤ count537 b)) else (if i < 544 then decide (7 ≤ count537 b) else decide (8 ≤ count537 b)))) else (if i < 548 then (if i < 546 then decide (9 ≤ count537 b) else (if i < 547 then decide (10 ≤ count537 b) else decide (11 ≤ count537 b))) else (if i < 550 then (if i < 549 then decide (12 ≤ count537 b) else decide (13 ≤ count537 b)) else (if i < 551 then decide (14 ≤ count537 b) else decide (15 ≤ count537 b))))) else (if i < 559 then (if i < 555 then (if i < 553 then decide (1 ≤ count552 b) else (if i < 554 then decide (2 ≤ count552 b) else decide (1 ≤ count554 b))) else (if i < 557 then (if i < 556 then decide (2 ≤ count554 b) else decide (1 ≤ count556 b)) else (if i < 558 then decide (2 ≤ count556 b) else decide (3 ≤ count556 b)))) else (if i < 563 then (if i < 561 then (if i < 560 then decide (4 ≤ count556 b) else decide (1 ≤ count560 b)) else (if i < 562 then decide (2 ≤ count560 b) else decide (1 ≤ count562 b))) else (if i < 565 then (if i < 564 then decide (2 ≤ count562 b) else decide (1 ≤ count564 b)) else (if i < 566 then decide (2 ≤ count564 b) else decide (3 ≤ count564 b)))))))) else (if i < 624 then (if i < 595 then (if i < 581 then (if i < 574 then (if i < 570 then (if i < 568 then decide (4 ≤ count564 b) else (if i < 569 then decide (1 ≤ count568 b) else decide (2 ≤ count568 b))) else (if i < 572 then (if i < 571 then decide (3 ≤ count568 b) else decide (4 ≤ count568 b)) else (if i < 573 then decide (5 ≤ count568 b) else decide (6 ≤ count568 b)))) else (if i < 577 then (if i < 575 then decide (7 ≤ count568 b) else (if i < 576 then decide (8 ≤ count568 b) else decide (1 ≤ count576 b))) else (if i < 579 then (if i < 578 then decide (2 ≤ count576 b) else decide (1 ≤ count578 b)) else (if i < 580 then decide (2 ≤ count578 b) else decide (1 ≤ count580 b))))) else (if i < 588 then (if i < 584 then (if i < 582 then decide (2 ≤ count580 b) else (if i < 583 then decide (3 ≤ count580 b) else decide (4 ≤ count580 b))) else (if i < 586 then (if i < 585 then decide (1 ≤ count584 b) else decide (2 ≤ count584 b)) else (if i < 587 then decide (1 ≤ count586 b) else decide (2 ≤ count586 b)))) else (if i < 591 then (if i < 589 then decide (1 ≤ count588 b) else (if i < 590 then decide (2 ≤ count588 b) else decide (3 ≤ count588 b))) else (if i < 593 then (if i < 592 then decide (4 ≤ count588 b) else decide (1 ≤ count592 b)) else (if i < 594 then decide (2 ≤ count592 b) else decide (3 ≤ count592 b)))))) else (if i < 609 then (if i < 602 then (if i < 598 then (if i < 596 then decide (4 ≤ count592 b) else (if i < 597 then decide (5 ≤ count592 b) else decide (6 ≤ count592 b))) else (if i < 600 then (if i < 599 then decide (7 ≤ count592 b) else decide (8 ≤ count592 b)) else (if i < 601 then decide (1 ≤ count600 b) else decide (2 ≤ count600 b)))) else (if i < 605 then (if i < 603 then decide (3 ≤ count600 b) else (if i < 604 then decide (4 ≤ count600 b) else decide (5 ≤ count600 b))) else (if i < 607 then (if i < 606 then decide (6 ≤ count600 b) else decide (7 ≤ count600 b)) else (if i < 608 then decide (8 ≤ count600 b) else decide (9 ≤ count600 b))))) else (if i < 616 then (if i < 612 then (if i < 610 then decide (10 ≤ count600 b) else (if i < 611 then decide (11 ≤ count600 b) else decide (12 ≤ count600 b))) else (if i < 614 then (if i < 613 then decide (13 ≤ count600 b) else decide (14 ≤ count600 b)) else (if i < 615 then decide (15 ≤ count600 b) else decide (16 ≤ count600 b)))) else (if i < 620 then (if i < 618 then (if i < 617 then decide (1 ≤ count616 b) else decide (2 ≤ count616 b)) else (if i < 619 then decide (3 ≤ count616 b) else decide (4 ≤ count616 b))) else (if i < 622 then (if i < 621 then decide (5 ≤ count616 b) else decide (6 ≤ count616 b)) else (if i < 623 then decide (7 ≤ count616 b) else decide (8 ≤ count616 b))))))) else (if i < 652 then (if i < 638 then (if i < 631 then (if i < 627 then (if i < 625 then decide (9 ≤ count616 b) else (if i < 626 then decide (10 ≤ count616 b) else decide (11 ≤ count616 b))) else (if i < 629 then (if i < 628 then decide (12 ≤ count616 b) else decide (13 ≤ count616 b)) else (if i < 630 then decide (14 ≤ count616 b) else decide (15 ≤ count616 b)))) else (if i < 634 then (if i < 632 then decide (16 ≤ count616 b) else (if i < 633 then decide (17 ≤ count616 b) else decide (18 ≤ count616 b))) else (if i < 636 then (if i < 635 then decide (19 ≤ count616 b) else decide (20 ≤ count616 b)) else (if i < 637 then decide (21 ≤ count616 b) else decide (22 ≤ count616 b))))) else (if i < 645 then (if i < 641 then (if i < 639 then decide (23 ≤ count616 b) else (if i < 640 then decide (24 ≤ count616 b) else decide (25 ≤ count616 b))) else (if i < 643 then (if i < 642 then decide (26 ≤ count616 b) else decide (27 ≤ count616 b)) else (if i < 644 then decide (28 ≤ count616 b) else decide (29 ≤ count616 b)))) else (if i < 648 then (if i < 646 then decide (30 ≤ count616 b) else (if i < 647 then decide (31 ≤ count616 b) else decide (1 ≤ count647 b))) else (if i < 650 then (if i < 649 then decide (2 ≤ count647 b) else decide (1 ≤ count649 b)) else (if i < 651 then decide (2 ≤ count649 b) else decide (3 ≤ count649 b)))))) else (if i < 666 then (if i < 659 then (if i < 655 then (if i < 653 then decide (1 ≤ count652 b) else (if i < 654 then decide (2 ≤ count652 b) else decide (1 ≤ count654 b))) else (if i < 657 then (if i < 656 then decide (2 ≤ count654 b) else decide (1 ≤ count656 b)) else (if i < 658 then decide (2 ≤ count656 b) else decide (3 ≤ count656 b)))) else (if i < 662 then (if i < 660 then decide (4 ≤ count656 b) else (if i < 661 then decide (1 ≤ count660 b) else decide (2 ≤ count660 b))) else (if i < 664 then (if i < 663 then decide (3 ≤ count660 b) else decide (4 ≤ count660 b)) else (if i < 665 then decide (5 ≤ count660 b) else decide (6 ≤ count660 b))))) else (if i < 673 then (if i < 669 then (if i < 667 then decide (7 ≤ count660 b) else (if i < 668 then decide (1 ≤ count667 b) else decide (2 ≤ count667 b))) else (if i < 671 then (if i < 670 then decide (1 ≤ count669 b) else decide (2 ≤ count669 b)) else (if i < 672 then decide (1 ≤ count671 b) else decide (2 ≤ count671 b)))) else (if i < 677 then (if i < 675 then (if i < 674 then decide (3 ≤ count671 b) else decide (4 ≤ count671 b)) else (if i < 676 then decide (1 ≤ count675 b) else decide (2 ≤ count675 b))) else (if i < 679 then (if i < 678 then decide (1 ≤ count677 b) else decide (2 ≤ count677 b)) else (if i < 680 then decide (1 ≤ count679 b) else decide (2 ≤ count679 b))))))))) else (if i < 794 then (if i < 737 then (if i < 709 then (if i < 695 then (if i < 688 then (if i < 684 then (if i < 682 then decide (3 ≤ count679 b) else (if i < 683 then decide (4 ≤ count679 b) else decide (1 ≤ count683 b))) else (if i < 686 then (if i < 685 then decide (2 ≤ count683 b) else decide (3 ≤ count683 b)) else (if i < 687 then decide (4 ≤ count683 b) else decide (5 ≤ count683 b)))) else (if i < 691 then (if i < 689 then decide (6 ≤ count683 b) else (if i < 690 then decide (7 ≤ count683 b) else decide (8 ≤ count683 b))) else (if i < 693 then (if i < 692 then decide (1 ≤ count691 b) else decide (2 ≤ count691 b)) else (if i < 694 then decide (3 ≤ count691 b) else decide (4 ≤ count691 b))))) else (if i < 702 then (if i < 698 then (if i < 696 then decide (5 ≤ count691 b) else (if i < 697 then decide (6 ≤ count691 b) else decide (7 ≤ count691 b))) else (if i < 700 then (if i < 699 then decide (8 ≤ count691 b) else decide (9 ≤ count691 b)) else (if i < 701 then decide (10 ≤ count691 b) else decide (11 ≤ count691 b)))) else (if i < 705 then (if i < 703 then decide (12 ≤ count691 b) else (if i < 704 then decide (13 ≤ count691 b) else decide (14 ≤ count691 b))) else (if i < 707 then (if i < 706 then decide (15 ≤ count691 b) else decide (1 ≤ count706 b)) else (if i < 708 then decide (2 ≤ count706 b) else decide (1 ≤ count708 b)))))) else (if i < 723 then (if i < 716 then (if i < 712 then (if i < 710 then decide (2 ≤ count708 b) else (if i < 711 then decide (1 ≤ count710 b) else decide (2 ≤ count710 b))) else (if i < 714 then (if i < 713 then decide (3 ≤ count710 b) else decide (4 ≤ count710 b)) else (if i < 715 then decide (1 ≤ count714 b) else decide (2 ≤ count714 b)))) else (if i < 719 then (if i < 717 then decide (1 ≤ count716 b) else (if i < 718 then decide (2 ≤ count716 b) else decide (1 ≤ count718 b))) else (if i < 721 then (if i < 720 then decide (2 ≤ count718 b) else decide (3 ≤ count718 b)) else (if i < 722 then decide (4 ≤ count718 b) else decide (1 ≤ count722 b))))) else (if i < 730 then (if i < 726 then (if i < 724 then decide (2 ≤ count722 b) else (if i < 725 then decide (3 ≤ count722 b) else decide (4 ≤ count722 b))) else (if i < 728 then (if i < 727 then decide (5 ≤ count722 b) else decide (6 ≤ count722 b)) else (if i < 729 then decide (7 ≤ count722 b) else decide (8 ≤ count722 b)))) else (if i < 733 then (if i < 731 then decide (1 ≤ count730 b) else (if i < 732 then decide (2 ≤ count730 b) else decide (1 ≤ count732 b))) else (if i < 735 then (if i < 734 then decide (2 ≤ count732 b) else decide (1 ≤ count734 b)) else (if i < 736 then decide (2 ≤ count734 b) else decide (3 ≤ count734 b))))))) else (if i < 765 then (if i < 751 then (if i < 744 then (if i < 740 then (if i < 738 then decide (4 ≤ count734 b) else (if i < 739 then decide (1 ≤ count738 b) else decide (2 ≤ count738 b))) else (if i < 742 then (if i < 741 then decide (1 ≤ count740 b) else decide (2 ≤ count740 b)) else (if i < 743 then decide (1 ≤ count742 b) else decide (2 ≤ count742 b)))) else (if i < 747 then (if i < 745 then decide (3 ≤ count742 b) else (if i < 746 then decide (4 ≤ count742 b) else decide (1 ≤ count746 b))) else (if i < 749 then (if i < 748 then decide (2 ≤ count746 b) else decide (3 ≤ count746 b)) else (if i < 750 then decide (4 ≤ count746 b) else decide (5 ≤ count746 b))))) else (if i < 758 then (if i < 754 then (if i < 752 then decide (6 ≤ count746 b) else (if i < 753 then decide (7 ≤ count746 b) else decide (8 ≤ count746 b))) else (if i < 756 then (if i < 755 then decide (1 ≤ count754 b) else decide (2 ≤ count754 b)) else (if i < 757 then decide (3 ≤ count754 b) else decide (4 ≤ count754 b)))) else (if i < 761 then (if i < 759 then decide (5 ≤ count754 b) else (if i < 760 then decide (6 ≤ count754 b) else decide (7 ≤ count754 b))) else (if i < 763 then (if i < 762 then decide (8 ≤ count754 b) else decide (9 ≤ count754 b)) else (if i < 764 then decide (10 ≤ count754 b) else decide (11 ≤ count754 b)))))) else (if i < 779 then (if i < 772 then (if i < 768 then (if i < 766 then decide (12 ≤ count754 b) else (if i < 767 then decide (13 ≤ count754 b) else decide (14 ≤ count754 b))) else (if i < 770 then (if i < 769 then decide (15 ≤ count754 b) else decide (16 ≤ count754 b)) else (if i < 771 then decide (1 ≤ count770 b) else decide (2 ≤ count770 b)))) else (if i < 775 then (if i < 773 then decide (3 ≤ count770 b) else (if i < 774 then decide (4 ≤ count770 b) else decide (5 ≤ count770 b))) else (if i < 777 then (if i < 776 then decide (6 ≤ count770 b) else decide (7 ≤ count770 b)) else (if i < 778 then decide (8 ≤ count770 b) else decide (9 ≤ count770 b))))) else (if i < 786 then (if i < 782 then (if i < 780 then decide (10 ≤ count770 b) else (if i < 781 then decide (11 ≤ count770 b) else decide (12 ≤ count770 b))) else (if i < 784 then (if i < 783 then decide (13 ≤ count770 b) else decide (14 ≤ count770 b)) else (if i < 785 then decide (15 ≤ count770 b) else decide (16 ≤ count770 b)))) else (if i < 790 then (if i < 788 then (if i < 787 then decide (17 ≤ count770 b) else decide (18 ≤ count770 b)) else (if i < 789 then decide (19 ≤ count770 b) else decide (20 ≤ count770 b))) else (if i < 792 then (if i < 791 then decide (21 ≤ count770 b) else decide (22 ≤ count770 b)) else (if i < 793 then decide (23 ≤ count770 b) else decide (24 ≤ count770 b)))))))) else (if i < 851 then (if i < 822 then (if i < 808 then (if i < 801 then (if i < 797 then (if i < 795 then decide (25 ≤ count770 b) else (if i < 796 then decide (26 ≤ count770 b) else decide (27 ≤ count770 b))) else (if i < 799 then (if i < 798 then decide (28 ≤ count770 b) else decide (29 ≤ count770 b)) else (if i < 800 then decide (30 ≤ count770 b) else decide (31 ≤ count770 b)))) else (if i < 804 then (if i < 802 then decide (1 ≤ count801 b) else (if i < 803 then decide (2 ≤ count801 b) else decide (3 ≤ count801 b))) else (if i < 806 then (if i < 805 then decide (4 ≤ count801 b) else decide (5 ≤ count801 b)) else (if i < 807 then decide (6 ≤ count801 b) else decide (7 ≤ count801 b))))) else (if i < 815 then (if i < 811 then (if i < 809 then decide (8 ≤ count801 b) else (if i < 810 then decide (9 ≤ count801 b) else decide (10 ≤ count801 b))) else (if i < 813 then (if i < 812 then decide (11 ≤ count801 b) else decide (12 ≤ count801 b)) else (if i < 814 then decide (13 ≤ count801 b) else decide (14 ≤ count801 b)))) else (if i < 818 then (if i < 816 then decide (15 ≤ count801 b) else (if i < 817 then decide (16 ≤ count801 b) else decide (17 ≤ count801 b))) else (if i < 820 then (if i < 819 then decide (18 ≤ count801 b) else decide (19 ≤ count801 b)) else (if i < 821 then decide (20 ≤ count801 b) else decide (21 ≤ count801 b)))))) else (if i < 836 then (if i < 829 then (if i < 825 then (if i < 823 then decide (22 ≤ count801 b) else (if i < 824 then decide (23 ≤ count801 b) else decide (24 ≤ count801 b))) else (if i < 827 then (if i < 826 then decide (25 ≤ count801 b) else decide (26 ≤ count801 b)) else (if i < 828 then decide (27 ≤ count801 b) else decide (28 ≤ count801 b)))) else (if i < 832 then (if i < 830 then decide (29 ≤ count801 b) else (if i < 831 then decide (30 ≤ count801 b) else decide (31 ≤ count801 b))) else (if i < 834 then (if i < 833 then decide (32 ≤ count801 b) else decide (33 ≤ count801 b)) else (if i < 835 then decide (34 ≤ count801 b) else decide (35 ≤ count801 b))))) else (if i < 843 then (if i < 839 then (if i < 837 then decide (36 ≤ count801 b) else (if i < 838 then decide (37 ≤ count801 b) else decide (38 ≤ count801 b))) else (if i < 841 then (if i < 840 then decide (39 ≤ count801 b) else decide (40 ≤ count801 b)) else (if i < 842 then decide (41 ≤ count801 b) else decide (42 ≤ count801 b)))) else (if i < 847 then (if i < 845 then (if i < 844 then decide (1 ≤ count843 b) else decide (2 ≤ count843 b)) else (if i < 846 then decide (1 ≤ count845 b) else decide (2 ≤ count845 b))) else (if i < 849 then (if i < 848 then decide (3 ≤ count845 b) else decide (1 ≤ count848 b)) else (if i < 850 then decide (2 ≤ count848 b) else decide (1 ≤ count850 b))))))) else (if i < 879 then (if i < 865 then (if i < 858 then (if i < 854 then (if i < 852 then decide (2 ≤ count850 b) else (if i < 853 then decide (1 ≤ count852 b) else decide (2 ≤ count852 b))) else (if i < 856 then (if i < 855 then decide (3 ≤ count852 b) else decide (4 ≤ count852 b)) else (if i < 857 then decide (1 ≤ count856 b) else decide (2 ≤ count856 b)))) else (if i < 861 then (if i < 859 then decide (3 ≤ count856 b) else (if i < 860 then decide (4 ≤ count856 b) else decide (5 ≤ count856 b))) else (if i < 863 then (if i < 862 then decide (6 ≤ count856 b) else decide (7 ≤ count856 b)) else (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b))))) else (if i < 872 then (if i < 868 then (if i < 866 then decide (1 ≤ count865 b) else (if i < 867 then decide (2 ≤ count865 b) else decide (1 ≤ count867 b))) else (if i < 870 then (if i < 869 then decide (2 ≤ count867 b) else decide (3 ≤ count867 b)) else (if i < 871 then decide (4 ≤ count867 b) else decide (1 ≤ count871 b)))) else (if i < 875 then (if i < 873 then decide (2 ≤ count871 b) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b))) else (if i < 877 then (if i < 876 then decide (1 ≤ count875 b) else decide (2 ≤ count875 b)) else (if i < 878 then decide (3 ≤ count875 b) else decide (4 ≤ count875 b)))))) else (if i < 893 then (if i < 886 then (if i < 882 then (if i < 880 then decide (1 ≤ count879 b) else (if i < 881 then decide (2 ≤ count879 b) else decide (3 ≤ count879 b))) else (if i < 884 then (if i < 883 then decide (4 ≤ count879 b) else decide (5 ≤ count879 b)) else (if i < 885 then decide (6 ≤ count879 b) else decide (7 ≤ count879 b)))) else (if i < 889 then (if i < 887 then decide (8 ≤ count879 b) else (if i < 888 then decide (1 ≤ count887 b) else decide (2 ≤ count887 b))) else (if i < 891 then (if i < 890 then decide (3 ≤ count887 b) else decide (4 ≤ count887 b)) else (if i < 892 then decide (5 ≤ count887 b) else decide (6 ≤ count887 b))))) else (if i < 900 then (if i < 896 then (if i < 894 then decide (7 ≤ count887 b) else (if i < 895 then decide (8 ≤ count887 b) else decide (9 ≤ count887 b))) else (if i < 898 then (if i < 897 then decide (10 ≤ count887 b) else decide (11 ≤ count887 b)) else (if i < 899 then decide (12 ≤ count887 b) else decide (13 ≤ count887 b)))) else (if i < 904 then (if i < 902 then (if i < 901 then decide (14 ≤ count887 b) else decide (15 ≤ count887 b)) else (if i < 903 then decide (1 ≤ count902 b) else decide (2 ≤ count902 b))) else (if i < 906 then (if i < 905 then decide (1 ≤ count904 b) else decide (2 ≤ count904 b)) else (if i < 907 then decide (1 ≤ count906 b) else decide (2 ≤ count906 b))))))))))) else (if i < 1362 then (if i < 1135 then (if i < 1021 then (if i < 964 then (if i < 936 then (if i < 922 then (if i < 915 then (if i < 911 then (if i < 909 then decide (3 ≤ count906 b) else (if i < 910 then decide (4 ≤ count906 b) else decide (1 ≤ count910 b))) else (if i < 913 then (if i < 912 then decide (2 ≤ count910 b) else decide (1 ≤ count912 b)) else (if i < 914 then decide (2 ≤ count912 b) else decide (1 ≤ count914 b)))) else (if i < 918 then (if i < 916 then decide (2 ≤ count914 b) else (if i < 917 then decide (3 ≤ count914 b) else decide (4 ≤ count914 b))) else (if i < 920 then (if i < 919 then decide (1 ≤ count918 b) else decide (2 ≤ count918 b)) else (if i < 921 then decide (3 ≤ count918 b) else decide (4 ≤ count918 b))))) else (if i < 929 then (if i < 925 then (if i < 923 then decide (5 ≤ count918 b) else (if i < 924 then decide (6 ≤ count918 b) else decide (7 ≤ count918 b))) else (if i < 927 then (if i < 926 then decide (8 ≤ count918 b) else decide (1 ≤ count926 b)) else (if i < 928 then decide (2 ≤ count926 b) else decide (1 ≤ count928 b)))) else (if i < 932 then (if i < 930 then decide (2 ≤ count928 b) else (if i < 931 then decide (1 ≤ count930 b) else decide (2 ≤ count930 b))) else (if i < 934 then (if i < 933 then decide (3 ≤ count930 b) else decide (4 ≤ count930 b)) else (if i < 935 then decide (1 ≤ count934 b) else decide (2 ≤ count934 b)))))) else (if i < 950 then (if i < 943 then (if i < 939 then (if i < 937 then decide (1 ≤ count936 b) else (if i < 938 then decide (2 ≤ count936 b) else decide (1 ≤ count938 b))) else (if i < 941 then (if i < 940 then decide (2 ≤ count938 b) else decide (3 ≤ count938 b)) else (if i < 942 then decide (4 ≤ count938 b) else decide (1 ≤ count942 b)))) else (if i < 946 then (if i < 944 then decide (2 ≤ count942 b) else (if i < 945 then decide (3 ≤ count942 b) else decide (4 ≤ count942 b))) else (if i < 948 then (if i < 947 then decide (5 ≤ count942 b) else decide (6 ≤ count942 b)) else (if i < 949 then decide (7 ≤ count942 b) else decide (8 ≤ count942 b))))) else (if i < 957 then (if i < 953 then (if i < 951 then decide (1 ≤ count950 b) else (if i < 952 then decide (2 ≤ count950 b) else decide (3 ≤ count950 b))) else (if i < 955 then (if i < 954 then decide (4 ≤ count950 b) else decide (5 ≤ count950 b)) else (if i < 956 then decide (6 ≤ count950 b) else decide (7 ≤ count950 b)))) else (if i < 960 then (if i < 958 then decide (8 ≤ count950 b) else (if i < 959 then decide (9 ≤ count950 b) else decide (10 ≤ count950 b))) else (if i < 962 then (if i < 961 then decide (11 ≤ count950 b) else decide (12 ≤ count950 b)) else (if i < 963 then decide (13 ≤ count950 b) else decide (14 ≤ count950 b))))))) else (if i < 992 then (if i < 978 then (if i < 971 then (if i < 967 then (if i < 965 then decide (15 ≤ count950 b) else (if i < 966 then decide (16 ≤ count950 b) else decide (1 ≤ count966 b))) else (if i < 969 then (if i < 968 then decide (2 ≤ count966 b) else decide (3 ≤ count966 b)) else (if i < 970 then decide (4 ≤ count966 b) else decide (5 ≤ count966 b)))) else (if i < 974 then (if i < 972 then decide (6 ≤ count966 b) else (if i < 973 then decide (7 ≤ count966 b) else decide (8 ≤ count966 b))) else (if i < 976 then (if i < 975 then decide (9 ≤ count966 b) else decide (10 ≤ count966 b)) else (if i < 977 then decide (11 ≤ count966 b) else decide (12 ≤ count966 b))))) else (if i < 985 then (if i < 981 then (if i < 979 then decide (13 ≤ count966 b) else (if i < 980 then decide (14 ≤ count966 b) else decide (15 ≤ count966 b))) else (if i < 983 then (if i < 982 then decide (16 ≤ count966 b) else decide (17 ≤ count966 b)) else (if i < 984 then decide (18 ≤ count966 b) else decide (19 ≤ count966 b)))) else (if i < 988 then (if i < 986 then decide (20 ≤ count966 b) else (if i < 987 then decide (21 ≤ count966 b) else decide (22 ≤ count966 b))) else (if i < 990 then (if i < 989 then decide (1 ≤ count988 b) else decide (2 ≤ count988 b)) else (if i < 991 then decide (1 ≤ count990 b) else decide (2 ≤ count990 b)))))) else (if i < 1006 then (if i < 999 then (if i < 995 then (if i < 993 then decide (3 ≤ count990 b) else (if i < 994 then decide (1 ≤ count993 b) else decide (2 ≤ count993 b))) else (if i < 997 then (if i < 996 then decide (1 ≤ count995 b) else decide (2 ≤ count995 b)) else (if i < 998 then decide (1 ≤ count997 b) else decide (2 ≤ count997 b)))) else (if i < 1002 then (if i < 1000 then decide (3 ≤ count997 b) else (if i < 1001 then decide (4 ≤ count997 b) else decide (1 ≤ count1001 b))) else (if i < 1004 then (if i < 1003 then decide (2 ≤ count1001 b) else decide (3 ≤ count1001 b)) else (if i < 1005 then decide (4 ≤ count1001 b) else decide (5 ≤ count1001 b))))) else (if i < 1013 then (if i < 1009 then (if i < 1007 then decide (6 ≤ count1001 b) else (if i < 1008 then decide (7 ≤ count1001 b) else decide (1 ≤ count1008 b))) else (if i < 1011 then (if i < 1010 then decide (2 ≤ count1008 b) else decide (1 ≤ count1010 b)) else (if i < 1012 then decide (2 ≤ count1010 b) else decide (1 ≤ count1012 b)))) else (if i < 1017 then (if i < 1015 then (if i < 1014 then decide (2 ≤ count1012 b) else decide (3 ≤ count1012 b)) else (if i < 1016 then decide (4 ≤ count1012 b) else decide (1 ≤ count1016 b))) else (if i < 1019 then (if i < 1018 then decide (2 ≤ count1016 b) else decide (1 ≤ count1018 b)) else (if i < 1020 then decide (2 ≤ count1018 b) else decide (1 ≤ count1020 b)))))))) else (if i < 1078 then (if i < 1049 then (if i < 1035 then (if i < 1028 then (if i < 1024 then (if i < 1022 then decide (2 ≤ count1020 b) else (if i < 1023 then decide (3 ≤ count1020 b) else decide (4 ≤ count1020 b))) else (if i < 1026 then (if i < 1025 then decide (1 ≤ count1024 b) else decide (2 ≤ count1024 b)) else (if i < 1027 then decide (3 ≤ count1024 b) else decide (4 ≤ count1024 b)))) else (if i < 1031 then (if i < 1029 then decide (5 ≤ count1024 b) else (if i < 1030 then decide (6 ≤ count1024 b) else decide (7 ≤ count1024 b))) else (if i < 1033 then (if i < 1032 then decide (8 ≤ count1024 b) else decide (1 ≤ count1032 b)) else (if i < 1034 then decide (2 ≤ count1032 b) else decide (3 ≤ count1032 b))))) else (if i < 1042 then (if i < 1038 then (if i < 1036 then decide (4 ≤ count1032 b) else (if i < 1037 then decide (5 ≤ count1032 b) else decide (6 ≤ count1032 b))) else (if i < 1040 then (if i < 1039 then decide (7 ≤ count1032 b) else decide (8 ≤ count1032 b)) else (if i < 1041 then decide (9 ≤ count1032 b) else decide (10 ≤ count1032 b)))) else (if i < 1045 then (if i < 1043 then decide (11 ≤ count1032 b) else (if i < 1044 then decide (12 ≤ count1032 b) else decide (13 ≤ count1032 b))) else (if i < 1047 then (if i < 1046 then decide (14 ≤ count1032 b) else decide (15 ≤ count1032 b)) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b)))))) else (if i < 1063 then (if i < 1056 then (if i < 1052 then (if i < 1050 then decide (1 ≤ count1049 b) else (if i < 1051 then decide (2 ≤ count1049 b) else decide (1 ≤ count1051 b))) else (if i < 1054 then (if i < 1053 then decide (2 ≤ count1051 b) else decide (3 ≤ count1051 b)) else (if i < 1055 then decide (4 ≤ count1051 b) else decide (1 ≤ count1055 b)))) else (if i < 1059 then (if i < 1057 then decide (2 ≤ count1055 b) else (if i < 1058 then decide (1 ≤ count1057 b) else decide (2 ≤ count1057 b))) else (if i < 1061 then (if i < 1060 then decide (1 ≤ count1059 b) else decide (2 ≤ count1059 b)) else (if i < 1062 then decide (3 ≤ count1059 b) else decide (4 ≤ count1059 b))))) else (if i < 1070 then (if i < 1066 then (if i < 1064 then decide (1 ≤ count1063 b) else (if i < 1065 then decide (2 ≤ count1063 b) else decide (3 ≤ count1063 b))) else (if i < 1068 then (if i < 1067 then decide (4 ≤ count1063 b) else decide (5 ≤ count1063 b)) else (if i < 1069 then decide (6 ≤ count1063 b) else decide (7 ≤ count1063 b)))) else (if i < 1074 then (if i < 1072 then (if i < 1071 then decide (8 ≤ count1063 b) else decide (1 ≤ count1071 b)) else (if i < 1073 then decide (2 ≤ count1071 b) else decide (1 ≤ count1073 b))) else (if i < 1076 then (if i < 1075 then decide (2 ≤ count1073 b) else decide (1 ≤ count1075 b)) else (if i < 1077 then decide (2 ≤ count1075 b) else decide (3 ≤ count1075 b))))))) else (if i < 1106 then (if i < 1092 then (if i < 1085 then (if i < 1081 then (if i < 1079 then decide (4 ≤ count1075 b) else (if i < 1080 then decide (1 ≤ count1079 b) else decide (2 ≤ count1079 b))) else (if i < 1083 then (if i < 1082 then decide (1 ≤ count1081 b) else decide (2 ≤ count1081 b)) else (if i < 1084 then decide (1 ≤ count1083 b) else decide (2 ≤ count1083 b)))) else (if i < 1088 then (if i < 1086 then decide (3 ≤ count1083 b) else (if i < 1087 then decide (4 ≤ count1083 b) else decide (1 ≤ count1087 b))) else (if i < 1090 then (if i < 1089 then decide (2 ≤ count1087 b) else decide (3 ≤ count1087 b)) else (if i < 1091 then decide (4 ≤ count1087 b) else decide (5 ≤ count1087 b))))) else (if i < 1099 then (if i < 1095 then (if i < 1093 then decide (6 ≤ count1087 b) else (if i < 1094 then decide (7 ≤ count1087 b) else decide (8 ≤ count1087 b))) else (if i < 1097 then (if i < 1096 then decide (1 ≤ count1095 b) else decide (2 ≤ count1095 b)) else (if i < 1098 then decide (3 ≤ count1095 b) else decide (4 ≤ count1095 b)))) else (if i < 1102 then (if i < 1100 then decide (5 ≤ count1095 b) else (if i < 1101 then decide (6 ≤ count1095 b) else decide (7 ≤ count1095 b))) else (if i < 1104 then (if i < 1103 then decide (8 ≤ count1095 b) else decide (9 ≤ count1095 b)) else (if i < 1105 then decide (10 ≤ count1095 b) else decide (11 ≤ count1095 b)))))) else (if i < 1120 then (if i < 1113 then (if i < 1109 then (if i < 1107 then decide (12 ≤ count1095 b) else (if i < 1108 then decide (13 ≤ count1095 b) else decide (14 ≤ count1095 b))) else (if i < 1111 then (if i < 1110 then decide (15 ≤ count1095 b) else decide (16 ≤ count1095 b)) else (if i < 1112 then decide (1 ≤ count1111 b) else decide (2 ≤ count1111 b)))) else (if i < 1116 then (if i < 1114 then decide (3 ≤ count1111 b) else (if i < 1115 then decide (4 ≤ count1111 b) else decide (5 ≤ count1111 b))) else (if i < 1118 then (if i < 1117 then decide (6 ≤ count1111 b) else decide (7 ≤ count1111 b)) else (if i < 1119 then decide (8 ≤ count1111 b) else decide (9 ≤ count1111 b))))) else (if i < 1127 then (if i < 1123 then (if i < 1121 then decide (10 ≤ count1111 b) else (if i < 1122 then decide (11 ≤ count1111 b) else decide (12 ≤ count1111 b))) else (if i < 1125 then (if i < 1124 then decide (13 ≤ count1111 b) else decide (14 ≤ count1111 b)) else (if i < 1126 then decide (15 ≤ count1111 b) else decide (16 ≤ count1111 b)))) else (if i < 1131 then (if i < 1129 then (if i < 1128 then decide (17 ≤ count1111 b) else decide (18 ≤ count1111 b)) else (if i < 1130 then decide (19 ≤ count1111 b) else decide (20 ≤ count1111 b))) else (if i < 1133 then (if i < 1132 then decide (21 ≤ count1111 b) else decide (22 ≤ count1111 b)) else (if i < 1134 then decide (1 ≤ count1133 b) else decide (2 ≤ count1133 b))))))))) else (if i < 1248 then (if i < 1191 then (if i < 1163 then (if i < 1149 then (if i < 1142 then (if i < 1138 then (if i < 1136 then decide (3 ≤ count1133 b) else (if i < 1137 then decide (4 ≤ count1133 b) else decide (5 ≤ count1133 b))) else (if i < 1140 then (if i < 1139 then decide (6 ≤ count1133 b) else decide (7 ≤ count1133 b)) else (if i < 1141 then decide (8 ≤ count1133 b) else decide (9 ≤ count1133 b)))) else (if i < 1145 then (if i < 1143 then decide (10 ≤ count1133 b) else (if i < 1144 then decide (11 ≤ count1133 b) else decide (12 ≤ count1133 b))) else (if i < 1147 then (if i < 1146 then decide (13 ≤ count1133 b) else decide (14 ≤ count1133 b)) else (if i < 1148 then decide (15 ≤ count1133 b) else decide (16 ≤ count1133 b))))) else (if i < 1156 then (if i < 1152 then (if i < 1150 then decide (17 ≤ count1133 b) else (if i < 1151 then decide (18 ≤ count1133 b) else decide (19 ≤ count1133 b))) else (if i < 1154 then (if i < 1153 then decide (20 ≤ count1133 b) else decide (21 ≤ count1133 b)) else (if i < 1155 then decide (22 ≤ count1133 b) else decide (1 ≤ count1155 b)))) else (if i < 1159 then (if i < 1157 then decide (2 ≤ count1155 b) else (if i < 1158 then decide (1 ≤ count1157 b) else decide (2 ≤ count1157 b))) else (if i < 1161 then (if i < 1160 then decide (3 ≤ count1157 b) else decide (1 ≤ count1160 b)) else (if i < 1162 then decide (2 ≤ count1160 b) else decide (1 ≤ count1162 b)))))) else (if i < 1177 then (if i < 1170 then (if i < 1166 then (if i < 1164 then decide (2 ≤ count1162 b) else (if i < 1165 then decide (1 ≤ count1164 b) else decide (2 ≤ count1164 b))) else (if i < 1168 then (if i < 1167 then decide (3 ≤ count1164 b) else decide (4 ≤ count1164 b)) else (if i < 1169 then decide (1 ≤ count1168 b) else decide (2 ≤ count1168 b)))) else (if i < 1173 then (if i < 1171 then decide (3 ≤ count1168 b) else (if i < 1172 then decide (4 ≤ count1168 b) else decide (5 ≤ count1168 b))) else (if i < 1175 then (if i < 1174 then decide (6 ≤ count1168 b) else decide (7 ≤ count1168 b)) else (if i < 1176 then decide (1 ≤ count1175 b) else decide (2 ≤ count1175 b))))) else (if i < 1184 then (if i < 1180 then (if i < 1178 then decide (1 ≤ count1177 b) else (if i < 1179 then decide (2 ≤ count1177 b) else decide (1 ≤ count1179 b))) else (if i < 1182 then (if i < 1181 then decide (2 ≤ count1179 b) else decide (3 ≤ count1179 b)) else (if i < 1183 then decide (4 ≤ count1179 b) else decide (1 ≤ count1183 b)))) else (if i < 1187 then (if i < 1185 then decide (2 ≤ count1183 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b))) else (if i < 1189 then (if i < 1188 then decide (1 ≤ count1187 b) else decide (2 ≤ count1187 b)) else (if i < 1190 then decide (3 ≤ count1187 b) else decide (4 ≤ count1187 b))))))) else (if i < 1219 then (if i < 1205 then (if i < 1198 then (if i < 1194 then (if i < 1192 then decide (1 ≤ count1191 b) else (if i < 1193 then decide (2 ≤ count1191 b) else decide (3 ≤ count1191 b))) else (if i < 1196 then (if i < 1195 then decide (4 ≤ count1191 b) else decide (5 ≤ count1191 b)) else (if i < 1197 then decide (6 ≤ count1191 b) else decide (7 ≤ count1191 b)))) else (if i < 1201 then (if i < 1199 then decide (8 ≤ count1191 b) else (if i < 1200 then decide (1 ≤ count1199 b) else decide (2 ≤ count1199 b))) else (if i < 1203 then (if i < 1202 then decide (3 ≤ count1199 b) else decide (4 ≤ count1199 b)) else (if i < 1204 then decide (5 ≤ count1199 b) else decide (6 ≤ count1199 b))))) else (if i < 1212 then (if i < 1208 then (if i < 1206 then decide (7 ≤ count1199 b) else (if i < 1207 then decide (8 ≤ count1199 b) else decide (9 ≤ count1199 b))) else (if i < 1210 then (if i < 1209 then decide (10 ≤ count1199 b) else decide (11 ≤ count1199 b)) else (if i < 1211 then decide (12 ≤ count1199 b) else decide (13 ≤ count1199 b)))) else (if i < 1215 then (if i < 1213 then decide (14 ≤ count1199 b) else (if i < 1214 then decide (15 ≤ count1199 b) else decide (1 ≤ count1214 b))) else (if i < 1217 then (if i < 1216 then decide (2 ≤ count1214 b) else decide (1 ≤ count1216 b)) else (if i < 1218 then decide (2 ≤ count1216 b) else decide (1 ≤ count1218 b)))))) else (if i < 1233 then (if i < 1226 then (if i < 1222 then (if i < 1220 then decide (2 ≤ count1218 b) else (if i < 1221 then decide (3 ≤ count1218 b) else decide (4 ≤ count1218 b))) else (if i < 1224 then (if i < 1223 then decide (1 ≤ count1222 b) else decide (2 ≤ count1222 b)) else (if i < 1225 then decide (1 ≤ count1224 b) else decide (2 ≤ count1224 b)))) else (if i < 1229 then (if i < 1227 then decide (1 ≤ count1226 b) else (if i < 1228 then decide (2 ≤ count1226 b) else decide (3 ≤ count1226 b))) else (if i < 1231 then (if i < 1230 then decide (4 ≤ count1226 b) else decide (1 ≤ count1230 b)) else (if i < 1232 then decide (2 ≤ count1230 b) else decide (3 ≤ count1230 b))))) else (if i < 1240 then (if i < 1236 then (if i < 1234 then decide (4 ≤ count1230 b) else (if i < 1235 then decide (5 ≤ count1230 b) else decide (6 ≤ count1230 b))) else (if i < 1238 then (if i < 1237 then decide (7 ≤ count1230 b) else decide (8 ≤ count1230 b)) else (if i < 1239 then decide (1 ≤ count1238 b) else decide (2 ≤ count1238 b)))) else (if i < 1244 then (if i < 1242 then (if i < 1241 then decide (1 ≤ count1240 b) else decide (2 ≤ count1240 b)) else (if i < 1243 then decide (1 ≤ count1242 b) else decide (2 ≤ count1242 b))) else (if i < 1246 then (if i < 1245 then decide (3 ≤ count1242 b) else decide (4 ≤ count1242 b)) else (if i < 1247 then decide (1 ≤ count1246 b) else decide (2 ≤ count1246 b)))))))) else (if i < 1305 then (if i < 1276 then (if i < 1262 then (if i < 1255 then (if i < 1251 then (if i < 1249 then decide (1 ≤ count1248 b) else (if i < 1250 then decide (2 ≤ count1248 b) else decide (1 ≤ count1250 b))) else (if i < 1253 then (if i < 1252 then decide (2 ≤ count1250 b) else decide (3 ≤ count1250 b)) else (if i < 1254 then decide (4 ≤ count1250 b) else decide (1 ≤ count1254 b)))) else (if i < 1258 then (if i < 1256 then decide (2 ≤ count1254 b) else (if i < 1257 then decide (3 ≤ count1254 b) else decide (4 ≤ count1254 b))) else (if i < 1260 then (if i < 1259 then decide (5 ≤ count1254 b) else decide (6 ≤ count1254 b)) else (if i < 1261 then decide (7 ≤ count1254 b) else decide (8 ≤ count1254 b))))) else (if i < 1269 then (if i < 1265 then (if i < 1263 then decide (1 ≤ count1262 b) else (if i < 1264 then decide (2 ≤ count1262 b) else decide (3 ≤ count1262 b))) else (if i < 1267 then (if i < 1266 then decide (4 ≤ count1262 b) else decide (5 ≤ count1262 b)) else (if i < 1268 then decide (6 ≤ count1262 b) else decide (7 ≤ count1262 b)))) else (if i < 1272 then (if i < 1270 then decide (8 ≤ count1262 b) else (if i < 1271 then decide (9 ≤ count1262 b) else decide (10 ≤ count1262 b))) else (if i < 1274 then (if i < 1273 then decide (11 ≤ count1262 b) else decide (12 ≤ count1262 b)) else (if i < 1275 then decide (13 ≤ count1262 b) else decide (14 ≤ count1262 b)))))) else (if i < 1290 then (if i < 1283 then (if i < 1279 then (if i < 1277 then decide (15 ≤ count1262 b) else (if i < 1278 then decide (16 ≤ count1262 b) else decide (1 ≤ count1278 b))) else (if i < 1281 then (if i < 1280 then decide (2 ≤ count1278 b) else decide (3 ≤ count1278 b)) else (if i < 1282 then decide (4 ≤ count1278 b) else decide (5 ≤ count1278 b)))) else (if i < 1286 then (if i < 1284 then decide (6 ≤ count1278 b) else (if i < 1285 then decide (7 ≤ count1278 b) else decide (8 ≤ count1278 b))) else (if i < 1288 then (if i < 1287 then decide (9 ≤ count1278 b) else decide (10 ≤ count1278 b)) else (if i < 1289 then decide (11 ≤ count1278 b) else decide (12 ≤ count1278 b))))) else (if i < 1297 then (if i < 1293 then (if i < 1291 then decide (13 ≤ count1278 b) else (if i < 1292 then decide (14 ≤ count1278 b) else decide (15 ≤ count1278 b))) else (if i < 1295 then (if i < 1294 then decide (16 ≤ count1278 b) else decide (17 ≤ count1278 b)) else (if i < 1296 then decide (18 ≤ count1278 b) else decide (19 ≤ count1278 b)))) else (if i < 1301 then (if i < 1299 then (if i < 1298 then decide (20 ≤ count1278 b) else decide (21 ≤ count1278 b)) else (if i < 1300 then decide (22 ≤ count1278 b) else decide (23 ≤ count1278 b))) else (if i < 1303 then (if i < 1302 then decide (24 ≤ count1278 b) else decide (25 ≤ count1278 b)) else (if i < 1304 then decide (26 ≤ count1278 b) else decide (27 ≤ count1278 b))))))) else (if i < 1333 then (if i < 1319 then (if i < 1312 then (if i < 1308 then (if i < 1306 then decide (28 ≤ count1278 b) else (if i < 1307 then decide (29 ≤ count1278 b) else decide (30 ≤ count1278 b))) else (if i < 1310 then (if i < 1309 then decide (31 ≤ count1278 b) else decide (1 ≤ count1309 b)) else (if i < 1311 then decide (2 ≤ count1309 b) else decide (1 ≤ count1311 b)))) else (if i < 1315 then (if i < 1313 then decide (2 ≤ count1311 b) else (if i < 1314 then decide (3 ≤ count1311 b) else decide (1 ≤ count1314 b))) else (if i < 1317 then (if i < 1316 then decide (2 ≤ count1314 b) else decide (1 ≤ count1316 b)) else (if i < 1318 then decide (2 ≤ count1316 b) else decide (1 ≤ count1318 b))))) else (if i < 1326 then (if i < 1322 then (if i < 1320 then decide (2 ≤ count1318 b) else (if i < 1321 then decide (3 ≤ count1318 b) else decide (4 ≤ count1318 b))) else (if i < 1324 then (if i < 1323 then decide (1 ≤ count1322 b) else decide (2 ≤ count1322 b)) else (if i < 1325 then decide (3 ≤ count1322 b) else decide (4 ≤ count1322 b)))) else (if i < 1329 then (if i < 1327 then decide (5 ≤ count1322 b) else (if i < 1328 then decide (6 ≤ count1322 b) else decide (7 ≤ count1322 b))) else (if i < 1331 then (if i < 1330 then decide (1 ≤ count1329 b) else decide (2 ≤ count1329 b)) else (if i < 1332 then decide (1 ≤ count1331 b) else decide (2 ≤ count1331 b)))))) else (if i < 1347 then (if i < 1340 then (if i < 1336 then (if i < 1334 then decide (1 ≤ count1333 b) else (if i < 1335 then decide (2 ≤ count1333 b) else decide (3 ≤ count1333 b))) else (if i < 1338 then (if i < 1337 then decide (4 ≤ count1333 b) else decide (1 ≤ count1337 b)) else (if i < 1339 then decide (2 ≤ count1337 b) else decide (1 ≤ count1339 b)))) else (if i < 1343 then (if i < 1341 then decide (2 ≤ count1339 b) else (if i < 1342 then decide (1 ≤ count1341 b) else decide (2 ≤ count1341 b))) else (if i < 1345 then (if i < 1344 then decide (3 ≤ count1341 b) else decide (4 ≤ count1341 b)) else (if i < 1346 then decide (1 ≤ count1345 b) else decide (2 ≤ count1345 b))))) else (if i < 1354 then (if i < 1350 then (if i < 1348 then decide (3 ≤ count1345 b) else (if i < 1349 then decide (4 ≤ count1345 b) else decide (5 ≤ count1345 b))) else (if i < 1352 then (if i < 1351 then decide (6 ≤ count1345 b) else decide (7 ≤ count1345 b)) else (if i < 1353 then decide (8 ≤ count1345 b) else decide (1 ≤ count1353 b)))) else (if i < 1358 then (if i < 1356 then (if i < 1355 then decide (2 ≤ count1353 b) else decide (3 ≤ count1353 b)) else (if i < 1357 then decide (4 ≤ count1353 b) else decide (5 ≤ count1353 b))) else (if i < 1360 then (if i < 1359 then decide (6 ≤ count1353 b) else decide (7 ≤ count1353 b)) else (if i < 1361 then decide (8 ≤ count1353 b) else decide (9 ≤ count1353 b)))))))))) else (if i < 1589 then (if i < 1475 then (if i < 1418 then (if i < 1390 then (if i < 1376 then (if i < 1369 then (if i < 1365 then (if i < 1363 then decide (10 ≤ count1353 b) else (if i < 1364 then decide (11 ≤ count1353 b) else decide (12 ≤ count1353 b))) else (if i < 1367 then (if i < 1366 then decide (13 ≤ count1353 b) else decide (14 ≤ count1353 b)) else (if i < 1368 then decide (15 ≤ count1353 b) else decide (1 ≤ count1368 b)))) else (if i < 1372 then (if i < 1370 then decide (2 ≤ count1368 b) else (if i < 1371 then decide (1 ≤ count1370 b) else decide (2 ≤ count1370 b))) else (if i < 1374 then (if i < 1373 then decide (1 ≤ count1372 b) else decide (2 ≤ count1372 b)) else (if i < 1375 then decide (3 ≤ count1372 b) else decide (4 ≤ count1372 b))))) else (if i < 1383 then (if i < 1379 then (if i < 1377 then decide (1 ≤ count1376 b) else (if i < 1378 then decide (2 ≤ count1376 b) else decide (1 ≤ count1378 b))) else (if i < 1381 then (if i < 1380 then decide (2 ≤ count1378 b) else decide (1 ≤ count1380 b)) else (if i < 1382 then decide (2 ≤ count1380 b) else decide (3 ≤ count1380 b)))) else (if i < 1386 then (if i < 1384 then decide (4 ≤ count1380 b) else (if i < 1385 then decide (1 ≤ count1384 b) else decide (2 ≤ count1384 b))) else (if i < 1388 then (if i < 1387 then decide (3 ≤ count1384 b) else decide (4 ≤ count1384 b)) else (if i < 1389 then decide (5 ≤ count1384 b) else decide (6 ≤ count1384 b)))))) else (if i < 1404 then (if i < 1397 then (if i < 1393 then (if i < 1391 then decide (7 ≤ count1384 b) else (if i < 1392 then decide (8 ≤ count1384 b) else decide (1 ≤ count1392 b))) else (if i < 1395 then (if i < 1394 then decide (2 ≤ count1392 b) else decide (1 ≤ count1394 b)) else (if i < 1396 then decide (2 ≤ count1394 b) else decide (1 ≤ count1396 b)))) else (if i < 1400 then (if i < 1398 then decide (2 ≤ count1396 b) else (if i < 1399 then decide (3 ≤ count1396 b) else decide (4 ≤ count1396 b))) else (if i < 1402 then (if i < 1401 then decide (1 ≤ count1400 b) else decide (2 ≤ count1400 b)) else (if i < 1403 then decide (1 ≤ count1402 b) else decide (2 ≤ count1402 b))))) else (if i < 1411 then (if i < 1407 then (if i < 1405 then decide (1 ≤ count1404 b) else (if i < 1406 then decide (2 ≤ count1404 b) else decide (3 ≤ count1404 b))) else (if i < 1409 then (if i < 1408 then decide (4 ≤ count1404 b) else decide (1 ≤ count1408 b)) else (if i < 1410 then decide (2 ≤ count1408 b) else decide (3 ≤ count1408 b)))) else (if i < 1414 then (if i < 1412 then decide (4 ≤ count1408 b) else (if i < 1413 then decide (5 ≤ count1408 b) else decide (6 ≤ count1408 b))) else (if i < 1416 then (if i < 1415 then decide (7 ≤ count1408 b) else decide (8 ≤ count1408 b)) else (if i < 1417 then decide (1 ≤ count1416 b) else decide (2 ≤ count1416 b))))))) else (if i < 1446 then (if i < 1432 then (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (3 ≤ count1416 b) else (if i < 1420 then decide (4 ≤ count1416 b) else decide (5 ≤ count1416 b))) else (if i < 1423 then (if i < 1422 then decide (6 ≤ count1416 b) else decide (7 ≤ count1416 b)) else (if i < 1424 then decide (8 ≤ count1416 b) else decide (9 ≤ count1416 b)))) else (if i < 1428 then (if i < 1426 then decide (10 ≤ count1416 b) else (if i < 1427 then decide (11 ≤ count1416 b) else decide (12 ≤ count1416 b))) else (if i < 1430 then (if i < 1429 then decide (13 ≤ count1416 b) else decide (14 ≤ count1416 b)) else (if i < 1431 then decide (15 ≤ count1416 b) else decide (16 ≤ count1416 b))))) else (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (1 ≤ count1432 b) else (if i < 1434 then decide (2 ≤ count1432 b) else decide (3 ≤ count1432 b))) else (if i < 1437 then (if i < 1436 then decide (4 ≤ count1432 b) else decide (5 ≤ count1432 b)) else (if i < 1438 then decide (6 ≤ count1432 b) else decide (7 ≤ count1432 b)))) else (if i < 1442 then (if i < 1440 then decide (8 ≤ count1432 b) else (if i < 1441 then decide (9 ≤ count1432 b) else decide (10 ≤ count1432 b))) else (if i < 1444 then (if i < 1443 then decide (11 ≤ count1432 b) else decide (12 ≤ count1432 b)) else (if i < 1445 then decide (13 ≤ count1432 b) else decide (14 ≤ count1432 b)))))) else (if i < 1460 then (if i < 1453 then (if i < 1449 then (if i < 1447 then decide (15 ≤ count1432 b) else (if i < 1448 then decide (16 ≤ count1432 b) else decide (17 ≤ count1432 b))) else (if i < 1451 then (if i < 1450 then decide (18 ≤ count1432 b) else decide (19 ≤ count1432 b)) else (if i < 1452 then decide (20 ≤ count1432 b) else decide (21 ≤ count1432 b)))) else (if i < 1456 then (if i < 1454 then decide (22 ≤ count1432 b) else (if i < 1455 then decide (23 ≤ count1432 b) else decide (24 ≤ count1432 b))) else (if i < 1458 then (if i < 1457 then decide (25 ≤ count1432 b) else decide (26 ≤ count1432 b)) else (if i < 1459 then decide (27 ≤ count1432 b) else decide (28 ≤ count1432 b))))) else (if i < 1467 then (if i < 1463 then (if i < 1461 then decide (29 ≤ count1432 b) else (if i < 1462 then decide (30 ≤ count1432 b) else decide (31 ≤ count1432 b))) else (if i < 1465 then (if i < 1464 then decide (1 ≤ count1463 b) else decide (2 ≤ count1463 b)) else (if i < 1466 then decide (3 ≤ count1463 b) else decide (4 ≤ count1463 b)))) else (if i < 1471 then (if i < 1469 then (if i < 1468 then decide (5 ≤ count1463 b) else decide (6 ≤ count1463 b)) else (if i < 1470 then decide (7 ≤ count1463 b) else decide (8 ≤ count1463 b))) else (if i < 1473 then (if i < 1472 then decide (9 ≤ count1463 b) else decide (10 ≤ count1463 b)) else (if i < 1474 then decide (11 ≤ count1463 b) else decide (12 ≤ count1463 b)))))))) else (if i < 1532 then (if i < 1503 then (if i < 1489 then (if i < 1482 then (if i < 1478 then (if i < 1476 then decide (13 ≤ count1463 b) else (if i < 1477 then decide (14 ≤ count1463 b) else decide (15 ≤ count1463 b))) else (if i < 1480 then (if i < 1479 then decide (16 ≤ count1463 b) else decide (17 ≤ count1463 b)) else (if i < 1481 then decide (18 ≤ count1463 b) else decide (19 ≤ count1463 b)))) else (if i < 1485 then (if i < 1483 then decide (20 ≤ count1463 b) else (if i < 1484 then decide (21 ≤ count1463 b) else decide (22 ≤ count1463 b))) else (if i < 1487 then (if i < 1486 then decide (23 ≤ count1463 b) else decide (24 ≤ count1463 b)) else (if i < 1488 then decide (25 ≤ count1463 b) else decide (26 ≤ count1463 b))))) else (if i < 1496 then (if i < 1492 then (if i < 1490 then decide (27 ≤ count1463 b) else (if i < 1491 then decide (28 ≤ count1463 b) else decide (29 ≤ count1463 b))) else (if i < 1494 then (if i < 1493 then decide (30 ≤ count1463 b) else decide (31 ≤ count1463 b)) else (if i < 1495 then decide (32 ≤ count1463 b) else decide (33 ≤ count1463 b)))) else (if i < 1499 then (if i < 1497 then decide (34 ≤ count1463 b) else (if i < 1498 then decide (35 ≤ count1463 b) else decide (36 ≤ count1463 b))) else (if i < 1501 then (if i < 1500 then decide (37 ≤ count1463 b) else decide (38 ≤ count1463 b)) else (if i < 1502 then decide (39 ≤ count1463 b) else decide (40 ≤ count1463 b)))))) else (if i < 1517 then (if i < 1510 then (if i < 1506 then (if i < 1504 then decide (41 ≤ count1463 b) else (if i < 1505 then decide (42 ≤ count1463 b) else decide (1 ≤ count1505 b))) else (if i < 1508 then (if i < 1507 then decide (2 ≤ count1505 b) else decide (1 ≤ count1507 b)) else (if i < 1509 then decide (2 ≤ count1507 b) else decide (3 ≤ count1507 b)))) else (if i < 1513 then (if i < 1511 then decide (1 ≤ count1510 b) else (if i < 1512 then decide (2 ≤ count1510 b) else decide (1 ≤ count1512 b))) else (if i < 1515 then (if i < 1514 then decide (2 ≤ count1512 b) else decide (1 ≤ count1514 b)) else (if i < 1516 then decide (2 ≤ count1514 b) else decide (3 ≤ count1514 b))))) else (if i < 1524 then (if i < 1520 then (if i < 1518 then decide (4 ≤ count1514 b) else (if i < 1519 then decide (1 ≤ count1518 b) else decide (2 ≤ count1518 b))) else (if i < 1522 then (if i < 1521 then decide (3 ≤ count1518 b) else decide (4 ≤ count1518 b)) else (if i < 1523 then decide (5 ≤ count1518 b) else decide (6 ≤ count1518 b)))) else (if i < 1528 then (if i < 1526 then (if i < 1525 then decide (7 ≤ count1518 b) else decide (1 ≤ count1525 b)) else (if i < 1527 then decide (2 ≤ count1525 b) else decide (1 ≤ count1527 b))) else (if i < 1530 then (if i < 1529 then decide (2 ≤ count1527 b) else decide (1 ≤ count1529 b)) else (if i < 1531 then decide (2 ≤ count1529 b) else decide (3 ≤ count1529 b))))))) else (if i < 1560 then (if i < 1546 then (if i < 1539 then (if i < 1535 then (if i < 1533 then decide (4 ≤ count1529 b) else (if i < 1534 then decide (1 ≤ count1533 b) else decide (2 ≤ count1533 b))) else (if i < 1537 then (if i < 1536 then decide (1 ≤ count1535 b) else decide (2 ≤ count1535 b)) else (if i < 1538 then decide (1 ≤ count1537 b) else decide (2 ≤ count1537 b)))) else (if i < 1542 then (if i < 1540 then decide (3 ≤ count1537 b) else (if i < 1541 then decide (4 ≤ count1537 b) else decide (1 ≤ count1541 b))) else (if i < 1544 then (if i < 1543 then decide (2 ≤ count1541 b) else decide (3 ≤ count1541 b)) else (if i < 1545 then decide (4 ≤ count1541 b) else decide (5 ≤ count1541 b))))) else (if i < 1553 then (if i < 1549 then (if i < 1547 then decide (6 ≤ count1541 b) else (if i < 1548 then decide (7 ≤ count1541 b) else decide (8 ≤ count1541 b))) else (if i < 1551 then (if i < 1550 then decide (1 ≤ count1549 b) else decide (2 ≤ count1549 b)) else (if i < 1552 then decide (3 ≤ count1549 b) else decide (4 ≤ count1549 b)))) else (if i < 1556 then (if i < 1554 then decide (5 ≤ count1549 b) else (if i < 1555 then decide (6 ≤ count1549 b) else decide (7 ≤ count1549 b))) else (if i < 1558 then (if i < 1557 then decide (8 ≤ count1549 b) else decide (9 ≤ count1549 b)) else (if i < 1559 then decide (10 ≤ count1549 b) else decide (11 ≤ count1549 b)))))) else (if i < 1574 then (if i < 1567 then (if i < 1563 then (if i < 1561 then decide (12 ≤ count1549 b) else (if i < 1562 then decide (13 ≤ count1549 b) else decide (14 ≤ count1549 b))) else (if i < 1565 then (if i < 1564 then decide (15 ≤ count1549 b) else decide (1 ≤ count1564 b)) else (if i < 1566 then decide (2 ≤ count1564 b) else decide (1 ≤ count1566 b)))) else (if i < 1570 then (if i < 1568 then decide (2 ≤ count1566 b) else (if i < 1569 then decide (1 ≤ count1568 b) else decide (2 ≤ count1568 b))) else (if i < 1572 then (if i < 1571 then decide (3 ≤ count1568 b) else decide (4 ≤ count1568 b)) else (if i < 1573 then decide (1 ≤ count1572 b) else decide (2 ≤ count1572 b))))) else (if i < 1581 then (if i < 1577 then (if i < 1575 then decide (1 ≤ count1574 b) else (if i < 1576 then decide (2 ≤ count1574 b) else decide (1 ≤ count1576 b))) else (if i < 1579 then (if i < 1578 then decide (2 ≤ count1576 b) else decide (3 ≤ count1576 b)) else (if i < 1580 then decide (4 ≤ count1576 b) else decide (1 ≤ count1580 b)))) else (if i < 1585 then (if i < 1583 then (if i < 1582 then decide (2 ≤ count1580 b) else decide (3 ≤ count1580 b)) else (if i < 1584 then decide (4 ≤ count1580 b) else decide (5 ≤ count1580 b))) else (if i < 1587 then (if i < 1586 then decide (6 ≤ count1580 b) else decide (7 ≤ count1580 b)) else (if i < 1588 then decide (8 ≤ count1580 b) else decide (1 ≤ count1588 b))))))))) else (if i < 1703 then (if i < 1646 then (if i < 1617 then (if i < 1603 then (if i < 1596 then (if i < 1592 then (if i < 1590 then decide (2 ≤ count1588 b) else (if i < 1591 then decide (1 ≤ count1590 b) else decide (2 ≤ count1590 b))) else (if i < 1594 then (if i < 1593 then decide (1 ≤ count1592 b) else decide (2 ≤ count1592 b)) else (if i < 1595 then decide (3 ≤ count1592 b) else decide (4 ≤ count1592 b)))) else (if i < 1599 then (if i < 1597 then decide (1 ≤ count1596 b) else (if i < 1598 then decide (2 ≤ count1596 b) else decide (1 ≤ count1598 b))) else (if i < 1601 then (if i < 1600 then decide (2 ≤ count1598 b) else decide (1 ≤ count1600 b)) else (if i < 1602 then decide (2 ≤ count1600 b) else decide (3 ≤ count1600 b))))) else (if i < 1610 then (if i < 1606 then (if i < 1604 then decide (4 ≤ count1600 b) else (if i < 1605 then decide (1 ≤ count1604 b) else decide (2 ≤ count1604 b))) else (if i < 1608 then (if i < 1607 then decide (3 ≤ count1604 b) else decide (4 ≤ count1604 b)) else (if i < 1609 then decide (5 ≤ count1604 b) else decide (6 ≤ count1604 b)))) else (if i < 1613 then (if i < 1611 then decide (7 ≤ count1604 b) else (if i < 1612 then decide (8 ≤ count1604 b) else decide (1 ≤ count1612 b))) else (if i < 1615 then (if i < 1614 then decide (2 ≤ count1612 b) else decide (3 ≤ count1612 b)) else (if i < 1616 then decide (4 ≤ count1612 b) else decide (5 ≤ count1612 b)))))) else (if i < 1631 then (if i < 1624 then (if i < 1620 then (if i < 1618 then decide (6 ≤ count1612 b) else (if i < 1619 then decide (7 ≤ count1612 b) else decide (8 ≤ count1612 b))) else (if i < 1622 then (if i < 1621 then decide (9 ≤ count1612 b) else decide (10 ≤ count1612 b)) else (if i < 1623 then decide (11 ≤ count1612 b) else decide (12 ≤ count1612 b)))) else (if i < 1627 then (if i < 1625 then decide (13 ≤ count1612 b) else (if i < 1626 then decide (14 ≤ count1612 b) else decide (15 ≤ count1612 b))) else (if i < 1629 then (if i < 1628 then decide (16 ≤ count1612 b) else decide (1 ≤ count1628 b)) else (if i < 1630 then decide (2 ≤ count1628 b) else decide (3 ≤ count1628 b))))) else (if i < 1638 then (if i < 1634 then (if i < 1632 then decide (4 ≤ count1628 b) else (if i < 1633 then decide (5 ≤ count1628 b) else decide (6 ≤ count1628 b))) else (if i < 1636 then (if i < 1635 then decide (7 ≤ count1628 b) else decide (8 ≤ count1628 b)) else (if i < 1637 then decide (9 ≤ count1628 b) else decide (10 ≤ count1628 b)))) else (if i < 1642 then (if i < 1640 then (if i < 1639 then decide (11 ≤ count1628 b) else decide (12 ≤ count1628 b)) else (if i < 1641 then decide (13 ≤ count1628 b) else decide (14 ≤ count1628 b))) else (if i < 1644 then (if i < 1643 then decide (15 ≤ count1628 b) else decide (16 ≤ count1628 b)) else (if i < 1645 then decide (17 ≤ count1628 b) else decide (18 ≤ count1628 b))))))) else (if i < 1674 then (if i < 1660 then (if i < 1653 then (if i < 1649 then (if i < 1647 then decide (19 ≤ count1628 b) else (if i < 1648 then decide (20 ≤ count1628 b) else decide (21 ≤ count1628 b))) else (if i < 1651 then (if i < 1650 then decide (22 ≤ count1628 b) else decide (1 ≤ count1650 b)) else (if i < 1652 then decide (2 ≤ count1650 b) else decide (1 ≤ count1652 b)))) else (if i < 1656 then (if i < 1654 then decide (2 ≤ count1652 b) else (if i < 1655 then decide (3 ≤ count1652 b) else decide (1 ≤ count1655 b))) else (if i < 1658 then (if i < 1657 then decide (2 ≤ count1655 b) else decide (1 ≤ count1657 b)) else (if i < 1659 then decide (2 ≤ count1657 b) else decide (1 ≤ count1659 b))))) else (if i < 1667 then (if i < 1663 then (if i < 1661 then decide (2 ≤ count1659 b) else (if i < 1662 then decide (3 ≤ count1659 b) else decide (4 ≤ count1659 b))) else (if i < 1665 then (if i < 1664 then decide (1 ≤ count1663 b) else decide (2 ≤ count1663 b)) else (if i < 1666 then decide (3 ≤ count1663 b) else decide (4 ≤ count1663 b)))) else (if i < 1670 then (if i < 1668 then decide (5 ≤ count1663 b) else (if i < 1669 then decide (6 ≤ count1663 b) else decide (7 ≤ count1663 b))) else (if i < 1672 then (if i < 1671 then decide (1 ≤ count1670 b) else decide (2 ≤ count1670 b)) else (if i < 1673 then decide (1 ≤ count1672 b) else decide (2 ≤ count1672 b)))))) else (if i < 1688 then (if i < 1681 then (if i < 1677 then (if i < 1675 then decide (1 ≤ count1674 b) else (if i < 1676 then decide (2 ≤ count1674 b) else decide (3 ≤ count1674 b))) else (if i < 1679 then (if i < 1678 then decide (4 ≤ count1674 b) else decide (1 ≤ count1678 b)) else (if i < 1680 then decide (2 ≤ count1678 b) else decide (1 ≤ count1680 b)))) else (if i < 1684 then (if i < 1682 then decide (2 ≤ count1680 b) else (if i < 1683 then decide (1 ≤ count1682 b) else decide (2 ≤ count1682 b))) else (if i < 1686 then (if i < 1685 then decide (3 ≤ count1682 b) else decide (4 ≤ count1682 b)) else (if i < 1687 then decide (1 ≤ count1686 b) else decide (2 ≤ count1686 b))))) else (if i < 1695 then (if i < 1691 then (if i < 1689 then decide (3 ≤ count1686 b) else (if i < 1690 then decide (4 ≤ count1686 b) else decide (5 ≤ count1686 b))) else (if i < 1693 then (if i < 1692 then decide (6 ≤ count1686 b) else decide (7 ≤ count1686 b)) else (if i < 1694 then decide (8 ≤ count1686 b) else decide (1 ≤ count1694 b)))) else (if i < 1699 then (if i < 1697 then (if i < 1696 then decide (2 ≤ count1694 b) else decide (3 ≤ count1694 b)) else (if i < 1698 then decide (4 ≤ count1694 b) else decide (5 ≤ count1694 b))) else (if i < 1701 then (if i < 1700 then decide (6 ≤ count1694 b) else decide (7 ≤ count1694 b)) else (if i < 1702 then decide (8 ≤ count1694 b) else decide (9 ≤ count1694 b)))))))) else (if i < 1760 then (if i < 1731 then (if i < 1717 then (if i < 1710 then (if i < 1706 then (if i < 1704 then decide (10 ≤ count1694 b) else (if i < 1705 then decide (11 ≤ count1694 b) else decide (12 ≤ count1694 b))) else (if i < 1708 then (if i < 1707 then decide (13 ≤ count1694 b) else decide (14 ≤ count1694 b)) else (if i < 1709 then decide (15 ≤ count1694 b) else decide (1 ≤ count1709 b)))) else (if i < 1713 then (if i < 1711 then decide (2 ≤ count1709 b) else (if i < 1712 then decide (1 ≤ count1711 b) else decide (2 ≤ count1711 b))) else (if i < 1715 then (if i < 1714 then decide (1 ≤ count1713 b) else decide (2 ≤ count1713 b)) else (if i < 1716 then decide (3 ≤ count1713 b) else decide (4 ≤ count1713 b))))) else (if i < 1724 then (if i < 1720 then (if i < 1718 then decide (1 ≤ count1717 b) else (if i < 1719 then decide (2 ≤ count1717 b) else decide (1 ≤ count1719 b))) else (if i < 1722 then (if i < 1721 then decide (2 ≤ count1719 b) else decide (1 ≤ count1721 b)) else (if i < 1723 then decide (2 ≤ count1721 b) else decide (3 ≤ count1721 b)))) else (if i < 1727 then (if i < 1725 then decide (4 ≤ count1721 b) else (if i < 1726 then decide (1 ≤ count1725 b) else decide (2 ≤ count1725 b))) else (if i < 1729 then (if i < 1728 then decide (3 ≤ count1725 b) else decide (4 ≤ count1725 b)) else (if i < 1730 then decide (5 ≤ count1725 b) else decide (6 ≤ count1725 b)))))) else (if i < 1745 then (if i < 1738 then (if i < 1734 then (if i < 1732 then decide (7 ≤ count1725 b) else (if i < 1733 then decide (8 ≤ count1725 b) else decide (1 ≤ count1733 b))) else (if i < 1736 then (if i < 1735 then decide (2 ≤ count1733 b) else decide (1 ≤ count1735 b)) else (if i < 1737 then decide (2 ≤ count1735 b) else decide (1 ≤ count1737 b)))) else (if i < 1741 then (if i < 1739 then decide (2 ≤ count1737 b) else (if i < 1740 then decide (3 ≤ count1737 b) else decide (4 ≤ count1737 b))) else (if i < 1743 then (if i < 1742 then decide (1 ≤ count1741 b) else decide (2 ≤ count1741 b)) else (if i < 1744 then decide (1 ≤ count1743 b) else decide (2 ≤ count1743 b))))) else (if i < 1752 then (if i < 1748 then (if i < 1746 then decide (1 ≤ count1745 b) else (if i < 1747 then decide (2 ≤ count1745 b) else decide (3 ≤ count1745 b))) else (if i < 1750 then (if i < 1749 then decide (4 ≤ count1745 b) else decide (1 ≤ count1749 b)) else (if i < 1751 then decide (2 ≤ count1749 b) else decide (3 ≤ count1749 b)))) else (if i < 1756 then (if i < 1754 then (if i < 1753 then decide (4 ≤ count1749 b) else decide (5 ≤ count1749 b)) else (if i < 1755 then decide (6 ≤ count1749 b) else decide (7 ≤ count1749 b))) else (if i < 1758 then (if i < 1757 then decide (8 ≤ count1749 b) else decide (1 ≤ count1757 b)) else (if i < 1759 then decide (2 ≤ count1757 b) else decide (3 ≤ count1757 b))))))) else (if i < 1788 then (if i < 1774 then (if i < 1767 then (if i < 1763 then (if i < 1761 then decide (4 ≤ count1757 b) else (if i < 1762 then decide (5 ≤ count1757 b) else decide (6 ≤ count1757 b))) else (if i < 1765 then (if i < 1764 then decide (7 ≤ count1757 b) else decide (8 ≤ count1757 b)) else (if i < 1766 then decide (9 ≤ count1757 b) else decide (10 ≤ count1757 b)))) else (if i < 1770 then (if i < 1768 then decide (11 ≤ count1757 b) else (if i < 1769 then decide (12 ≤ count1757 b) else decide (13 ≤ count1757 b))) else (if i < 1772 then (if i < 1771 then decide (14 ≤ count1757 b) else decide (15 ≤ count1757 b)) else (if i < 1773 then decide (16 ≤ count1757 b) else decide (1 ≤ count1773 b))))) else (if i < 1781 then (if i < 1777 then (if i < 1775 then decide (2 ≤ count1773 b) else (if i < 1776 then decide (3 ≤ count1773 b) else decide (4 ≤ count1773 b))) else (if i < 1779 then (if i < 1778 then decide (5 ≤ count1773 b) else decide (6 ≤ count1773 b)) else (if i < 1780 then decide (7 ≤ count1773 b) else decide (8 ≤ count1773 b)))) else (if i < 1784 then (if i < 1782 then decide (9 ≤ count1773 b) else (if i < 1783 then decide (10 ≤ count1773 b) else decide (11 ≤ count1773 b))) else (if i < 1786 then (if i < 1785 then decide (12 ≤ count1773 b) else decide (13 ≤ count1773 b)) else (if i < 1787 then decide (14 ≤ count1773 b) else decide (15 ≤ count1773 b)))))) else (if i < 1802 then (if i < 1795 then (if i < 1791 then (if i < 1789 then decide (16 ≤ count1773 b) else (if i < 1790 then decide (17 ≤ count1773 b) else decide (18 ≤ count1773 b))) else (if i < 1793 then (if i < 1792 then decide (19 ≤ count1773 b) else decide (20 ≤ count1773 b)) else (if i < 1794 then decide (21 ≤ count1773 b) else decide (22 ≤ count1773 b)))) else (if i < 1798 then (if i < 1796 then decide (1 ≤ count1795 b) else (if i < 1797 then decide (2 ≤ count1795 b) else decide (3 ≤ count1795 b))) else (if i < 1800 then (if i < 1799 then decide (4 ≤ count1795 b) else decide (5 ≤ count1795 b)) else (if i < 1801 then decide (6 ≤ count1795 b) else decide (7 ≤ count1795 b))))) else (if i < 1809 then (if i < 1805 then (if i < 1803 then decide (8 ≤ count1795 b) else (if i < 1804 then decide (9 ≤ count1795 b) else decide (10 ≤ count1795 b))) else (if i < 1807 then (if i < 1806 then decide (11 ≤ count1795 b) else decide (12 ≤ count1795 b)) else (if i < 1808 then decide (13 ≤ count1795 b) else decide (14 ≤ count1795 b)))) else (if i < 1813 then (if i < 1811 then (if i < 1810 then decide (15 ≤ count1795 b) else decide (16 ≤ count1795 b)) else (if i < 1812 then decide (17 ≤ count1795 b) else decide (18 ≤ count1795 b))) else (if i < 1815 then (if i < 1814 then decide (19 ≤ count1795 b) else decide (20 ≤ count1795 b)) else (if i < 1816 then decide (21 ≤ count1795 b) else decide (22 ≤ count1795 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (3 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (5 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (7 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (9 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (10 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (11 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (13 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (14 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (16 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (18 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (19 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (22 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (28 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (29 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (30 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (64 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (65 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (66 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (68 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (70 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (72 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (73 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (76 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (78 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (79 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (83 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (84 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (85 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (87 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (88 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (90 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (91 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (95 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (129 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (130 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (132 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (134 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (136 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (137 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (138 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (139 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (140 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (143 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (145 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (148 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (149 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (150 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (151 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (152 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (153 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (154 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (155 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (159 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (193 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (194 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (195 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (197 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (198 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (199 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (200 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (201 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (203 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (204 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (205 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (206 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (207 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (208 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (209 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (210 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (211 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (214 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (216 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (218 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (220 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (221 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (222 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (259 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (264 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (266 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (282 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (323 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (325 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (327 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (330 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (331 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (332 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (333 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (384 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (386 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (387 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (389 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (391 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (394 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (395 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (396 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (397 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (400 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (401 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (402 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (403 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (406 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (412 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (413 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (414 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (448 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (449 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (450 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (452 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (454 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (456 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (457 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (462 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (463 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (467 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (468 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (469 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (471 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (472 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (474 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (475 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (477 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (479 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (3 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (5 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (7 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (9 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (16 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (30 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (64 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (65 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (68 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (70 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (72 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (78 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (83 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (85 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (87 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (88 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (90 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (91 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (129 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (136 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (143 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (145 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (150 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (153 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (154 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (194 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (195 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (197 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (198 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (201 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (203 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (204 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (206 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (208 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (209 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (210 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (216 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (282 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (323 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (325 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (330 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (331 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (387 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (389 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (394 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (395 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (396 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (400 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (402 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (448 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (449 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (450 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (452 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (454 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (456 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (457 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (463 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (467 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (468 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (469 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (471 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (BallClauseLogic.Endpoint q (474 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (BallClauseLogic.Endpoint q (477 : Vertex)) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (BallClauseLogic.Endpoint q (479 : Vertex)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value262 (q : Snake 81) : valuation q 262 = decide (2 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value264 (q : Snake 81) : valuation q 264 = decide (2 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value274 (q : Snake 81) : valuation q 274 = decide (2 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value276 (q : Snake 81) : valuation q 276 = decide (2 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value300 (q : Snake 81) : valuation q 300 = decide (2 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value310 (q : Snake 81) : valuation q 310 = decide (2 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value324 (q : Snake 81) : valuation q 324 = decide (2 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value330 (q : Snake 81) : valuation q 330 = decide (2 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value332 (q : Snake 81) : valuation q 332 = decide (2 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value334 (q : Snake 81) : valuation q 334 = decide (2 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value364 (q : Snake 81) : valuation q 364 = decide (2 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value366 (q : Snake 81) : valuation q 366 = decide (2 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value368 (q : Snake 81) : valuation q 368 = decide (2 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value380 (q : Snake 81) : valuation q 380 = decide (2 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value396 (q : Snake 81) : valuation q 396 = decide (2 ≤ count395 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value424 (q : Snake 81) : valuation q 424 = decide (2 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value426 (q : Snake 81) : valuation q 426 = decide (2 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value432 (q : Snake 81) : valuation q 432 = decide (2 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value440 (q : Snake 81) : valuation q 440 = decide (2 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value446 (q : Snake 81) : valuation q 446 = decide (2 ≤ count445 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value454 (q : Snake 81) : valuation q 454 = decide (2 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value456 (q : Snake 81) : valuation q 456 = decide (2 ≤ count455 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value468 (q : Snake 81) : valuation q 468 = decide (2 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value470 (q : Snake 81) : valuation q 470 = decide (2 ≤ count469 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value474 (q : Snake 81) : valuation q 474 = decide (2 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value476 (q : Snake 81) : valuation q 476 = decide (2 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value479 (q : Snake 81) : valuation q 479 = decide (1 ≤ count479 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value482 (q : Snake 81) : valuation q 482 = decide (2 ≤ count481 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value484 (q : Snake 81) : valuation q 484 = decide (2 ≤ count483 (baseVal q)) := rfl
theorem value485 (q : Snake 81) : valuation q 485 = decide (1 ≤ count485 (baseVal q)) := rfl
theorem value486 (q : Snake 81) : valuation q 486 = decide (2 ≤ count485 (baseVal q)) := rfl
theorem value487 (q : Snake 81) : valuation q 487 = decide (1 ≤ count487 (baseVal q)) := rfl
theorem value488 (q : Snake 81) : valuation q 488 = decide (2 ≤ count487 (baseVal q)) := rfl
theorem value489 (q : Snake 81) : valuation q 489 = decide (1 ≤ count489 (baseVal q)) := rfl
theorem value490 (q : Snake 81) : valuation q 490 = decide (2 ≤ count489 (baseVal q)) := rfl
theorem value492 (q : Snake 81) : valuation q 492 = decide (2 ≤ count491 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (1 ≤ count1505 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (2 ≤ count1505 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (1 ≤ count1507 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (2 ≤ count1507 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (3 ≤ count1507 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (1 ≤ count1510 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (2 ≤ count1510 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (1 ≤ count1512 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (2 ≤ count1512 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (1 ≤ count1514 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (2 ≤ count1514 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (3 ≤ count1514 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (1 ≤ count1518 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (2 ≤ count1518 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (3 ≤ count1518 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (4 ≤ count1518 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (5 ≤ count1518 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (1 ≤ count1525 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (2 ≤ count1525 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (1 ≤ count1527 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (2 ≤ count1527 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (1 ≤ count1529 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (2 ≤ count1529 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (3 ≤ count1529 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (4 ≤ count1529 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (1 ≤ count1533 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (2 ≤ count1533 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (1 ≤ count1535 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (2 ≤ count1535 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (1 ≤ count1537 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (2 ≤ count1537 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (3 ≤ count1537 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (4 ≤ count1537 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (1 ≤ count1541 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (2 ≤ count1541 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (3 ≤ count1541 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (4 ≤ count1541 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (5 ≤ count1541 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (6 ≤ count1541 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (7 ≤ count1541 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (3 ≤ count1549 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (4 ≤ count1549 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (5 ≤ count1549 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (6 ≤ count1549 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (7 ≤ count1549 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (8 ≤ count1549 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (9 ≤ count1549 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (1 ≤ count1566 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (2 ≤ count1566 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (1 ≤ count1568 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (2 ≤ count1568 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (3 ≤ count1568 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (4 ≤ count1568 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (1 ≤ count1572 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (2 ≤ count1572 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (1 ≤ count1574 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (2 ≤ count1574 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (1 ≤ count1576 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (2 ≤ count1576 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (3 ≤ count1576 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (4 ≤ count1576 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (1 ≤ count1580 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (3 ≤ count1580 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (4 ≤ count1580 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (5 ≤ count1580 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (6 ≤ count1580 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (7 ≤ count1580 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (1 ≤ count1588 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (2 ≤ count1588 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (1 ≤ count1590 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (2 ≤ count1590 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (1 ≤ count1592 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (2 ≤ count1592 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (3 ≤ count1592 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (4 ≤ count1592 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (1 ≤ count1596 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (2 ≤ count1596 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (1 ≤ count1598 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (2 ≤ count1598 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (1 ≤ count1600 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (2 ≤ count1600 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (3 ≤ count1600 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (4 ≤ count1600 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (1 ≤ count1604 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (2 ≤ count1604 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (3 ≤ count1604 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (4 ≤ count1604 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (5 ≤ count1604 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (6 ≤ count1604 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (7 ≤ count1604 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (2 ≤ count1612 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (3 ≤ count1612 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (4 ≤ count1612 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (5 ≤ count1612 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (6 ≤ count1612 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (7 ≤ count1612 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (8 ≤ count1612 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (9 ≤ count1612 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (10 ≤ count1612 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (6 ≤ count1628 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (7 ≤ count1628 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (8 ≤ count1628 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (9 ≤ count1628 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (10 ≤ count1628 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (11 ≤ count1628 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (12 ≤ count1628 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (13 ≤ count1628 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (14 ≤ count1628 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (15 ≤ count1628 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (1 ≤ count1650 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (2 ≤ count1650 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (1 ≤ count1652 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (2 ≤ count1652 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (3 ≤ count1652 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (1 ≤ count1655 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (2 ≤ count1655 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (1 ≤ count1657 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (2 ≤ count1657 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (1 ≤ count1659 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (2 ≤ count1659 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (3 ≤ count1659 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (4 ≤ count1659 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (1 ≤ count1663 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (2 ≤ count1663 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (3 ≤ count1663 (baseVal q)) := rfl
theorem value1666 (q : Snake 81) : valuation q 1666 = decide (4 ≤ count1663 (baseVal q)) := rfl
theorem value1667 (q : Snake 81) : valuation q 1667 = decide (5 ≤ count1663 (baseVal q)) := rfl
theorem value1668 (q : Snake 81) : valuation q 1668 = decide (6 ≤ count1663 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (7 ≤ count1663 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (1 ≤ count1670 (baseVal q)) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (2 ≤ count1670 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (1 ≤ count1672 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (2 ≤ count1672 (baseVal q)) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (1 ≤ count1674 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (2 ≤ count1674 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (3 ≤ count1674 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (4 ≤ count1674 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (1 ≤ count1678 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (2 ≤ count1678 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (1 ≤ count1680 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (2 ≤ count1680 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (1 ≤ count1682 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (2 ≤ count1682 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (3 ≤ count1682 (baseVal q)) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (4 ≤ count1682 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (1 ≤ count1686 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (2 ≤ count1686 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (3 ≤ count1686 (baseVal q)) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (4 ≤ count1686 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (5 ≤ count1686 (baseVal q)) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (6 ≤ count1686 (baseVal q)) := rfl
theorem value1692 (q : Snake 81) : valuation q 1692 = decide (7 ≤ count1686 (baseVal q)) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (2 ≤ count1694 (baseVal q)) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (3 ≤ count1694 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (4 ≤ count1694 (baseVal q)) := rfl
theorem value1698 (q : Snake 81) : valuation q 1698 = decide (5 ≤ count1694 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (6 ≤ count1694 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (7 ≤ count1694 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (8 ≤ count1694 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (9 ≤ count1694 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (10 ≤ count1694 (baseVal q)) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (11 ≤ count1694 (baseVal q)) := rfl
theorem value1705 (q : Snake 81) : valuation q 1705 = decide (12 ≤ count1694 (baseVal q)) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (13 ≤ count1694 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (14 ≤ count1694 (baseVal q)) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (1 ≤ count1709 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (2 ≤ count1709 (baseVal q)) := rfl
theorem value1711 (q : Snake 81) : valuation q 1711 = decide (1 ≤ count1711 (baseVal q)) := rfl
theorem value1712 (q : Snake 81) : valuation q 1712 = decide (2 ≤ count1711 (baseVal q)) := rfl
theorem value1713 (q : Snake 81) : valuation q 1713 = decide (1 ≤ count1713 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (2 ≤ count1713 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (3 ≤ count1713 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (4 ≤ count1713 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (1 ≤ count1717 (baseVal q)) := rfl
theorem value1718 (q : Snake 81) : valuation q 1718 = decide (2 ≤ count1717 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (1 ≤ count1719 (baseVal q)) := rfl
theorem value1720 (q : Snake 81) : valuation q 1720 = decide (2 ≤ count1719 (baseVal q)) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (1 ≤ count1721 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (2 ≤ count1721 (baseVal q)) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (3 ≤ count1721 (baseVal q)) := rfl
theorem value1724 (q : Snake 81) : valuation q 1724 = decide (4 ≤ count1721 (baseVal q)) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (1 ≤ count1725 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (2 ≤ count1725 (baseVal q)) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (3 ≤ count1725 (baseVal q)) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (4 ≤ count1725 (baseVal q)) := rfl
theorem value1729 (q : Snake 81) : valuation q 1729 = decide (5 ≤ count1725 (baseVal q)) := rfl
theorem value1730 (q : Snake 81) : valuation q 1730 = decide (6 ≤ count1725 (baseVal q)) := rfl
theorem value1733 (q : Snake 81) : valuation q 1733 = decide (1 ≤ count1733 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (2 ≤ count1733 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (1 ≤ count1735 (baseVal q)) := rfl
theorem value1736 (q : Snake 81) : valuation q 1736 = decide (2 ≤ count1735 (baseVal q)) := rfl
theorem value1737 (q : Snake 81) : valuation q 1737 = decide (1 ≤ count1737 (baseVal q)) := rfl
theorem value1738 (q : Snake 81) : valuation q 1738 = decide (2 ≤ count1737 (baseVal q)) := rfl
theorem value1739 (q : Snake 81) : valuation q 1739 = decide (3 ≤ count1737 (baseVal q)) := rfl
theorem value1740 (q : Snake 81) : valuation q 1740 = decide (4 ≤ count1737 (baseVal q)) := rfl
theorem value1741 (q : Snake 81) : valuation q 1741 = decide (1 ≤ count1741 (baseVal q)) := rfl
theorem value1742 (q : Snake 81) : valuation q 1742 = decide (2 ≤ count1741 (baseVal q)) := rfl
theorem value1743 (q : Snake 81) : valuation q 1743 = decide (1 ≤ count1743 (baseVal q)) := rfl
theorem value1744 (q : Snake 81) : valuation q 1744 = decide (2 ≤ count1743 (baseVal q)) := rfl
theorem value1745 (q : Snake 81) : valuation q 1745 = decide (1 ≤ count1745 (baseVal q)) := rfl
theorem value1746 (q : Snake 81) : valuation q 1746 = decide (2 ≤ count1745 (baseVal q)) := rfl
theorem value1747 (q : Snake 81) : valuation q 1747 = decide (3 ≤ count1745 (baseVal q)) := rfl
theorem value1749 (q : Snake 81) : valuation q 1749 = decide (1 ≤ count1749 (baseVal q)) := rfl
theorem value1750 (q : Snake 81) : valuation q 1750 = decide (2 ≤ count1749 (baseVal q)) := rfl
theorem value1751 (q : Snake 81) : valuation q 1751 = decide (3 ≤ count1749 (baseVal q)) := rfl
theorem value1752 (q : Snake 81) : valuation q 1752 = decide (4 ≤ count1749 (baseVal q)) := rfl
theorem value1753 (q : Snake 81) : valuation q 1753 = decide (5 ≤ count1749 (baseVal q)) := rfl
theorem value1757 (q : Snake 81) : valuation q 1757 = decide (1 ≤ count1757 (baseVal q)) := rfl
theorem value1758 (q : Snake 81) : valuation q 1758 = decide (2 ≤ count1757 (baseVal q)) := rfl
theorem value1759 (q : Snake 81) : valuation q 1759 = decide (3 ≤ count1757 (baseVal q)) := rfl
theorem value1760 (q : Snake 81) : valuation q 1760 = decide (4 ≤ count1757 (baseVal q)) := rfl
theorem value1761 (q : Snake 81) : valuation q 1761 = decide (5 ≤ count1757 (baseVal q)) := rfl
theorem value1762 (q : Snake 81) : valuation q 1762 = decide (6 ≤ count1757 (baseVal q)) := rfl
theorem value1763 (q : Snake 81) : valuation q 1763 = decide (7 ≤ count1757 (baseVal q)) := rfl
theorem value1764 (q : Snake 81) : valuation q 1764 = decide (8 ≤ count1757 (baseVal q)) := rfl
theorem value1765 (q : Snake 81) : valuation q 1765 = decide (9 ≤ count1757 (baseVal q)) := rfl
theorem value1779 (q : Snake 81) : valuation q 1779 = decide (7 ≤ count1773 (baseVal q)) := rfl
theorem value1780 (q : Snake 81) : valuation q 1780 = decide (8 ≤ count1773 (baseVal q)) := rfl
theorem value1781 (q : Snake 81) : valuation q 1781 = decide (9 ≤ count1773 (baseVal q)) := rfl
theorem value1782 (q : Snake 81) : valuation q 1782 = decide (10 ≤ count1773 (baseVal q)) := rfl
theorem value1783 (q : Snake 81) : valuation q 1783 = decide (11 ≤ count1773 (baseVal q)) := rfl
theorem value1784 (q : Snake 81) : valuation q 1784 = decide (12 ≤ count1773 (baseVal q)) := rfl
theorem value1785 (q : Snake 81) : valuation q 1785 = decide (13 ≤ count1773 (baseVal q)) := rfl
theorem value1786 (q : Snake 81) : valuation q 1786 = decide (14 ≤ count1773 (baseVal q)) := rfl
theorem value1787 (q : Snake 81) : valuation q 1787 = decide (15 ≤ count1773 (baseVal q)) := rfl
theorem value1788 (q : Snake 81) : valuation q 1788 = decide (16 ≤ count1773 (baseVal q)) := rfl
theorem value1816 (q : Snake 81) : valuation q 1816 = decide (22 ≤ count1795 (baseVal q)) := rfl
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
theorem meaningNeg117 (b : Nat → Bool) : literal (valuationOf b) (-117) = decide (1 ≤ countLit b [-117]) := by
  change literal b (-117) = decide (1 ≤ countLit b [-117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-117) <;> decide
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
theorem meaningNeg111 (b : Nat → Bool) : literal (valuationOf b) (-111) = decide (1 ≤ countLit b [-111]) := by
  change literal b (-111) = decide (1 ≤ countLit b [-111])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-111) <;> decide
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
theorem meaningNeg54 (b : Nat → Bool) : literal (valuationOf b) (-54) = decide (1 ≤ countLit b [-54]) := by
  change literal b (-54) = decide (1 ≤ countLit b [-54])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-54) <;> decide
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
theorem meaningNeg39 (b : Nat → Bool) : literal (valuationOf b) (-39) = decide (1 ≤ countLit b [-39]) := by
  change literal b (-39) = decide (1 ≤ countLit b [-39])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-39) <;> decide
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
theorem meaningNeg24 (b : Nat → Bool) : literal (valuationOf b) (-24) = decide (1 ≤ countLit b [-24]) := by
  change literal b (-24) = decide (1 ≤ countLit b [-24])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-24) <;> decide
theorem meaningNeg22 (b : Nat → Bool) : literal (valuationOf b) (-22) = decide (1 ≤ countLit b [-22]) := by
  change literal b (-22) = decide (1 ≤ countLit b [-22])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-22) <;> decide
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
theorem meaning126 (b : Nat → Bool) : literal (valuationOf b) (126) = decide (1 ≤ countLit b [126]) := by
  change literal b (126) = decide (1 ≤ countLit b [126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (126) <;> decide
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
theorem meaning134 (b : Nat → Bool) : literal (valuationOf b) (134) = decide (1 ≤ countLit b [134]) := by
  change literal b (134) = decide (1 ≤ countLit b [134])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (134) <;> decide
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
theorem meaning153 (b : Nat → Bool) : literal (valuationOf b) (153) = decide (1 ≤ countLit b [153]) := by
  change literal b (153) = decide (1 ≤ countLit b [153])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (153) <;> decide
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
theorem meaning158 (b : Nat → Bool) : literal (valuationOf b) (158) = decide (1 ≤ countLit b [158]) := by
  change literal b (158) = decide (1 ≤ countLit b [158])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (158) <;> decide
theorem meaning163 (b : Nat → Bool) : literal (valuationOf b) (163) = decide (1 ≤ countLit b [163]) := by
  change literal b (163) = decide (1 ≤ countLit b [163])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (163) <;> decide
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
theorem meaning170 (b : Nat → Bool) : literal (valuationOf b) (170) = decide (1 ≤ countLit b [170]) := by
  change literal b (170) = decide (1 ≤ countLit b [170])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (170) <;> decide
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
theorem meaning175 (b : Nat → Bool) : literal (valuationOf b) (175) = decide (1 ≤ countLit b [175]) := by
  change literal b (175) = decide (1 ≤ countLit b [175])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (175) <;> decide
theorem meaning178 (b : Nat → Bool) : literal (valuationOf b) (178) = decide (1 ≤ countLit b [178]) := by
  change literal b (178) = decide (1 ≤ countLit b [178])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (178) <;> decide
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
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
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
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) (215) = decide (1 ≤ countLit b [215]) := by
  change literal b (215) = decide (1 ≤ countLit b [215])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (215) <;> decide
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
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) (231) = decide (1 ≤ countLit b [231]) := by
  change literal b (231) = decide (1 ≤ countLit b [231])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (231) <;> decide
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
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning262 (b : Nat → Bool) : literal (valuationOf b) 262 = decide (2 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning264 (b : Nat → Bool) : literal (valuationOf b) 264 = decide (2 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning274 (b : Nat → Bool) : literal (valuationOf b) 274 = decide (2 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning276 (b : Nat → Bool) : literal (valuationOf b) 276 = decide (2 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning300 (b : Nat → Bool) : literal (valuationOf b) 300 = decide (2 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning302 (b : Nat → Bool) : literal (valuationOf b) 302 = decide (2 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning310 (b : Nat → Bool) : literal (valuationOf b) 310 = decide (2 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning324 (b : Nat → Bool) : literal (valuationOf b) 324 = decide (2 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning330 (b : Nat → Bool) : literal (valuationOf b) 330 = decide (2 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning332 (b : Nat → Bool) : literal (valuationOf b) 332 = decide (2 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning334 (b : Nat → Bool) : literal (valuationOf b) 334 = decide (2 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning364 (b : Nat → Bool) : literal (valuationOf b) 364 = decide (2 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning366 (b : Nat → Bool) : literal (valuationOf b) 366 = decide (2 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning368 (b : Nat → Bool) : literal (valuationOf b) 368 = decide (2 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning380 (b : Nat → Bool) : literal (valuationOf b) 380 = decide (2 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning396 (b : Nat → Bool) : literal (valuationOf b) 396 = decide (2 ≤ count395 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning424 (b : Nat → Bool) : literal (valuationOf b) 424 = decide (2 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning426 (b : Nat → Bool) : literal (valuationOf b) 426 = decide (2 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning432 (b : Nat → Bool) : literal (valuationOf b) 432 = decide (2 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning440 (b : Nat → Bool) : literal (valuationOf b) 440 = decide (2 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning446 (b : Nat → Bool) : literal (valuationOf b) 446 = decide (2 ≤ count445 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning454 (b : Nat → Bool) : literal (valuationOf b) 454 = decide (2 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning456 (b : Nat → Bool) : literal (valuationOf b) 456 = decide (2 ≤ count455 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning468 (b : Nat → Bool) : literal (valuationOf b) 468 = decide (2 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning470 (b : Nat → Bool) : literal (valuationOf b) 470 = decide (2 ≤ count469 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning474 (b : Nat → Bool) : literal (valuationOf b) 474 = decide (2 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning476 (b : Nat → Bool) : literal (valuationOf b) 476 = decide (2 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning479 (b : Nat → Bool) : literal (valuationOf b) 479 = decide (1 ≤ count479 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning482 (b : Nat → Bool) : literal (valuationOf b) 482 = decide (2 ≤ count481 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning484 (b : Nat → Bool) : literal (valuationOf b) 484 = decide (2 ≤ count483 b) := rfl
theorem meaning485 (b : Nat → Bool) : literal (valuationOf b) 485 = decide (1 ≤ count485 b) := rfl
theorem meaning486 (b : Nat → Bool) : literal (valuationOf b) 486 = decide (2 ≤ count485 b) := rfl
theorem meaning487 (b : Nat → Bool) : literal (valuationOf b) 487 = decide (1 ≤ count487 b) := rfl
theorem meaning488 (b : Nat → Bool) : literal (valuationOf b) 488 = decide (2 ≤ count487 b) := rfl
theorem meaning489 (b : Nat → Bool) : literal (valuationOf b) 489 = decide (1 ≤ count489 b) := rfl
theorem meaning490 (b : Nat → Bool) : literal (valuationOf b) 490 = decide (2 ≤ count489 b) := rfl
theorem meaning492 (b : Nat → Bool) : literal (valuationOf b) 492 = decide (2 ≤ count491 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (1 ≤ count1505 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (2 ≤ count1505 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (1 ≤ count1507 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (2 ≤ count1507 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (3 ≤ count1507 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (1 ≤ count1510 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (2 ≤ count1510 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (1 ≤ count1512 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (2 ≤ count1512 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (1 ≤ count1514 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (2 ≤ count1514 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (3 ≤ count1514 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (1 ≤ count1518 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (2 ≤ count1518 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (3 ≤ count1518 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (4 ≤ count1518 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (5 ≤ count1518 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (1 ≤ count1525 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (2 ≤ count1525 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (1 ≤ count1527 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (2 ≤ count1527 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (1 ≤ count1529 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (2 ≤ count1529 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (3 ≤ count1529 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (4 ≤ count1529 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (1 ≤ count1533 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (2 ≤ count1533 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (1 ≤ count1535 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (2 ≤ count1535 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (1 ≤ count1537 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (2 ≤ count1537 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (3 ≤ count1537 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (4 ≤ count1537 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (1 ≤ count1541 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (2 ≤ count1541 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (3 ≤ count1541 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (4 ≤ count1541 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (5 ≤ count1541 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (6 ≤ count1541 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (7 ≤ count1541 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (3 ≤ count1549 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (4 ≤ count1549 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (5 ≤ count1549 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (6 ≤ count1549 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (7 ≤ count1549 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (8 ≤ count1549 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (9 ≤ count1549 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (1 ≤ count1566 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (2 ≤ count1566 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (1 ≤ count1568 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (2 ≤ count1568 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (3 ≤ count1568 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (4 ≤ count1568 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (1 ≤ count1572 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (2 ≤ count1572 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (1 ≤ count1574 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (2 ≤ count1574 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (1 ≤ count1576 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (2 ≤ count1576 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (3 ≤ count1576 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (4 ≤ count1576 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (1 ≤ count1580 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (3 ≤ count1580 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (4 ≤ count1580 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (5 ≤ count1580 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (6 ≤ count1580 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (7 ≤ count1580 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (1 ≤ count1588 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (2 ≤ count1588 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (1 ≤ count1590 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (2 ≤ count1590 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (1 ≤ count1592 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (2 ≤ count1592 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (3 ≤ count1592 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (4 ≤ count1592 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (1 ≤ count1596 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (2 ≤ count1596 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (1 ≤ count1598 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (2 ≤ count1598 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (1 ≤ count1600 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (2 ≤ count1600 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (3 ≤ count1600 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (4 ≤ count1600 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (1 ≤ count1604 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (2 ≤ count1604 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (3 ≤ count1604 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (4 ≤ count1604 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (5 ≤ count1604 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (6 ≤ count1604 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (7 ≤ count1604 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (2 ≤ count1612 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (3 ≤ count1612 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (4 ≤ count1612 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (5 ≤ count1612 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (6 ≤ count1612 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (7 ≤ count1612 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (8 ≤ count1612 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (9 ≤ count1612 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (10 ≤ count1612 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (6 ≤ count1628 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (7 ≤ count1628 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (8 ≤ count1628 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (9 ≤ count1628 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (10 ≤ count1628 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (11 ≤ count1628 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (12 ≤ count1628 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (13 ≤ count1628 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (14 ≤ count1628 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (15 ≤ count1628 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (1 ≤ count1650 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (2 ≤ count1650 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (1 ≤ count1652 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (2 ≤ count1652 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (3 ≤ count1652 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (1 ≤ count1655 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (2 ≤ count1655 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (1 ≤ count1657 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (2 ≤ count1657 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (1 ≤ count1659 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (2 ≤ count1659 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (3 ≤ count1659 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (4 ≤ count1659 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (1 ≤ count1663 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (2 ≤ count1663 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (3 ≤ count1663 b) := rfl
theorem meaning1666 (b : Nat → Bool) : literal (valuationOf b) 1666 = decide (4 ≤ count1663 b) := rfl
theorem meaning1667 (b : Nat → Bool) : literal (valuationOf b) 1667 = decide (5 ≤ count1663 b) := rfl
theorem meaning1668 (b : Nat → Bool) : literal (valuationOf b) 1668 = decide (6 ≤ count1663 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (7 ≤ count1663 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (1 ≤ count1670 b) := rfl
theorem meaning1671 (b : Nat → Bool) : literal (valuationOf b) 1671 = decide (2 ≤ count1670 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (1 ≤ count1672 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (2 ≤ count1672 b) := rfl
theorem meaning1674 (b : Nat → Bool) : literal (valuationOf b) 1674 = decide (1 ≤ count1674 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (2 ≤ count1674 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (3 ≤ count1674 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (4 ≤ count1674 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (1 ≤ count1678 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (2 ≤ count1678 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (1 ≤ count1680 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (2 ≤ count1680 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (1 ≤ count1682 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (2 ≤ count1682 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (3 ≤ count1682 b) := rfl
theorem meaning1685 (b : Nat → Bool) : literal (valuationOf b) 1685 = decide (4 ≤ count1682 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (1 ≤ count1686 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (2 ≤ count1686 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (3 ≤ count1686 b) := rfl
theorem meaning1689 (b : Nat → Bool) : literal (valuationOf b) 1689 = decide (4 ≤ count1686 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (5 ≤ count1686 b) := rfl
theorem meaning1691 (b : Nat → Bool) : literal (valuationOf b) 1691 = decide (6 ≤ count1686 b) := rfl
theorem meaning1692 (b : Nat → Bool) : literal (valuationOf b) 1692 = decide (7 ≤ count1686 b) := rfl
theorem meaning1695 (b : Nat → Bool) : literal (valuationOf b) 1695 = decide (2 ≤ count1694 b) := rfl
theorem meaning1696 (b : Nat → Bool) : literal (valuationOf b) 1696 = decide (3 ≤ count1694 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (4 ≤ count1694 b) := rfl
theorem meaning1698 (b : Nat → Bool) : literal (valuationOf b) 1698 = decide (5 ≤ count1694 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (6 ≤ count1694 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (7 ≤ count1694 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (8 ≤ count1694 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (9 ≤ count1694 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (10 ≤ count1694 b) := rfl
theorem meaning1704 (b : Nat → Bool) : literal (valuationOf b) 1704 = decide (11 ≤ count1694 b) := rfl
theorem meaning1705 (b : Nat → Bool) : literal (valuationOf b) 1705 = decide (12 ≤ count1694 b) := rfl
theorem meaning1706 (b : Nat → Bool) : literal (valuationOf b) 1706 = decide (13 ≤ count1694 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (14 ≤ count1694 b) := rfl
theorem meaning1709 (b : Nat → Bool) : literal (valuationOf b) 1709 = decide (1 ≤ count1709 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (2 ≤ count1709 b) := rfl
theorem meaning1711 (b : Nat → Bool) : literal (valuationOf b) 1711 = decide (1 ≤ count1711 b) := rfl
theorem meaning1712 (b : Nat → Bool) : literal (valuationOf b) 1712 = decide (2 ≤ count1711 b) := rfl
theorem meaning1713 (b : Nat → Bool) : literal (valuationOf b) 1713 = decide (1 ≤ count1713 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (2 ≤ count1713 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (3 ≤ count1713 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (4 ≤ count1713 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (1 ≤ count1717 b) := rfl
theorem meaning1718 (b : Nat → Bool) : literal (valuationOf b) 1718 = decide (2 ≤ count1717 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (1 ≤ count1719 b) := rfl
theorem meaning1720 (b : Nat → Bool) : literal (valuationOf b) 1720 = decide (2 ≤ count1719 b) := rfl
theorem meaning1721 (b : Nat → Bool) : literal (valuationOf b) 1721 = decide (1 ≤ count1721 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (2 ≤ count1721 b) := rfl
theorem meaning1723 (b : Nat → Bool) : literal (valuationOf b) 1723 = decide (3 ≤ count1721 b) := rfl
theorem meaning1724 (b : Nat → Bool) : literal (valuationOf b) 1724 = decide (4 ≤ count1721 b) := rfl
theorem meaning1725 (b : Nat → Bool) : literal (valuationOf b) 1725 = decide (1 ≤ count1725 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (2 ≤ count1725 b) := rfl
theorem meaning1727 (b : Nat → Bool) : literal (valuationOf b) 1727 = decide (3 ≤ count1725 b) := rfl
theorem meaning1728 (b : Nat → Bool) : literal (valuationOf b) 1728 = decide (4 ≤ count1725 b) := rfl
theorem meaning1729 (b : Nat → Bool) : literal (valuationOf b) 1729 = decide (5 ≤ count1725 b) := rfl
theorem meaning1730 (b : Nat → Bool) : literal (valuationOf b) 1730 = decide (6 ≤ count1725 b) := rfl
theorem meaning1733 (b : Nat → Bool) : literal (valuationOf b) 1733 = decide (1 ≤ count1733 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (2 ≤ count1733 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (1 ≤ count1735 b) := rfl
theorem meaning1736 (b : Nat → Bool) : literal (valuationOf b) 1736 = decide (2 ≤ count1735 b) := rfl
theorem meaning1737 (b : Nat → Bool) : literal (valuationOf b) 1737 = decide (1 ≤ count1737 b) := rfl
theorem meaning1738 (b : Nat → Bool) : literal (valuationOf b) 1738 = decide (2 ≤ count1737 b) := rfl
theorem meaning1739 (b : Nat → Bool) : literal (valuationOf b) 1739 = decide (3 ≤ count1737 b) := rfl
theorem meaning1740 (b : Nat → Bool) : literal (valuationOf b) 1740 = decide (4 ≤ count1737 b) := rfl
theorem meaning1741 (b : Nat → Bool) : literal (valuationOf b) 1741 = decide (1 ≤ count1741 b) := rfl
theorem meaning1742 (b : Nat → Bool) : literal (valuationOf b) 1742 = decide (2 ≤ count1741 b) := rfl
theorem meaning1743 (b : Nat → Bool) : literal (valuationOf b) 1743 = decide (1 ≤ count1743 b) := rfl
theorem meaning1744 (b : Nat → Bool) : literal (valuationOf b) 1744 = decide (2 ≤ count1743 b) := rfl
theorem meaning1745 (b : Nat → Bool) : literal (valuationOf b) 1745 = decide (1 ≤ count1745 b) := rfl
theorem meaning1746 (b : Nat → Bool) : literal (valuationOf b) 1746 = decide (2 ≤ count1745 b) := rfl
theorem meaning1747 (b : Nat → Bool) : literal (valuationOf b) 1747 = decide (3 ≤ count1745 b) := rfl
theorem meaning1749 (b : Nat → Bool) : literal (valuationOf b) 1749 = decide (1 ≤ count1749 b) := rfl
theorem meaning1750 (b : Nat → Bool) : literal (valuationOf b) 1750 = decide (2 ≤ count1749 b) := rfl
theorem meaning1751 (b : Nat → Bool) : literal (valuationOf b) 1751 = decide (3 ≤ count1749 b) := rfl
theorem meaning1752 (b : Nat → Bool) : literal (valuationOf b) 1752 = decide (4 ≤ count1749 b) := rfl
theorem meaning1753 (b : Nat → Bool) : literal (valuationOf b) 1753 = decide (5 ≤ count1749 b) := rfl
theorem meaning1757 (b : Nat → Bool) : literal (valuationOf b) 1757 = decide (1 ≤ count1757 b) := rfl
theorem meaning1758 (b : Nat → Bool) : literal (valuationOf b) 1758 = decide (2 ≤ count1757 b) := rfl
theorem meaning1759 (b : Nat → Bool) : literal (valuationOf b) 1759 = decide (3 ≤ count1757 b) := rfl
theorem meaning1760 (b : Nat → Bool) : literal (valuationOf b) 1760 = decide (4 ≤ count1757 b) := rfl
theorem meaning1761 (b : Nat → Bool) : literal (valuationOf b) 1761 = decide (5 ≤ count1757 b) := rfl
theorem meaning1762 (b : Nat → Bool) : literal (valuationOf b) 1762 = decide (6 ≤ count1757 b) := rfl
theorem meaning1763 (b : Nat → Bool) : literal (valuationOf b) 1763 = decide (7 ≤ count1757 b) := rfl
theorem meaning1764 (b : Nat → Bool) : literal (valuationOf b) 1764 = decide (8 ≤ count1757 b) := rfl
theorem meaning1765 (b : Nat → Bool) : literal (valuationOf b) 1765 = decide (9 ≤ count1757 b) := rfl
theorem meaning1779 (b : Nat → Bool) : literal (valuationOf b) 1779 = decide (7 ≤ count1773 b) := rfl
theorem meaning1780 (b : Nat → Bool) : literal (valuationOf b) 1780 = decide (8 ≤ count1773 b) := rfl
theorem meaning1781 (b : Nat → Bool) : literal (valuationOf b) 1781 = decide (9 ≤ count1773 b) := rfl
theorem meaning1782 (b : Nat → Bool) : literal (valuationOf b) 1782 = decide (10 ≤ count1773 b) := rfl
theorem meaning1783 (b : Nat → Bool) : literal (valuationOf b) 1783 = decide (11 ≤ count1773 b) := rfl
theorem meaning1784 (b : Nat → Bool) : literal (valuationOf b) 1784 = decide (12 ≤ count1773 b) := rfl
theorem meaning1785 (b : Nat → Bool) : literal (valuationOf b) 1785 = decide (13 ≤ count1773 b) := rfl
theorem meaning1786 (b : Nat → Bool) : literal (valuationOf b) 1786 = decide (14 ≤ count1773 b) := rfl
theorem meaning1787 (b : Nat → Bool) : literal (valuationOf b) 1787 = decide (15 ≤ count1773 b) := rfl
theorem meaning1788 (b : Nat → Bool) : literal (valuationOf b) 1788 = decide (16 ≤ count1773 b) := rfl
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
end Snake9.Regrowth.E112089
