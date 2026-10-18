import E112187Data
namespace Snake9.Regrowth.E112187
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 119 then (if i < 59 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (6 : Vertex)) else decide (InPath q (7 : Vertex))) else (if i < 6 then decide (InPath q (9 : Vertex)) else decide (InPath q (13 : Vertex))))) else (if i < 10 then (if i < 8 then decide (InPath q (15 : Vertex)) else (if i < 9 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex)))) else (if i < 12 then (if i < 11 then decide (InPath q (19 : Vertex)) else decide (InPath q (22 : Vertex))) else (if i < 13 then decide (InPath q (26 : Vertex)) else decide (InPath q (28 : Vertex)))))) else (if i < 21 then (if i < 17 then (if i < 15 then decide (InPath q (29 : Vertex)) else (if i < 16 then decide (InPath q (30 : Vertex)) else decide (InPath q (66 : Vertex)))) else (if i < 19 then (if i < 18 then decide (InPath q (70 : Vertex)) else decide (InPath q (78 : Vertex))) else (if i < 20 then decide (InPath q (102 : Vertex)) else decide (InPath q (105 : Vertex))))) else (if i < 25 then (if i < 23 then (if i < 22 then decide (InPath q (109 : Vertex)) else decide (InPath q (111 : Vertex))) else (if i < 24 then decide (InPath q (118 : Vertex)) else decide (InPath q (122 : Vertex)))) else (if i < 27 then (if i < 26 then decide (InPath q (124 : Vertex)) else decide (InPath q (125 : Vertex))) else (if i < 28 then decide (InPath q (126 : Vertex)) else decide (InPath q (160 : Vertex))))))) else (if i < 44 then (if i < 36 then (if i < 32 then (if i < 30 then decide (InPath q (161 : Vertex)) else (if i < 31 then decide (InPath q (166 : Vertex)) else decide (InPath q (167 : Vertex)))) else (if i < 34 then (if i < 33 then decide (InPath q (168 : Vertex)) else decide (InPath q (169 : Vertex))) else (if i < 35 then decide (InPath q (171 : Vertex)) else decide (InPath q (173 : Vertex))))) else (if i < 40 then (if i < 38 then (if i < 37 then decide (InPath q (175 : Vertex)) else decide (InPath q (177 : Vertex))) else (if i < 39 then decide (InPath q (178 : Vertex)) else decide (InPath q (179 : Vertex)))) else (if i < 42 then (if i < 41 then decide (InPath q (182 : Vertex)) else decide (InPath q (186 : Vertex))) else (if i < 43 then decide (InPath q (188 : Vertex)) else decide (InPath q (189 : Vertex)))))) else (if i < 51 then (if i < 47 then (if i < 45 then decide (InPath q (190 : Vertex)) else (if i < 46 then decide (InPath q (288 : Vertex)) else decide (InPath q (289 : Vertex)))) else (if i < 49 then (if i < 48 then decide (InPath q (294 : Vertex)) else decide (InPath q (295 : Vertex))) else (if i < 50 then decide (InPath q (296 : Vertex)) else decide (InPath q (297 : Vertex))))) else (if i < 55 then (if i < 53 then (if i < 52 then decide (InPath q (299 : Vertex)) else decide (InPath q (301 : Vertex))) else (if i < 54 then decide (InPath q (303 : Vertex)) else decide (InPath q (305 : Vertex)))) else (if i < 57 then (if i < 56 then decide (InPath q (306 : Vertex)) else decide (InPath q (307 : Vertex))) else (if i < 58 then decide (InPath q (308 : Vertex)) else decide (InPath q (310 : Vertex)))))))) else (if i < 89 then (if i < 74 then (if i < 66 then (if i < 62 then (if i < 60 then decide (InPath q (314 : Vertex)) else (if i < 61 then decide (InPath q (316 : Vertex)) else decide (InPath q (317 : Vertex)))) else (if i < 64 then (if i < 63 then decide (InPath q (318 : Vertex)) else decide (InPath q (354 : Vertex))) else (if i < 65 then decide (InPath q (356 : Vertex)) else decide (InPath q (357 : Vertex))))) else (if i < 70 then (if i < 68 then (if i < 67 then decide (InPath q (358 : Vertex)) else decide (InPath q (359 : Vertex))) else (if i < 69 then decide (InPath q (361 : Vertex)) else decide (InPath q (362 : Vertex)))) else (if i < 72 then (if i < 71 then decide (InPath q (364 : Vertex)) else decide (InPath q (366 : Vertex))) else (if i < 73 then decide (InPath q (372 : Vertex)) else decide (InPath q (373 : Vertex)))))) else (if i < 81 then (if i < 77 then (if i < 75 then decide (InPath q (375 : Vertex)) else (if i < 76 then decide (InPath q (376 : Vertex)) else decide (InPath q (377 : Vertex)))) else (if i < 79 then (if i < 78 then decide (InPath q (378 : Vertex)) else decide (InPath q (379 : Vertex))) else (if i < 80 then decide (InPath q (383 : Vertex)) else decide (InPath q (416 : Vertex))))) else (if i < 85 then (if i < 83 then (if i < 82 then decide (InPath q (417 : Vertex)) else decide (InPath q (418 : Vertex))) else (if i < 84 then decide (InPath q (420 : Vertex)) else decide (InPath q (421 : Vertex)))) else (if i < 87 then (if i < 86 then decide (InPath q (422 : Vertex)) else decide (InPath q (423 : Vertex))) else (if i < 88 then decide (InPath q (424 : Vertex)) else decide (InPath q (426 : Vertex))))))) else (if i < 104 then (if i < 96 then (if i < 92 then (if i < 90 then decide (InPath q (427 : Vertex)) else (if i < 91 then decide (InPath q (428 : Vertex)) else decide (InPath q (430 : Vertex)))) else (if i < 94 then (if i < 93 then decide (InPath q (431 : Vertex)) else decide (InPath q (433 : Vertex))) else (if i < 95 then decide (InPath q (435 : Vertex)) else decide (InPath q (436 : Vertex))))) else (if i < 100 then (if i < 98 then (if i < 97 then decide (InPath q (437 : Vertex)) else decide (InPath q (439 : Vertex))) else (if i < 99 then decide (InPath q (440 : Vertex)) else decide (InPath q (441 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (442 : Vertex)) else decide (InPath q (443 : Vertex))) else (if i < 103 then decide (InPath q (447 : Vertex)) else decide (InPath q (480 : Vertex)))))) else (if i < 111 then (if i < 107 then (if i < 105 then decide (InPath q (481 : Vertex)) else (if i < 106 then decide (InPath q (485 : Vertex)) else decide (InPath q (486 : Vertex)))) else (if i < 109 then (if i < 108 then decide (InPath q (488 : Vertex)) else decide (InPath q (491 : Vertex))) else (if i < 110 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))))) else (if i < 115 then (if i < 113 then (if i < 112 then decide (InPath q (496 : Vertex)) else decide (InPath q (497 : Vertex))) else (if i < 114 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex)))) else (if i < 117 then (if i < 116 then decide (InPath q (502 : Vertex)) else decide (InPath q (504 : Vertex))) else (if i < 118 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 179 then (if i < 149 then (if i < 134 then (if i < 126 then (if i < 122 then (if i < 120 then decide (InPath q (510 : Vertex)) else (if i < 121 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 124 then (if i < 123 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else decide (BallClauseLogic.Endpoint q (7 : Vertex))) else (if i < 125 then decide (BallClauseLogic.Endpoint q (9 : Vertex)) else decide (BallClauseLogic.Endpoint q (13 : Vertex))))) else (if i < 130 then (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (15 : Vertex)) else decide (BallClauseLogic.Endpoint q (17 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (18 : Vertex)) else decide (BallClauseLogic.Endpoint q (19 : Vertex)))) else (if i < 132 then (if i < 131 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (26 : Vertex))) else (if i < 133 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex)))))) else (if i < 141 then (if i < 137 then (if i < 135 then decide (BallClauseLogic.Endpoint q (30 : Vertex)) else (if i < 136 then decide (BallClauseLogic.Endpoint q (66 : Vertex)) else decide (BallClauseLogic.Endpoint q (70 : Vertex)))) else (if i < 139 then (if i < 138 then decide (BallClauseLogic.Endpoint q (78 : Vertex)) else decide (BallClauseLogic.Endpoint q (102 : Vertex))) else (if i < 140 then decide (BallClauseLogic.Endpoint q (105 : Vertex)) else decide (BallClauseLogic.Endpoint q (109 : Vertex))))) else (if i < 145 then (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (111 : Vertex)) else decide (BallClauseLogic.Endpoint q (118 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (122 : Vertex)) else decide (BallClauseLogic.Endpoint q (124 : Vertex)))) else (if i < 147 then (if i < 146 then decide (BallClauseLogic.Endpoint q (125 : Vertex)) else decide (BallClauseLogic.Endpoint q (126 : Vertex))) else (if i < 148 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (161 : Vertex))))))) else (if i < 164 then (if i < 156 then (if i < 152 then (if i < 150 then decide (BallClauseLogic.Endpoint q (166 : Vertex)) else (if i < 151 then decide (BallClauseLogic.Endpoint q (167 : Vertex)) else decide (BallClauseLogic.Endpoint q (168 : Vertex)))) else (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (169 : Vertex)) else decide (BallClauseLogic.Endpoint q (171 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (173 : Vertex)) else decide (BallClauseLogic.Endpoint q (175 : Vertex))))) else (if i < 160 then (if i < 158 then (if i < 157 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else decide (BallClauseLogic.Endpoint q (178 : Vertex))) else (if i < 159 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex)))) else (if i < 162 then (if i < 161 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (188 : Vertex))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (190 : Vertex)))))) else (if i < 171 then (if i < 167 then (if i < 165 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else (if i < 166 then decide (BallClauseLogic.Endpoint q (289 : Vertex)) else decide (BallClauseLogic.Endpoint q (294 : Vertex)))) else (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (295 : Vertex)) else decide (BallClauseLogic.Endpoint q (296 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (297 : Vertex)) else decide (BallClauseLogic.Endpoint q (299 : Vertex))))) else (if i < 175 then (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (301 : Vertex)) else decide (BallClauseLogic.Endpoint q (303 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (305 : Vertex)) else decide (BallClauseLogic.Endpoint q (306 : Vertex)))) else (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (307 : Vertex)) else decide (BallClauseLogic.Endpoint q (308 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (310 : Vertex)) else decide (BallClauseLogic.Endpoint q (314 : Vertex)))))))) else (if i < 209 then (if i < 194 then (if i < 186 then (if i < 182 then (if i < 180 then decide (BallClauseLogic.Endpoint q (316 : Vertex)) else (if i < 181 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (318 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (354 : Vertex)) else decide (BallClauseLogic.Endpoint q (356 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else decide (BallClauseLogic.Endpoint q (358 : Vertex))))) else (if i < 190 then (if i < 188 then (if i < 187 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (361 : Vertex))) else (if i < 189 then decide (BallClauseLogic.Endpoint q (362 : Vertex)) else decide (BallClauseLogic.Endpoint q (364 : Vertex)))) else (if i < 192 then (if i < 191 then decide (BallClauseLogic.Endpoint q (366 : Vertex)) else decide (BallClauseLogic.Endpoint q (372 : Vertex))) else (if i < 193 then decide (BallClauseLogic.Endpoint q (373 : Vertex)) else decide (BallClauseLogic.Endpoint q (375 : Vertex)))))) else (if i < 201 then (if i < 197 then (if i < 195 then decide (BallClauseLogic.Endpoint q (376 : Vertex)) else (if i < 196 then decide (BallClauseLogic.Endpoint q (377 : Vertex)) else decide (BallClauseLogic.Endpoint q (378 : Vertex)))) else (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (379 : Vertex)) else decide (BallClauseLogic.Endpoint q (383 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex))))) else (if i < 205 then (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (420 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))))))) else (if i < 224 then (if i < 216 then (if i < 212 then (if i < 210 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else (if i < 211 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (431 : Vertex)))) else (if i < 214 then (if i < 213 then decide (BallClauseLogic.Endpoint q (433 : Vertex)) else decide (BallClauseLogic.Endpoint q (435 : Vertex))) else (if i < 215 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (437 : Vertex))))) else (if i < 220 then (if i < 218 then (if i < 217 then decide (BallClauseLogic.Endpoint q (439 : Vertex)) else decide (BallClauseLogic.Endpoint q (440 : Vertex))) else (if i < 219 then decide (BallClauseLogic.Endpoint q (441 : Vertex)) else decide (BallClauseLogic.Endpoint q (442 : Vertex)))) else (if i < 222 then (if i < 221 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))) else (if i < 223 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))))) else (if i < 231 then (if i < 227 then (if i < 225 then decide (BallClauseLogic.Endpoint q (485 : Vertex)) else (if i < 226 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))) else (if i < 229 then (if i < 228 then decide (BallClauseLogic.Endpoint q (491 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex))) else (if i < 230 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (496 : Vertex))))) else (if i < 235 then (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 237 then (if i < 236 then decide (BallClauseLogic.Endpoint q (504 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 238 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count239 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count241 (b : Nat → Bool) : Nat := countLit b [120, 121, 122]
def count243 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count247 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126]
def count249 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125, 126]
def count251 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [127, 128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count259 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132, 133]
def count263 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133]
def count265 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [134, 135, 136]
def count269 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137, 138, 139, 140]
def count277 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count287 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
def count293 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
def count295 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [149, 150, 151]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count301 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155]
def count307 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count317 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]
def count323 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [164, 165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167, 168, 169, 170]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]
def count351 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]
def count353 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]
def count355 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count357 (b : Nat → Bool) : Nat := countLit b [179, 180, 181]
def count359 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185]
def count367 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count375 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192]
def count379 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]
def count381 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [193, 194, 195]
def count385 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count389 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199]
def count391 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199]
def count393 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count395 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count397 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count403 (b : Nat → Bool) : Nat := countLit b [204, 205, 206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203, 204, 205, 206, 207]
def count407 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
def count409 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
def count411 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count413 (b : Nat → Bool) : Nat := countLit b [208, 209, 210]
def count415 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count419 (b : Nat → Bool) : Nat := countLit b [211, 212, 213, 214]
def count421 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211, 212, 213, 214]
def count423 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count425 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218]
def count429 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [219, 220, 221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218, 219, 220, 221, 222]
def count437 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count439 (b : Nat → Bool) : Nat := countLit b [224, 225]
def count441 (b : Nat → Bool) : Nat := countLit b [223, 224, 225]
def count443 (b : Nat → Bool) : Nat := countLit b [226, 227]
def count445 (b : Nat → Bool) : Nat := countLit b [228, 229]
def count447 (b : Nat → Bool) : Nat := countLit b [226, 227, 228, 229]
def count449 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229]
def count451 (b : Nat → Bool) : Nat := countLit b [230, 231]
def count453 (b : Nat → Bool) : Nat := countLit b [232, 233]
def count455 (b : Nat → Bool) : Nat := countLit b [230, 231, 232, 233]
def count457 (b : Nat → Bool) : Nat := countLit b [234, 236]
def count459 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count461 (b : Nat → Bool) : Nat := countLit b [234, 236, 237, 238]
def count463 (b : Nat → Bool) : Nat := countLit b [230, 231, 232, 233, 234, 236, 237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]
def count467 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]
def count469 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]
def count471 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 236, 237, 238]
def count473 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count475 (b : Nat → Bool) : Nat := countLit b [1, 3, 5]
def count478 (b : Nat → Bool) : Nat := countLit b [7, 8]
def count480 (b : Nat → Bool) : Nat := countLit b [9, 14]
def count482 (b : Nat → Bool) : Nat := countLit b [7, 8, 9, 14]
def count486 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 8, 9, 14]
def count493 (b : Nat → Bool) : Nat := countLit b [15, 16]
def count495 (b : Nat → Bool) : Nat := countLit b [18, 19]
def count497 (b : Nat → Bool) : Nat := countLit b [15, 16, 18, 19]
def count501 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count503 (b : Nat → Bool) : Nat := countLit b [26, 27]
def count505 (b : Nat → Bool) : Nat := countLit b [20, 22, 26, 27]
def count509 (b : Nat → Bool) : Nat := countLit b [15, 16, 18, 19, 20, 22, 26, 27]
def count517 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 8, 9, 14, 15, 16, 18, 19, 20, 22, 26, 27]
def count532 (b : Nat → Bool) : Nat := countLit b [30, 33]
def count534 (b : Nat → Bool) : Nat := countLit b [28, 30, 33]
def count537 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count539 (b : Nat → Bool) : Nat := countLit b [38, 43]
def count541 (b : Nat → Bool) : Nat := countLit b [36, 37, 38, 43]
def count545 (b : Nat → Bool) : Nat := countLit b [28, 30, 33, 36, 37, 38, 43]
def count552 (b : Nat → Bool) : Nat := countLit b [44, 45]
def count554 (b : Nat → Bool) : Nat := countLit b [47, 50]
def count556 (b : Nat → Bool) : Nat := countLit b [44, 45, 47, 50]
def count560 (b : Nat → Bool) : Nat := countLit b [53, 54]
def count562 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count564 (b : Nat → Bool) : Nat := countLit b [53, 54, 55, 57]
def count568 (b : Nat → Bool) : Nat := countLit b [44, 45, 47, 50, 53, 54, 55, 57]
def count576 (b : Nat → Bool) : Nat := countLit b [28, 30, 33, 36, 37, 38, 43, 44, 45, 47, 50, 53, 54, 55, 57]
def count591 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 8, 9, 14, 15, 16, 18, 19, 20, 22, 26, 27, 28, 30, 33, 36, 37, 38, 43, 44, 45, 47, 50, 53, 54, 55, 57]
def count621 (b : Nat → Bool) : Nat := countLit b [62, 63]
def count623 (b : Nat → Bool) : Nat := countLit b [61, 62, 63]
def count626 (b : Nat → Bool) : Nat := countLit b [64, 67]
def count628 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count630 (b : Nat → Bool) : Nat := countLit b [64, 67, 71, 73]
def count634 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 64, 67, 71, 73]
def count641 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count643 (b : Nat → Bool) : Nat := countLit b [79, 81]
def count645 (b : Nat → Bool) : Nat := countLit b [76, 77, 79, 81]
def count649 (b : Nat → Bool) : Nat := countLit b [82, 83]
def count651 (b : Nat → Bool) : Nat := countLit b [86, 87]
def count653 (b : Nat → Bool) : Nat := countLit b [82, 83, 86, 87]
def count657 (b : Nat → Bool) : Nat := countLit b [76, 77, 79, 81, 82, 83, 86, 87]
def count665 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 64, 67, 71, 73, 76, 77, 79, 81, 82, 83, 86, 87]
def count680 (b : Nat → Bool) : Nat := countLit b [89, 91]
def count682 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count684 (b : Nat → Bool) : Nat := countLit b [89, 91, 94, 96]
def count688 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count690 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count692 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 103]
def count696 (b : Nat → Bool) : Nat := countLit b [89, 91, 94, 96, 99, 100, 102, 103]
def count704 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count706 (b : Nat → Bool) : Nat := countLit b [110, 112]
def count708 (b : Nat → Bool) : Nat := countLit b [105, 106, 110, 112]
def count712 (b : Nat → Bool) : Nat := countLit b [113, 116]
def count714 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count716 (b : Nat → Bool) : Nat := countLit b [113, 116, 118, 119]
def count720 (b : Nat → Bool) : Nat := countLit b [105, 106, 110, 112, 113, 116, 118, 119]
def count728 (b : Nat → Bool) : Nat := countLit b [89, 91, 94, 96, 99, 100, 102, 103, 105, 106, 110, 112, 113, 116, 118, 119]
def count744 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 64, 67, 71, 73, 76, 77, 79, 81, 82, 83, 86, 87, 89, 91, 94, 96, 99, 100, 102, 103, 105, 106, 110, 112, 113, 116, 118, 119]
def count775 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 8, 9, 14, 15, 16, 18, 19, 20, 22, 26, 27, 28, 30, 33, 36, 37, 38, 43, 44, 45, 47, 50, 53, 54, 55, 57, 61, 62, 63, 64, 67, 71, 73, 76, 77, 79, 81, 82, 83, 86, 87, 89, 91, 94, 96, 99, 100, 102, 103, 105, 106, 110, 112, 113, 116, 118, 119]
def count817 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count819 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5]
def count822 (b : Nat → Bool) : Nat := countLit b [-7, -8]
def count824 (b : Nat → Bool) : Nat := countLit b [-9, -14]
def count826 (b : Nat → Bool) : Nat := countLit b [-7, -8, -9, -14]
def count830 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -8, -9, -14]
def count837 (b : Nat → Bool) : Nat := countLit b [-15, -16]
def count839 (b : Nat → Bool) : Nat := countLit b [-18, -19]
def count841 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18, -19]
def count845 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count847 (b : Nat → Bool) : Nat := countLit b [-26, -27]
def count849 (b : Nat → Bool) : Nat := countLit b [-20, -22, -26, -27]
def count853 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18, -19, -20, -22, -26, -27]
def count861 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -8, -9, -14, -15, -16, -18, -19, -20, -22, -26, -27]
def count876 (b : Nat → Bool) : Nat := countLit b [-30, -33]
def count878 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33]
def count881 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count883 (b : Nat → Bool) : Nat := countLit b [-38, -43]
def count885 (b : Nat → Bool) : Nat := countLit b [-36, -37, -38, -43]
def count889 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33, -36, -37, -38, -43]
def count896 (b : Nat → Bool) : Nat := countLit b [-44, -45]
def count898 (b : Nat → Bool) : Nat := countLit b [-47, -50]
def count900 (b : Nat → Bool) : Nat := countLit b [-44, -45, -47, -50]
def count904 (b : Nat → Bool) : Nat := countLit b [-53, -54]
def count906 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count908 (b : Nat → Bool) : Nat := countLit b [-53, -54, -55, -57]
def count912 (b : Nat → Bool) : Nat := countLit b [-44, -45, -47, -50, -53, -54, -55, -57]
def count920 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33, -36, -37, -38, -43, -44, -45, -47, -50, -53, -54, -55, -57]
def count935 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -8, -9, -14, -15, -16, -18, -19, -20, -22, -26, -27, -28, -30, -33, -36, -37, -38, -43, -44, -45, -47, -50, -53, -54, -55, -57]
def count956 (b : Nat → Bool) : Nat := countLit b [-62, -63]
def count958 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63]
def count961 (b : Nat → Bool) : Nat := countLit b [-64, -67]
def count963 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count965 (b : Nat → Bool) : Nat := countLit b [-64, -67, -71, -73]
def count969 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -64, -67, -71, -73]
def count976 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count978 (b : Nat → Bool) : Nat := countLit b [-79, -81]
def count980 (b : Nat → Bool) : Nat := countLit b [-76, -77, -79, -81]
def count984 (b : Nat → Bool) : Nat := countLit b [-82, -83]
def count986 (b : Nat → Bool) : Nat := countLit b [-86, -87]
def count988 (b : Nat → Bool) : Nat := countLit b [-82, -83, -86, -87]
def count992 (b : Nat → Bool) : Nat := countLit b [-76, -77, -79, -81, -82, -83, -86, -87]
def count1000 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -64, -67, -71, -73, -76, -77, -79, -81, -82, -83, -86, -87]
def count1015 (b : Nat → Bool) : Nat := countLit b [-89, -91]
def count1017 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1019 (b : Nat → Bool) : Nat := countLit b [-89, -91, -94, -96]
def count1023 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1025 (b : Nat → Bool) : Nat := countLit b [-102, -103]
def count1027 (b : Nat → Bool) : Nat := countLit b [-99, -100, -102, -103]
def count1031 (b : Nat → Bool) : Nat := countLit b [-89, -91, -94, -96, -99, -100, -102, -103]
def count1039 (b : Nat → Bool) : Nat := countLit b [-105, -106]
def count1041 (b : Nat → Bool) : Nat := countLit b [-110, -112]
def count1043 (b : Nat → Bool) : Nat := countLit b [-105, -106, -110, -112]
def count1047 (b : Nat → Bool) : Nat := countLit b [-113, -116]
def count1049 (b : Nat → Bool) : Nat := countLit b [-118, -119]
def count1051 (b : Nat → Bool) : Nat := countLit b [-113, -116, -118, -119]
def count1055 (b : Nat → Bool) : Nat := countLit b [-105, -106, -110, -112, -113, -116, -118, -119]
def count1063 (b : Nat → Bool) : Nat := countLit b [-89, -91, -94, -96, -99, -100, -102, -103, -105, -106, -110, -112, -113, -116, -118, -119]
def count1079 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -64, -67, -71, -73, -76, -77, -79, -81, -82, -83, -86, -87, -89, -91, -94, -96, -99, -100, -102, -103, -105, -106, -110, -112, -113, -116, -118, -119]
def count1100 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -8, -9, -14, -15, -16, -18, -19, -20, -22, -26, -27, -28, -30, -33, -36, -37, -38, -43, -44, -45, -47, -50, -53, -54, -55, -57, -61, -62, -63, -64, -67, -71, -73, -76, -77, -79, -81, -82, -83, -86, -87, -89, -91, -94, -96, -99, -100, -102, -103, -105, -106, -110, -112, -113, -116, -118, -119]
def count1121 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count1123 (b : Nat → Bool) : Nat := countLit b [2, 4, 6]
def count1126 (b : Nat → Bool) : Nat := countLit b [10, 11]
def count1128 (b : Nat → Bool) : Nat := countLit b [12, 13]
def count1130 (b : Nat → Bool) : Nat := countLit b [10, 11, 12, 13]
def count1134 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 10, 11, 12, 13]
def count1141 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count1143 (b : Nat → Bool) : Nat := countLit b [17, 21, 23]
def count1146 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count1148 (b : Nat → Bool) : Nat := countLit b [29, 31]
def count1150 (b : Nat → Bool) : Nat := countLit b [24, 25, 29, 31]
def count1154 (b : Nat → Bool) : Nat := countLit b [17, 21, 23, 24, 25, 29, 31]
def count1161 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 10, 11, 12, 13, 17, 21, 23, 24, 25, 29, 31]
def count1175 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count1177 (b : Nat → Bool) : Nat := countLit b [32, 34, 35]
def count1180 (b : Nat → Bool) : Nat := countLit b [39, 40]
def count1182 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count1184 (b : Nat → Bool) : Nat := countLit b [39, 40, 41, 42]
def count1188 (b : Nat → Bool) : Nat := countLit b [32, 34, 35, 39, 40, 41, 42]
def count1195 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count1197 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count1199 (b : Nat → Bool) : Nat := countLit b [46, 48, 49, 51]
def count1203 (b : Nat → Bool) : Nat := countLit b [52, 56]
def count1205 (b : Nat → Bool) : Nat := countLit b [58, 59]
def count1207 (b : Nat → Bool) : Nat := countLit b [52, 56, 58, 59]
def count1211 (b : Nat → Bool) : Nat := countLit b [46, 48, 49, 51, 52, 56, 58, 59]
def count1219 (b : Nat → Bool) : Nat := countLit b [32, 34, 35, 39, 40, 41, 42, 46, 48, 49, 51, 52, 56, 58, 59]
def count1234 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 10, 11, 12, 13, 17, 21, 23, 24, 25, 29, 31, 32, 34, 35, 39, 40, 41, 42, 46, 48, 49, 51, 52, 56, 58, 59]
def count1263 (b : Nat → Bool) : Nat := countLit b [65, 66]
def count1265 (b : Nat → Bool) : Nat := countLit b [60, 65, 66]
def count1268 (b : Nat → Bool) : Nat := countLit b [68, 69]
def count1270 (b : Nat → Bool) : Nat := countLit b [70, 72]
def count1272 (b : Nat → Bool) : Nat := countLit b [68, 69, 70, 72]
def count1276 (b : Nat → Bool) : Nat := countLit b [60, 65, 66, 68, 69, 70, 72]
def count1283 (b : Nat → Bool) : Nat := countLit b [75, 78]
def count1285 (b : Nat → Bool) : Nat := countLit b [74, 75, 78]
def count1288 (b : Nat → Bool) : Nat := countLit b [80, 84]
def count1290 (b : Nat → Bool) : Nat := countLit b [85, 88]
def count1292 (b : Nat → Bool) : Nat := countLit b [80, 84, 85, 88]
def count1296 (b : Nat → Bool) : Nat := countLit b [74, 75, 78, 80, 84, 85, 88]
def count1303 (b : Nat → Bool) : Nat := countLit b [60, 65, 66, 68, 69, 70, 72, 74, 75, 78, 80, 84, 85, 88]
def count1317 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count1319 (b : Nat → Bool) : Nat := countLit b [90, 92, 93]
def count1322 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count1324 (b : Nat → Bool) : Nat := countLit b [98, 101]
def count1326 (b : Nat → Bool) : Nat := countLit b [95, 97, 98, 101]
def count1330 (b : Nat → Bool) : Nat := countLit b [90, 92, 93, 95, 97, 98, 101]
def count1337 (b : Nat → Bool) : Nat := countLit b [104, 107]
def count1339 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count1341 (b : Nat → Bool) : Nat := countLit b [104, 107, 108, 109]
def count1345 (b : Nat → Bool) : Nat := countLit b [111, 114]
def count1347 (b : Nat → Bool) : Nat := countLit b [115, 117]
def count1349 (b : Nat → Bool) : Nat := countLit b [111, 114, 115, 117]
def count1353 (b : Nat → Bool) : Nat := countLit b [104, 107, 108, 109, 111, 114, 115, 117]
def count1361 (b : Nat → Bool) : Nat := countLit b [90, 92, 93, 95, 97, 98, 101, 104, 107, 108, 109, 111, 114, 115, 117]
def count1376 (b : Nat → Bool) : Nat := countLit b [60, 65, 66, 68, 69, 70, 72, 74, 75, 78, 80, 84, 85, 88, 90, 92, 93, 95, 97, 98, 101, 104, 107, 108, 109, 111, 114, 115, 117]
def count1405 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 10, 11, 12, 13, 17, 21, 23, 24, 25, 29, 31, 32, 34, 35, 39, 40, 41, 42, 46, 48, 49, 51, 52, 56, 58, 59, 60, 65, 66, 68, 69, 70, 72, 74, 75, 78, 80, 84, 85, 88, 90, 92, 93, 95, 97, 98, 101, 104, 107, 108, 109, 111, 114, 115, 117]
def count1447 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count1449 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6]
def count1452 (b : Nat → Bool) : Nat := countLit b [-10, -11]
def count1454 (b : Nat → Bool) : Nat := countLit b [-12, -13]
def count1456 (b : Nat → Bool) : Nat := countLit b [-10, -11, -12, -13]
def count1460 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -10, -11, -12, -13]
def count1467 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count1469 (b : Nat → Bool) : Nat := countLit b [-17, -21, -23]
def count1472 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count1474 (b : Nat → Bool) : Nat := countLit b [-29, -31]
def count1476 (b : Nat → Bool) : Nat := countLit b [-24, -25, -29, -31]
def count1480 (b : Nat → Bool) : Nat := countLit b [-17, -21, -23, -24, -25, -29, -31]
def count1487 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]
def count1501 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count1503 (b : Nat → Bool) : Nat := countLit b [-32, -34, -35]
def count1506 (b : Nat → Bool) : Nat := countLit b [-39, -40]
def count1508 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count1510 (b : Nat → Bool) : Nat := countLit b [-39, -40, -41, -42]
def count1514 (b : Nat → Bool) : Nat := countLit b [-32, -34, -35, -39, -40, -41, -42]
def count1521 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count1523 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count1525 (b : Nat → Bool) : Nat := countLit b [-46, -48, -49, -51]
def count1529 (b : Nat → Bool) : Nat := countLit b [-52, -56]
def count1531 (b : Nat → Bool) : Nat := countLit b [-58, -59]
def count1533 (b : Nat → Bool) : Nat := countLit b [-52, -56, -58, -59]
def count1537 (b : Nat → Bool) : Nat := countLit b [-46, -48, -49, -51, -52, -56, -58, -59]
def count1545 (b : Nat → Bool) : Nat := countLit b [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]
def count1560 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]
def count1578 (b : Nat → Bool) : Nat := countLit b [-65, -66]
def count1580 (b : Nat → Bool) : Nat := countLit b [-60, -65, -66]
def count1583 (b : Nat → Bool) : Nat := countLit b [-68, -69]
def count1585 (b : Nat → Bool) : Nat := countLit b [-70, -72]
def count1587 (b : Nat → Bool) : Nat := countLit b [-68, -69, -70, -72]
def count1591 (b : Nat → Bool) : Nat := countLit b [-60, -65, -66, -68, -69, -70, -72]
def count1598 (b : Nat → Bool) : Nat := countLit b [-75, -78]
def count1600 (b : Nat → Bool) : Nat := countLit b [-74, -75, -78]
def count1603 (b : Nat → Bool) : Nat := countLit b [-80, -84]
def count1605 (b : Nat → Bool) : Nat := countLit b [-85, -88]
def count1607 (b : Nat → Bool) : Nat := countLit b [-80, -84, -85, -88]
def count1611 (b : Nat → Bool) : Nat := countLit b [-74, -75, -78, -80, -84, -85, -88]
def count1618 (b : Nat → Bool) : Nat := countLit b [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]
def count1632 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1634 (b : Nat → Bool) : Nat := countLit b [-90, -92, -93]
def count1637 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count1639 (b : Nat → Bool) : Nat := countLit b [-98, -101]
def count1641 (b : Nat → Bool) : Nat := countLit b [-95, -97, -98, -101]
def count1645 (b : Nat → Bool) : Nat := countLit b [-90, -92, -93, -95, -97, -98, -101]
def count1652 (b : Nat → Bool) : Nat := countLit b [-104, -107]
def count1654 (b : Nat → Bool) : Nat := countLit b [-108, -109]
def count1656 (b : Nat → Bool) : Nat := countLit b [-104, -107, -108, -109]
def count1660 (b : Nat → Bool) : Nat := countLit b [-111, -114]
def count1662 (b : Nat → Bool) : Nat := countLit b [-115, -117]
def count1664 (b : Nat → Bool) : Nat := countLit b [-111, -114, -115, -117]
def count1668 (b : Nat → Bool) : Nat := countLit b [-104, -107, -108, -109, -111, -114, -115, -117]
def count1676 (b : Nat → Bool) : Nat := countLit b [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]
def count1691 (b : Nat → Bool) : Nat := countLit b [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]
def count1709 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59, -60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 863 then (if i < 431 then (if i < 215 then (if i < 107 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 19 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 17 then b 16 else (if i < 18 then b 17 else b 18))) else (if i < 22 then (if i < 20 then b 19 else (if i < 21 then b 20 else b 21)) else (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else b 25))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31))) else (if i < 35 then (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)) else (if i < 37 then (if i < 36 then b 35 else b 36) else (if i < 38 then b 37 else b 38)))) else (if i < 46 then (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 44 then (if i < 43 then b 42 else b 43) else (if i < 45 then b 44 else b 45))) else (if i < 49 then (if i < 47 then b 46 else (if i < 48 then b 47 else b 48)) else (if i < 51 then (if i < 50 then b 49 else b 50) else (if i < 52 then b 51 else b 52)))))) else (if i < 80 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)) else (if i < 57 then b 56 else (if i < 58 then b 57 else b 58))) else (if i < 62 then (if i < 60 then b 59 else (if i < 61 then b 60 else b 61)) else (if i < 64 then (if i < 63 then b 62 else b 63) else (if i < 65 then b 64 else b 65)))) else (if i < 73 then (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 71 then (if i < 70 then b 69 else b 70) else (if i < 72 then b 71 else b 72))) else (if i < 76 then (if i < 74 then b 73 else (if i < 75 then b 74 else b 75)) else (if i < 78 then (if i < 77 then b 76 else b 77) else (if i < 79 then b 78 else b 79))))) else (if i < 93 then (if i < 86 then (if i < 83 then (if i < 81 then b 80 else (if i < 82 then b 81 else b 82)) else (if i < 84 then b 83 else (if i < 85 then b 84 else b 85))) else (if i < 89 then (if i < 87 then b 86 else (if i < 88 then b 87 else b 88)) else (if i < 91 then (if i < 90 then b 89 else b 90) else (if i < 92 then b 91 else b 92)))) else (if i < 100 then (if i < 96 then (if i < 94 then b 93 else (if i < 95 then b 94 else b 95)) else (if i < 98 then (if i < 97 then b 96 else b 97) else (if i < 99 then b 98 else b 99))) else (if i < 103 then (if i < 101 then b 100 else (if i < 102 then b 101 else b 102)) else (if i < 105 then (if i < 104 then b 103 else b 104) else (if i < 106 then b 105 else b 106))))))) else (if i < 161 then (if i < 134 then (if i < 120 then (if i < 113 then (if i < 110 then (if i < 108 then b 107 else (if i < 109 then b 108 else b 109)) else (if i < 111 then b 110 else (if i < 112 then b 111 else b 112))) else (if i < 116 then (if i < 114 then b 113 else (if i < 115 then b 114 else b 115)) else (if i < 118 then (if i < 117 then b 116 else b 117) else (if i < 119 then b 118 else b 119)))) else (if i < 127 then (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 125 then (if i < 124 then b 123 else b 124) else (if i < 126 then b 125 else b 126))) else (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 132 then (if i < 131 then b 130 else b 131) else (if i < 133 then b 132 else b 133))))) else (if i < 147 then (if i < 140 then (if i < 137 then (if i < 135 then b 134 else (if i < 136 then b 135 else b 136)) else (if i < 138 then b 137 else (if i < 139 then b 138 else b 139))) else (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 145 then (if i < 144 then b 143 else b 144) else (if i < 146 then b 145 else b 146)))) else (if i < 154 then (if i < 150 then (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)) else (if i < 152 then (if i < 151 then b 150 else b 151) else (if i < 153 then b 152 else b 153))) else (if i < 157 then (if i < 155 then b 154 else (if i < 156 then b 155 else b 156)) else (if i < 159 then (if i < 158 then b 157 else b 158) else (if i < 160 then b 159 else b 160)))))) else (if i < 188 then (if i < 174 then (if i < 167 then (if i < 164 then (if i < 162 then b 161 else (if i < 163 then b 162 else b 163)) else (if i < 165 then b 164 else (if i < 166 then b 165 else b 166))) else (if i < 170 then (if i < 168 then b 167 else (if i < 169 then b 168 else b 169)) else (if i < 172 then (if i < 171 then b 170 else b 171) else (if i < 173 then b 172 else b 173)))) else (if i < 181 then (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 179 then (if i < 178 then b 177 else b 178) else (if i < 180 then b 179 else b 180))) else (if i < 184 then (if i < 182 then b 181 else (if i < 183 then b 182 else b 183)) else (if i < 186 then (if i < 185 then b 184 else b 185) else (if i < 187 then b 186 else b 187))))) else (if i < 201 then (if i < 194 then (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 192 then b 191 else (if i < 193 then b 192 else b 193))) else (if i < 197 then (if i < 195 then b 194 else (if i < 196 then b 195 else b 196)) else (if i < 199 then (if i < 198 then b 197 else b 198) else (if i < 200 then b 199 else b 200)))) else (if i < 208 then (if i < 204 then (if i < 202 then b 201 else (if i < 203 then b 202 else b 203)) else (if i < 206 then (if i < 205 then b 204 else b 205) else (if i < 207 then b 206 else b 207))) else (if i < 211 then (if i < 209 then b 208 else (if i < 210 then b 209 else b 210)) else (if i < 213 then (if i < 212 then b 211 else b 212) else (if i < 214 then b 213 else b 214)))))))) else (if i < 323 then (if i < 269 then (if i < 242 then (if i < 228 then (if i < 221 then (if i < 218 then (if i < 216 then b 215 else (if i < 217 then b 216 else b 217)) else (if i < 219 then b 218 else (if i < 220 then b 219 else b 220))) else (if i < 224 then (if i < 222 then b 221 else (if i < 223 then b 222 else b 223)) else (if i < 226 then (if i < 225 then b 224 else b 225) else (if i < 227 then b 226 else b 227)))) else (if i < 235 then (if i < 231 then (if i < 229 then b 228 else (if i < 230 then b 229 else b 230)) else (if i < 233 then (if i < 232 then b 231 else b 232) else (if i < 234 then b 233 else b 234))) else (if i < 238 then (if i < 236 then b 235 else (if i < 237 then b 236 else b 237)) else (if i < 240 then (if i < 239 then b 238 else decide (1 ≤ count239 b)) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b)))))) else (if i < 255 then (if i < 248 then (if i < 245 then (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b))) else (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b)))) else (if i < 251 then (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 253 then (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))))) else (if i < 262 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 260 then (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b)) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))) else (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 267 then (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b))))))) else (if i < 296 then (if i < 282 then (if i < 275 then (if i < 272 then (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))) else (if i < 273 then decide (2 ≤ count271 b) else (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b)))) else (if i < 278 then (if i < 276 then decide (1 ≤ count275 b) else (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b))) else (if i < 280 then (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))))) else (if i < 289 then (if i < 285 then (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))) else (if i < 287 then (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)))) else (if i < 292 then (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b))) else (if i < 294 then (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b)) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)))))) else (if i < 309 then (if i < 302 then (if i < 299 then (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b))) else (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))) else (if i < 305 then (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))) else (if i < 307 then (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))))) else (if i < 316 then (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 314 then (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)))) else (if i < 319 then (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b))) else (if i < 321 then (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b)) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)))))))) else (if i < 377 then (if i < 350 then (if i < 336 then (if i < 329 then (if i < 326 then (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))) else (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)))) else (if i < 332 then (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))) else (if i < 334 then (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))))) else (if i < 343 then (if i < 339 then (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))) else (if i < 341 then (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)))) else (if i < 346 then (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)))))) else (if i < 363 then (if i < 356 then (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b)))) else (if i < 359 then (if i < 357 then decide (2 ≤ count355 b) else (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b))) else (if i < 361 then (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b))))) else (if i < 370 then (if i < 366 then (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b))) else (if i < 368 then (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b)))) else (if i < 373 then (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))) else (if i < 375 then (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b))))))) else (if i < 404 then (if i < 390 then (if i < 383 then (if i < 380 then (if i < 378 then decide (1 ≤ count377 b) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b))) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))) else (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 388 then (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b))))) else (if i < 397 then (if i < 393 then (if i < 391 then decide (2 ≤ count389 b) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))) else (if i < 395 then (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)))) else (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)))))) else (if i < 417 then (if i < 410 then (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 408 then decide (1 ≤ count407 b) else (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)))) else (if i < 413 then (if i < 411 then decide (2 ≤ count409 b) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))) else (if i < 415 then (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)) else (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b))))) else (if i < 424 then (if i < 420 then (if i < 418 then decide (1 ≤ count417 b) else (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b))) else (if i < 422 then (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b)) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b)))) else (if i < 427 then (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b))) else (if i < 429 then (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b)))))))))) else (if i < 647 then (if i < 539 then (if i < 485 then (if i < 458 then (if i < 444 then (if i < 437 then (if i < 434 then (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))) else (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)))) else (if i < 440 then (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b))) else (if i < 442 then (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b))))) else (if i < 451 then (if i < 447 then (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b))) else (if i < 449 then (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b)) else (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)))) else (if i < 454 then (if i < 452 then decide (1 ≤ count451 b) else (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b))) else (if i < 456 then (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b)) else (if i < 457 then decide (2 ≤ count455 b) else decide (1 ≤ count457 b)))))) else (if i < 471 then (if i < 464 then (if i < 461 then (if i < 459 then decide (2 ≤ count457 b) else (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b))) else (if i < 462 then decide (1 ≤ count461 b) else (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b)))) else (if i < 467 then (if i < 465 then decide (2 ≤ count463 b) else (if i < 466 then decide (1 ≤ count465 b) else decide (2 ≤ count465 b))) else (if i < 469 then (if i < 468 then decide (1 ≤ count467 b) else decide (2 ≤ count467 b)) else (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b))))) else (if i < 478 then (if i < 474 then (if i < 472 then decide (1 ≤ count471 b) else (if i < 473 then decide (2 ≤ count471 b) else decide (1 ≤ count473 b))) else (if i < 476 then (if i < 475 then decide (2 ≤ count473 b) else decide (1 ≤ count475 b)) else (if i < 477 then decide (2 ≤ count475 b) else decide (3 ≤ count475 b)))) else (if i < 481 then (if i < 479 then decide (1 ≤ count478 b) else (if i < 480 then decide (2 ≤ count478 b) else decide (1 ≤ count480 b))) else (if i < 483 then (if i < 482 then decide (2 ≤ count480 b) else decide (1 ≤ count482 b)) else (if i < 484 then decide (2 ≤ count482 b) else decide (3 ≤ count482 b))))))) else (if i < 512 then (if i < 498 then (if i < 491 then (if i < 488 then (if i < 486 then decide (4 ≤ count482 b) else (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b))) else (if i < 489 then decide (3 ≤ count486 b) else (if i < 490 then decide (4 ≤ count486 b) else decide (5 ≤ count486 b)))) else (if i < 494 then (if i < 492 then decide (6 ≤ count486 b) else (if i < 493 then decide (7 ≤ count486 b) else decide (1 ≤ count493 b))) else (if i < 496 then (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b)) else (if i < 497 then decide (2 ≤ count495 b) else decide (1 ≤ count497 b))))) else (if i < 505 then (if i < 501 then (if i < 499 then decide (2 ≤ count497 b) else (if i < 500 then decide (3 ≤ count497 b) else decide (4 ≤ count497 b))) else (if i < 503 then (if i < 502 then decide (1 ≤ count501 b) else decide (2 ≤ count501 b)) else (if i < 504 then decide (1 ≤ count503 b) else decide (2 ≤ count503 b)))) else (if i < 508 then (if i < 506 then decide (1 ≤ count505 b) else (if i < 507 then decide (2 ≤ count505 b) else decide (3 ≤ count505 b))) else (if i < 510 then (if i < 509 then decide (4 ≤ count505 b) else decide (1 ≤ count509 b)) else (if i < 511 then decide (2 ≤ count509 b) else decide (3 ≤ count509 b)))))) else (if i < 525 then (if i < 518 then (if i < 515 then (if i < 513 then decide (4 ≤ count509 b) else (if i < 514 then decide (5 ≤ count509 b) else decide (6 ≤ count509 b))) else (if i < 516 then decide (7 ≤ count509 b) else (if i < 517 then decide (8 ≤ count509 b) else decide (1 ≤ count517 b)))) else (if i < 521 then (if i < 519 then decide (2 ≤ count517 b) else (if i < 520 then decide (3 ≤ count517 b) else decide (4 ≤ count517 b))) else (if i < 523 then (if i < 522 then decide (5 ≤ count517 b) else decide (6 ≤ count517 b)) else (if i < 524 then decide (7 ≤ count517 b) else decide (8 ≤ count517 b))))) else (if i < 532 then (if i < 528 then (if i < 526 then decide (9 ≤ count517 b) else (if i < 527 then decide (10 ≤ count517 b) else decide (11 ≤ count517 b))) else (if i < 530 then (if i < 529 then decide (12 ≤ count517 b) else decide (13 ≤ count517 b)) else (if i < 531 then decide (14 ≤ count517 b) else decide (15 ≤ count517 b)))) else (if i < 535 then (if i < 533 then decide (1 ≤ count532 b) else (if i < 534 then decide (2 ≤ count532 b) else decide (1 ≤ count534 b))) else (if i < 537 then (if i < 536 then decide (2 ≤ count534 b) else decide (3 ≤ count534 b)) else (if i < 538 then decide (1 ≤ count537 b) else decide (2 ≤ count537 b)))))))) else (if i < 593 then (if i < 566 then (if i < 552 then (if i < 545 then (if i < 542 then (if i < 540 then decide (1 ≤ count539 b) else (if i < 541 then decide (2 ≤ count539 b) else decide (1 ≤ count541 b))) else (if i < 543 then decide (2 ≤ count541 b) else (if i < 544 then decide (3 ≤ count541 b) else decide (4 ≤ count541 b)))) else (if i < 548 then (if i < 546 then decide (1 ≤ count545 b) else (if i < 547 then decide (2 ≤ count545 b) else decide (3 ≤ count545 b))) else (if i < 550 then (if i < 549 then decide (4 ≤ count545 b) else decide (5 ≤ count545 b)) else (if i < 551 then decide (6 ≤ count545 b) else decide (7 ≤ count545 b))))) else (if i < 559 then (if i < 555 then (if i < 553 then decide (1 ≤ count552 b) else (if i < 554 then decide (2 ≤ count552 b) else decide (1 ≤ count554 b))) else (if i < 557 then (if i < 556 then decide (2 ≤ count554 b) else decide (1 ≤ count556 b)) else (if i < 558 then decide (2 ≤ count556 b) else decide (3 ≤ count556 b)))) else (if i < 562 then (if i < 560 then decide (4 ≤ count556 b) else (if i < 561 then decide (1 ≤ count560 b) else decide (2 ≤ count560 b))) else (if i < 564 then (if i < 563 then decide (1 ≤ count562 b) else decide (2 ≤ count562 b)) else (if i < 565 then decide (1 ≤ count564 b) else decide (2 ≤ count564 b)))))) else (if i < 579 then (if i < 572 then (if i < 569 then (if i < 567 then decide (3 ≤ count564 b) else (if i < 568 then decide (4 ≤ count564 b) else decide (1 ≤ count568 b))) else (if i < 570 then decide (2 ≤ count568 b) else (if i < 571 then decide (3 ≤ count568 b) else decide (4 ≤ count568 b)))) else (if i < 575 then (if i < 573 then decide (5 ≤ count568 b) else (if i < 574 then decide (6 ≤ count568 b) else decide (7 ≤ count568 b))) else (if i < 577 then (if i < 576 then decide (8 ≤ count568 b) else decide (1 ≤ count576 b)) else (if i < 578 then decide (2 ≤ count576 b) else decide (3 ≤ count576 b))))) else (if i < 586 then (if i < 582 then (if i < 580 then decide (4 ≤ count576 b) else (if i < 581 then decide (5 ≤ count576 b) else decide (6 ≤ count576 b))) else (if i < 584 then (if i < 583 then decide (7 ≤ count576 b) else decide (8 ≤ count576 b)) else (if i < 585 then decide (9 ≤ count576 b) else decide (10 ≤ count576 b)))) else (if i < 589 then (if i < 587 then decide (11 ≤ count576 b) else (if i < 588 then decide (12 ≤ count576 b) else decide (13 ≤ count576 b))) else (if i < 591 then (if i < 590 then decide (14 ≤ count576 b) else decide (15 ≤ count576 b)) else (if i < 592 then decide (1 ≤ count591 b) else decide (2 ≤ count591 b))))))) else (if i < 620 then (if i < 606 then (if i < 599 then (if i < 596 then (if i < 594 then decide (3 ≤ count591 b) else (if i < 595 then decide (4 ≤ count591 b) else decide (5 ≤ count591 b))) else (if i < 597 then decide (6 ≤ count591 b) else (if i < 598 then decide (7 ≤ count591 b) else decide (8 ≤ count591 b)))) else (if i < 602 then (if i < 600 then decide (9 ≤ count591 b) else (if i < 601 then decide (10 ≤ count591 b) else decide (11 ≤ count591 b))) else (if i < 604 then (if i < 603 then decide (12 ≤ count591 b) else decide (13 ≤ count591 b)) else (if i < 605 then decide (14 ≤ count591 b) else decide (15 ≤ count591 b))))) else (if i < 613 then (if i < 609 then (if i < 607 then decide (16 ≤ count591 b) else (if i < 608 then decide (17 ≤ count591 b) else decide (18 ≤ count591 b))) else (if i < 611 then (if i < 610 then decide (19 ≤ count591 b) else decide (20 ≤ count591 b)) else (if i < 612 then decide (21 ≤ count591 b) else decide (22 ≤ count591 b)))) else (if i < 616 then (if i < 614 then decide (23 ≤ count591 b) else (if i < 615 then decide (24 ≤ count591 b) else decide (25 ≤ count591 b))) else (if i < 618 then (if i < 617 then decide (26 ≤ count591 b) else decide (27 ≤ count591 b)) else (if i < 619 then decide (28 ≤ count591 b) else decide (29 ≤ count591 b)))))) else (if i < 633 then (if i < 626 then (if i < 623 then (if i < 621 then decide (30 ≤ count591 b) else (if i < 622 then decide (1 ≤ count621 b) else decide (2 ≤ count621 b))) else (if i < 624 then decide (1 ≤ count623 b) else (if i < 625 then decide (2 ≤ count623 b) else decide (3 ≤ count623 b)))) else (if i < 629 then (if i < 627 then decide (1 ≤ count626 b) else (if i < 628 then decide (2 ≤ count626 b) else decide (1 ≤ count628 b))) else (if i < 631 then (if i < 630 then decide (2 ≤ count628 b) else decide (1 ≤ count630 b)) else (if i < 632 then decide (2 ≤ count630 b) else decide (3 ≤ count630 b))))) else (if i < 640 then (if i < 636 then (if i < 634 then decide (4 ≤ count630 b) else (if i < 635 then decide (1 ≤ count634 b) else decide (2 ≤ count634 b))) else (if i < 638 then (if i < 637 then decide (3 ≤ count634 b) else decide (4 ≤ count634 b)) else (if i < 639 then decide (5 ≤ count634 b) else decide (6 ≤ count634 b)))) else (if i < 643 then (if i < 641 then decide (7 ≤ count634 b) else (if i < 642 then decide (1 ≤ count641 b) else decide (2 ≤ count641 b))) else (if i < 645 then (if i < 644 then decide (1 ≤ count643 b) else decide (2 ≤ count643 b)) else (if i < 646 then decide (1 ≤ count645 b) else decide (2 ≤ count645 b))))))))) else (if i < 755 then (if i < 701 then (if i < 674 then (if i < 660 then (if i < 653 then (if i < 650 then (if i < 648 then decide (3 ≤ count645 b) else (if i < 649 then decide (4 ≤ count645 b) else decide (1 ≤ count649 b))) else (if i < 651 then decide (2 ≤ count649 b) else (if i < 652 then decide (1 ≤ count651 b) else decide (2 ≤ count651 b)))) else (if i < 656 then (if i < 654 then decide (1 ≤ count653 b) else (if i < 655 then decide (2 ≤ count653 b) else decide (3 ≤ count653 b))) else (if i < 658 then (if i < 657 then decide (4 ≤ count653 b) else decide (1 ≤ count657 b)) else (if i < 659 then decide (2 ≤ count657 b) else decide (3 ≤ count657 b))))) else (if i < 667 then (if i < 663 then (if i < 661 then decide (4 ≤ count657 b) else (if i < 662 then decide (5 ≤ count657 b) else decide (6 ≤ count657 b))) else (if i < 665 then (if i < 664 then decide (7 ≤ count657 b) else decide (8 ≤ count657 b)) else (if i < 666 then decide (1 ≤ count665 b) else decide (2 ≤ count665 b)))) else (if i < 670 then (if i < 668 then decide (3 ≤ count665 b) else (if i < 669 then decide (4 ≤ count665 b) else decide (5 ≤ count665 b))) else (if i < 672 then (if i < 671 then decide (6 ≤ count665 b) else decide (7 ≤ count665 b)) else (if i < 673 then decide (8 ≤ count665 b) else decide (9 ≤ count665 b)))))) else (if i < 687 then (if i < 680 then (if i < 677 then (if i < 675 then decide (10 ≤ count665 b) else (if i < 676 then decide (11 ≤ count665 b) else decide (12 ≤ count665 b))) else (if i < 678 then decide (13 ≤ count665 b) else (if i < 679 then decide (14 ≤ count665 b) else decide (15 ≤ count665 b)))) else (if i < 683 then (if i < 681 then decide (1 ≤ count680 b) else (if i < 682 then decide (2 ≤ count680 b) else decide (1 ≤ count682 b))) else (if i < 685 then (if i < 684 then decide (2 ≤ count682 b) else decide (1 ≤ count684 b)) else (if i < 686 then decide (2 ≤ count684 b) else decide (3 ≤ count684 b))))) else (if i < 694 then (if i < 690 then (if i < 688 then decide (4 ≤ count684 b) else (if i < 689 then decide (1 ≤ count688 b) else decide (2 ≤ count688 b))) else (if i < 692 then (if i < 691 then decide (1 ≤ count690 b) else decide (2 ≤ count690 b)) else (if i < 693 then decide (1 ≤ count692 b) else decide (2 ≤ count692 b)))) else (if i < 697 then (if i < 695 then decide (3 ≤ count692 b) else (if i < 696 then decide (4 ≤ count692 b) else decide (1 ≤ count696 b))) else (if i < 699 then (if i < 698 then decide (2 ≤ count696 b) else decide (3 ≤ count696 b)) else (if i < 700 then decide (4 ≤ count696 b) else decide (5 ≤ count696 b))))))) else (if i < 728 then (if i < 714 then (if i < 707 then (if i < 704 then (if i < 702 then decide (6 ≤ count696 b) else (if i < 703 then decide (7 ≤ count696 b) else decide (8 ≤ count696 b))) else (if i < 705 then decide (1 ≤ count704 b) else (if i < 706 then decide (2 ≤ count704 b) else decide (1 ≤ count706 b)))) else (if i < 710 then (if i < 708 then decide (2 ≤ count706 b) else (if i < 709 then decide (1 ≤ count708 b) else decide (2 ≤ count708 b))) else (if i < 712 then (if i < 711 then decide (3 ≤ count708 b) else decide (4 ≤ count708 b)) else (if i < 713 then decide (1 ≤ count712 b) else decide (2 ≤ count712 b))))) else (if i < 721 then (if i < 717 then (if i < 715 then decide (1 ≤ count714 b) else (if i < 716 then decide (2 ≤ count714 b) else decide (1 ≤ count716 b))) else (if i < 719 then (if i < 718 then decide (2 ≤ count716 b) else decide (3 ≤ count716 b)) else (if i < 720 then decide (4 ≤ count716 b) else decide (1 ≤ count720 b)))) else (if i < 724 then (if i < 722 then decide (2 ≤ count720 b) else (if i < 723 then decide (3 ≤ count720 b) else decide (4 ≤ count720 b))) else (if i < 726 then (if i < 725 then decide (5 ≤ count720 b) else decide (6 ≤ count720 b)) else (if i < 727 then decide (7 ≤ count720 b) else decide (8 ≤ count720 b)))))) else (if i < 741 then (if i < 734 then (if i < 731 then (if i < 729 then decide (1 ≤ count728 b) else (if i < 730 then decide (2 ≤ count728 b) else decide (3 ≤ count728 b))) else (if i < 732 then decide (4 ≤ count728 b) else (if i < 733 then decide (5 ≤ count728 b) else decide (6 ≤ count728 b)))) else (if i < 737 then (if i < 735 then decide (7 ≤ count728 b) else (if i < 736 then decide (8 ≤ count728 b) else decide (9 ≤ count728 b))) else (if i < 739 then (if i < 738 then decide (10 ≤ count728 b) else decide (11 ≤ count728 b)) else (if i < 740 then decide (12 ≤ count728 b) else decide (13 ≤ count728 b))))) else (if i < 748 then (if i < 744 then (if i < 742 then decide (14 ≤ count728 b) else (if i < 743 then decide (15 ≤ count728 b) else decide (16 ≤ count728 b))) else (if i < 746 then (if i < 745 then decide (1 ≤ count744 b) else decide (2 ≤ count744 b)) else (if i < 747 then decide (3 ≤ count744 b) else decide (4 ≤ count744 b)))) else (if i < 751 then (if i < 749 then decide (5 ≤ count744 b) else (if i < 750 then decide (6 ≤ count744 b) else decide (7 ≤ count744 b))) else (if i < 753 then (if i < 752 then decide (8 ≤ count744 b) else decide (9 ≤ count744 b)) else (if i < 754 then decide (10 ≤ count744 b) else decide (11 ≤ count744 b)))))))) else (if i < 809 then (if i < 782 then (if i < 768 then (if i < 761 then (if i < 758 then (if i < 756 then decide (12 ≤ count744 b) else (if i < 757 then decide (13 ≤ count744 b) else decide (14 ≤ count744 b))) else (if i < 759 then decide (15 ≤ count744 b) else (if i < 760 then decide (16 ≤ count744 b) else decide (17 ≤ count744 b)))) else (if i < 764 then (if i < 762 then decide (18 ≤ count744 b) else (if i < 763 then decide (19 ≤ count744 b) else decide (20 ≤ count744 b))) else (if i < 766 then (if i < 765 then decide (21 ≤ count744 b) else decide (22 ≤ count744 b)) else (if i < 767 then decide (23 ≤ count744 b) else decide (24 ≤ count744 b))))) else (if i < 775 then (if i < 771 then (if i < 769 then decide (25 ≤ count744 b) else (if i < 770 then decide (26 ≤ count744 b) else decide (27 ≤ count744 b))) else (if i < 773 then (if i < 772 then decide (28 ≤ count744 b) else decide (29 ≤ count744 b)) else (if i < 774 then decide (30 ≤ count744 b) else decide (31 ≤ count744 b)))) else (if i < 778 then (if i < 776 then decide (1 ≤ count775 b) else (if i < 777 then decide (2 ≤ count775 b) else decide (3 ≤ count775 b))) else (if i < 780 then (if i < 779 then decide (4 ≤ count775 b) else decide (5 ≤ count775 b)) else (if i < 781 then decide (6 ≤ count775 b) else decide (7 ≤ count775 b)))))) else (if i < 795 then (if i < 788 then (if i < 785 then (if i < 783 then decide (8 ≤ count775 b) else (if i < 784 then decide (9 ≤ count775 b) else decide (10 ≤ count775 b))) else (if i < 786 then decide (11 ≤ count775 b) else (if i < 787 then decide (12 ≤ count775 b) else decide (13 ≤ count775 b)))) else (if i < 791 then (if i < 789 then decide (14 ≤ count775 b) else (if i < 790 then decide (15 ≤ count775 b) else decide (16 ≤ count775 b))) else (if i < 793 then (if i < 792 then decide (17 ≤ count775 b) else decide (18 ≤ count775 b)) else (if i < 794 then decide (19 ≤ count775 b) else decide (20 ≤ count775 b))))) else (if i < 802 then (if i < 798 then (if i < 796 then decide (21 ≤ count775 b) else (if i < 797 then decide (22 ≤ count775 b) else decide (23 ≤ count775 b))) else (if i < 800 then (if i < 799 then decide (24 ≤ count775 b) else decide (25 ≤ count775 b)) else (if i < 801 then decide (26 ≤ count775 b) else decide (27 ≤ count775 b)))) else (if i < 805 then (if i < 803 then decide (28 ≤ count775 b) else (if i < 804 then decide (29 ≤ count775 b) else decide (30 ≤ count775 b))) else (if i < 807 then (if i < 806 then decide (31 ≤ count775 b) else decide (32 ≤ count775 b)) else (if i < 808 then decide (33 ≤ count775 b) else decide (34 ≤ count775 b))))))) else (if i < 836 then (if i < 822 then (if i < 815 then (if i < 812 then (if i < 810 then decide (35 ≤ count775 b) else (if i < 811 then decide (36 ≤ count775 b) else decide (37 ≤ count775 b))) else (if i < 813 then decide (38 ≤ count775 b) else (if i < 814 then decide (39 ≤ count775 b) else decide (40 ≤ count775 b)))) else (if i < 818 then (if i < 816 then decide (41 ≤ count775 b) else (if i < 817 then decide (42 ≤ count775 b) else decide (1 ≤ count817 b))) else (if i < 820 then (if i < 819 then decide (2 ≤ count817 b) else decide (1 ≤ count819 b)) else (if i < 821 then decide (2 ≤ count819 b) else decide (3 ≤ count819 b))))) else (if i < 829 then (if i < 825 then (if i < 823 then decide (1 ≤ count822 b) else (if i < 824 then decide (2 ≤ count822 b) else decide (1 ≤ count824 b))) else (if i < 827 then (if i < 826 then decide (2 ≤ count824 b) else decide (1 ≤ count826 b)) else (if i < 828 then decide (2 ≤ count826 b) else decide (3 ≤ count826 b)))) else (if i < 832 then (if i < 830 then decide (4 ≤ count826 b) else (if i < 831 then decide (1 ≤ count830 b) else decide (2 ≤ count830 b))) else (if i < 834 then (if i < 833 then decide (3 ≤ count830 b) else decide (4 ≤ count830 b)) else (if i < 835 then decide (5 ≤ count830 b) else decide (6 ≤ count830 b)))))) else (if i < 849 then (if i < 842 then (if i < 839 then (if i < 837 then decide (7 ≤ count830 b) else (if i < 838 then decide (1 ≤ count837 b) else decide (2 ≤ count837 b))) else (if i < 840 then decide (1 ≤ count839 b) else (if i < 841 then decide (2 ≤ count839 b) else decide (1 ≤ count841 b)))) else (if i < 845 then (if i < 843 then decide (2 ≤ count841 b) else (if i < 844 then decide (3 ≤ count841 b) else decide (4 ≤ count841 b))) else (if i < 847 then (if i < 846 then decide (1 ≤ count845 b) else decide (2 ≤ count845 b)) else (if i < 848 then decide (1 ≤ count847 b) else decide (2 ≤ count847 b))))) else (if i < 856 then (if i < 852 then (if i < 850 then decide (1 ≤ count849 b) else (if i < 851 then decide (2 ≤ count849 b) else decide (3 ≤ count849 b))) else (if i < 854 then (if i < 853 then decide (4 ≤ count849 b) else decide (1 ≤ count853 b)) else (if i < 855 then decide (2 ≤ count853 b) else decide (3 ≤ count853 b)))) else (if i < 859 then (if i < 857 then decide (4 ≤ count853 b) else (if i < 858 then decide (5 ≤ count853 b) else decide (6 ≤ count853 b))) else (if i < 861 then (if i < 860 then decide (7 ≤ count853 b) else decide (8 ≤ count853 b)) else (if i < 862 then decide (1 ≤ count861 b) else decide (2 ≤ count861 b))))))))))) else (if i < 1295 then (if i < 1079 then (if i < 971 then (if i < 917 then (if i < 890 then (if i < 876 then (if i < 869 then (if i < 866 then (if i < 864 then decide (3 ≤ count861 b) else (if i < 865 then decide (4 ≤ count861 b) else decide (5 ≤ count861 b))) else (if i < 867 then decide (6 ≤ count861 b) else (if i < 868 then decide (7 ≤ count861 b) else decide (8 ≤ count861 b)))) else (if i < 872 then (if i < 870 then decide (9 ≤ count861 b) else (if i < 871 then decide (10 ≤ count861 b) else decide (11 ≤ count861 b))) else (if i < 874 then (if i < 873 then decide (12 ≤ count861 b) else decide (13 ≤ count861 b)) else (if i < 875 then decide (14 ≤ count861 b) else decide (15 ≤ count861 b))))) else (if i < 883 then (if i < 879 then (if i < 877 then decide (1 ≤ count876 b) else (if i < 878 then decide (2 ≤ count876 b) else decide (1 ≤ count878 b))) else (if i < 881 then (if i < 880 then decide (2 ≤ count878 b) else decide (3 ≤ count878 b)) else (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b)))) else (if i < 886 then (if i < 884 then decide (1 ≤ count883 b) else (if i < 885 then decide (2 ≤ count883 b) else decide (1 ≤ count885 b))) else (if i < 888 then (if i < 887 then decide (2 ≤ count885 b) else decide (3 ≤ count885 b)) else (if i < 889 then decide (4 ≤ count885 b) else decide (1 ≤ count889 b)))))) else (if i < 903 then (if i < 896 then (if i < 893 then (if i < 891 then decide (2 ≤ count889 b) else (if i < 892 then decide (3 ≤ count889 b) else decide (4 ≤ count889 b))) else (if i < 894 then decide (5 ≤ count889 b) else (if i < 895 then decide (6 ≤ count889 b) else decide (7 ≤ count889 b)))) else (if i < 899 then (if i < 897 then decide (1 ≤ count896 b) else (if i < 898 then decide (2 ≤ count896 b) else decide (1 ≤ count898 b))) else (if i < 901 then (if i < 900 then decide (2 ≤ count898 b) else decide (1 ≤ count900 b)) else (if i < 902 then decide (2 ≤ count900 b) else decide (3 ≤ count900 b))))) else (if i < 910 then (if i < 906 then (if i < 904 then decide (4 ≤ count900 b) else (if i < 905 then decide (1 ≤ count904 b) else decide (2 ≤ count904 b))) else (if i < 908 then (if i < 907 then decide (1 ≤ count906 b) else decide (2 ≤ count906 b)) else (if i < 909 then decide (1 ≤ count908 b) else decide (2 ≤ count908 b)))) else (if i < 913 then (if i < 911 then decide (3 ≤ count908 b) else (if i < 912 then decide (4 ≤ count908 b) else decide (1 ≤ count912 b))) else (if i < 915 then (if i < 914 then decide (2 ≤ count912 b) else decide (3 ≤ count912 b)) else (if i < 916 then decide (4 ≤ count912 b) else decide (5 ≤ count912 b))))))) else (if i < 944 then (if i < 930 then (if i < 923 then (if i < 920 then (if i < 918 then decide (6 ≤ count912 b) else (if i < 919 then decide (7 ≤ count912 b) else decide (8 ≤ count912 b))) else (if i < 921 then decide (1 ≤ count920 b) else (if i < 922 then decide (2 ≤ count920 b) else decide (3 ≤ count920 b)))) else (if i < 926 then (if i < 924 then decide (4 ≤ count920 b) else (if i < 925 then decide (5 ≤ count920 b) else decide (6 ≤ count920 b))) else (if i < 928 then (if i < 927 then decide (7 ≤ count920 b) else decide (8 ≤ count920 b)) else (if i < 929 then decide (9 ≤ count920 b) else decide (10 ≤ count920 b))))) else (if i < 937 then (if i < 933 then (if i < 931 then decide (11 ≤ count920 b) else (if i < 932 then decide (12 ≤ count920 b) else decide (13 ≤ count920 b))) else (if i < 935 then (if i < 934 then decide (14 ≤ count920 b) else decide (15 ≤ count920 b)) else (if i < 936 then decide (1 ≤ count935 b) else decide (2 ≤ count935 b)))) else (if i < 940 then (if i < 938 then decide (3 ≤ count935 b) else (if i < 939 then decide (4 ≤ count935 b) else decide (5 ≤ count935 b))) else (if i < 942 then (if i < 941 then decide (6 ≤ count935 b) else decide (7 ≤ count935 b)) else (if i < 943 then decide (8 ≤ count935 b) else decide (9 ≤ count935 b)))))) else (if i < 957 then (if i < 950 then (if i < 947 then (if i < 945 then decide (10 ≤ count935 b) else (if i < 946 then decide (11 ≤ count935 b) else decide (12 ≤ count935 b))) else (if i < 948 then decide (13 ≤ count935 b) else (if i < 949 then decide (14 ≤ count935 b) else decide (15 ≤ count935 b)))) else (if i < 953 then (if i < 951 then decide (16 ≤ count935 b) else (if i < 952 then decide (17 ≤ count935 b) else decide (18 ≤ count935 b))) else (if i < 955 then (if i < 954 then decide (19 ≤ count935 b) else decide (20 ≤ count935 b)) else (if i < 956 then decide (21 ≤ count935 b) else decide (1 ≤ count956 b))))) else (if i < 964 then (if i < 960 then (if i < 958 then decide (2 ≤ count956 b) else (if i < 959 then decide (1 ≤ count958 b) else decide (2 ≤ count958 b))) else (if i < 962 then (if i < 961 then decide (3 ≤ count958 b) else decide (1 ≤ count961 b)) else (if i < 963 then decide (2 ≤ count961 b) else decide (1 ≤ count963 b)))) else (if i < 967 then (if i < 965 then decide (2 ≤ count963 b) else (if i < 966 then decide (1 ≤ count965 b) else decide (2 ≤ count965 b))) else (if i < 969 then (if i < 968 then decide (3 ≤ count965 b) else decide (4 ≤ count965 b)) else (if i < 970 then decide (1 ≤ count969 b) else decide (2 ≤ count969 b)))))))) else (if i < 1025 then (if i < 998 then (if i < 984 then (if i < 977 then (if i < 974 then (if i < 972 then decide (3 ≤ count969 b) else (if i < 973 then decide (4 ≤ count969 b) else decide (5 ≤ count969 b))) else (if i < 975 then decide (6 ≤ count969 b) else (if i < 976 then decide (7 ≤ count969 b) else decide (1 ≤ count976 b)))) else (if i < 980 then (if i < 978 then decide (2 ≤ count976 b) else (if i < 979 then decide (1 ≤ count978 b) else decide (2 ≤ count978 b))) else (if i < 982 then (if i < 981 then decide (1 ≤ count980 b) else decide (2 ≤ count980 b)) else (if i < 983 then decide (3 ≤ count980 b) else decide (4 ≤ count980 b))))) else (if i < 991 then (if i < 987 then (if i < 985 then decide (1 ≤ count984 b) else (if i < 986 then decide (2 ≤ count984 b) else decide (1 ≤ count986 b))) else (if i < 989 then (if i < 988 then decide (2 ≤ count986 b) else decide (1 ≤ count988 b)) else (if i < 990 then decide (2 ≤ count988 b) else decide (3 ≤ count988 b)))) else (if i < 994 then (if i < 992 then decide (4 ≤ count988 b) else (if i < 993 then decide (1 ≤ count992 b) else decide (2 ≤ count992 b))) else (if i < 996 then (if i < 995 then decide (3 ≤ count992 b) else decide (4 ≤ count992 b)) else (if i < 997 then decide (5 ≤ count992 b) else decide (6 ≤ count992 b)))))) else (if i < 1011 then (if i < 1004 then (if i < 1001 then (if i < 999 then decide (7 ≤ count992 b) else (if i < 1000 then decide (8 ≤ count992 b) else decide (1 ≤ count1000 b))) else (if i < 1002 then decide (2 ≤ count1000 b) else (if i < 1003 then decide (3 ≤ count1000 b) else decide (4 ≤ count1000 b)))) else (if i < 1007 then (if i < 1005 then decide (5 ≤ count1000 b) else (if i < 1006 then decide (6 ≤ count1000 b) else decide (7 ≤ count1000 b))) else (if i < 1009 then (if i < 1008 then decide (8 ≤ count1000 b) else decide (9 ≤ count1000 b)) else (if i < 1010 then decide (10 ≤ count1000 b) else decide (11 ≤ count1000 b))))) else (if i < 1018 then (if i < 1014 then (if i < 1012 then decide (12 ≤ count1000 b) else (if i < 1013 then decide (13 ≤ count1000 b) else decide (14 ≤ count1000 b))) else (if i < 1016 then (if i < 1015 then decide (15 ≤ count1000 b) else decide (1 ≤ count1015 b)) else (if i < 1017 then decide (2 ≤ count1015 b) else decide (1 ≤ count1017 b)))) else (if i < 1021 then (if i < 1019 then decide (2 ≤ count1017 b) else (if i < 1020 then decide (1 ≤ count1019 b) else decide (2 ≤ count1019 b))) else (if i < 1023 then (if i < 1022 then decide (3 ≤ count1019 b) else decide (4 ≤ count1019 b)) else (if i < 1024 then decide (1 ≤ count1023 b) else decide (2 ≤ count1023 b))))))) else (if i < 1052 then (if i < 1038 then (if i < 1031 then (if i < 1028 then (if i < 1026 then decide (1 ≤ count1025 b) else (if i < 1027 then decide (2 ≤ count1025 b) else decide (1 ≤ count1027 b))) else (if i < 1029 then decide (2 ≤ count1027 b) else (if i < 1030 then decide (3 ≤ count1027 b) else decide (4 ≤ count1027 b)))) else (if i < 1034 then (if i < 1032 then decide (1 ≤ count1031 b) else (if i < 1033 then decide (2 ≤ count1031 b) else decide (3 ≤ count1031 b))) else (if i < 1036 then (if i < 1035 then decide (4 ≤ count1031 b) else decide (5 ≤ count1031 b)) else (if i < 1037 then decide (6 ≤ count1031 b) else decide (7 ≤ count1031 b))))) else (if i < 1045 then (if i < 1041 then (if i < 1039 then decide (8 ≤ count1031 b) else (if i < 1040 then decide (1 ≤ count1039 b) else decide (2 ≤ count1039 b))) else (if i < 1043 then (if i < 1042 then decide (1 ≤ count1041 b) else decide (2 ≤ count1041 b)) else (if i < 1044 then decide (1 ≤ count1043 b) else decide (2 ≤ count1043 b)))) else (if i < 1048 then (if i < 1046 then decide (3 ≤ count1043 b) else (if i < 1047 then decide (4 ≤ count1043 b) else decide (1 ≤ count1047 b))) else (if i < 1050 then (if i < 1049 then decide (2 ≤ count1047 b) else decide (1 ≤ count1049 b)) else (if i < 1051 then decide (2 ≤ count1049 b) else decide (1 ≤ count1051 b)))))) else (if i < 1065 then (if i < 1058 then (if i < 1055 then (if i < 1053 then decide (2 ≤ count1051 b) else (if i < 1054 then decide (3 ≤ count1051 b) else decide (4 ≤ count1051 b))) else (if i < 1056 then decide (1 ≤ count1055 b) else (if i < 1057 then decide (2 ≤ count1055 b) else decide (3 ≤ count1055 b)))) else (if i < 1061 then (if i < 1059 then decide (4 ≤ count1055 b) else (if i < 1060 then decide (5 ≤ count1055 b) else decide (6 ≤ count1055 b))) else (if i < 1063 then (if i < 1062 then decide (7 ≤ count1055 b) else decide (8 ≤ count1055 b)) else (if i < 1064 then decide (1 ≤ count1063 b) else decide (2 ≤ count1063 b))))) else (if i < 1072 then (if i < 1068 then (if i < 1066 then decide (3 ≤ count1063 b) else (if i < 1067 then decide (4 ≤ count1063 b) else decide (5 ≤ count1063 b))) else (if i < 1070 then (if i < 1069 then decide (6 ≤ count1063 b) else decide (7 ≤ count1063 b)) else (if i < 1071 then decide (8 ≤ count1063 b) else decide (9 ≤ count1063 b)))) else (if i < 1075 then (if i < 1073 then decide (10 ≤ count1063 b) else (if i < 1074 then decide (11 ≤ count1063 b) else decide (12 ≤ count1063 b))) else (if i < 1077 then (if i < 1076 then decide (13 ≤ count1063 b) else decide (14 ≤ count1063 b)) else (if i < 1078 then decide (15 ≤ count1063 b) else decide (16 ≤ count1063 b))))))))) else (if i < 1187 then (if i < 1133 then (if i < 1106 then (if i < 1092 then (if i < 1085 then (if i < 1082 then (if i < 1080 then decide (1 ≤ count1079 b) else (if i < 1081 then decide (2 ≤ count1079 b) else decide (3 ≤ count1079 b))) else (if i < 1083 then decide (4 ≤ count1079 b) else (if i < 1084 then decide (5 ≤ count1079 b) else decide (6 ≤ count1079 b)))) else (if i < 1088 then (if i < 1086 then decide (7 ≤ count1079 b) else (if i < 1087 then decide (8 ≤ count1079 b) else decide (9 ≤ count1079 b))) else (if i < 1090 then (if i < 1089 then decide (10 ≤ count1079 b) else decide (11 ≤ count1079 b)) else (if i < 1091 then decide (12 ≤ count1079 b) else decide (13 ≤ count1079 b))))) else (if i < 1099 then (if i < 1095 then (if i < 1093 then decide (14 ≤ count1079 b) else (if i < 1094 then decide (15 ≤ count1079 b) else decide (16 ≤ count1079 b))) else (if i < 1097 then (if i < 1096 then decide (17 ≤ count1079 b) else decide (18 ≤ count1079 b)) else (if i < 1098 then decide (19 ≤ count1079 b) else decide (20 ≤ count1079 b)))) else (if i < 1102 then (if i < 1100 then decide (21 ≤ count1079 b) else (if i < 1101 then decide (1 ≤ count1100 b) else decide (2 ≤ count1100 b))) else (if i < 1104 then (if i < 1103 then decide (3 ≤ count1100 b) else decide (4 ≤ count1100 b)) else (if i < 1105 then decide (5 ≤ count1100 b) else decide (6 ≤ count1100 b)))))) else (if i < 1119 then (if i < 1112 then (if i < 1109 then (if i < 1107 then decide (7 ≤ count1100 b) else (if i < 1108 then decide (8 ≤ count1100 b) else decide (9 ≤ count1100 b))) else (if i < 1110 then decide (10 ≤ count1100 b) else (if i < 1111 then decide (11 ≤ count1100 b) else decide (12 ≤ count1100 b)))) else (if i < 1115 then (if i < 1113 then decide (13 ≤ count1100 b) else (if i < 1114 then decide (14 ≤ count1100 b) else decide (15 ≤ count1100 b))) else (if i < 1117 then (if i < 1116 then decide (16 ≤ count1100 b) else decide (17 ≤ count1100 b)) else (if i < 1118 then decide (18 ≤ count1100 b) else decide (19 ≤ count1100 b))))) else (if i < 1126 then (if i < 1122 then (if i < 1120 then decide (20 ≤ count1100 b) else (if i < 1121 then decide (21 ≤ count1100 b) else decide (1 ≤ count1121 b))) else (if i < 1124 then (if i < 1123 then decide (2 ≤ count1121 b) else decide (1 ≤ count1123 b)) else (if i < 1125 then decide (2 ≤ count1123 b) else decide (3 ≤ count1123 b)))) else (if i < 1129 then (if i < 1127 then decide (1 ≤ count1126 b) else (if i < 1128 then decide (2 ≤ count1126 b) else decide (1 ≤ count1128 b))) else (if i < 1131 then (if i < 1130 then decide (2 ≤ count1128 b) else decide (1 ≤ count1130 b)) else (if i < 1132 then decide (2 ≤ count1130 b) else decide (3 ≤ count1130 b))))))) else (if i < 1160 then (if i < 1146 then (if i < 1139 then (if i < 1136 then (if i < 1134 then decide (4 ≤ count1130 b) else (if i < 1135 then decide (1 ≤ count1134 b) else decide (2 ≤ count1134 b))) else (if i < 1137 then decide (3 ≤ count1134 b) else (if i < 1138 then decide (4 ≤ count1134 b) else decide (5 ≤ count1134 b)))) else (if i < 1142 then (if i < 1140 then decide (6 ≤ count1134 b) else (if i < 1141 then decide (7 ≤ count1134 b) else decide (1 ≤ count1141 b))) else (if i < 1144 then (if i < 1143 then decide (2 ≤ count1141 b) else decide (1 ≤ count1143 b)) else (if i < 1145 then decide (2 ≤ count1143 b) else decide (3 ≤ count1143 b))))) else (if i < 1153 then (if i < 1149 then (if i < 1147 then decide (1 ≤ count1146 b) else (if i < 1148 then decide (2 ≤ count1146 b) else decide (1 ≤ count1148 b))) else (if i < 1151 then (if i < 1150 then decide (2 ≤ count1148 b) else decide (1 ≤ count1150 b)) else (if i < 1152 then decide (2 ≤ count1150 b) else decide (3 ≤ count1150 b)))) else (if i < 1156 then (if i < 1154 then decide (4 ≤ count1150 b) else (if i < 1155 then decide (1 ≤ count1154 b) else decide (2 ≤ count1154 b))) else (if i < 1158 then (if i < 1157 then decide (3 ≤ count1154 b) else decide (4 ≤ count1154 b)) else (if i < 1159 then decide (5 ≤ count1154 b) else decide (6 ≤ count1154 b)))))) else (if i < 1173 then (if i < 1166 then (if i < 1163 then (if i < 1161 then decide (7 ≤ count1154 b) else (if i < 1162 then decide (1 ≤ count1161 b) else decide (2 ≤ count1161 b))) else (if i < 1164 then decide (3 ≤ count1161 b) else (if i < 1165 then decide (4 ≤ count1161 b) else decide (5 ≤ count1161 b)))) else (if i < 1169 then (if i < 1167 then decide (6 ≤ count1161 b) else (if i < 1168 then decide (7 ≤ count1161 b) else decide (8 ≤ count1161 b))) else (if i < 1171 then (if i < 1170 then decide (9 ≤ count1161 b) else decide (10 ≤ count1161 b)) else (if i < 1172 then decide (11 ≤ count1161 b) else decide (12 ≤ count1161 b))))) else (if i < 1180 then (if i < 1176 then (if i < 1174 then decide (13 ≤ count1161 b) else (if i < 1175 then decide (14 ≤ count1161 b) else decide (1 ≤ count1175 b))) else (if i < 1178 then (if i < 1177 then decide (2 ≤ count1175 b) else decide (1 ≤ count1177 b)) else (if i < 1179 then decide (2 ≤ count1177 b) else decide (3 ≤ count1177 b)))) else (if i < 1183 then (if i < 1181 then decide (1 ≤ count1180 b) else (if i < 1182 then decide (2 ≤ count1180 b) else decide (1 ≤ count1182 b))) else (if i < 1185 then (if i < 1184 then decide (2 ≤ count1182 b) else decide (1 ≤ count1184 b)) else (if i < 1186 then decide (2 ≤ count1184 b) else decide (3 ≤ count1184 b)))))))) else (if i < 1241 then (if i < 1214 then (if i < 1200 then (if i < 1193 then (if i < 1190 then (if i < 1188 then decide (4 ≤ count1184 b) else (if i < 1189 then decide (1 ≤ count1188 b) else decide (2 ≤ count1188 b))) else (if i < 1191 then decide (3 ≤ count1188 b) else (if i < 1192 then decide (4 ≤ count1188 b) else decide (5 ≤ count1188 b)))) else (if i < 1196 then (if i < 1194 then decide (6 ≤ count1188 b) else (if i < 1195 then decide (7 ≤ count1188 b) else decide (1 ≤ count1195 b))) else (if i < 1198 then (if i < 1197 then decide (2 ≤ count1195 b) else decide (1 ≤ count1197 b)) else (if i < 1199 then decide (2 ≤ count1197 b) else decide (1 ≤ count1199 b))))) else (if i < 1207 then (if i < 1203 then (if i < 1201 then decide (2 ≤ count1199 b) else (if i < 1202 then decide (3 ≤ count1199 b) else decide (4 ≤ count1199 b))) else (if i < 1205 then (if i < 1204 then decide (1 ≤ count1203 b) else decide (2 ≤ count1203 b)) else (if i < 1206 then decide (1 ≤ count1205 b) else decide (2 ≤ count1205 b)))) else (if i < 1210 then (if i < 1208 then decide (1 ≤ count1207 b) else (if i < 1209 then decide (2 ≤ count1207 b) else decide (3 ≤ count1207 b))) else (if i < 1212 then (if i < 1211 then decide (4 ≤ count1207 b) else decide (1 ≤ count1211 b)) else (if i < 1213 then decide (2 ≤ count1211 b) else decide (3 ≤ count1211 b)))))) else (if i < 1227 then (if i < 1220 then (if i < 1217 then (if i < 1215 then decide (4 ≤ count1211 b) else (if i < 1216 then decide (5 ≤ count1211 b) else decide (6 ≤ count1211 b))) else (if i < 1218 then decide (7 ≤ count1211 b) else (if i < 1219 then decide (8 ≤ count1211 b) else decide (1 ≤ count1219 b)))) else (if i < 1223 then (if i < 1221 then decide (2 ≤ count1219 b) else (if i < 1222 then decide (3 ≤ count1219 b) else decide (4 ≤ count1219 b))) else (if i < 1225 then (if i < 1224 then decide (5 ≤ count1219 b) else decide (6 ≤ count1219 b)) else (if i < 1226 then decide (7 ≤ count1219 b) else decide (8 ≤ count1219 b))))) else (if i < 1234 then (if i < 1230 then (if i < 1228 then decide (9 ≤ count1219 b) else (if i < 1229 then decide (10 ≤ count1219 b) else decide (11 ≤ count1219 b))) else (if i < 1232 then (if i < 1231 then decide (12 ≤ count1219 b) else decide (13 ≤ count1219 b)) else (if i < 1233 then decide (14 ≤ count1219 b) else decide (15 ≤ count1219 b)))) else (if i < 1237 then (if i < 1235 then decide (1 ≤ count1234 b) else (if i < 1236 then decide (2 ≤ count1234 b) else decide (3 ≤ count1234 b))) else (if i < 1239 then (if i < 1238 then decide (4 ≤ count1234 b) else decide (5 ≤ count1234 b)) else (if i < 1240 then decide (6 ≤ count1234 b) else decide (7 ≤ count1234 b))))))) else (if i < 1268 then (if i < 1254 then (if i < 1247 then (if i < 1244 then (if i < 1242 then decide (8 ≤ count1234 b) else (if i < 1243 then decide (9 ≤ count1234 b) else decide (10 ≤ count1234 b))) else (if i < 1245 then decide (11 ≤ count1234 b) else (if i < 1246 then decide (12 ≤ count1234 b) else decide (13 ≤ count1234 b)))) else (if i < 1250 then (if i < 1248 then decide (14 ≤ count1234 b) else (if i < 1249 then decide (15 ≤ count1234 b) else decide (16 ≤ count1234 b))) else (if i < 1252 then (if i < 1251 then decide (17 ≤ count1234 b) else decide (18 ≤ count1234 b)) else (if i < 1253 then decide (19 ≤ count1234 b) else decide (20 ≤ count1234 b))))) else (if i < 1261 then (if i < 1257 then (if i < 1255 then decide (21 ≤ count1234 b) else (if i < 1256 then decide (22 ≤ count1234 b) else decide (23 ≤ count1234 b))) else (if i < 1259 then (if i < 1258 then decide (24 ≤ count1234 b) else decide (25 ≤ count1234 b)) else (if i < 1260 then decide (26 ≤ count1234 b) else decide (27 ≤ count1234 b)))) else (if i < 1264 then (if i < 1262 then decide (28 ≤ count1234 b) else (if i < 1263 then decide (29 ≤ count1234 b) else decide (1 ≤ count1263 b))) else (if i < 1266 then (if i < 1265 then decide (2 ≤ count1263 b) else decide (1 ≤ count1265 b)) else (if i < 1267 then decide (2 ≤ count1265 b) else decide (3 ≤ count1265 b)))))) else (if i < 1281 then (if i < 1274 then (if i < 1271 then (if i < 1269 then decide (1 ≤ count1268 b) else (if i < 1270 then decide (2 ≤ count1268 b) else decide (1 ≤ count1270 b))) else (if i < 1272 then decide (2 ≤ count1270 b) else (if i < 1273 then decide (1 ≤ count1272 b) else decide (2 ≤ count1272 b)))) else (if i < 1277 then (if i < 1275 then decide (3 ≤ count1272 b) else (if i < 1276 then decide (4 ≤ count1272 b) else decide (1 ≤ count1276 b))) else (if i < 1279 then (if i < 1278 then decide (2 ≤ count1276 b) else decide (3 ≤ count1276 b)) else (if i < 1280 then decide (4 ≤ count1276 b) else decide (5 ≤ count1276 b))))) else (if i < 1288 then (if i < 1284 then (if i < 1282 then decide (6 ≤ count1276 b) else (if i < 1283 then decide (7 ≤ count1276 b) else decide (1 ≤ count1283 b))) else (if i < 1286 then (if i < 1285 then decide (2 ≤ count1283 b) else decide (1 ≤ count1285 b)) else (if i < 1287 then decide (2 ≤ count1285 b) else decide (3 ≤ count1285 b)))) else (if i < 1291 then (if i < 1289 then decide (1 ≤ count1288 b) else (if i < 1290 then decide (2 ≤ count1288 b) else decide (1 ≤ count1290 b))) else (if i < 1293 then (if i < 1292 then decide (2 ≤ count1290 b) else decide (1 ≤ count1292 b)) else (if i < 1294 then decide (2 ≤ count1292 b) else decide (3 ≤ count1292 b)))))))))) else (if i < 1511 then (if i < 1403 then (if i < 1349 then (if i < 1322 then (if i < 1308 then (if i < 1301 then (if i < 1298 then (if i < 1296 then decide (4 ≤ count1292 b) else (if i < 1297 then decide (1 ≤ count1296 b) else decide (2 ≤ count1296 b))) else (if i < 1299 then decide (3 ≤ count1296 b) else (if i < 1300 then decide (4 ≤ count1296 b) else decide (5 ≤ count1296 b)))) else (if i < 1304 then (if i < 1302 then decide (6 ≤ count1296 b) else (if i < 1303 then decide (7 ≤ count1296 b) else decide (1 ≤ count1303 b))) else (if i < 1306 then (if i < 1305 then decide (2 ≤ count1303 b) else decide (3 ≤ count1303 b)) else (if i < 1307 then decide (4 ≤ count1303 b) else decide (5 ≤ count1303 b))))) else (if i < 1315 then (if i < 1311 then (if i < 1309 then decide (6 ≤ count1303 b) else (if i < 1310 then decide (7 ≤ count1303 b) else decide (8 ≤ count1303 b))) else (if i < 1313 then (if i < 1312 then decide (9 ≤ count1303 b) else decide (10 ≤ count1303 b)) else (if i < 1314 then decide (11 ≤ count1303 b) else decide (12 ≤ count1303 b)))) else (if i < 1318 then (if i < 1316 then decide (13 ≤ count1303 b) else (if i < 1317 then decide (14 ≤ count1303 b) else decide (1 ≤ count1317 b))) else (if i < 1320 then (if i < 1319 then decide (2 ≤ count1317 b) else decide (1 ≤ count1319 b)) else (if i < 1321 then decide (2 ≤ count1319 b) else decide (3 ≤ count1319 b)))))) else (if i < 1335 then (if i < 1328 then (if i < 1325 then (if i < 1323 then decide (1 ≤ count1322 b) else (if i < 1324 then decide (2 ≤ count1322 b) else decide (1 ≤ count1324 b))) else (if i < 1326 then decide (2 ≤ count1324 b) else (if i < 1327 then decide (1 ≤ count1326 b) else decide (2 ≤ count1326 b)))) else (if i < 1331 then (if i < 1329 then decide (3 ≤ count1326 b) else (if i < 1330 then decide (4 ≤ count1326 b) else decide (1 ≤ count1330 b))) else (if i < 1333 then (if i < 1332 then decide (2 ≤ count1330 b) else decide (3 ≤ count1330 b)) else (if i < 1334 then decide (4 ≤ count1330 b) else decide (5 ≤ count1330 b))))) else (if i < 1342 then (if i < 1338 then (if i < 1336 then decide (6 ≤ count1330 b) else (if i < 1337 then decide (7 ≤ count1330 b) else decide (1 ≤ count1337 b))) else (if i < 1340 then (if i < 1339 then decide (2 ≤ count1337 b) else decide (1 ≤ count1339 b)) else (if i < 1341 then decide (2 ≤ count1339 b) else decide (1 ≤ count1341 b)))) else (if i < 1345 then (if i < 1343 then decide (2 ≤ count1341 b) else (if i < 1344 then decide (3 ≤ count1341 b) else decide (4 ≤ count1341 b))) else (if i < 1347 then (if i < 1346 then decide (1 ≤ count1345 b) else decide (2 ≤ count1345 b)) else (if i < 1348 then decide (1 ≤ count1347 b) else decide (2 ≤ count1347 b))))))) else (if i < 1376 then (if i < 1362 then (if i < 1355 then (if i < 1352 then (if i < 1350 then decide (1 ≤ count1349 b) else (if i < 1351 then decide (2 ≤ count1349 b) else decide (3 ≤ count1349 b))) else (if i < 1353 then decide (4 ≤ count1349 b) else (if i < 1354 then decide (1 ≤ count1353 b) else decide (2 ≤ count1353 b)))) else (if i < 1358 then (if i < 1356 then decide (3 ≤ count1353 b) else (if i < 1357 then decide (4 ≤ count1353 b) else decide (5 ≤ count1353 b))) else (if i < 1360 then (if i < 1359 then decide (6 ≤ count1353 b) else decide (7 ≤ count1353 b)) else (if i < 1361 then decide (8 ≤ count1353 b) else decide (1 ≤ count1361 b))))) else (if i < 1369 then (if i < 1365 then (if i < 1363 then decide (2 ≤ count1361 b) else (if i < 1364 then decide (3 ≤ count1361 b) else decide (4 ≤ count1361 b))) else (if i < 1367 then (if i < 1366 then decide (5 ≤ count1361 b) else decide (6 ≤ count1361 b)) else (if i < 1368 then decide (7 ≤ count1361 b) else decide (8 ≤ count1361 b)))) else (if i < 1372 then (if i < 1370 then decide (9 ≤ count1361 b) else (if i < 1371 then decide (10 ≤ count1361 b) else decide (11 ≤ count1361 b))) else (if i < 1374 then (if i < 1373 then decide (12 ≤ count1361 b) else decide (13 ≤ count1361 b)) else (if i < 1375 then decide (14 ≤ count1361 b) else decide (15 ≤ count1361 b)))))) else (if i < 1389 then (if i < 1382 then (if i < 1379 then (if i < 1377 then decide (1 ≤ count1376 b) else (if i < 1378 then decide (2 ≤ count1376 b) else decide (3 ≤ count1376 b))) else (if i < 1380 then decide (4 ≤ count1376 b) else (if i < 1381 then decide (5 ≤ count1376 b) else decide (6 ≤ count1376 b)))) else (if i < 1385 then (if i < 1383 then decide (7 ≤ count1376 b) else (if i < 1384 then decide (8 ≤ count1376 b) else decide (9 ≤ count1376 b))) else (if i < 1387 then (if i < 1386 then decide (10 ≤ count1376 b) else decide (11 ≤ count1376 b)) else (if i < 1388 then decide (12 ≤ count1376 b) else decide (13 ≤ count1376 b))))) else (if i < 1396 then (if i < 1392 then (if i < 1390 then decide (14 ≤ count1376 b) else (if i < 1391 then decide (15 ≤ count1376 b) else decide (16 ≤ count1376 b))) else (if i < 1394 then (if i < 1393 then decide (17 ≤ count1376 b) else decide (18 ≤ count1376 b)) else (if i < 1395 then decide (19 ≤ count1376 b) else decide (20 ≤ count1376 b)))) else (if i < 1399 then (if i < 1397 then decide (21 ≤ count1376 b) else (if i < 1398 then decide (22 ≤ count1376 b) else decide (23 ≤ count1376 b))) else (if i < 1401 then (if i < 1400 then decide (24 ≤ count1376 b) else decide (25 ≤ count1376 b)) else (if i < 1402 then decide (26 ≤ count1376 b) else decide (27 ≤ count1376 b)))))))) else (if i < 1457 then (if i < 1430 then (if i < 1416 then (if i < 1409 then (if i < 1406 then (if i < 1404 then decide (28 ≤ count1376 b) else (if i < 1405 then decide (29 ≤ count1376 b) else decide (1 ≤ count1405 b))) else (if i < 1407 then decide (2 ≤ count1405 b) else (if i < 1408 then decide (3 ≤ count1405 b) else decide (4 ≤ count1405 b)))) else (if i < 1412 then (if i < 1410 then decide (5 ≤ count1405 b) else (if i < 1411 then decide (6 ≤ count1405 b) else decide (7 ≤ count1405 b))) else (if i < 1414 then (if i < 1413 then decide (8 ≤ count1405 b) else decide (9 ≤ count1405 b)) else (if i < 1415 then decide (10 ≤ count1405 b) else decide (11 ≤ count1405 b))))) else (if i < 1423 then (if i < 1419 then (if i < 1417 then decide (12 ≤ count1405 b) else (if i < 1418 then decide (13 ≤ count1405 b) else decide (14 ≤ count1405 b))) else (if i < 1421 then (if i < 1420 then decide (15 ≤ count1405 b) else decide (16 ≤ count1405 b)) else (if i < 1422 then decide (17 ≤ count1405 b) else decide (18 ≤ count1405 b)))) else (if i < 1426 then (if i < 1424 then decide (19 ≤ count1405 b) else (if i < 1425 then decide (20 ≤ count1405 b) else decide (21 ≤ count1405 b))) else (if i < 1428 then (if i < 1427 then decide (22 ≤ count1405 b) else decide (23 ≤ count1405 b)) else (if i < 1429 then decide (24 ≤ count1405 b) else decide (25 ≤ count1405 b)))))) else (if i < 1443 then (if i < 1436 then (if i < 1433 then (if i < 1431 then decide (26 ≤ count1405 b) else (if i < 1432 then decide (27 ≤ count1405 b) else decide (28 ≤ count1405 b))) else (if i < 1434 then decide (29 ≤ count1405 b) else (if i < 1435 then decide (30 ≤ count1405 b) else decide (31 ≤ count1405 b)))) else (if i < 1439 then (if i < 1437 then decide (32 ≤ count1405 b) else (if i < 1438 then decide (33 ≤ count1405 b) else decide (34 ≤ count1405 b))) else (if i < 1441 then (if i < 1440 then decide (35 ≤ count1405 b) else decide (36 ≤ count1405 b)) else (if i < 1442 then decide (37 ≤ count1405 b) else decide (38 ≤ count1405 b))))) else (if i < 1450 then (if i < 1446 then (if i < 1444 then decide (39 ≤ count1405 b) else (if i < 1445 then decide (40 ≤ count1405 b) else decide (41 ≤ count1405 b))) else (if i < 1448 then (if i < 1447 then decide (42 ≤ count1405 b) else decide (1 ≤ count1447 b)) else (if i < 1449 then decide (2 ≤ count1447 b) else decide (1 ≤ count1449 b)))) else (if i < 1453 then (if i < 1451 then decide (2 ≤ count1449 b) else (if i < 1452 then decide (3 ≤ count1449 b) else decide (1 ≤ count1452 b))) else (if i < 1455 then (if i < 1454 then decide (2 ≤ count1452 b) else decide (1 ≤ count1454 b)) else (if i < 1456 then decide (2 ≤ count1454 b) else decide (1 ≤ count1456 b))))))) else (if i < 1484 then (if i < 1470 then (if i < 1463 then (if i < 1460 then (if i < 1458 then decide (2 ≤ count1456 b) else (if i < 1459 then decide (3 ≤ count1456 b) else decide (4 ≤ count1456 b))) else (if i < 1461 then decide (1 ≤ count1460 b) else (if i < 1462 then decide (2 ≤ count1460 b) else decide (3 ≤ count1460 b)))) else (if i < 1466 then (if i < 1464 then decide (4 ≤ count1460 b) else (if i < 1465 then decide (5 ≤ count1460 b) else decide (6 ≤ count1460 b))) else (if i < 1468 then (if i < 1467 then decide (7 ≤ count1460 b) else decide (1 ≤ count1467 b)) else (if i < 1469 then decide (2 ≤ count1467 b) else decide (1 ≤ count1469 b))))) else (if i < 1477 then (if i < 1473 then (if i < 1471 then decide (2 ≤ count1469 b) else (if i < 1472 then decide (3 ≤ count1469 b) else decide (1 ≤ count1472 b))) else (if i < 1475 then (if i < 1474 then decide (2 ≤ count1472 b) else decide (1 ≤ count1474 b)) else (if i < 1476 then decide (2 ≤ count1474 b) else decide (1 ≤ count1476 b)))) else (if i < 1480 then (if i < 1478 then decide (2 ≤ count1476 b) else (if i < 1479 then decide (3 ≤ count1476 b) else decide (4 ≤ count1476 b))) else (if i < 1482 then (if i < 1481 then decide (1 ≤ count1480 b) else decide (2 ≤ count1480 b)) else (if i < 1483 then decide (3 ≤ count1480 b) else decide (4 ≤ count1480 b)))))) else (if i < 1497 then (if i < 1490 then (if i < 1487 then (if i < 1485 then decide (5 ≤ count1480 b) else (if i < 1486 then decide (6 ≤ count1480 b) else decide (7 ≤ count1480 b))) else (if i < 1488 then decide (1 ≤ count1487 b) else (if i < 1489 then decide (2 ≤ count1487 b) else decide (3 ≤ count1487 b)))) else (if i < 1493 then (if i < 1491 then decide (4 ≤ count1487 b) else (if i < 1492 then decide (5 ≤ count1487 b) else decide (6 ≤ count1487 b))) else (if i < 1495 then (if i < 1494 then decide (7 ≤ count1487 b) else decide (8 ≤ count1487 b)) else (if i < 1496 then decide (9 ≤ count1487 b) else decide (10 ≤ count1487 b))))) else (if i < 1504 then (if i < 1500 then (if i < 1498 then decide (11 ≤ count1487 b) else (if i < 1499 then decide (12 ≤ count1487 b) else decide (13 ≤ count1487 b))) else (if i < 1502 then (if i < 1501 then decide (14 ≤ count1487 b) else decide (1 ≤ count1501 b)) else (if i < 1503 then decide (2 ≤ count1501 b) else decide (1 ≤ count1503 b)))) else (if i < 1507 then (if i < 1505 then decide (2 ≤ count1503 b) else (if i < 1506 then decide (3 ≤ count1503 b) else decide (1 ≤ count1506 b))) else (if i < 1509 then (if i < 1508 then decide (2 ≤ count1506 b) else decide (1 ≤ count1508 b)) else (if i < 1510 then decide (2 ≤ count1508 b) else decide (1 ≤ count1510 b))))))))) else (if i < 1619 then (if i < 1565 then (if i < 1538 then (if i < 1524 then (if i < 1517 then (if i < 1514 then (if i < 1512 then decide (2 ≤ count1510 b) else (if i < 1513 then decide (3 ≤ count1510 b) else decide (4 ≤ count1510 b))) else (if i < 1515 then decide (1 ≤ count1514 b) else (if i < 1516 then decide (2 ≤ count1514 b) else decide (3 ≤ count1514 b)))) else (if i < 1520 then (if i < 1518 then decide (4 ≤ count1514 b) else (if i < 1519 then decide (5 ≤ count1514 b) else decide (6 ≤ count1514 b))) else (if i < 1522 then (if i < 1521 then decide (7 ≤ count1514 b) else decide (1 ≤ count1521 b)) else (if i < 1523 then decide (2 ≤ count1521 b) else decide (1 ≤ count1523 b))))) else (if i < 1531 then (if i < 1527 then (if i < 1525 then decide (2 ≤ count1523 b) else (if i < 1526 then decide (1 ≤ count1525 b) else decide (2 ≤ count1525 b))) else (if i < 1529 then (if i < 1528 then decide (3 ≤ count1525 b) else decide (4 ≤ count1525 b)) else (if i < 1530 then decide (1 ≤ count1529 b) else decide (2 ≤ count1529 b)))) else (if i < 1534 then (if i < 1532 then decide (1 ≤ count1531 b) else (if i < 1533 then decide (2 ≤ count1531 b) else decide (1 ≤ count1533 b))) else (if i < 1536 then (if i < 1535 then decide (2 ≤ count1533 b) else decide (3 ≤ count1533 b)) else (if i < 1537 then decide (4 ≤ count1533 b) else decide (1 ≤ count1537 b)))))) else (if i < 1551 then (if i < 1544 then (if i < 1541 then (if i < 1539 then decide (2 ≤ count1537 b) else (if i < 1540 then decide (3 ≤ count1537 b) else decide (4 ≤ count1537 b))) else (if i < 1542 then decide (5 ≤ count1537 b) else (if i < 1543 then decide (6 ≤ count1537 b) else decide (7 ≤ count1537 b)))) else (if i < 1547 then (if i < 1545 then decide (8 ≤ count1537 b) else (if i < 1546 then decide (1 ≤ count1545 b) else decide (2 ≤ count1545 b))) else (if i < 1549 then (if i < 1548 then decide (3 ≤ count1545 b) else decide (4 ≤ count1545 b)) else (if i < 1550 then decide (5 ≤ count1545 b) else decide (6 ≤ count1545 b))))) else (if i < 1558 then (if i < 1554 then (if i < 1552 then decide (7 ≤ count1545 b) else (if i < 1553 then decide (8 ≤ count1545 b) else decide (9 ≤ count1545 b))) else (if i < 1556 then (if i < 1555 then decide (10 ≤ count1545 b) else decide (11 ≤ count1545 b)) else (if i < 1557 then decide (12 ≤ count1545 b) else decide (13 ≤ count1545 b)))) else (if i < 1561 then (if i < 1559 then decide (14 ≤ count1545 b) else (if i < 1560 then decide (15 ≤ count1545 b) else decide (1 ≤ count1560 b))) else (if i < 1563 then (if i < 1562 then decide (2 ≤ count1560 b) else decide (3 ≤ count1560 b)) else (if i < 1564 then decide (4 ≤ count1560 b) else decide (5 ≤ count1560 b))))))) else (if i < 1592 then (if i < 1578 then (if i < 1571 then (if i < 1568 then (if i < 1566 then decide (6 ≤ count1560 b) else (if i < 1567 then decide (7 ≤ count1560 b) else decide (8 ≤ count1560 b))) else (if i < 1569 then decide (9 ≤ count1560 b) else (if i < 1570 then decide (10 ≤ count1560 b) else decide (11 ≤ count1560 b)))) else (if i < 1574 then (if i < 1572 then decide (12 ≤ count1560 b) else (if i < 1573 then decide (13 ≤ count1560 b) else decide (14 ≤ count1560 b))) else (if i < 1576 then (if i < 1575 then decide (15 ≤ count1560 b) else decide (16 ≤ count1560 b)) else (if i < 1577 then decide (17 ≤ count1560 b) else decide (18 ≤ count1560 b))))) else (if i < 1585 then (if i < 1581 then (if i < 1579 then decide (1 ≤ count1578 b) else (if i < 1580 then decide (2 ≤ count1578 b) else decide (1 ≤ count1580 b))) else (if i < 1583 then (if i < 1582 then decide (2 ≤ count1580 b) else decide (3 ≤ count1580 b)) else (if i < 1584 then decide (1 ≤ count1583 b) else decide (2 ≤ count1583 b)))) else (if i < 1588 then (if i < 1586 then decide (1 ≤ count1585 b) else (if i < 1587 then decide (2 ≤ count1585 b) else decide (1 ≤ count1587 b))) else (if i < 1590 then (if i < 1589 then decide (2 ≤ count1587 b) else decide (3 ≤ count1587 b)) else (if i < 1591 then decide (4 ≤ count1587 b) else decide (1 ≤ count1591 b)))))) else (if i < 1605 then (if i < 1598 then (if i < 1595 then (if i < 1593 then decide (2 ≤ count1591 b) else (if i < 1594 then decide (3 ≤ count1591 b) else decide (4 ≤ count1591 b))) else (if i < 1596 then decide (5 ≤ count1591 b) else (if i < 1597 then decide (6 ≤ count1591 b) else decide (7 ≤ count1591 b)))) else (if i < 1601 then (if i < 1599 then decide (1 ≤ count1598 b) else (if i < 1600 then decide (2 ≤ count1598 b) else decide (1 ≤ count1600 b))) else (if i < 1603 then (if i < 1602 then decide (2 ≤ count1600 b) else decide (3 ≤ count1600 b)) else (if i < 1604 then decide (1 ≤ count1603 b) else decide (2 ≤ count1603 b))))) else (if i < 1612 then (if i < 1608 then (if i < 1606 then decide (1 ≤ count1605 b) else (if i < 1607 then decide (2 ≤ count1605 b) else decide (1 ≤ count1607 b))) else (if i < 1610 then (if i < 1609 then decide (2 ≤ count1607 b) else decide (3 ≤ count1607 b)) else (if i < 1611 then decide (4 ≤ count1607 b) else decide (1 ≤ count1611 b)))) else (if i < 1615 then (if i < 1613 then decide (2 ≤ count1611 b) else (if i < 1614 then decide (3 ≤ count1611 b) else decide (4 ≤ count1611 b))) else (if i < 1617 then (if i < 1616 then decide (5 ≤ count1611 b) else decide (6 ≤ count1611 b)) else (if i < 1618 then decide (7 ≤ count1611 b) else decide (1 ≤ count1618 b)))))))) else (if i < 1673 then (if i < 1646 then (if i < 1632 then (if i < 1625 then (if i < 1622 then (if i < 1620 then decide (2 ≤ count1618 b) else (if i < 1621 then decide (3 ≤ count1618 b) else decide (4 ≤ count1618 b))) else (if i < 1623 then decide (5 ≤ count1618 b) else (if i < 1624 then decide (6 ≤ count1618 b) else decide (7 ≤ count1618 b)))) else (if i < 1628 then (if i < 1626 then decide (8 ≤ count1618 b) else (if i < 1627 then decide (9 ≤ count1618 b) else decide (10 ≤ count1618 b))) else (if i < 1630 then (if i < 1629 then decide (11 ≤ count1618 b) else decide (12 ≤ count1618 b)) else (if i < 1631 then decide (13 ≤ count1618 b) else decide (14 ≤ count1618 b))))) else (if i < 1639 then (if i < 1635 then (if i < 1633 then decide (1 ≤ count1632 b) else (if i < 1634 then decide (2 ≤ count1632 b) else decide (1 ≤ count1634 b))) else (if i < 1637 then (if i < 1636 then decide (2 ≤ count1634 b) else decide (3 ≤ count1634 b)) else (if i < 1638 then decide (1 ≤ count1637 b) else decide (2 ≤ count1637 b)))) else (if i < 1642 then (if i < 1640 then decide (1 ≤ count1639 b) else (if i < 1641 then decide (2 ≤ count1639 b) else decide (1 ≤ count1641 b))) else (if i < 1644 then (if i < 1643 then decide (2 ≤ count1641 b) else decide (3 ≤ count1641 b)) else (if i < 1645 then decide (4 ≤ count1641 b) else decide (1 ≤ count1645 b)))))) else (if i < 1659 then (if i < 1652 then (if i < 1649 then (if i < 1647 then decide (2 ≤ count1645 b) else (if i < 1648 then decide (3 ≤ count1645 b) else decide (4 ≤ count1645 b))) else (if i < 1650 then decide (5 ≤ count1645 b) else (if i < 1651 then decide (6 ≤ count1645 b) else decide (7 ≤ count1645 b)))) else (if i < 1655 then (if i < 1653 then decide (1 ≤ count1652 b) else (if i < 1654 then decide (2 ≤ count1652 b) else decide (1 ≤ count1654 b))) else (if i < 1657 then (if i < 1656 then decide (2 ≤ count1654 b) else decide (1 ≤ count1656 b)) else (if i < 1658 then decide (2 ≤ count1656 b) else decide (3 ≤ count1656 b))))) else (if i < 1666 then (if i < 1662 then (if i < 1660 then decide (4 ≤ count1656 b) else (if i < 1661 then decide (1 ≤ count1660 b) else decide (2 ≤ count1660 b))) else (if i < 1664 then (if i < 1663 then decide (1 ≤ count1662 b) else decide (2 ≤ count1662 b)) else (if i < 1665 then decide (1 ≤ count1664 b) else decide (2 ≤ count1664 b)))) else (if i < 1669 then (if i < 1667 then decide (3 ≤ count1664 b) else (if i < 1668 then decide (4 ≤ count1664 b) else decide (1 ≤ count1668 b))) else (if i < 1671 then (if i < 1670 then decide (2 ≤ count1668 b) else decide (3 ≤ count1668 b)) else (if i < 1672 then decide (4 ≤ count1668 b) else decide (5 ≤ count1668 b))))))) else (if i < 1700 then (if i < 1686 then (if i < 1679 then (if i < 1676 then (if i < 1674 then decide (6 ≤ count1668 b) else (if i < 1675 then decide (7 ≤ count1668 b) else decide (8 ≤ count1668 b))) else (if i < 1677 then decide (1 ≤ count1676 b) else (if i < 1678 then decide (2 ≤ count1676 b) else decide (3 ≤ count1676 b)))) else (if i < 1682 then (if i < 1680 then decide (4 ≤ count1676 b) else (if i < 1681 then decide (5 ≤ count1676 b) else decide (6 ≤ count1676 b))) else (if i < 1684 then (if i < 1683 then decide (7 ≤ count1676 b) else decide (8 ≤ count1676 b)) else (if i < 1685 then decide (9 ≤ count1676 b) else decide (10 ≤ count1676 b))))) else (if i < 1693 then (if i < 1689 then (if i < 1687 then decide (11 ≤ count1676 b) else (if i < 1688 then decide (12 ≤ count1676 b) else decide (13 ≤ count1676 b))) else (if i < 1691 then (if i < 1690 then decide (14 ≤ count1676 b) else decide (15 ≤ count1676 b)) else (if i < 1692 then decide (1 ≤ count1691 b) else decide (2 ≤ count1691 b)))) else (if i < 1696 then (if i < 1694 then decide (3 ≤ count1691 b) else (if i < 1695 then decide (4 ≤ count1691 b) else decide (5 ≤ count1691 b))) else (if i < 1698 then (if i < 1697 then decide (6 ≤ count1691 b) else decide (7 ≤ count1691 b)) else (if i < 1699 then decide (8 ≤ count1691 b) else decide (9 ≤ count1691 b)))))) else (if i < 1713 then (if i < 1706 then (if i < 1703 then (if i < 1701 then decide (10 ≤ count1691 b) else (if i < 1702 then decide (11 ≤ count1691 b) else decide (12 ≤ count1691 b))) else (if i < 1704 then decide (13 ≤ count1691 b) else (if i < 1705 then decide (14 ≤ count1691 b) else decide (15 ≤ count1691 b)))) else (if i < 1709 then (if i < 1707 then decide (16 ≤ count1691 b) else (if i < 1708 then decide (17 ≤ count1691 b) else decide (18 ≤ count1691 b))) else (if i < 1711 then (if i < 1710 then decide (1 ≤ count1709 b) else decide (2 ≤ count1709 b)) else (if i < 1712 then decide (3 ≤ count1709 b) else decide (4 ≤ count1709 b))))) else (if i < 1720 then (if i < 1716 then (if i < 1714 then decide (5 ≤ count1709 b) else (if i < 1715 then decide (6 ≤ count1709 b) else decide (7 ≤ count1709 b))) else (if i < 1718 then (if i < 1717 then decide (8 ≤ count1709 b) else decide (9 ≤ count1709 b)) else (if i < 1719 then decide (10 ≤ count1709 b) else decide (11 ≤ count1709 b)))) else (if i < 1723 then (if i < 1721 then decide (12 ≤ count1709 b) else (if i < 1722 then decide (13 ≤ count1709 b) else decide (14 ≤ count1709 b))) else (if i < 1725 then (if i < 1724 then decide (15 ≤ count1709 b) else decide (16 ≤ count1709 b)) else (if i < 1726 then decide (17 ≤ count1709 b) else decide (18 ≤ count1709 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (7 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (9 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (13 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (15 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (17 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (18 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (19 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (22 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (26 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (28 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (29 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (30 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (66 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (70 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (78 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (102 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (105 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (109 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (111 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (118 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (122 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (124 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (125 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (126 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (160 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (161 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (166 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (167 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (168 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (169 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (171 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (173 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (175 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (177 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (178 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (179 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (182 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (186 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (188 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (189 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (190 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (288 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (289 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (294 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (295 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (296 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (297 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (299 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (301 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (303 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (305 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (306 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (307 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (308 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (310 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (314 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (316 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (317 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (318 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (354 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (356 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (357 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (358 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (359 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (361 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (362 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (364 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (366 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (372 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (373 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (375 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (376 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (377 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (378 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (379 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (383 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (416 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (417 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (418 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (420 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (421 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (422 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (423 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (424 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (426 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (427 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (428 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (430 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (431 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (433 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (435 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (436 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (437 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (439 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (440 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (441 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (442 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (443 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (447 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (480 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (481 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (485 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (486 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (488 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (491 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (493 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (495 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (496 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (497 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (498 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (499 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (502 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (504 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (508 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (509 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (510 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (7 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (70 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (78 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (105 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (109 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (111 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (124 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (126 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (178 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (289 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (297 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (299 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (301 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (303 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (307 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (310 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (314 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (316 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (317 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (318 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (354 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (361 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (362 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (364 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (366 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (372 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (375 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (377 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (379 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (383 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (424 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (441 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (485 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (504 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (510 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value292 (q : Snake 81) : valuation q 292 = decide (2 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value298 (q : Snake 81) : valuation q 298 = decide (2 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value320 (q : Snake 81) : valuation q 320 = decide (2 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value322 (q : Snake 81) : valuation q 322 = decide (2 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value332 (q : Snake 81) : valuation q 332 = decide (2 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value334 (q : Snake 81) : valuation q 334 = decide (2 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value350 (q : Snake 81) : valuation q 350 = decide (2 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value352 (q : Snake 81) : valuation q 352 = decide (2 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value380 (q : Snake 81) : valuation q 380 = decide (2 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value408 (q : Snake 81) : valuation q 408 = decide (2 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value422 (q : Snake 81) : valuation q 422 = decide (2 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value444 (q : Snake 81) : valuation q 444 = decide (2 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value448 (q : Snake 81) : valuation q 448 = decide (2 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value450 (q : Snake 81) : valuation q 450 = decide (2 ≤ count449 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value464 (q : Snake 81) : valuation q 464 = decide (2 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value466 (q : Snake 81) : valuation q 466 = decide (2 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value468 (q : Snake 81) : valuation q 468 = decide (2 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value470 (q : Snake 81) : valuation q 470 = decide (2 ≤ count469 (baseVal q)) := rfl
theorem value472 (q : Snake 81) : valuation q 472 = decide (2 ≤ count471 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (1 ≤ count1447 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (1 ≤ count1449 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (1 ≤ count1452 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (1 ≤ count1454 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (2 ≤ count1454 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (1 ≤ count1456 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (2 ≤ count1456 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (1 ≤ count1460 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (2 ≤ count1460 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (1 ≤ count1467 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (2 ≤ count1467 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (1 ≤ count1469 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (2 ≤ count1469 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (1 ≤ count1472 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (2 ≤ count1472 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (1 ≤ count1474 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (2 ≤ count1474 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (1 ≤ count1476 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (2 ≤ count1476 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (3 ≤ count1476 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (1 ≤ count1480 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (2 ≤ count1480 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (3 ≤ count1480 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (4 ≤ count1480 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (2 ≤ count1487 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (3 ≤ count1487 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (4 ≤ count1487 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (5 ≤ count1487 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (6 ≤ count1487 (baseVal q)) := rfl
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
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (1 ≤ count1514 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (2 ≤ count1514 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (3 ≤ count1514 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (4 ≤ count1514 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (5 ≤ count1514 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (1 ≤ count1521 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (2 ≤ count1521 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (1 ≤ count1523 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (2 ≤ count1523 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (1 ≤ count1525 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (2 ≤ count1525 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (3 ≤ count1525 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (1 ≤ count1529 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (2 ≤ count1529 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (1 ≤ count1531 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (1 ≤ count1533 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (2 ≤ count1533 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (3 ≤ count1533 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (1 ≤ count1537 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (2 ≤ count1537 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (3 ≤ count1537 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (4 ≤ count1537 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (2 ≤ count1545 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (3 ≤ count1545 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (4 ≤ count1545 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (5 ≤ count1545 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (6 ≤ count1545 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (5 ≤ count1560 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (6 ≤ count1560 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (7 ≤ count1560 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (8 ≤ count1560 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (1 ≤ count1578 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (2 ≤ count1578 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (1 ≤ count1580 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (3 ≤ count1580 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (1 ≤ count1583 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (2 ≤ count1583 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (1 ≤ count1585 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (2 ≤ count1585 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (1 ≤ count1587 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (2 ≤ count1587 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (3 ≤ count1587 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (1 ≤ count1591 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (2 ≤ count1591 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (3 ≤ count1591 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (4 ≤ count1591 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (1 ≤ count1598 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (2 ≤ count1598 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (1 ≤ count1600 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (2 ≤ count1600 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (3 ≤ count1600 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (1 ≤ count1603 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (2 ≤ count1603 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (1 ≤ count1605 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (2 ≤ count1605 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (1 ≤ count1607 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (2 ≤ count1607 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (3 ≤ count1607 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (4 ≤ count1607 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (1 ≤ count1611 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (2 ≤ count1611 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (3 ≤ count1611 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (4 ≤ count1611 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (5 ≤ count1611 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (2 ≤ count1618 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (3 ≤ count1618 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (4 ≤ count1618 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (5 ≤ count1618 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (6 ≤ count1618 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (7 ≤ count1618 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (8 ≤ count1618 (baseVal q)) := rfl
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
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (1 ≤ count1652 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (2 ≤ count1652 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (1 ≤ count1654 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (2 ≤ count1654 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (1 ≤ count1656 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (2 ≤ count1656 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (3 ≤ count1656 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (1 ≤ count1660 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (2 ≤ count1660 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (1 ≤ count1662 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (2 ≤ count1662 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (1 ≤ count1664 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (2 ≤ count1664 (baseVal q)) := rfl
theorem value1666 (q : Snake 81) : valuation q 1666 = decide (3 ≤ count1664 (baseVal q)) := rfl
theorem value1667 (q : Snake 81) : valuation q 1667 = decide (4 ≤ count1664 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (2 ≤ count1668 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (3 ≤ count1668 (baseVal q)) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (4 ≤ count1668 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (5 ≤ count1668 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (6 ≤ count1668 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (4 ≤ count1676 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (5 ≤ count1676 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (6 ≤ count1676 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (7 ≤ count1676 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (8 ≤ count1676 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (9 ≤ count1676 (baseVal q)) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (10 ≤ count1676 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (10 ≤ count1691 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (11 ≤ count1691 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (12 ≤ count1691 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (13 ≤ count1691 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (18 ≤ count1709 (baseVal q)) := rfl
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
theorem meaningNeg104 (b : Nat → Bool) : literal (valuationOf b) (-104) = decide (1 ≤ countLit b [-104]) := by
  change literal b (-104) = decide (1 ≤ countLit b [-104])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-104) <;> decide
theorem meaningNeg101 (b : Nat → Bool) : literal (valuationOf b) (-101) = decide (1 ≤ countLit b [-101]) := by
  change literal b (-101) = decide (1 ≤ countLit b [-101])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-101) <;> decide
theorem meaningNeg98 (b : Nat → Bool) : literal (valuationOf b) (-98) = decide (1 ≤ countLit b [-98]) := by
  change literal b (-98) = decide (1 ≤ countLit b [-98])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-98) <;> decide
theorem meaningNeg97 (b : Nat → Bool) : literal (valuationOf b) (-97) = decide (1 ≤ countLit b [-97]) := by
  change literal b (-97) = decide (1 ≤ countLit b [-97])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-97) <;> decide
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
theorem meaningNeg88 (b : Nat → Bool) : literal (valuationOf b) (-88) = decide (1 ≤ countLit b [-88]) := by
  change literal b (-88) = decide (1 ≤ countLit b [-88])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-88) <;> decide
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
theorem meaningNeg56 (b : Nat → Bool) : literal (valuationOf b) (-56) = decide (1 ≤ countLit b [-56]) := by
  change literal b (-56) = decide (1 ≤ countLit b [-56])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-56) <;> decide
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
theorem meaningNeg46 (b : Nat → Bool) : literal (valuationOf b) (-46) = decide (1 ≤ countLit b [-46]) := by
  change literal b (-46) = decide (1 ≤ countLit b [-46])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-46) <;> decide
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
theorem meaningNeg21 (b : Nat → Bool) : literal (valuationOf b) (-21) = decide (1 ≤ countLit b [-21]) := by
  change literal b (-21) = decide (1 ≤ countLit b [-21])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-21) <;> decide
theorem meaningNeg17 (b : Nat → Bool) : literal (valuationOf b) (-17) = decide (1 ≤ countLit b [-17]) := by
  change literal b (-17) = decide (1 ≤ countLit b [-17])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-17) <;> decide
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
theorem meaningNeg6 (b : Nat → Bool) : literal (valuationOf b) (-6) = decide (1 ≤ countLit b [-6]) := by
  change literal b (-6) = decide (1 ≤ countLit b [-6])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-6) <;> decide
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
theorem meaning142 (b : Nat → Bool) : literal (valuationOf b) (142) = decide (1 ≤ countLit b [142]) := by
  change literal b (142) = decide (1 ≤ countLit b [142])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (142) <;> decide
theorem meaning143 (b : Nat → Bool) : literal (valuationOf b) (143) = decide (1 ≤ countLit b [143]) := by
  change literal b (143) = decide (1 ≤ countLit b [143])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (143) <;> decide
theorem meaning144 (b : Nat → Bool) : literal (valuationOf b) (144) = decide (1 ≤ countLit b [144]) := by
  change literal b (144) = decide (1 ≤ countLit b [144])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (144) <;> decide
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
theorem meaning153 (b : Nat → Bool) : literal (valuationOf b) (153) = decide (1 ≤ countLit b [153]) := by
  change literal b (153) = decide (1 ≤ countLit b [153])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (153) <;> decide
theorem meaning154 (b : Nat → Bool) : literal (valuationOf b) (154) = decide (1 ≤ countLit b [154]) := by
  change literal b (154) = decide (1 ≤ countLit b [154])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (154) <;> decide
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
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
theorem meaning161 (b : Nat → Bool) : literal (valuationOf b) (161) = decide (1 ≤ countLit b [161]) := by
  change literal b (161) = decide (1 ≤ countLit b [161])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (161) <;> decide
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
theorem meaning175 (b : Nat → Bool) : literal (valuationOf b) (175) = decide (1 ≤ countLit b [175]) := by
  change literal b (175) = decide (1 ≤ countLit b [175])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (175) <;> decide
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
theorem meaning184 (b : Nat → Bool) : literal (valuationOf b) (184) = decide (1 ≤ countLit b [184]) := by
  change literal b (184) = decide (1 ≤ countLit b [184])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (184) <;> decide
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
theorem meaning197 (b : Nat → Bool) : literal (valuationOf b) (197) = decide (1 ≤ countLit b [197]) := by
  change literal b (197) = decide (1 ≤ countLit b [197])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (197) <;> decide
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
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
theorem meaning214 (b : Nat → Bool) : literal (valuationOf b) (214) = decide (1 ≤ countLit b [214]) := by
  change literal b (214) = decide (1 ≤ countLit b [214])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (214) <;> decide
theorem meaning216 (b : Nat → Bool) : literal (valuationOf b) (216) = decide (1 ≤ countLit b [216]) := by
  change literal b (216) = decide (1 ≤ countLit b [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (216) <;> decide
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) (217) = decide (1 ≤ countLit b [217]) := by
  change literal b (217) = decide (1 ≤ countLit b [217])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (217) <;> decide
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
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning292 (b : Nat → Bool) : literal (valuationOf b) 292 = decide (2 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning298 (b : Nat → Bool) : literal (valuationOf b) 298 = decide (2 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning320 (b : Nat → Bool) : literal (valuationOf b) 320 = decide (2 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning322 (b : Nat → Bool) : literal (valuationOf b) 322 = decide (2 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning332 (b : Nat → Bool) : literal (valuationOf b) 332 = decide (2 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning334 (b : Nat → Bool) : literal (valuationOf b) 334 = decide (2 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning350 (b : Nat → Bool) : literal (valuationOf b) 350 = decide (2 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning352 (b : Nat → Bool) : literal (valuationOf b) 352 = decide (2 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning380 (b : Nat → Bool) : literal (valuationOf b) 380 = decide (2 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning408 (b : Nat → Bool) : literal (valuationOf b) 408 = decide (2 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning422 (b : Nat → Bool) : literal (valuationOf b) 422 = decide (2 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning444 (b : Nat → Bool) : literal (valuationOf b) 444 = decide (2 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning448 (b : Nat → Bool) : literal (valuationOf b) 448 = decide (2 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning450 (b : Nat → Bool) : literal (valuationOf b) 450 = decide (2 ≤ count449 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning464 (b : Nat → Bool) : literal (valuationOf b) 464 = decide (2 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning466 (b : Nat → Bool) : literal (valuationOf b) 466 = decide (2 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning468 (b : Nat → Bool) : literal (valuationOf b) 468 = decide (2 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning470 (b : Nat → Bool) : literal (valuationOf b) 470 = decide (2 ≤ count469 b) := rfl
theorem meaning472 (b : Nat → Bool) : literal (valuationOf b) 472 = decide (2 ≤ count471 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (1 ≤ count1447 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (1 ≤ count1449 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (1 ≤ count1452 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (1 ≤ count1454 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (2 ≤ count1454 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (1 ≤ count1456 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (2 ≤ count1456 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (1 ≤ count1460 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (2 ≤ count1460 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (1 ≤ count1467 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (2 ≤ count1467 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (1 ≤ count1469 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (2 ≤ count1469 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (1 ≤ count1472 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (2 ≤ count1472 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (1 ≤ count1474 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (2 ≤ count1474 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (1 ≤ count1476 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (2 ≤ count1476 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (3 ≤ count1476 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (1 ≤ count1480 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (2 ≤ count1480 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (3 ≤ count1480 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (4 ≤ count1480 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (2 ≤ count1487 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (3 ≤ count1487 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (4 ≤ count1487 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (5 ≤ count1487 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (6 ≤ count1487 b) := rfl
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
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (1 ≤ count1514 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (2 ≤ count1514 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (3 ≤ count1514 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (4 ≤ count1514 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (5 ≤ count1514 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (1 ≤ count1521 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (2 ≤ count1521 b) := rfl
theorem meaning1523 (b : Nat → Bool) : literal (valuationOf b) 1523 = decide (1 ≤ count1523 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (2 ≤ count1523 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (1 ≤ count1525 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (2 ≤ count1525 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (3 ≤ count1525 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (1 ≤ count1529 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (2 ≤ count1529 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (1 ≤ count1531 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (1 ≤ count1533 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (2 ≤ count1533 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (3 ≤ count1533 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (1 ≤ count1537 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (2 ≤ count1537 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (3 ≤ count1537 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (4 ≤ count1537 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (2 ≤ count1545 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (3 ≤ count1545 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (4 ≤ count1545 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (5 ≤ count1545 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (6 ≤ count1545 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (5 ≤ count1560 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (6 ≤ count1560 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (7 ≤ count1560 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (8 ≤ count1560 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (1 ≤ count1578 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (2 ≤ count1578 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (1 ≤ count1580 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (3 ≤ count1580 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (1 ≤ count1583 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (2 ≤ count1583 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (1 ≤ count1585 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (2 ≤ count1585 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (1 ≤ count1587 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (2 ≤ count1587 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (3 ≤ count1587 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (1 ≤ count1591 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (2 ≤ count1591 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (3 ≤ count1591 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (4 ≤ count1591 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (1 ≤ count1598 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (2 ≤ count1598 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (1 ≤ count1600 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (2 ≤ count1600 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (3 ≤ count1600 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (1 ≤ count1603 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (2 ≤ count1603 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (1 ≤ count1605 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (2 ≤ count1605 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (1 ≤ count1607 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (2 ≤ count1607 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (3 ≤ count1607 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (4 ≤ count1607 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (1 ≤ count1611 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (2 ≤ count1611 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (3 ≤ count1611 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (4 ≤ count1611 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (5 ≤ count1611 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (2 ≤ count1618 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (3 ≤ count1618 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (4 ≤ count1618 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (5 ≤ count1618 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (6 ≤ count1618 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (7 ≤ count1618 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (8 ≤ count1618 b) := rfl
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
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (1 ≤ count1652 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (2 ≤ count1652 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (1 ≤ count1654 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (2 ≤ count1654 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (1 ≤ count1656 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (2 ≤ count1656 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (3 ≤ count1656 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (1 ≤ count1660 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (2 ≤ count1660 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (1 ≤ count1662 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (2 ≤ count1662 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (1 ≤ count1664 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (2 ≤ count1664 b) := rfl
theorem meaning1666 (b : Nat → Bool) : literal (valuationOf b) 1666 = decide (3 ≤ count1664 b) := rfl
theorem meaning1667 (b : Nat → Bool) : literal (valuationOf b) 1667 = decide (4 ≤ count1664 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (2 ≤ count1668 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (3 ≤ count1668 b) := rfl
theorem meaning1671 (b : Nat → Bool) : literal (valuationOf b) 1671 = decide (4 ≤ count1668 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (5 ≤ count1668 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (6 ≤ count1668 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (4 ≤ count1676 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (5 ≤ count1676 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (6 ≤ count1676 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (7 ≤ count1676 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (8 ≤ count1676 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (9 ≤ count1676 b) := rfl
theorem meaning1685 (b : Nat → Bool) : literal (valuationOf b) 1685 = decide (10 ≤ count1676 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (10 ≤ count1691 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (11 ≤ count1691 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (12 ≤ count1691 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (13 ≤ count1691 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (18 ≤ count1709 b) := rfl
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
end Snake9.Regrowth.E112187
