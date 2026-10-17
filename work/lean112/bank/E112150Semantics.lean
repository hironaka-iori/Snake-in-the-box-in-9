import E112150Data
namespace Snake9.Regrowth.E112150
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (12 : Vertex)) else decide (InPath q (13 : Vertex)))) else (if i < 4 then decide (InPath q (14 : Vertex)) else (if i < 5 then decide (InPath q (17 : Vertex)) else decide (InPath q (21 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (23 : Vertex)) else (if i < 8 then decide (InPath q (25 : Vertex)) else decide (InPath q (27 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (29 : Vertex)) else decide (InPath q (30 : Vertex))) else (if i < 12 then decide (InPath q (31 : Vertex)) else decide (InPath q (67 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (68 : Vertex)) else (if i < 15 then decide (InPath q (69 : Vertex)) else decide (InPath q (71 : Vertex)))) else (if i < 17 then decide (InPath q (72 : Vertex)) else (if i < 18 then decide (InPath q (74 : Vertex)) else decide (InPath q (75 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (79 : Vertex)) else (if i < 21 then decide (InPath q (80 : Vertex)) else decide (InPath q (81 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (84 : Vertex)) else decide (InPath q (86 : Vertex))) else (if i < 25 then decide (InPath q (88 : Vertex)) else decide (InPath q (89 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (94 : Vertex)) else (if i < 28 then decide (InPath q (95 : Vertex)) else decide (InPath q (131 : Vertex)))) else (if i < 30 then decide (InPath q (132 : Vertex)) else (if i < 31 then decide (InPath q (133 : Vertex)) else decide (InPath q (135 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (136 : Vertex)) else (if i < 34 then decide (InPath q (138 : Vertex)) else decide (InPath q (139 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (143 : Vertex)) else decide (InPath q (144 : Vertex))) else (if i < 38 then decide (InPath q (145 : Vertex)) else decide (InPath q (148 : Vertex)))))) else (if i < 46 then (if i < 42 then (if i < 40 then decide (InPath q (150 : Vertex)) else (if i < 41 then decide (InPath q (152 : Vertex)) else decide (InPath q (153 : Vertex)))) else (if i < 44 then (if i < 43 then decide (InPath q (158 : Vertex)) else decide (InPath q (159 : Vertex))) else (if i < 45 then decide (InPath q (227 : Vertex)) else decide (InPath q (228 : Vertex))))) else (if i < 49 then (if i < 47 then decide (InPath q (229 : Vertex)) else (if i < 48 then decide (InPath q (231 : Vertex)) else decide (InPath q (232 : Vertex)))) else (if i < 51 then (if i < 50 then decide (InPath q (234 : Vertex)) else decide (InPath q (235 : Vertex))) else (if i < 52 then decide (InPath q (239 : Vertex)) else decide (InPath q (240 : Vertex)))))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then decide (InPath q (241 : Vertex)) else (if i < 55 then decide (InPath q (244 : Vertex)) else decide (InPath q (246 : Vertex)))) else (if i < 57 then decide (InPath q (248 : Vertex)) else (if i < 58 then decide (InPath q (249 : Vertex)) else decide (InPath q (254 : Vertex))))) else (if i < 62 then (if i < 60 then decide (InPath q (255 : Vertex)) else (if i < 61 then decide (InPath q (356 : Vertex)) else decide (InPath q (357 : Vertex)))) else (if i < 64 then (if i < 63 then decide (InPath q (359 : Vertex)) else decide (InPath q (360 : Vertex))) else (if i < 65 then decide (InPath q (362 : Vertex)) else decide (InPath q (363 : Vertex)))))) else (if i < 72 then (if i < 69 then (if i < 67 then decide (InPath q (367 : Vertex)) else (if i < 68 then decide (InPath q (369 : Vertex)) else decide (InPath q (372 : Vertex)))) else (if i < 70 then decide (InPath q (374 : Vertex)) else (if i < 71 then decide (InPath q (376 : Vertex)) else decide (InPath q (377 : Vertex))))) else (if i < 75 then (if i < 73 then decide (InPath q (382 : Vertex)) else (if i < 74 then decide (InPath q (383 : Vertex)) else decide (InPath q (384 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (386 : Vertex)) else decide (InPath q (387 : Vertex))) else (if i < 78 then decide (InPath q (388 : Vertex)) else decide (InPath q (390 : Vertex))))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then decide (InPath q (396 : Vertex)) else (if i < 81 then decide (InPath q (397 : Vertex)) else decide (InPath q (398 : Vertex)))) else (if i < 83 then decide (InPath q (400 : Vertex)) else (if i < 84 then decide (InPath q (401 : Vertex)) else decide (InPath q (403 : Vertex))))) else (if i < 88 then (if i < 86 then decide (InPath q (405 : Vertex)) else (if i < 87 then decide (InPath q (407 : Vertex)) else decide (InPath q (409 : Vertex)))) else (if i < 90 then (if i < 89 then decide (InPath q (411 : Vertex)) else decide (InPath q (413 : Vertex))) else (if i < 91 then decide (InPath q (414 : Vertex)) else decide (InPath q (415 : Vertex)))))) else (if i < 99 then (if i < 95 then (if i < 93 then decide (InPath q (451 : Vertex)) else (if i < 94 then decide (InPath q (452 : Vertex)) else decide (InPath q (453 : Vertex)))) else (if i < 97 then (if i < 96 then decide (InPath q (455 : Vertex)) else decide (InPath q (463 : Vertex))) else (if i < 98 then decide (InPath q (464 : Vertex)) else decide (InPath q (465 : Vertex))))) else (if i < 102 then (if i < 100 then decide (InPath q (468 : Vertex)) else (if i < 101 then decide (InPath q (470 : Vertex)) else decide (InPath q (479 : Vertex)))) else (if i < 104 then (if i < 103 then decide (InPath q (497 : Vertex)) else decide (InPath q (501 : Vertex))) else (if i < 105 then decide (InPath q (503 : Vertex)) else decide (InPath q (507 : Vertex))))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then decide (InPath q (511 : Vertex)) else (if i < 108 then decide (BallClauseLogic.Endpoint q (12 : Vertex)) else decide (BallClauseLogic.Endpoint q (13 : Vertex)))) else (if i < 110 then decide (BallClauseLogic.Endpoint q (14 : Vertex)) else (if i < 111 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (21 : Vertex))))) else (if i < 115 then (if i < 113 then decide (BallClauseLogic.Endpoint q (23 : Vertex)) else (if i < 114 then decide (BallClauseLogic.Endpoint q (25 : Vertex)) else decide (BallClauseLogic.Endpoint q (27 : Vertex)))) else (if i < 117 then (if i < 116 then decide (BallClauseLogic.Endpoint q (29 : Vertex)) else decide (BallClauseLogic.Endpoint q (30 : Vertex))) else (if i < 118 then decide (BallClauseLogic.Endpoint q (31 : Vertex)) else decide (BallClauseLogic.Endpoint q (67 : Vertex)))))) else (if i < 125 then (if i < 122 then (if i < 120 then decide (BallClauseLogic.Endpoint q (68 : Vertex)) else (if i < 121 then decide (BallClauseLogic.Endpoint q (69 : Vertex)) else decide (BallClauseLogic.Endpoint q (71 : Vertex)))) else (if i < 123 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (74 : Vertex)) else decide (BallClauseLogic.Endpoint q (75 : Vertex))))) else (if i < 128 then (if i < 126 then decide (BallClauseLogic.Endpoint q (79 : Vertex)) else (if i < 127 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else decide (BallClauseLogic.Endpoint q (81 : Vertex)))) else (if i < 130 then (if i < 129 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (86 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (88 : Vertex)) else decide (BallClauseLogic.Endpoint q (89 : Vertex))))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then decide (BallClauseLogic.Endpoint q (94 : Vertex)) else (if i < 134 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else decide (BallClauseLogic.Endpoint q (131 : Vertex)))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (135 : Vertex))))) else (if i < 141 then (if i < 139 then decide (BallClauseLogic.Endpoint q (136 : Vertex)) else (if i < 140 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex)))) else (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (143 : Vertex)) else decide (BallClauseLogic.Endpoint q (144 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (145 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex)))))) else (if i < 152 then (if i < 148 then (if i < 146 then decide (BallClauseLogic.Endpoint q (150 : Vertex)) else (if i < 147 then decide (BallClauseLogic.Endpoint q (152 : Vertex)) else decide (BallClauseLogic.Endpoint q (153 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (158 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (227 : Vertex)) else decide (BallClauseLogic.Endpoint q (228 : Vertex))))) else (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (231 : Vertex)) else decide (BallClauseLogic.Endpoint q (232 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (234 : Vertex)) else decide (BallClauseLogic.Endpoint q (235 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (239 : Vertex)) else decide (BallClauseLogic.Endpoint q (240 : Vertex)))))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (241 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (246 : Vertex)))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (248 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (249 : Vertex)) else decide (BallClauseLogic.Endpoint q (254 : Vertex))))) else (if i < 168 then (if i < 166 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (356 : Vertex)) else decide (BallClauseLogic.Endpoint q (357 : Vertex)))) else (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (360 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (362 : Vertex)) else decide (BallClauseLogic.Endpoint q (363 : Vertex)))))) else (if i < 179 then (if i < 175 then (if i < 173 then decide (BallClauseLogic.Endpoint q (367 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (369 : Vertex)) else decide (BallClauseLogic.Endpoint q (372 : Vertex)))) else (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (374 : Vertex)) else decide (BallClauseLogic.Endpoint q (376 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (377 : Vertex)) else decide (BallClauseLogic.Endpoint q (382 : Vertex))))) else (if i < 182 then (if i < 180 then decide (BallClauseLogic.Endpoint q (383 : Vertex)) else (if i < 181 then decide (BallClauseLogic.Endpoint q (384 : Vertex)) else decide (BallClauseLogic.Endpoint q (386 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (387 : Vertex)) else decide (BallClauseLogic.Endpoint q (388 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (390 : Vertex)) else decide (BallClauseLogic.Endpoint q (396 : Vertex))))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (398 : Vertex)) else decide (BallClauseLogic.Endpoint q (400 : Vertex)))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else (if i < 191 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else decide (BallClauseLogic.Endpoint q (405 : Vertex))))) else (if i < 195 then (if i < 193 then decide (BallClauseLogic.Endpoint q (407 : Vertex)) else (if i < 194 then decide (BallClauseLogic.Endpoint q (409 : Vertex)) else decide (BallClauseLogic.Endpoint q (411 : Vertex)))) else (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (413 : Vertex)) else decide (BallClauseLogic.Endpoint q (414 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (415 : Vertex)) else decide (BallClauseLogic.Endpoint q (451 : Vertex)))))) else (if i < 206 then (if i < 202 then (if i < 200 then decide (BallClauseLogic.Endpoint q (452 : Vertex)) else (if i < 201 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else decide (BallClauseLogic.Endpoint q (455 : Vertex)))) else (if i < 204 then (if i < 203 then decide (BallClauseLogic.Endpoint q (463 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))) else (if i < 205 then decide (BallClauseLogic.Endpoint q (465 : Vertex)) else decide (BallClauseLogic.Endpoint q (468 : Vertex))))) else (if i < 209 then (if i < 207 then decide (BallClauseLogic.Endpoint q (470 : Vertex)) else (if i < 208 then decide (BallClauseLogic.Endpoint q (479 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex)))) else (if i < 211 then (if i < 210 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else decide (BallClauseLogic.Endpoint q (503 : Vertex))) else (if i < 212 then decide (BallClauseLogic.Endpoint q (507 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count213 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count215 (b : Nat → Bool) : Nat := countLit b [107, 108, 109]
def count217 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count219 (b : Nat → Bool) : Nat := countLit b [110, 111, 112]
def count221 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112]
def count223 (b : Nat → Bool) : Nat := countLit b [114, 115]
def count225 (b : Nat → Bool) : Nat := countLit b [113, 114, 115]
def count227 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count229 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count231 (b : Nat → Bool) : Nat := countLit b [116, 117, 118, 119]
def count233 (b : Nat → Bool) : Nat := countLit b [113, 114, 115, 116, 117, 118, 119]
def count235 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
def count237 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count239 (b : Nat → Bool) : Nat := countLit b [120, 121, 122]
def count241 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count243 (b : Nat → Bool) : Nat := countLit b [123, 124, 125]
def count245 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125]
def count247 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count249 (b : Nat → Bool) : Nat := countLit b [126, 127, 128]
def count251 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count255 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [126, 127, 128, 129, 130, 131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count281 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count303 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count305 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]
def count313 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [159, 160, 161]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171]
def count337 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]
def count339 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [172, 173, 174]
def count343 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177]
def count349 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count357 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count377 (b : Nat → Bool) : Nat := countLit b [192, 193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count381 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count383 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count391 (b : Nat → Bool) : Nat := countLit b [199, 200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count395 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205]
def count399 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202, 203, 204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count403 (b : Nat → Bool) : Nat := countLit b [206, 207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count407 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count409 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212]
def count411 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209, 210, 211, 212]
def count413 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count419 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count421 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count423 (b : Nat → Bool) : Nat := countLit b [1, 4, 6]
def count426 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count428 (b : Nat → Bool) : Nat := countLit b [8, 9, 10]
def count431 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 8, 9, 10]
def count437 (b : Nat → Bool) : Nat := countLit b [15, 16]
def count439 (b : Nat → Bool) : Nat := countLit b [13, 15, 16]
def count442 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count444 (b : Nat → Bool) : Nat := countLit b [23, 25]
def count446 (b : Nat → Bool) : Nat := countLit b [18, 20, 23, 25]
def count450 (b : Nat → Bool) : Nat := countLit b [13, 15, 16, 18, 20, 23, 25]
def count457 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 8, 9, 10, 13, 15, 16, 18, 20, 23, 25]
def count470 (b : Nat → Bool) : Nat := countLit b [29, 31]
def count472 (b : Nat → Bool) : Nat := countLit b [27, 29, 31]
def count475 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count477 (b : Nat → Bool) : Nat := countLit b [36, 39]
def count479 (b : Nat → Bool) : Nat := countLit b [32, 34, 36, 39]
def count483 (b : Nat → Bool) : Nat := countLit b [27, 29, 31, 32, 34, 36, 39]
def count490 (b : Nat → Bool) : Nat := countLit b [43, 45]
def count492 (b : Nat → Bool) : Nat := countLit b [41, 43, 45]
def count495 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count497 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count499 (b : Nat → Bool) : Nat := countLit b [47, 48, 50, 52]
def count503 (b : Nat → Bool) : Nat := countLit b [41, 43, 45, 47, 48, 50, 52]
def count510 (b : Nat → Bool) : Nat := countLit b [27, 29, 31, 32, 34, 36, 39, 41, 43, 45, 47, 48, 50, 52]
def count524 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 8, 9, 10, 13, 15, 16, 18, 20, 23, 25, 27, 29, 31, 32, 34, 36, 39, 41, 43, 45, 47, 48, 50, 52]
def count551 (b : Nat → Bool) : Nat := countLit b [57, 59]
def count553 (b : Nat → Bool) : Nat := countLit b [55, 57, 59]
def count556 (b : Nat → Bool) : Nat := countLit b [62, 63]
def count558 (b : Nat → Bool) : Nat := countLit b [60, 62, 63]
def count561 (b : Nat → Bool) : Nat := countLit b [55, 57, 59, 60, 62, 63]
def count567 (b : Nat → Bool) : Nat := countLit b [69, 71]
def count569 (b : Nat → Bool) : Nat := countLit b [65, 69, 71]
def count572 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count574 (b : Nat → Bool) : Nat := countLit b [76, 78]
def count576 (b : Nat → Bool) : Nat := countLit b [73, 74, 76, 78]
def count580 (b : Nat → Bool) : Nat := countLit b [65, 69, 71, 73, 74, 76, 78]
def count587 (b : Nat → Bool) : Nat := countLit b [55, 57, 59, 60, 62, 63, 65, 69, 71, 73, 74, 76, 78]
def count600 (b : Nat → Bool) : Nat := countLit b [83, 86]
def count602 (b : Nat → Bool) : Nat := countLit b [79, 83, 86]
def count605 (b : Nat → Bool) : Nat := countLit b [88, 89]
def count607 (b : Nat → Bool) : Nat := countLit b [90, 93]
def count609 (b : Nat → Bool) : Nat := countLit b [88, 89, 90, 93]
def count613 (b : Nat → Bool) : Nat := countLit b [79, 83, 86, 88, 89, 90, 93]
def count620 (b : Nat → Bool) : Nat := countLit b [97, 100]
def count622 (b : Nat → Bool) : Nat := countLit b [95, 97, 100]
def count625 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count627 (b : Nat → Bool) : Nat := countLit b [104, 105]
def count629 (b : Nat → Bool) : Nat := countLit b [101, 102, 104, 105]
def count633 (b : Nat → Bool) : Nat := countLit b [95, 97, 100, 101, 102, 104, 105]
def count640 (b : Nat → Bool) : Nat := countLit b [79, 83, 86, 88, 89, 90, 93, 95, 97, 100, 101, 102, 104, 105]
def count654 (b : Nat → Bool) : Nat := countLit b [55, 57, 59, 60, 62, 63, 65, 69, 71, 73, 74, 76, 78, 79, 83, 86, 88, 89, 90, 93, 95, 97, 100, 101, 102, 104, 105]
def count681 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 8, 9, 10, 13, 15, 16, 18, 20, 23, 25, 27, 29, 31, 32, 34, 36, 39, 41, 43, 45, 47, 48, 50, 52, 55, 57, 59, 60, 62, 63, 65, 69, 71, 73, 74, 76, 78, 79, 83, 86, 88, 89, 90, 93, 95, 97, 100, 101, 102, 104, 105]
def count723 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count725 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6]
def count728 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count730 (b : Nat → Bool) : Nat := countLit b [-8, -9, -10]
def count733 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -8, -9, -10]
def count739 (b : Nat → Bool) : Nat := countLit b [-15, -16]
def count741 (b : Nat → Bool) : Nat := countLit b [-13, -15, -16]
def count744 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count746 (b : Nat → Bool) : Nat := countLit b [-23, -25]
def count748 (b : Nat → Bool) : Nat := countLit b [-18, -20, -23, -25]
def count752 (b : Nat → Bool) : Nat := countLit b [-13, -15, -16, -18, -20, -23, -25]
def count759 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -8, -9, -10, -13, -15, -16, -18, -20, -23, -25]
def count772 (b : Nat → Bool) : Nat := countLit b [-29, -31]
def count774 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31]
def count777 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count779 (b : Nat → Bool) : Nat := countLit b [-36, -39]
def count781 (b : Nat → Bool) : Nat := countLit b [-32, -34, -36, -39]
def count785 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31, -32, -34, -36, -39]
def count792 (b : Nat → Bool) : Nat := countLit b [-43, -45]
def count794 (b : Nat → Bool) : Nat := countLit b [-41, -43, -45]
def count797 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count799 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count801 (b : Nat → Bool) : Nat := countLit b [-47, -48, -50, -52]
def count805 (b : Nat → Bool) : Nat := countLit b [-41, -43, -45, -47, -48, -50, -52]
def count812 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31, -32, -34, -36, -39, -41, -43, -45, -47, -48, -50, -52]
def count826 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -8, -9, -10, -13, -15, -16, -18, -20, -23, -25, -27, -29, -31, -32, -34, -36, -39, -41, -43, -45, -47, -48, -50, -52]
def count840 (b : Nat → Bool) : Nat := countLit b [-57, -59]
def count842 (b : Nat → Bool) : Nat := countLit b [-55, -57, -59]
def count845 (b : Nat → Bool) : Nat := countLit b [-62, -63]
def count847 (b : Nat → Bool) : Nat := countLit b [-60, -62, -63]
def count850 (b : Nat → Bool) : Nat := countLit b [-55, -57, -59, -60, -62, -63]
def count856 (b : Nat → Bool) : Nat := countLit b [-69, -71]
def count858 (b : Nat → Bool) : Nat := countLit b [-65, -69, -71]
def count861 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count863 (b : Nat → Bool) : Nat := countLit b [-76, -78]
def count865 (b : Nat → Bool) : Nat := countLit b [-73, -74, -76, -78]
def count869 (b : Nat → Bool) : Nat := countLit b [-65, -69, -71, -73, -74, -76, -78]
def count876 (b : Nat → Bool) : Nat := countLit b [-55, -57, -59, -60, -62, -63, -65, -69, -71, -73, -74, -76, -78]
def count889 (b : Nat → Bool) : Nat := countLit b [-83, -86]
def count891 (b : Nat → Bool) : Nat := countLit b [-79, -83, -86]
def count894 (b : Nat → Bool) : Nat := countLit b [-88, -89]
def count896 (b : Nat → Bool) : Nat := countLit b [-90, -93]
def count898 (b : Nat → Bool) : Nat := countLit b [-88, -89, -90, -93]
def count902 (b : Nat → Bool) : Nat := countLit b [-79, -83, -86, -88, -89, -90, -93]
def count909 (b : Nat → Bool) : Nat := countLit b [-97, -100]
def count911 (b : Nat → Bool) : Nat := countLit b [-95, -97, -100]
def count914 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count916 (b : Nat → Bool) : Nat := countLit b [-104, -105]
def count918 (b : Nat → Bool) : Nat := countLit b [-101, -102, -104, -105]
def count922 (b : Nat → Bool) : Nat := countLit b [-95, -97, -100, -101, -102, -104, -105]
def count929 (b : Nat → Bool) : Nat := countLit b [-79, -83, -86, -88, -89, -90, -93, -95, -97, -100, -101, -102, -104, -105]
def count943 (b : Nat → Bool) : Nat := countLit b [-55, -57, -59, -60, -62, -63, -65, -69, -71, -73, -74, -76, -78, -79, -83, -86, -88, -89, -90, -93, -95, -97, -100, -101, -102, -104, -105]
def count957 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -8, -9, -10, -13, -15, -16, -18, -20, -23, -25, -27, -29, -31, -32, -34, -36, -39, -41, -43, -45, -47, -48, -50, -52, -55, -57, -59, -60, -62, -63, -65, -69, -71, -73, -74, -76, -78, -79, -83, -86, -88, -89, -90, -93, -95, -97, -100, -101, -102, -104, -105]
def count971 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count973 (b : Nat → Bool) : Nat := countLit b [2, 3, 5]
def count976 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count978 (b : Nat → Bool) : Nat := countLit b [7, 11, 12]
def count981 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 7, 11, 12]
def count987 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count989 (b : Nat → Bool) : Nat := countLit b [14, 17, 19]
def count992 (b : Nat → Bool) : Nat := countLit b [21, 22]
def count994 (b : Nat → Bool) : Nat := countLit b [24, 26]
def count996 (b : Nat → Bool) : Nat := countLit b [21, 22, 24, 26]
def count1000 (b : Nat → Bool) : Nat := countLit b [14, 17, 19, 21, 22, 24, 26]
def count1007 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 7, 11, 12, 14, 17, 19, 21, 22, 24, 26]
def count1020 (b : Nat → Bool) : Nat := countLit b [30, 33]
def count1022 (b : Nat → Bool) : Nat := countLit b [28, 30, 33]
def count1025 (b : Nat → Bool) : Nat := countLit b [37, 38]
def count1027 (b : Nat → Bool) : Nat := countLit b [35, 37, 38]
def count1030 (b : Nat → Bool) : Nat := countLit b [28, 30, 33, 35, 37, 38]
def count1036 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count1038 (b : Nat → Bool) : Nat := countLit b [40, 42, 44]
def count1041 (b : Nat → Bool) : Nat := countLit b [46, 49]
def count1043 (b : Nat → Bool) : Nat := countLit b [51, 53]
def count1045 (b : Nat → Bool) : Nat := countLit b [46, 49, 51, 53]
def count1049 (b : Nat → Bool) : Nat := countLit b [40, 42, 44, 46, 49, 51, 53]
def count1056 (b : Nat → Bool) : Nat := countLit b [28, 30, 33, 35, 37, 38, 40, 42, 44, 46, 49, 51, 53]
def count1069 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 7, 11, 12, 14, 17, 19, 21, 22, 24, 26, 28, 30, 33, 35, 37, 38, 40, 42, 44, 46, 49, 51, 53]
def count1095 (b : Nat → Bool) : Nat := countLit b [56, 58]
def count1097 (b : Nat → Bool) : Nat := countLit b [54, 56, 58]
def count1100 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count1102 (b : Nat → Bool) : Nat := countLit b [61, 64, 66]
def count1105 (b : Nat → Bool) : Nat := countLit b [54, 56, 58, 61, 64, 66]
def count1111 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count1113 (b : Nat → Bool) : Nat := countLit b [67, 68, 70]
def count1116 (b : Nat → Bool) : Nat := countLit b [72, 75]
def count1118 (b : Nat → Bool) : Nat := countLit b [77, 80]
def count1120 (b : Nat → Bool) : Nat := countLit b [72, 75, 77, 80]
def count1124 (b : Nat → Bool) : Nat := countLit b [67, 68, 70, 72, 75, 77, 80]
def count1131 (b : Nat → Bool) : Nat := countLit b [54, 56, 58, 61, 64, 66, 67, 68, 70, 72, 75, 77, 80]
def count1144 (b : Nat → Bool) : Nat := countLit b [82, 84]
def count1146 (b : Nat → Bool) : Nat := countLit b [81, 82, 84]
def count1149 (b : Nat → Bool) : Nat := countLit b [87, 91]
def count1151 (b : Nat → Bool) : Nat := countLit b [85, 87, 91]
def count1154 (b : Nat → Bool) : Nat := countLit b [81, 82, 84, 85, 87, 91]
def count1160 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count1162 (b : Nat → Bool) : Nat := countLit b [92, 94, 96]
def count1165 (b : Nat → Bool) : Nat := countLit b [98, 99]
def count1167 (b : Nat → Bool) : Nat := countLit b [103, 106]
def count1169 (b : Nat → Bool) : Nat := countLit b [98, 99, 103, 106]
def count1173 (b : Nat → Bool) : Nat := countLit b [92, 94, 96, 98, 99, 103, 106]
def count1180 (b : Nat → Bool) : Nat := countLit b [81, 82, 84, 85, 87, 91, 92, 94, 96, 98, 99, 103, 106]
def count1193 (b : Nat → Bool) : Nat := countLit b [54, 56, 58, 61, 64, 66, 67, 68, 70, 72, 75, 77, 80, 81, 82, 84, 85, 87, 91, 92, 94, 96, 98, 99, 103, 106]
def count1219 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 7, 11, 12, 14, 17, 19, 21, 22, 24, 26, 28, 30, 33, 35, 37, 38, 40, 42, 44, 46, 49, 51, 53, 54, 56, 58, 61, 64, 66, 67, 68, 70, 72, 75, 77, 80, 81, 82, 84, 85, 87, 91, 92, 94, 96, 98, 99, 103, 106]
def count1261 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count1263 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5]
def count1266 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count1268 (b : Nat → Bool) : Nat := countLit b [-7, -11, -12]
def count1271 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -7, -11, -12]
def count1277 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count1279 (b : Nat → Bool) : Nat := countLit b [-14, -17, -19]
def count1282 (b : Nat → Bool) : Nat := countLit b [-21, -22]
def count1284 (b : Nat → Bool) : Nat := countLit b [-24, -26]
def count1286 (b : Nat → Bool) : Nat := countLit b [-21, -22, -24, -26]
def count1290 (b : Nat → Bool) : Nat := countLit b [-14, -17, -19, -21, -22, -24, -26]
def count1297 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]
def count1309 (b : Nat → Bool) : Nat := countLit b [-30, -33]
def count1311 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33]
def count1314 (b : Nat → Bool) : Nat := countLit b [-37, -38]
def count1316 (b : Nat → Bool) : Nat := countLit b [-35, -37, -38]
def count1319 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33, -35, -37, -38]
def count1325 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count1327 (b : Nat → Bool) : Nat := countLit b [-40, -42, -44]
def count1330 (b : Nat → Bool) : Nat := countLit b [-46, -49]
def count1332 (b : Nat → Bool) : Nat := countLit b [-51, -53]
def count1334 (b : Nat → Bool) : Nat := countLit b [-46, -49, -51, -53]
def count1338 (b : Nat → Bool) : Nat := countLit b [-40, -42, -44, -46, -49, -51, -53]
def count1345 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]
def count1357 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]
def count1369 (b : Nat → Bool) : Nat := countLit b [-56, -58]
def count1371 (b : Nat → Bool) : Nat := countLit b [-54, -56, -58]
def count1374 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count1376 (b : Nat → Bool) : Nat := countLit b [-61, -64, -66]
def count1379 (b : Nat → Bool) : Nat := countLit b [-54, -56, -58, -61, -64, -66]
def count1385 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count1387 (b : Nat → Bool) : Nat := countLit b [-67, -68, -70]
def count1390 (b : Nat → Bool) : Nat := countLit b [-72, -75]
def count1392 (b : Nat → Bool) : Nat := countLit b [-77, -80]
def count1394 (b : Nat → Bool) : Nat := countLit b [-72, -75, -77, -80]
def count1398 (b : Nat → Bool) : Nat := countLit b [-67, -68, -70, -72, -75, -77, -80]
def count1405 (b : Nat → Bool) : Nat := countLit b [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80]
def count1417 (b : Nat → Bool) : Nat := countLit b [-82, -84]
def count1419 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84]
def count1422 (b : Nat → Bool) : Nat := countLit b [-87, -91]
def count1424 (b : Nat → Bool) : Nat := countLit b [-85, -87, -91]
def count1427 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84, -85, -87, -91]
def count1433 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1435 (b : Nat → Bool) : Nat := countLit b [-92, -94, -96]
def count1438 (b : Nat → Bool) : Nat := countLit b [-98, -99]
def count1440 (b : Nat → Bool) : Nat := countLit b [-103, -106]
def count1442 (b : Nat → Bool) : Nat := countLit b [-98, -99, -103, -106]
def count1446 (b : Nat → Bool) : Nat := countLit b [-92, -94, -96, -98, -99, -103, -106]
def count1453 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]
def count1465 (b : Nat → Bool) : Nat := countLit b [-54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]
def count1477 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26, -28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53, -54, -56, -58, -61, -64, -66, -67, -68, -70, -72, -75, -77, -80, -81, -82, -84, -85, -87, -91, -92, -94, -96, -98, -99, -103, -106]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 744 then (if i < 372 then (if i < 186 then (if i < 93 then (if i < 46 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 17 then (if i < 14 then (if i < 12 then b 11 else (if i < 13 then b 12 else b 13)) else (if i < 15 then b 14 else (if i < 16 then b 15 else b 16))) else (if i < 20 then (if i < 18 then b 17 else (if i < 19 then b 18 else b 19)) else (if i < 21 then b 20 else (if i < 22 then b 21 else b 22))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then b 23 else b 24) else (if i < 26 then b 25 else (if i < 27 then b 26 else b 27))) else (if i < 31 then (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)) else (if i < 32 then b 31 else (if i < 33 then b 32 else b 33)))) else (if i < 40 then (if i < 37 then (if i < 35 then b 34 else (if i < 36 then b 35 else b 36)) else (if i < 38 then b 37 else (if i < 39 then b 38 else b 39))) else (if i < 43 then (if i < 41 then b 40 else (if i < 42 then b 41 else b 42)) else (if i < 44 then b 43 else (if i < 45 then b 44 else b 45)))))) else (if i < 69 then (if i < 57 then (if i < 51 then (if i < 48 then (if i < 47 then b 46 else b 47) else (if i < 49 then b 48 else (if i < 50 then b 49 else b 50))) else (if i < 54 then (if i < 52 then b 51 else (if i < 53 then b 52 else b 53)) else (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)))) else (if i < 63 then (if i < 60 then (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)) else (if i < 61 then b 60 else (if i < 62 then b 61 else b 62))) else (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 67 then b 66 else (if i < 68 then b 67 else b 68))))) else (if i < 81 then (if i < 75 then (if i < 72 then (if i < 70 then b 69 else (if i < 71 then b 70 else b 71)) else (if i < 73 then b 72 else (if i < 74 then b 73 else b 74))) else (if i < 78 then (if i < 76 then b 75 else (if i < 77 then b 76 else b 77)) else (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)))) else (if i < 87 then (if i < 84 then (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)) else (if i < 85 then b 84 else (if i < 86 then b 85 else b 86))) else (if i < 90 then (if i < 88 then b 87 else (if i < 89 then b 88 else b 89)) else (if i < 91 then b 90 else (if i < 92 then b 91 else b 92))))))) else (if i < 139 then (if i < 116 then (if i < 104 then (if i < 98 then (if i < 95 then (if i < 94 then b 93 else b 94) else (if i < 96 then b 95 else (if i < 97 then b 96 else b 97))) else (if i < 101 then (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)) else (if i < 102 then b 101 else (if i < 103 then b 102 else b 103)))) else (if i < 110 then (if i < 107 then (if i < 105 then b 104 else (if i < 106 then b 105 else b 106)) else (if i < 108 then b 107 else (if i < 109 then b 108 else b 109))) else (if i < 113 then (if i < 111 then b 110 else (if i < 112 then b 111 else b 112)) else (if i < 114 then b 113 else (if i < 115 then b 114 else b 115))))) else (if i < 127 then (if i < 121 then (if i < 118 then (if i < 117 then b 116 else b 117) else (if i < 119 then b 118 else (if i < 120 then b 119 else b 120))) else (if i < 124 then (if i < 122 then b 121 else (if i < 123 then b 122 else b 123)) else (if i < 125 then b 124 else (if i < 126 then b 125 else b 126)))) else (if i < 133 then (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 131 then b 130 else (if i < 132 then b 131 else b 132))) else (if i < 136 then (if i < 134 then b 133 else (if i < 135 then b 134 else b 135)) else (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)))))) else (if i < 162 then (if i < 150 then (if i < 144 then (if i < 141 then (if i < 140 then b 139 else b 140) else (if i < 142 then b 141 else (if i < 143 then b 142 else b 143))) else (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)))) else (if i < 156 then (if i < 153 then (if i < 151 then b 150 else (if i < 152 then b 151 else b 152)) else (if i < 154 then b 153 else (if i < 155 then b 154 else b 155))) else (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))))) else (if i < 174 then (if i < 168 then (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 166 then b 165 else (if i < 167 then b 166 else b 167))) else (if i < 171 then (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)) else (if i < 172 then b 171 else (if i < 173 then b 172 else b 173)))) else (if i < 180 then (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179))) else (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185)))))))) else (if i < 279 then (if i < 232 then (if i < 209 then (if i < 197 then (if i < 191 then (if i < 188 then (if i < 187 then b 186 else b 187) else (if i < 189 then b 188 else (if i < 190 then b 189 else b 190))) else (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 195 then b 194 else (if i < 196 then b 195 else b 196)))) else (if i < 203 then (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 201 then b 200 else (if i < 202 then b 201 else b 202))) else (if i < 206 then (if i < 204 then b 203 else (if i < 205 then b 204 else b 205)) else (if i < 207 then b 206 else (if i < 208 then b 207 else b 208))))) else (if i < 220 then (if i < 214 then (if i < 211 then (if i < 210 then b 209 else b 210) else (if i < 212 then b 211 else (if i < 213 then b 212 else decide (1 ≤ count213 b)))) else (if i < 217 then (if i < 215 then decide (2 ≤ count213 b) else (if i < 216 then decide (1 ≤ count215 b) else decide (2 ≤ count215 b))) else (if i < 218 then decide (1 ≤ count217 b) else (if i < 219 then decide (2 ≤ count217 b) else decide (1 ≤ count219 b))))) else (if i < 226 then (if i < 223 then (if i < 221 then decide (2 ≤ count219 b) else (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b))) else (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b)))) else (if i < 229 then (if i < 227 then decide (2 ≤ count225 b) else (if i < 228 then decide (1 ≤ count227 b) else decide (2 ≤ count227 b))) else (if i < 230 then decide (1 ≤ count229 b) else (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b))))))) else (if i < 255 then (if i < 243 then (if i < 237 then (if i < 234 then (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b)) else (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b)))) else (if i < 240 then (if i < 238 then decide (1 ≤ count237 b) else (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b))) else (if i < 241 then decide (2 ≤ count239 b) else (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b))))) else (if i < 249 then (if i < 246 then (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b))) else (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b)))) else (if i < 252 then (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))) else (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b)))))) else (if i < 267 then (if i < 261 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)))) else (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))))) else (if i < 273 then (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)))) else (if i < 276 then (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)))))))) else (if i < 325 then (if i < 302 then (if i < 290 then (if i < 284 then (if i < 281 then (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)) else (if i < 282 then decide (1 ≤ count281 b) else (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b)))) else (if i < 287 then (if i < 285 then decide (2 ≤ count283 b) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b))) else (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))))) else (if i < 296 then (if i < 293 then (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))) else (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)))) else (if i < 299 then (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b))) else (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))))) else (if i < 313 then (if i < 307 then (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)))) else (if i < 310 then (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b))) else (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))))) else (if i < 319 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)))) else (if i < 322 then (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))) else (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))))))) else (if i < 348 then (if i < 336 then (if i < 330 then (if i < 327 then (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)) else (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)))) else (if i < 333 then (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b))) else (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))))) else (if i < 342 then (if i < 339 then (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))) else (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)))) else (if i < 345 then (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b))) else (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)))))) else (if i < 360 then (if i < 354 then (if i < 351 then (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b))) else (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))) else (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))))) else (if i < 366 then (if i < 363 then (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b))) else (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))) else (if i < 369 then (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)))))))))) else (if i < 558 then (if i < 465 then (if i < 418 then (if i < 395 then (if i < 383 then (if i < 377 then (if i < 374 then (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)))) else (if i < 380 then (if i < 378 then decide (1 ≤ count377 b) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b))) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b))))) else (if i < 389 then (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 392 then (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))) else (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)))))) else (if i < 406 then (if i < 400 then (if i < 397 then (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)) else (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))) else (if i < 403 then (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))) else (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))))) else (if i < 412 then (if i < 409 then (if i < 407 then decide (2 ≤ count405 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))) else (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b)))) else (if i < 415 then (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))) else (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))))))) else (if i < 441 then (if i < 429 then (if i < 423 then (if i < 420 then (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)) else (if i < 421 then decide (2 ≤ count419 b) else (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b)))) else (if i < 426 then (if i < 424 then decide (1 ≤ count423 b) else (if i < 425 then decide (2 ≤ count423 b) else decide (3 ≤ count423 b))) else (if i < 427 then decide (1 ≤ count426 b) else (if i < 428 then decide (2 ≤ count426 b) else decide (1 ≤ count428 b))))) else (if i < 435 then (if i < 432 then (if i < 430 then decide (2 ≤ count428 b) else (if i < 431 then decide (3 ≤ count428 b) else decide (1 ≤ count431 b))) else (if i < 433 then decide (2 ≤ count431 b) else (if i < 434 then decide (3 ≤ count431 b) else decide (4 ≤ count431 b)))) else (if i < 438 then (if i < 436 then decide (5 ≤ count431 b) else (if i < 437 then decide (6 ≤ count431 b) else decide (1 ≤ count437 b))) else (if i < 439 then decide (2 ≤ count437 b) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b)))))) else (if i < 453 then (if i < 447 then (if i < 444 then (if i < 442 then decide (3 ≤ count439 b) else (if i < 443 then decide (1 ≤ count442 b) else decide (2 ≤ count442 b))) else (if i < 445 then decide (1 ≤ count444 b) else (if i < 446 then decide (2 ≤ count444 b) else decide (1 ≤ count446 b)))) else (if i < 450 then (if i < 448 then decide (2 ≤ count446 b) else (if i < 449 then decide (3 ≤ count446 b) else decide (4 ≤ count446 b))) else (if i < 451 then decide (1 ≤ count450 b) else (if i < 452 then decide (2 ≤ count450 b) else decide (3 ≤ count450 b))))) else (if i < 459 then (if i < 456 then (if i < 454 then decide (4 ≤ count450 b) else (if i < 455 then decide (5 ≤ count450 b) else decide (6 ≤ count450 b))) else (if i < 457 then decide (7 ≤ count450 b) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)))) else (if i < 462 then (if i < 460 then decide (3 ≤ count457 b) else (if i < 461 then decide (4 ≤ count457 b) else decide (5 ≤ count457 b))) else (if i < 463 then decide (6 ≤ count457 b) else (if i < 464 then decide (7 ≤ count457 b) else decide (8 ≤ count457 b)))))))) else (if i < 511 then (if i < 488 then (if i < 476 then (if i < 470 then (if i < 467 then (if i < 466 then decide (9 ≤ count457 b) else decide (10 ≤ count457 b)) else (if i < 468 then decide (11 ≤ count457 b) else (if i < 469 then decide (12 ≤ count457 b) else decide (13 ≤ count457 b)))) else (if i < 473 then (if i < 471 then decide (1 ≤ count470 b) else (if i < 472 then decide (2 ≤ count470 b) else decide (1 ≤ count472 b))) else (if i < 474 then decide (2 ≤ count472 b) else (if i < 475 then decide (3 ≤ count472 b) else decide (1 ≤ count475 b))))) else (if i < 482 then (if i < 479 then (if i < 477 then decide (2 ≤ count475 b) else (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b))) else (if i < 480 then decide (1 ≤ count479 b) else (if i < 481 then decide (2 ≤ count479 b) else decide (3 ≤ count479 b)))) else (if i < 485 then (if i < 483 then decide (4 ≤ count479 b) else (if i < 484 then decide (1 ≤ count483 b) else decide (2 ≤ count483 b))) else (if i < 486 then decide (3 ≤ count483 b) else (if i < 487 then decide (4 ≤ count483 b) else decide (5 ≤ count483 b)))))) else (if i < 499 then (if i < 493 then (if i < 490 then (if i < 489 then decide (6 ≤ count483 b) else decide (7 ≤ count483 b)) else (if i < 491 then decide (1 ≤ count490 b) else (if i < 492 then decide (2 ≤ count490 b) else decide (1 ≤ count492 b)))) else (if i < 496 then (if i < 494 then decide (2 ≤ count492 b) else (if i < 495 then decide (3 ≤ count492 b) else decide (1 ≤ count495 b))) else (if i < 497 then decide (2 ≤ count495 b) else (if i < 498 then decide (1 ≤ count497 b) else decide (2 ≤ count497 b))))) else (if i < 505 then (if i < 502 then (if i < 500 then decide (1 ≤ count499 b) else (if i < 501 then decide (2 ≤ count499 b) else decide (3 ≤ count499 b))) else (if i < 503 then decide (4 ≤ count499 b) else (if i < 504 then decide (1 ≤ count503 b) else decide (2 ≤ count503 b)))) else (if i < 508 then (if i < 506 then decide (3 ≤ count503 b) else (if i < 507 then decide (4 ≤ count503 b) else decide (5 ≤ count503 b))) else (if i < 509 then decide (6 ≤ count503 b) else (if i < 510 then decide (7 ≤ count503 b) else decide (1 ≤ count510 b))))))) else (if i < 534 then (if i < 522 then (if i < 516 then (if i < 513 then (if i < 512 then decide (2 ≤ count510 b) else decide (3 ≤ count510 b)) else (if i < 514 then decide (4 ≤ count510 b) else (if i < 515 then decide (5 ≤ count510 b) else decide (6 ≤ count510 b)))) else (if i < 519 then (if i < 517 then decide (7 ≤ count510 b) else (if i < 518 then decide (8 ≤ count510 b) else decide (9 ≤ count510 b))) else (if i < 520 then decide (10 ≤ count510 b) else (if i < 521 then decide (11 ≤ count510 b) else decide (12 ≤ count510 b))))) else (if i < 528 then (if i < 525 then (if i < 523 then decide (13 ≤ count510 b) else (if i < 524 then decide (14 ≤ count510 b) else decide (1 ≤ count524 b))) else (if i < 526 then decide (2 ≤ count524 b) else (if i < 527 then decide (3 ≤ count524 b) else decide (4 ≤ count524 b)))) else (if i < 531 then (if i < 529 then decide (5 ≤ count524 b) else (if i < 530 then decide (6 ≤ count524 b) else decide (7 ≤ count524 b))) else (if i < 532 then decide (8 ≤ count524 b) else (if i < 533 then decide (9 ≤ count524 b) else decide (10 ≤ count524 b)))))) else (if i < 546 then (if i < 540 then (if i < 537 then (if i < 535 then decide (11 ≤ count524 b) else (if i < 536 then decide (12 ≤ count524 b) else decide (13 ≤ count524 b))) else (if i < 538 then decide (14 ≤ count524 b) else (if i < 539 then decide (15 ≤ count524 b) else decide (16 ≤ count524 b)))) else (if i < 543 then (if i < 541 then decide (17 ≤ count524 b) else (if i < 542 then decide (18 ≤ count524 b) else decide (19 ≤ count524 b))) else (if i < 544 then decide (20 ≤ count524 b) else (if i < 545 then decide (21 ≤ count524 b) else decide (22 ≤ count524 b))))) else (if i < 552 then (if i < 549 then (if i < 547 then decide (23 ≤ count524 b) else (if i < 548 then decide (24 ≤ count524 b) else decide (25 ≤ count524 b))) else (if i < 550 then decide (26 ≤ count524 b) else (if i < 551 then decide (27 ≤ count524 b) else decide (1 ≤ count551 b)))) else (if i < 555 then (if i < 553 then decide (2 ≤ count551 b) else (if i < 554 then decide (1 ≤ count553 b) else decide (2 ≤ count553 b))) else (if i < 556 then decide (3 ≤ count553 b) else (if i < 557 then decide (1 ≤ count556 b) else decide (2 ≤ count556 b))))))))) else (if i < 651 then (if i < 604 then (if i < 581 then (if i < 569 then (if i < 563 then (if i < 560 then (if i < 559 then decide (1 ≤ count558 b) else decide (2 ≤ count558 b)) else (if i < 561 then decide (3 ≤ count558 b) else (if i < 562 then decide (1 ≤ count561 b) else decide (2 ≤ count561 b)))) else (if i < 566 then (if i < 564 then decide (3 ≤ count561 b) else (if i < 565 then decide (4 ≤ count561 b) else decide (5 ≤ count561 b))) else (if i < 567 then decide (6 ≤ count561 b) else (if i < 568 then decide (1 ≤ count567 b) else decide (2 ≤ count567 b))))) else (if i < 575 then (if i < 572 then (if i < 570 then decide (1 ≤ count569 b) else (if i < 571 then decide (2 ≤ count569 b) else decide (3 ≤ count569 b))) else (if i < 573 then decide (1 ≤ count572 b) else (if i < 574 then decide (2 ≤ count572 b) else decide (1 ≤ count574 b)))) else (if i < 578 then (if i < 576 then decide (2 ≤ count574 b) else (if i < 577 then decide (1 ≤ count576 b) else decide (2 ≤ count576 b))) else (if i < 579 then decide (3 ≤ count576 b) else (if i < 580 then decide (4 ≤ count576 b) else decide (1 ≤ count580 b)))))) else (if i < 592 then (if i < 586 then (if i < 583 then (if i < 582 then decide (2 ≤ count580 b) else decide (3 ≤ count580 b)) else (if i < 584 then decide (4 ≤ count580 b) else (if i < 585 then decide (5 ≤ count580 b) else decide (6 ≤ count580 b)))) else (if i < 589 then (if i < 587 then decide (7 ≤ count580 b) else (if i < 588 then decide (1 ≤ count587 b) else decide (2 ≤ count587 b))) else (if i < 590 then decide (3 ≤ count587 b) else (if i < 591 then decide (4 ≤ count587 b) else decide (5 ≤ count587 b))))) else (if i < 598 then (if i < 595 then (if i < 593 then decide (6 ≤ count587 b) else (if i < 594 then decide (7 ≤ count587 b) else decide (8 ≤ count587 b))) else (if i < 596 then decide (9 ≤ count587 b) else (if i < 597 then decide (10 ≤ count587 b) else decide (11 ≤ count587 b)))) else (if i < 601 then (if i < 599 then decide (12 ≤ count587 b) else (if i < 600 then decide (13 ≤ count587 b) else decide (1 ≤ count600 b))) else (if i < 602 then decide (2 ≤ count600 b) else (if i < 603 then decide (1 ≤ count602 b) else decide (2 ≤ count602 b))))))) else (if i < 627 then (if i < 615 then (if i < 609 then (if i < 606 then (if i < 605 then decide (3 ≤ count602 b) else decide (1 ≤ count605 b)) else (if i < 607 then decide (2 ≤ count605 b) else (if i < 608 then decide (1 ≤ count607 b) else decide (2 ≤ count607 b)))) else (if i < 612 then (if i < 610 then decide (1 ≤ count609 b) else (if i < 611 then decide (2 ≤ count609 b) else decide (3 ≤ count609 b))) else (if i < 613 then decide (4 ≤ count609 b) else (if i < 614 then decide (1 ≤ count613 b) else decide (2 ≤ count613 b))))) else (if i < 621 then (if i < 618 then (if i < 616 then decide (3 ≤ count613 b) else (if i < 617 then decide (4 ≤ count613 b) else decide (5 ≤ count613 b))) else (if i < 619 then decide (6 ≤ count613 b) else (if i < 620 then decide (7 ≤ count613 b) else decide (1 ≤ count620 b)))) else (if i < 624 then (if i < 622 then decide (2 ≤ count620 b) else (if i < 623 then decide (1 ≤ count622 b) else decide (2 ≤ count622 b))) else (if i < 625 then decide (3 ≤ count622 b) else (if i < 626 then decide (1 ≤ count625 b) else decide (2 ≤ count625 b)))))) else (if i < 639 then (if i < 633 then (if i < 630 then (if i < 628 then decide (1 ≤ count627 b) else (if i < 629 then decide (2 ≤ count627 b) else decide (1 ≤ count629 b))) else (if i < 631 then decide (2 ≤ count629 b) else (if i < 632 then decide (3 ≤ count629 b) else decide (4 ≤ count629 b)))) else (if i < 636 then (if i < 634 then decide (1 ≤ count633 b) else (if i < 635 then decide (2 ≤ count633 b) else decide (3 ≤ count633 b))) else (if i < 637 then decide (4 ≤ count633 b) else (if i < 638 then decide (5 ≤ count633 b) else decide (6 ≤ count633 b))))) else (if i < 645 then (if i < 642 then (if i < 640 then decide (7 ≤ count633 b) else (if i < 641 then decide (1 ≤ count640 b) else decide (2 ≤ count640 b))) else (if i < 643 then decide (3 ≤ count640 b) else (if i < 644 then decide (4 ≤ count640 b) else decide (5 ≤ count640 b)))) else (if i < 648 then (if i < 646 then decide (6 ≤ count640 b) else (if i < 647 then decide (7 ≤ count640 b) else decide (8 ≤ count640 b))) else (if i < 649 then decide (9 ≤ count640 b) else (if i < 650 then decide (10 ≤ count640 b) else decide (11 ≤ count640 b)))))))) else (if i < 697 then (if i < 674 then (if i < 662 then (if i < 656 then (if i < 653 then (if i < 652 then decide (12 ≤ count640 b) else decide (13 ≤ count640 b)) else (if i < 654 then decide (14 ≤ count640 b) else (if i < 655 then decide (1 ≤ count654 b) else decide (2 ≤ count654 b)))) else (if i < 659 then (if i < 657 then decide (3 ≤ count654 b) else (if i < 658 then decide (4 ≤ count654 b) else decide (5 ≤ count654 b))) else (if i < 660 then decide (6 ≤ count654 b) else (if i < 661 then decide (7 ≤ count654 b) else decide (8 ≤ count654 b))))) else (if i < 668 then (if i < 665 then (if i < 663 then decide (9 ≤ count654 b) else (if i < 664 then decide (10 ≤ count654 b) else decide (11 ≤ count654 b))) else (if i < 666 then decide (12 ≤ count654 b) else (if i < 667 then decide (13 ≤ count654 b) else decide (14 ≤ count654 b)))) else (if i < 671 then (if i < 669 then decide (15 ≤ count654 b) else (if i < 670 then decide (16 ≤ count654 b) else decide (17 ≤ count654 b))) else (if i < 672 then decide (18 ≤ count654 b) else (if i < 673 then decide (19 ≤ count654 b) else decide (20 ≤ count654 b)))))) else (if i < 685 then (if i < 679 then (if i < 676 then (if i < 675 then decide (21 ≤ count654 b) else decide (22 ≤ count654 b)) else (if i < 677 then decide (23 ≤ count654 b) else (if i < 678 then decide (24 ≤ count654 b) else decide (25 ≤ count654 b)))) else (if i < 682 then (if i < 680 then decide (26 ≤ count654 b) else (if i < 681 then decide (27 ≤ count654 b) else decide (1 ≤ count681 b))) else (if i < 683 then decide (2 ≤ count681 b) else (if i < 684 then decide (3 ≤ count681 b) else decide (4 ≤ count681 b))))) else (if i < 691 then (if i < 688 then (if i < 686 then decide (5 ≤ count681 b) else (if i < 687 then decide (6 ≤ count681 b) else decide (7 ≤ count681 b))) else (if i < 689 then decide (8 ≤ count681 b) else (if i < 690 then decide (9 ≤ count681 b) else decide (10 ≤ count681 b)))) else (if i < 694 then (if i < 692 then decide (11 ≤ count681 b) else (if i < 693 then decide (12 ≤ count681 b) else decide (13 ≤ count681 b))) else (if i < 695 then decide (14 ≤ count681 b) else (if i < 696 then decide (15 ≤ count681 b) else decide (16 ≤ count681 b))))))) else (if i < 720 then (if i < 708 then (if i < 702 then (if i < 699 then (if i < 698 then decide (17 ≤ count681 b) else decide (18 ≤ count681 b)) else (if i < 700 then decide (19 ≤ count681 b) else (if i < 701 then decide (20 ≤ count681 b) else decide (21 ≤ count681 b)))) else (if i < 705 then (if i < 703 then decide (22 ≤ count681 b) else (if i < 704 then decide (23 ≤ count681 b) else decide (24 ≤ count681 b))) else (if i < 706 then decide (25 ≤ count681 b) else (if i < 707 then decide (26 ≤ count681 b) else decide (27 ≤ count681 b))))) else (if i < 714 then (if i < 711 then (if i < 709 then decide (28 ≤ count681 b) else (if i < 710 then decide (29 ≤ count681 b) else decide (30 ≤ count681 b))) else (if i < 712 then decide (31 ≤ count681 b) else (if i < 713 then decide (32 ≤ count681 b) else decide (33 ≤ count681 b)))) else (if i < 717 then (if i < 715 then decide (34 ≤ count681 b) else (if i < 716 then decide (35 ≤ count681 b) else decide (36 ≤ count681 b))) else (if i < 718 then decide (37 ≤ count681 b) else (if i < 719 then decide (38 ≤ count681 b) else decide (39 ≤ count681 b)))))) else (if i < 732 then (if i < 726 then (if i < 723 then (if i < 721 then decide (40 ≤ count681 b) else (if i < 722 then decide (41 ≤ count681 b) else decide (42 ≤ count681 b))) else (if i < 724 then decide (1 ≤ count723 b) else (if i < 725 then decide (2 ≤ count723 b) else decide (1 ≤ count725 b)))) else (if i < 729 then (if i < 727 then decide (2 ≤ count725 b) else (if i < 728 then decide (3 ≤ count725 b) else decide (1 ≤ count728 b))) else (if i < 730 then decide (2 ≤ count728 b) else (if i < 731 then decide (1 ≤ count730 b) else decide (2 ≤ count730 b))))) else (if i < 738 then (if i < 735 then (if i < 733 then decide (3 ≤ count730 b) else (if i < 734 then decide (1 ≤ count733 b) else decide (2 ≤ count733 b))) else (if i < 736 then decide (3 ≤ count733 b) else (if i < 737 then decide (4 ≤ count733 b) else decide (5 ≤ count733 b)))) else (if i < 741 then (if i < 739 then decide (6 ≤ count733 b) else (if i < 740 then decide (1 ≤ count739 b) else decide (2 ≤ count739 b))) else (if i < 742 then decide (1 ≤ count741 b) else (if i < 743 then decide (2 ≤ count741 b) else decide (3 ≤ count741 b))))))))))) else (if i < 1116 then (if i < 930 then (if i < 837 then (if i < 790 then (if i < 767 then (if i < 755 then (if i < 749 then (if i < 746 then (if i < 745 then decide (1 ≤ count744 b) else decide (2 ≤ count744 b)) else (if i < 747 then decide (1 ≤ count746 b) else (if i < 748 then decide (2 ≤ count746 b) else decide (1 ≤ count748 b)))) else (if i < 752 then (if i < 750 then decide (2 ≤ count748 b) else (if i < 751 then decide (3 ≤ count748 b) else decide (4 ≤ count748 b))) else (if i < 753 then decide (1 ≤ count752 b) else (if i < 754 then decide (2 ≤ count752 b) else decide (3 ≤ count752 b))))) else (if i < 761 then (if i < 758 then (if i < 756 then decide (4 ≤ count752 b) else (if i < 757 then decide (5 ≤ count752 b) else decide (6 ≤ count752 b))) else (if i < 759 then decide (7 ≤ count752 b) else (if i < 760 then decide (1 ≤ count759 b) else decide (2 ≤ count759 b)))) else (if i < 764 then (if i < 762 then decide (3 ≤ count759 b) else (if i < 763 then decide (4 ≤ count759 b) else decide (5 ≤ count759 b))) else (if i < 765 then decide (6 ≤ count759 b) else (if i < 766 then decide (7 ≤ count759 b) else decide (8 ≤ count759 b)))))) else (if i < 778 then (if i < 772 then (if i < 769 then (if i < 768 then decide (9 ≤ count759 b) else decide (10 ≤ count759 b)) else (if i < 770 then decide (11 ≤ count759 b) else (if i < 771 then decide (12 ≤ count759 b) else decide (13 ≤ count759 b)))) else (if i < 775 then (if i < 773 then decide (1 ≤ count772 b) else (if i < 774 then decide (2 ≤ count772 b) else decide (1 ≤ count774 b))) else (if i < 776 then decide (2 ≤ count774 b) else (if i < 777 then decide (3 ≤ count774 b) else decide (1 ≤ count777 b))))) else (if i < 784 then (if i < 781 then (if i < 779 then decide (2 ≤ count777 b) else (if i < 780 then decide (1 ≤ count779 b) else decide (2 ≤ count779 b))) else (if i < 782 then decide (1 ≤ count781 b) else (if i < 783 then decide (2 ≤ count781 b) else decide (3 ≤ count781 b)))) else (if i < 787 then (if i < 785 then decide (4 ≤ count781 b) else (if i < 786 then decide (1 ≤ count785 b) else decide (2 ≤ count785 b))) else (if i < 788 then decide (3 ≤ count785 b) else (if i < 789 then decide (4 ≤ count785 b) else decide (5 ≤ count785 b))))))) else (if i < 813 then (if i < 801 then (if i < 795 then (if i < 792 then (if i < 791 then decide (6 ≤ count785 b) else decide (7 ≤ count785 b)) else (if i < 793 then decide (1 ≤ count792 b) else (if i < 794 then decide (2 ≤ count792 b) else decide (1 ≤ count794 b)))) else (if i < 798 then (if i < 796 then decide (2 ≤ count794 b) else (if i < 797 then decide (3 ≤ count794 b) else decide (1 ≤ count797 b))) else (if i < 799 then decide (2 ≤ count797 b) else (if i < 800 then decide (1 ≤ count799 b) else decide (2 ≤ count799 b))))) else (if i < 807 then (if i < 804 then (if i < 802 then decide (1 ≤ count801 b) else (if i < 803 then decide (2 ≤ count801 b) else decide (3 ≤ count801 b))) else (if i < 805 then decide (4 ≤ count801 b) else (if i < 806 then decide (1 ≤ count805 b) else decide (2 ≤ count805 b)))) else (if i < 810 then (if i < 808 then decide (3 ≤ count805 b) else (if i < 809 then decide (4 ≤ count805 b) else decide (5 ≤ count805 b))) else (if i < 811 then decide (6 ≤ count805 b) else (if i < 812 then decide (7 ≤ count805 b) else decide (1 ≤ count812 b)))))) else (if i < 825 then (if i < 819 then (if i < 816 then (if i < 814 then decide (2 ≤ count812 b) else (if i < 815 then decide (3 ≤ count812 b) else decide (4 ≤ count812 b))) else (if i < 817 then decide (5 ≤ count812 b) else (if i < 818 then decide (6 ≤ count812 b) else decide (7 ≤ count812 b)))) else (if i < 822 then (if i < 820 then decide (8 ≤ count812 b) else (if i < 821 then decide (9 ≤ count812 b) else decide (10 ≤ count812 b))) else (if i < 823 then decide (11 ≤ count812 b) else (if i < 824 then decide (12 ≤ count812 b) else decide (13 ≤ count812 b))))) else (if i < 831 then (if i < 828 then (if i < 826 then decide (14 ≤ count812 b) else (if i < 827 then decide (1 ≤ count826 b) else decide (2 ≤ count826 b))) else (if i < 829 then decide (3 ≤ count826 b) else (if i < 830 then decide (4 ≤ count826 b) else decide (5 ≤ count826 b)))) else (if i < 834 then (if i < 832 then decide (6 ≤ count826 b) else (if i < 833 then decide (7 ≤ count826 b) else decide (8 ≤ count826 b))) else (if i < 835 then decide (9 ≤ count826 b) else (if i < 836 then decide (10 ≤ count826 b) else decide (11 ≤ count826 b)))))))) else (if i < 883 then (if i < 860 then (if i < 848 then (if i < 842 then (if i < 839 then (if i < 838 then decide (12 ≤ count826 b) else decide (13 ≤ count826 b)) else (if i < 840 then decide (14 ≤ count826 b) else (if i < 841 then decide (1 ≤ count840 b) else decide (2 ≤ count840 b)))) else (if i < 845 then (if i < 843 then decide (1 ≤ count842 b) else (if i < 844 then decide (2 ≤ count842 b) else decide (3 ≤ count842 b))) else (if i < 846 then decide (1 ≤ count845 b) else (if i < 847 then decide (2 ≤ count845 b) else decide (1 ≤ count847 b))))) else (if i < 854 then (if i < 851 then (if i < 849 then decide (2 ≤ count847 b) else (if i < 850 then decide (3 ≤ count847 b) else decide (1 ≤ count850 b))) else (if i < 852 then decide (2 ≤ count850 b) else (if i < 853 then decide (3 ≤ count850 b) else decide (4 ≤ count850 b)))) else (if i < 857 then (if i < 855 then decide (5 ≤ count850 b) else (if i < 856 then decide (6 ≤ count850 b) else decide (1 ≤ count856 b))) else (if i < 858 then decide (2 ≤ count856 b) else (if i < 859 then decide (1 ≤ count858 b) else decide (2 ≤ count858 b)))))) else (if i < 871 then (if i < 865 then (if i < 862 then (if i < 861 then decide (3 ≤ count858 b) else decide (1 ≤ count861 b)) else (if i < 863 then decide (2 ≤ count861 b) else (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b)))) else (if i < 868 then (if i < 866 then decide (1 ≤ count865 b) else (if i < 867 then decide (2 ≤ count865 b) else decide (3 ≤ count865 b))) else (if i < 869 then decide (4 ≤ count865 b) else (if i < 870 then decide (1 ≤ count869 b) else decide (2 ≤ count869 b))))) else (if i < 877 then (if i < 874 then (if i < 872 then decide (3 ≤ count869 b) else (if i < 873 then decide (4 ≤ count869 b) else decide (5 ≤ count869 b))) else (if i < 875 then decide (6 ≤ count869 b) else (if i < 876 then decide (7 ≤ count869 b) else decide (1 ≤ count876 b)))) else (if i < 880 then (if i < 878 then decide (2 ≤ count876 b) else (if i < 879 then decide (3 ≤ count876 b) else decide (4 ≤ count876 b))) else (if i < 881 then decide (5 ≤ count876 b) else (if i < 882 then decide (6 ≤ count876 b) else decide (7 ≤ count876 b))))))) else (if i < 906 then (if i < 894 then (if i < 888 then (if i < 885 then (if i < 884 then decide (8 ≤ count876 b) else decide (9 ≤ count876 b)) else (if i < 886 then decide (10 ≤ count876 b) else (if i < 887 then decide (11 ≤ count876 b) else decide (12 ≤ count876 b)))) else (if i < 891 then (if i < 889 then decide (13 ≤ count876 b) else (if i < 890 then decide (1 ≤ count889 b) else decide (2 ≤ count889 b))) else (if i < 892 then decide (1 ≤ count891 b) else (if i < 893 then decide (2 ≤ count891 b) else decide (3 ≤ count891 b))))) else (if i < 900 then (if i < 897 then (if i < 895 then decide (1 ≤ count894 b) else (if i < 896 then decide (2 ≤ count894 b) else decide (1 ≤ count896 b))) else (if i < 898 then decide (2 ≤ count896 b) else (if i < 899 then decide (1 ≤ count898 b) else decide (2 ≤ count898 b)))) else (if i < 903 then (if i < 901 then decide (3 ≤ count898 b) else (if i < 902 then decide (4 ≤ count898 b) else decide (1 ≤ count902 b))) else (if i < 904 then decide (2 ≤ count902 b) else (if i < 905 then decide (3 ≤ count902 b) else decide (4 ≤ count902 b)))))) else (if i < 918 then (if i < 912 then (if i < 909 then (if i < 907 then decide (5 ≤ count902 b) else (if i < 908 then decide (6 ≤ count902 b) else decide (7 ≤ count902 b))) else (if i < 910 then decide (1 ≤ count909 b) else (if i < 911 then decide (2 ≤ count909 b) else decide (1 ≤ count911 b)))) else (if i < 915 then (if i < 913 then decide (2 ≤ count911 b) else (if i < 914 then decide (3 ≤ count911 b) else decide (1 ≤ count914 b))) else (if i < 916 then decide (2 ≤ count914 b) else (if i < 917 then decide (1 ≤ count916 b) else decide (2 ≤ count916 b))))) else (if i < 924 then (if i < 921 then (if i < 919 then decide (1 ≤ count918 b) else (if i < 920 then decide (2 ≤ count918 b) else decide (3 ≤ count918 b))) else (if i < 922 then decide (4 ≤ count918 b) else (if i < 923 then decide (1 ≤ count922 b) else decide (2 ≤ count922 b)))) else (if i < 927 then (if i < 925 then decide (3 ≤ count922 b) else (if i < 926 then decide (4 ≤ count922 b) else decide (5 ≤ count922 b))) else (if i < 928 then decide (6 ≤ count922 b) else (if i < 929 then decide (7 ≤ count922 b) else decide (1 ≤ count929 b))))))))) else (if i < 1023 then (if i < 976 then (if i < 953 then (if i < 941 then (if i < 935 then (if i < 932 then (if i < 931 then decide (2 ≤ count929 b) else decide (3 ≤ count929 b)) else (if i < 933 then decide (4 ≤ count929 b) else (if i < 934 then decide (5 ≤ count929 b) else decide (6 ≤ count929 b)))) else (if i < 938 then (if i < 936 then decide (7 ≤ count929 b) else (if i < 937 then decide (8 ≤ count929 b) else decide (9 ≤ count929 b))) else (if i < 939 then decide (10 ≤ count929 b) else (if i < 940 then decide (11 ≤ count929 b) else decide (12 ≤ count929 b))))) else (if i < 947 then (if i < 944 then (if i < 942 then decide (13 ≤ count929 b) else (if i < 943 then decide (14 ≤ count929 b) else decide (1 ≤ count943 b))) else (if i < 945 then decide (2 ≤ count943 b) else (if i < 946 then decide (3 ≤ count943 b) else decide (4 ≤ count943 b)))) else (if i < 950 then (if i < 948 then decide (5 ≤ count943 b) else (if i < 949 then decide (6 ≤ count943 b) else decide (7 ≤ count943 b))) else (if i < 951 then decide (8 ≤ count943 b) else (if i < 952 then decide (9 ≤ count943 b) else decide (10 ≤ count943 b)))))) else (if i < 964 then (if i < 958 then (if i < 955 then (if i < 954 then decide (11 ≤ count943 b) else decide (12 ≤ count943 b)) else (if i < 956 then decide (13 ≤ count943 b) else (if i < 957 then decide (14 ≤ count943 b) else decide (1 ≤ count957 b)))) else (if i < 961 then (if i < 959 then decide (2 ≤ count957 b) else (if i < 960 then decide (3 ≤ count957 b) else decide (4 ≤ count957 b))) else (if i < 962 then decide (5 ≤ count957 b) else (if i < 963 then decide (6 ≤ count957 b) else decide (7 ≤ count957 b))))) else (if i < 970 then (if i < 967 then (if i < 965 then decide (8 ≤ count957 b) else (if i < 966 then decide (9 ≤ count957 b) else decide (10 ≤ count957 b))) else (if i < 968 then decide (11 ≤ count957 b) else (if i < 969 then decide (12 ≤ count957 b) else decide (13 ≤ count957 b)))) else (if i < 973 then (if i < 971 then decide (14 ≤ count957 b) else (if i < 972 then decide (1 ≤ count971 b) else decide (2 ≤ count971 b))) else (if i < 974 then decide (1 ≤ count973 b) else (if i < 975 then decide (2 ≤ count973 b) else decide (3 ≤ count973 b))))))) else (if i < 999 then (if i < 987 then (if i < 981 then (if i < 978 then (if i < 977 then decide (1 ≤ count976 b) else decide (2 ≤ count976 b)) else (if i < 979 then decide (1 ≤ count978 b) else (if i < 980 then decide (2 ≤ count978 b) else decide (3 ≤ count978 b)))) else (if i < 984 then (if i < 982 then decide (1 ≤ count981 b) else (if i < 983 then decide (2 ≤ count981 b) else decide (3 ≤ count981 b))) else (if i < 985 then decide (4 ≤ count981 b) else (if i < 986 then decide (5 ≤ count981 b) else decide (6 ≤ count981 b))))) else (if i < 993 then (if i < 990 then (if i < 988 then decide (1 ≤ count987 b) else (if i < 989 then decide (2 ≤ count987 b) else decide (1 ≤ count989 b))) else (if i < 991 then decide (2 ≤ count989 b) else (if i < 992 then decide (3 ≤ count989 b) else decide (1 ≤ count992 b)))) else (if i < 996 then (if i < 994 then decide (2 ≤ count992 b) else (if i < 995 then decide (1 ≤ count994 b) else decide (2 ≤ count994 b))) else (if i < 997 then decide (1 ≤ count996 b) else (if i < 998 then decide (2 ≤ count996 b) else decide (3 ≤ count996 b)))))) else (if i < 1011 then (if i < 1005 then (if i < 1002 then (if i < 1000 then decide (4 ≤ count996 b) else (if i < 1001 then decide (1 ≤ count1000 b) else decide (2 ≤ count1000 b))) else (if i < 1003 then decide (3 ≤ count1000 b) else (if i < 1004 then decide (4 ≤ count1000 b) else decide (5 ≤ count1000 b)))) else (if i < 1008 then (if i < 1006 then decide (6 ≤ count1000 b) else (if i < 1007 then decide (7 ≤ count1000 b) else decide (1 ≤ count1007 b))) else (if i < 1009 then decide (2 ≤ count1007 b) else (if i < 1010 then decide (3 ≤ count1007 b) else decide (4 ≤ count1007 b))))) else (if i < 1017 then (if i < 1014 then (if i < 1012 then decide (5 ≤ count1007 b) else (if i < 1013 then decide (6 ≤ count1007 b) else decide (7 ≤ count1007 b))) else (if i < 1015 then decide (8 ≤ count1007 b) else (if i < 1016 then decide (9 ≤ count1007 b) else decide (10 ≤ count1007 b)))) else (if i < 1020 then (if i < 1018 then decide (11 ≤ count1007 b) else (if i < 1019 then decide (12 ≤ count1007 b) else decide (13 ≤ count1007 b))) else (if i < 1021 then decide (1 ≤ count1020 b) else (if i < 1022 then decide (2 ≤ count1020 b) else decide (1 ≤ count1022 b)))))))) else (if i < 1069 then (if i < 1046 then (if i < 1034 then (if i < 1028 then (if i < 1025 then (if i < 1024 then decide (2 ≤ count1022 b) else decide (3 ≤ count1022 b)) else (if i < 1026 then decide (1 ≤ count1025 b) else (if i < 1027 then decide (2 ≤ count1025 b) else decide (1 ≤ count1027 b)))) else (if i < 1031 then (if i < 1029 then decide (2 ≤ count1027 b) else (if i < 1030 then decide (3 ≤ count1027 b) else decide (1 ≤ count1030 b))) else (if i < 1032 then decide (2 ≤ count1030 b) else (if i < 1033 then decide (3 ≤ count1030 b) else decide (4 ≤ count1030 b))))) else (if i < 1040 then (if i < 1037 then (if i < 1035 then decide (5 ≤ count1030 b) else (if i < 1036 then decide (6 ≤ count1030 b) else decide (1 ≤ count1036 b))) else (if i < 1038 then decide (2 ≤ count1036 b) else (if i < 1039 then decide (1 ≤ count1038 b) else decide (2 ≤ count1038 b)))) else (if i < 1043 then (if i < 1041 then decide (3 ≤ count1038 b) else (if i < 1042 then decide (1 ≤ count1041 b) else decide (2 ≤ count1041 b))) else (if i < 1044 then decide (1 ≤ count1043 b) else (if i < 1045 then decide (2 ≤ count1043 b) else decide (1 ≤ count1045 b)))))) else (if i < 1057 then (if i < 1051 then (if i < 1048 then (if i < 1047 then decide (2 ≤ count1045 b) else decide (3 ≤ count1045 b)) else (if i < 1049 then decide (4 ≤ count1045 b) else (if i < 1050 then decide (1 ≤ count1049 b) else decide (2 ≤ count1049 b)))) else (if i < 1054 then (if i < 1052 then decide (3 ≤ count1049 b) else (if i < 1053 then decide (4 ≤ count1049 b) else decide (5 ≤ count1049 b))) else (if i < 1055 then decide (6 ≤ count1049 b) else (if i < 1056 then decide (7 ≤ count1049 b) else decide (1 ≤ count1056 b))))) else (if i < 1063 then (if i < 1060 then (if i < 1058 then decide (2 ≤ count1056 b) else (if i < 1059 then decide (3 ≤ count1056 b) else decide (4 ≤ count1056 b))) else (if i < 1061 then decide (5 ≤ count1056 b) else (if i < 1062 then decide (6 ≤ count1056 b) else decide (7 ≤ count1056 b)))) else (if i < 1066 then (if i < 1064 then decide (8 ≤ count1056 b) else (if i < 1065 then decide (9 ≤ count1056 b) else decide (10 ≤ count1056 b))) else (if i < 1067 then decide (11 ≤ count1056 b) else (if i < 1068 then decide (12 ≤ count1056 b) else decide (13 ≤ count1056 b))))))) else (if i < 1092 then (if i < 1080 then (if i < 1074 then (if i < 1071 then (if i < 1070 then decide (1 ≤ count1069 b) else decide (2 ≤ count1069 b)) else (if i < 1072 then decide (3 ≤ count1069 b) else (if i < 1073 then decide (4 ≤ count1069 b) else decide (5 ≤ count1069 b)))) else (if i < 1077 then (if i < 1075 then decide (6 ≤ count1069 b) else (if i < 1076 then decide (7 ≤ count1069 b) else decide (8 ≤ count1069 b))) else (if i < 1078 then decide (9 ≤ count1069 b) else (if i < 1079 then decide (10 ≤ count1069 b) else decide (11 ≤ count1069 b))))) else (if i < 1086 then (if i < 1083 then (if i < 1081 then decide (12 ≤ count1069 b) else (if i < 1082 then decide (13 ≤ count1069 b) else decide (14 ≤ count1069 b))) else (if i < 1084 then decide (15 ≤ count1069 b) else (if i < 1085 then decide (16 ≤ count1069 b) else decide (17 ≤ count1069 b)))) else (if i < 1089 then (if i < 1087 then decide (18 ≤ count1069 b) else (if i < 1088 then decide (19 ≤ count1069 b) else decide (20 ≤ count1069 b))) else (if i < 1090 then decide (21 ≤ count1069 b) else (if i < 1091 then decide (22 ≤ count1069 b) else decide (23 ≤ count1069 b)))))) else (if i < 1104 then (if i < 1098 then (if i < 1095 then (if i < 1093 then decide (24 ≤ count1069 b) else (if i < 1094 then decide (25 ≤ count1069 b) else decide (26 ≤ count1069 b))) else (if i < 1096 then decide (1 ≤ count1095 b) else (if i < 1097 then decide (2 ≤ count1095 b) else decide (1 ≤ count1097 b)))) else (if i < 1101 then (if i < 1099 then decide (2 ≤ count1097 b) else (if i < 1100 then decide (3 ≤ count1097 b) else decide (1 ≤ count1100 b))) else (if i < 1102 then decide (2 ≤ count1100 b) else (if i < 1103 then decide (1 ≤ count1102 b) else decide (2 ≤ count1102 b))))) else (if i < 1110 then (if i < 1107 then (if i < 1105 then decide (3 ≤ count1102 b) else (if i < 1106 then decide (1 ≤ count1105 b) else decide (2 ≤ count1105 b))) else (if i < 1108 then decide (3 ≤ count1105 b) else (if i < 1109 then decide (4 ≤ count1105 b) else decide (5 ≤ count1105 b)))) else (if i < 1113 then (if i < 1111 then decide (6 ≤ count1105 b) else (if i < 1112 then decide (1 ≤ count1111 b) else decide (2 ≤ count1111 b))) else (if i < 1114 then decide (1 ≤ count1113 b) else (if i < 1115 then decide (2 ≤ count1113 b) else decide (3 ≤ count1113 b)))))))))) else (if i < 1302 then (if i < 1209 then (if i < 1162 then (if i < 1139 then (if i < 1127 then (if i < 1121 then (if i < 1118 then (if i < 1117 then decide (1 ≤ count1116 b) else decide (2 ≤ count1116 b)) else (if i < 1119 then decide (1 ≤ count1118 b) else (if i < 1120 then decide (2 ≤ count1118 b) else decide (1 ≤ count1120 b)))) else (if i < 1124 then (if i < 1122 then decide (2 ≤ count1120 b) else (if i < 1123 then decide (3 ≤ count1120 b) else decide (4 ≤ count1120 b))) else (if i < 1125 then decide (1 ≤ count1124 b) else (if i < 1126 then decide (2 ≤ count1124 b) else decide (3 ≤ count1124 b))))) else (if i < 1133 then (if i < 1130 then (if i < 1128 then decide (4 ≤ count1124 b) else (if i < 1129 then decide (5 ≤ count1124 b) else decide (6 ≤ count1124 b))) else (if i < 1131 then decide (7 ≤ count1124 b) else (if i < 1132 then decide (1 ≤ count1131 b) else decide (2 ≤ count1131 b)))) else (if i < 1136 then (if i < 1134 then decide (3 ≤ count1131 b) else (if i < 1135 then decide (4 ≤ count1131 b) else decide (5 ≤ count1131 b))) else (if i < 1137 then decide (6 ≤ count1131 b) else (if i < 1138 then decide (7 ≤ count1131 b) else decide (8 ≤ count1131 b)))))) else (if i < 1150 then (if i < 1144 then (if i < 1141 then (if i < 1140 then decide (9 ≤ count1131 b) else decide (10 ≤ count1131 b)) else (if i < 1142 then decide (11 ≤ count1131 b) else (if i < 1143 then decide (12 ≤ count1131 b) else decide (13 ≤ count1131 b)))) else (if i < 1147 then (if i < 1145 then decide (1 ≤ count1144 b) else (if i < 1146 then decide (2 ≤ count1144 b) else decide (1 ≤ count1146 b))) else (if i < 1148 then decide (2 ≤ count1146 b) else (if i < 1149 then decide (3 ≤ count1146 b) else decide (1 ≤ count1149 b))))) else (if i < 1156 then (if i < 1153 then (if i < 1151 then decide (2 ≤ count1149 b) else (if i < 1152 then decide (1 ≤ count1151 b) else decide (2 ≤ count1151 b))) else (if i < 1154 then decide (3 ≤ count1151 b) else (if i < 1155 then decide (1 ≤ count1154 b) else decide (2 ≤ count1154 b)))) else (if i < 1159 then (if i < 1157 then decide (3 ≤ count1154 b) else (if i < 1158 then decide (4 ≤ count1154 b) else decide (5 ≤ count1154 b))) else (if i < 1160 then decide (6 ≤ count1154 b) else (if i < 1161 then decide (1 ≤ count1160 b) else decide (2 ≤ count1160 b))))))) else (if i < 1185 then (if i < 1173 then (if i < 1167 then (if i < 1164 then (if i < 1163 then decide (1 ≤ count1162 b) else decide (2 ≤ count1162 b)) else (if i < 1165 then decide (3 ≤ count1162 b) else (if i < 1166 then decide (1 ≤ count1165 b) else decide (2 ≤ count1165 b)))) else (if i < 1170 then (if i < 1168 then decide (1 ≤ count1167 b) else (if i < 1169 then decide (2 ≤ count1167 b) else decide (1 ≤ count1169 b))) else (if i < 1171 then decide (2 ≤ count1169 b) else (if i < 1172 then decide (3 ≤ count1169 b) else decide (4 ≤ count1169 b))))) else (if i < 1179 then (if i < 1176 then (if i < 1174 then decide (1 ≤ count1173 b) else (if i < 1175 then decide (2 ≤ count1173 b) else decide (3 ≤ count1173 b))) else (if i < 1177 then decide (4 ≤ count1173 b) else (if i < 1178 then decide (5 ≤ count1173 b) else decide (6 ≤ count1173 b)))) else (if i < 1182 then (if i < 1180 then decide (7 ≤ count1173 b) else (if i < 1181 then decide (1 ≤ count1180 b) else decide (2 ≤ count1180 b))) else (if i < 1183 then decide (3 ≤ count1180 b) else (if i < 1184 then decide (4 ≤ count1180 b) else decide (5 ≤ count1180 b)))))) else (if i < 1197 then (if i < 1191 then (if i < 1188 then (if i < 1186 then decide (6 ≤ count1180 b) else (if i < 1187 then decide (7 ≤ count1180 b) else decide (8 ≤ count1180 b))) else (if i < 1189 then decide (9 ≤ count1180 b) else (if i < 1190 then decide (10 ≤ count1180 b) else decide (11 ≤ count1180 b)))) else (if i < 1194 then (if i < 1192 then decide (12 ≤ count1180 b) else (if i < 1193 then decide (13 ≤ count1180 b) else decide (1 ≤ count1193 b))) else (if i < 1195 then decide (2 ≤ count1193 b) else (if i < 1196 then decide (3 ≤ count1193 b) else decide (4 ≤ count1193 b))))) else (if i < 1203 then (if i < 1200 then (if i < 1198 then decide (5 ≤ count1193 b) else (if i < 1199 then decide (6 ≤ count1193 b) else decide (7 ≤ count1193 b))) else (if i < 1201 then decide (8 ≤ count1193 b) else (if i < 1202 then decide (9 ≤ count1193 b) else decide (10 ≤ count1193 b)))) else (if i < 1206 then (if i < 1204 then decide (11 ≤ count1193 b) else (if i < 1205 then decide (12 ≤ count1193 b) else decide (13 ≤ count1193 b))) else (if i < 1207 then decide (14 ≤ count1193 b) else (if i < 1208 then decide (15 ≤ count1193 b) else decide (16 ≤ count1193 b)))))))) else (if i < 1255 then (if i < 1232 then (if i < 1220 then (if i < 1214 then (if i < 1211 then (if i < 1210 then decide (17 ≤ count1193 b) else decide (18 ≤ count1193 b)) else (if i < 1212 then decide (19 ≤ count1193 b) else (if i < 1213 then decide (20 ≤ count1193 b) else decide (21 ≤ count1193 b)))) else (if i < 1217 then (if i < 1215 then decide (22 ≤ count1193 b) else (if i < 1216 then decide (23 ≤ count1193 b) else decide (24 ≤ count1193 b))) else (if i < 1218 then decide (25 ≤ count1193 b) else (if i < 1219 then decide (26 ≤ count1193 b) else decide (1 ≤ count1219 b))))) else (if i < 1226 then (if i < 1223 then (if i < 1221 then decide (2 ≤ count1219 b) else (if i < 1222 then decide (3 ≤ count1219 b) else decide (4 ≤ count1219 b))) else (if i < 1224 then decide (5 ≤ count1219 b) else (if i < 1225 then decide (6 ≤ count1219 b) else decide (7 ≤ count1219 b)))) else (if i < 1229 then (if i < 1227 then decide (8 ≤ count1219 b) else (if i < 1228 then decide (9 ≤ count1219 b) else decide (10 ≤ count1219 b))) else (if i < 1230 then decide (11 ≤ count1219 b) else (if i < 1231 then decide (12 ≤ count1219 b) else decide (13 ≤ count1219 b)))))) else (if i < 1243 then (if i < 1237 then (if i < 1234 then (if i < 1233 then decide (14 ≤ count1219 b) else decide (15 ≤ count1219 b)) else (if i < 1235 then decide (16 ≤ count1219 b) else (if i < 1236 then decide (17 ≤ count1219 b) else decide (18 ≤ count1219 b)))) else (if i < 1240 then (if i < 1238 then decide (19 ≤ count1219 b) else (if i < 1239 then decide (20 ≤ count1219 b) else decide (21 ≤ count1219 b))) else (if i < 1241 then decide (22 ≤ count1219 b) else (if i < 1242 then decide (23 ≤ count1219 b) else decide (24 ≤ count1219 b))))) else (if i < 1249 then (if i < 1246 then (if i < 1244 then decide (25 ≤ count1219 b) else (if i < 1245 then decide (26 ≤ count1219 b) else decide (27 ≤ count1219 b))) else (if i < 1247 then decide (28 ≤ count1219 b) else (if i < 1248 then decide (29 ≤ count1219 b) else decide (30 ≤ count1219 b)))) else (if i < 1252 then (if i < 1250 then decide (31 ≤ count1219 b) else (if i < 1251 then decide (32 ≤ count1219 b) else decide (33 ≤ count1219 b))) else (if i < 1253 then decide (34 ≤ count1219 b) else (if i < 1254 then decide (35 ≤ count1219 b) else decide (36 ≤ count1219 b))))))) else (if i < 1278 then (if i < 1266 then (if i < 1260 then (if i < 1257 then (if i < 1256 then decide (37 ≤ count1219 b) else decide (38 ≤ count1219 b)) else (if i < 1258 then decide (39 ≤ count1219 b) else (if i < 1259 then decide (40 ≤ count1219 b) else decide (41 ≤ count1219 b)))) else (if i < 1263 then (if i < 1261 then decide (42 ≤ count1219 b) else (if i < 1262 then decide (1 ≤ count1261 b) else decide (2 ≤ count1261 b))) else (if i < 1264 then decide (1 ≤ count1263 b) else (if i < 1265 then decide (2 ≤ count1263 b) else decide (3 ≤ count1263 b))))) else (if i < 1272 then (if i < 1269 then (if i < 1267 then decide (1 ≤ count1266 b) else (if i < 1268 then decide (2 ≤ count1266 b) else decide (1 ≤ count1268 b))) else (if i < 1270 then decide (2 ≤ count1268 b) else (if i < 1271 then decide (3 ≤ count1268 b) else decide (1 ≤ count1271 b)))) else (if i < 1275 then (if i < 1273 then decide (2 ≤ count1271 b) else (if i < 1274 then decide (3 ≤ count1271 b) else decide (4 ≤ count1271 b))) else (if i < 1276 then decide (5 ≤ count1271 b) else (if i < 1277 then decide (6 ≤ count1271 b) else decide (1 ≤ count1277 b)))))) else (if i < 1290 then (if i < 1284 then (if i < 1281 then (if i < 1279 then decide (2 ≤ count1277 b) else (if i < 1280 then decide (1 ≤ count1279 b) else decide (2 ≤ count1279 b))) else (if i < 1282 then decide (3 ≤ count1279 b) else (if i < 1283 then decide (1 ≤ count1282 b) else decide (2 ≤ count1282 b)))) else (if i < 1287 then (if i < 1285 then decide (1 ≤ count1284 b) else (if i < 1286 then decide (2 ≤ count1284 b) else decide (1 ≤ count1286 b))) else (if i < 1288 then decide (2 ≤ count1286 b) else (if i < 1289 then decide (3 ≤ count1286 b) else decide (4 ≤ count1286 b))))) else (if i < 1296 then (if i < 1293 then (if i < 1291 then decide (1 ≤ count1290 b) else (if i < 1292 then decide (2 ≤ count1290 b) else decide (3 ≤ count1290 b))) else (if i < 1294 then decide (4 ≤ count1290 b) else (if i < 1295 then decide (5 ≤ count1290 b) else decide (6 ≤ count1290 b)))) else (if i < 1299 then (if i < 1297 then decide (7 ≤ count1290 b) else (if i < 1298 then decide (1 ≤ count1297 b) else decide (2 ≤ count1297 b))) else (if i < 1300 then decide (3 ≤ count1297 b) else (if i < 1301 then decide (4 ≤ count1297 b) else decide (5 ≤ count1297 b))))))))) else (if i < 1395 then (if i < 1348 then (if i < 1325 then (if i < 1313 then (if i < 1307 then (if i < 1304 then (if i < 1303 then decide (6 ≤ count1297 b) else decide (7 ≤ count1297 b)) else (if i < 1305 then decide (8 ≤ count1297 b) else (if i < 1306 then decide (9 ≤ count1297 b) else decide (10 ≤ count1297 b)))) else (if i < 1310 then (if i < 1308 then decide (11 ≤ count1297 b) else (if i < 1309 then decide (12 ≤ count1297 b) else decide (1 ≤ count1309 b))) else (if i < 1311 then decide (2 ≤ count1309 b) else (if i < 1312 then decide (1 ≤ count1311 b) else decide (2 ≤ count1311 b))))) else (if i < 1319 then (if i < 1316 then (if i < 1314 then decide (3 ≤ count1311 b) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b))) else (if i < 1317 then decide (1 ≤ count1316 b) else (if i < 1318 then decide (2 ≤ count1316 b) else decide (3 ≤ count1316 b)))) else (if i < 1322 then (if i < 1320 then decide (1 ≤ count1319 b) else (if i < 1321 then decide (2 ≤ count1319 b) else decide (3 ≤ count1319 b))) else (if i < 1323 then decide (4 ≤ count1319 b) else (if i < 1324 then decide (5 ≤ count1319 b) else decide (6 ≤ count1319 b)))))) else (if i < 1336 then (if i < 1330 then (if i < 1327 then (if i < 1326 then decide (1 ≤ count1325 b) else decide (2 ≤ count1325 b)) else (if i < 1328 then decide (1 ≤ count1327 b) else (if i < 1329 then decide (2 ≤ count1327 b) else decide (3 ≤ count1327 b)))) else (if i < 1333 then (if i < 1331 then decide (1 ≤ count1330 b) else (if i < 1332 then decide (2 ≤ count1330 b) else decide (1 ≤ count1332 b))) else (if i < 1334 then decide (2 ≤ count1332 b) else (if i < 1335 then decide (1 ≤ count1334 b) else decide (2 ≤ count1334 b))))) else (if i < 1342 then (if i < 1339 then (if i < 1337 then decide (3 ≤ count1334 b) else (if i < 1338 then decide (4 ≤ count1334 b) else decide (1 ≤ count1338 b))) else (if i < 1340 then decide (2 ≤ count1338 b) else (if i < 1341 then decide (3 ≤ count1338 b) else decide (4 ≤ count1338 b)))) else (if i < 1345 then (if i < 1343 then decide (5 ≤ count1338 b) else (if i < 1344 then decide (6 ≤ count1338 b) else decide (7 ≤ count1338 b))) else (if i < 1346 then decide (1 ≤ count1345 b) else (if i < 1347 then decide (2 ≤ count1345 b) else decide (3 ≤ count1345 b))))))) else (if i < 1371 then (if i < 1359 then (if i < 1353 then (if i < 1350 then (if i < 1349 then decide (4 ≤ count1345 b) else decide (5 ≤ count1345 b)) else (if i < 1351 then decide (6 ≤ count1345 b) else (if i < 1352 then decide (7 ≤ count1345 b) else decide (8 ≤ count1345 b)))) else (if i < 1356 then (if i < 1354 then decide (9 ≤ count1345 b) else (if i < 1355 then decide (10 ≤ count1345 b) else decide (11 ≤ count1345 b))) else (if i < 1357 then decide (12 ≤ count1345 b) else (if i < 1358 then decide (1 ≤ count1357 b) else decide (2 ≤ count1357 b))))) else (if i < 1365 then (if i < 1362 then (if i < 1360 then decide (3 ≤ count1357 b) else (if i < 1361 then decide (4 ≤ count1357 b) else decide (5 ≤ count1357 b))) else (if i < 1363 then decide (6 ≤ count1357 b) else (if i < 1364 then decide (7 ≤ count1357 b) else decide (8 ≤ count1357 b)))) else (if i < 1368 then (if i < 1366 then decide (9 ≤ count1357 b) else (if i < 1367 then decide (10 ≤ count1357 b) else decide (11 ≤ count1357 b))) else (if i < 1369 then decide (12 ≤ count1357 b) else (if i < 1370 then decide (1 ≤ count1369 b) else decide (2 ≤ count1369 b)))))) else (if i < 1383 then (if i < 1377 then (if i < 1374 then (if i < 1372 then decide (1 ≤ count1371 b) else (if i < 1373 then decide (2 ≤ count1371 b) else decide (3 ≤ count1371 b))) else (if i < 1375 then decide (1 ≤ count1374 b) else (if i < 1376 then decide (2 ≤ count1374 b) else decide (1 ≤ count1376 b)))) else (if i < 1380 then (if i < 1378 then decide (2 ≤ count1376 b) else (if i < 1379 then decide (3 ≤ count1376 b) else decide (1 ≤ count1379 b))) else (if i < 1381 then decide (2 ≤ count1379 b) else (if i < 1382 then decide (3 ≤ count1379 b) else decide (4 ≤ count1379 b))))) else (if i < 1389 then (if i < 1386 then (if i < 1384 then decide (5 ≤ count1379 b) else (if i < 1385 then decide (6 ≤ count1379 b) else decide (1 ≤ count1385 b))) else (if i < 1387 then decide (2 ≤ count1385 b) else (if i < 1388 then decide (1 ≤ count1387 b) else decide (2 ≤ count1387 b)))) else (if i < 1392 then (if i < 1390 then decide (3 ≤ count1387 b) else (if i < 1391 then decide (1 ≤ count1390 b) else decide (2 ≤ count1390 b))) else (if i < 1393 then decide (1 ≤ count1392 b) else (if i < 1394 then decide (2 ≤ count1392 b) else decide (1 ≤ count1394 b)))))))) else (if i < 1442 then (if i < 1418 then (if i < 1406 then (if i < 1400 then (if i < 1397 then (if i < 1396 then decide (2 ≤ count1394 b) else decide (3 ≤ count1394 b)) else (if i < 1398 then decide (4 ≤ count1394 b) else (if i < 1399 then decide (1 ≤ count1398 b) else decide (2 ≤ count1398 b)))) else (if i < 1403 then (if i < 1401 then decide (3 ≤ count1398 b) else (if i < 1402 then decide (4 ≤ count1398 b) else decide (5 ≤ count1398 b))) else (if i < 1404 then decide (6 ≤ count1398 b) else (if i < 1405 then decide (7 ≤ count1398 b) else decide (1 ≤ count1405 b))))) else (if i < 1412 then (if i < 1409 then (if i < 1407 then decide (2 ≤ count1405 b) else (if i < 1408 then decide (3 ≤ count1405 b) else decide (4 ≤ count1405 b))) else (if i < 1410 then decide (5 ≤ count1405 b) else (if i < 1411 then decide (6 ≤ count1405 b) else decide (7 ≤ count1405 b)))) else (if i < 1415 then (if i < 1413 then decide (8 ≤ count1405 b) else (if i < 1414 then decide (9 ≤ count1405 b) else decide (10 ≤ count1405 b))) else (if i < 1416 then decide (11 ≤ count1405 b) else (if i < 1417 then decide (12 ≤ count1405 b) else decide (1 ≤ count1417 b)))))) else (if i < 1430 then (if i < 1424 then (if i < 1421 then (if i < 1419 then decide (2 ≤ count1417 b) else (if i < 1420 then decide (1 ≤ count1419 b) else decide (2 ≤ count1419 b))) else (if i < 1422 then decide (3 ≤ count1419 b) else (if i < 1423 then decide (1 ≤ count1422 b) else decide (2 ≤ count1422 b)))) else (if i < 1427 then (if i < 1425 then decide (1 ≤ count1424 b) else (if i < 1426 then decide (2 ≤ count1424 b) else decide (3 ≤ count1424 b))) else (if i < 1428 then decide (1 ≤ count1427 b) else (if i < 1429 then decide (2 ≤ count1427 b) else decide (3 ≤ count1427 b))))) else (if i < 1436 then (if i < 1433 then (if i < 1431 then decide (4 ≤ count1427 b) else (if i < 1432 then decide (5 ≤ count1427 b) else decide (6 ≤ count1427 b))) else (if i < 1434 then decide (1 ≤ count1433 b) else (if i < 1435 then decide (2 ≤ count1433 b) else decide (1 ≤ count1435 b)))) else (if i < 1439 then (if i < 1437 then decide (2 ≤ count1435 b) else (if i < 1438 then decide (3 ≤ count1435 b) else decide (1 ≤ count1438 b))) else (if i < 1440 then decide (2 ≤ count1438 b) else (if i < 1441 then decide (1 ≤ count1440 b) else decide (2 ≤ count1440 b))))))) else (if i < 1465 then (if i < 1453 then (if i < 1447 then (if i < 1444 then (if i < 1443 then decide (1 ≤ count1442 b) else decide (2 ≤ count1442 b)) else (if i < 1445 then decide (3 ≤ count1442 b) else (if i < 1446 then decide (4 ≤ count1442 b) else decide (1 ≤ count1446 b)))) else (if i < 1450 then (if i < 1448 then decide (2 ≤ count1446 b) else (if i < 1449 then decide (3 ≤ count1446 b) else decide (4 ≤ count1446 b))) else (if i < 1451 then decide (5 ≤ count1446 b) else (if i < 1452 then decide (6 ≤ count1446 b) else decide (7 ≤ count1446 b))))) else (if i < 1459 then (if i < 1456 then (if i < 1454 then decide (1 ≤ count1453 b) else (if i < 1455 then decide (2 ≤ count1453 b) else decide (3 ≤ count1453 b))) else (if i < 1457 then decide (4 ≤ count1453 b) else (if i < 1458 then decide (5 ≤ count1453 b) else decide (6 ≤ count1453 b)))) else (if i < 1462 then (if i < 1460 then decide (7 ≤ count1453 b) else (if i < 1461 then decide (8 ≤ count1453 b) else decide (9 ≤ count1453 b))) else (if i < 1463 then decide (10 ≤ count1453 b) else (if i < 1464 then decide (11 ≤ count1453 b) else decide (12 ≤ count1453 b)))))) else (if i < 1477 then (if i < 1471 then (if i < 1468 then (if i < 1466 then decide (1 ≤ count1465 b) else (if i < 1467 then decide (2 ≤ count1465 b) else decide (3 ≤ count1465 b))) else (if i < 1469 then decide (4 ≤ count1465 b) else (if i < 1470 then decide (5 ≤ count1465 b) else decide (6 ≤ count1465 b)))) else (if i < 1474 then (if i < 1472 then decide (7 ≤ count1465 b) else (if i < 1473 then decide (8 ≤ count1465 b) else decide (9 ≤ count1465 b))) else (if i < 1475 then decide (10 ≤ count1465 b) else (if i < 1476 then decide (11 ≤ count1465 b) else decide (12 ≤ count1465 b))))) else (if i < 1483 then (if i < 1480 then (if i < 1478 then decide (1 ≤ count1477 b) else (if i < 1479 then decide (2 ≤ count1477 b) else decide (3 ≤ count1477 b))) else (if i < 1481 then decide (4 ≤ count1477 b) else (if i < 1482 then decide (5 ≤ count1477 b) else decide (6 ≤ count1477 b)))) else (if i < 1486 then (if i < 1484 then decide (7 ≤ count1477 b) else (if i < 1485 then decide (8 ≤ count1477 b) else decide (9 ≤ count1477 b))) else (if i < 1487 then decide (10 ≤ count1477 b) else (if i < 1488 then decide (11 ≤ count1477 b) else decide (12 ≤ count1477 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (13 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (14 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (17 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (21 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (25 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (29 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (30 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (31 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (67 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (69 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (71 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (74 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (75 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (79 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (80 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (81 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (84 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (88 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (89 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (94 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (95 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (131 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (132 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (133 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (135 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (138 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (139 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (143 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (144 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (145 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (148 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (152 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (153 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (158 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (227 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (229 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (231 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (234 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (235 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (239 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (240 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (241 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (244 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (248 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (254 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (255 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (356 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (357 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (359 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (360 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (362 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (363 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (367 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (369 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (372 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (374 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (376 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (377 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (382 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (383 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (384 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (386 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (387 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (388 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (390 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (396 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (397 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (398 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (400 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (401 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (403 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (405 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (407 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (409 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (411 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (413 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (415 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (451 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (452 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (453 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (455 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (463 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (464 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (465 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (468 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (479 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (497 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (501 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (503 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (511 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (67 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (74 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (81 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (145 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (241 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (254 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (356 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (359 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (360 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (362 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (363 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (367 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (369 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (372 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (374 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (377 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (382 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (398 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (405 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (451 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (463 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (465 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (468 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (501 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (503 : Vertex)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 (baseVal q)) := rfl
theorem value420 (q : Snake 81) : valuation q 420 = decide (2 ≤ count419 (baseVal q)) := rfl
theorem value1261 (q : Snake 81) : valuation q 1261 = decide (1 ≤ count1261 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (2 ≤ count1261 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (1 ≤ count1263 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (2 ≤ count1263 (baseVal q)) := rfl
theorem value1266 (q : Snake 81) : valuation q 1266 = decide (1 ≤ count1266 (baseVal q)) := rfl
theorem value1267 (q : Snake 81) : valuation q 1267 = decide (2 ≤ count1266 (baseVal q)) := rfl
theorem value1268 (q : Snake 81) : valuation q 1268 = decide (1 ≤ count1268 (baseVal q)) := rfl
theorem value1269 (q : Snake 81) : valuation q 1269 = decide (2 ≤ count1268 (baseVal q)) := rfl
theorem value1270 (q : Snake 81) : valuation q 1270 = decide (3 ≤ count1268 (baseVal q)) := rfl
theorem value1271 (q : Snake 81) : valuation q 1271 = decide (1 ≤ count1271 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (2 ≤ count1271 (baseVal q)) := rfl
theorem value1273 (q : Snake 81) : valuation q 1273 = decide (3 ≤ count1271 (baseVal q)) := rfl
theorem value1274 (q : Snake 81) : valuation q 1274 = decide (4 ≤ count1271 (baseVal q)) := rfl
theorem value1277 (q : Snake 81) : valuation q 1277 = decide (1 ≤ count1277 (baseVal q)) := rfl
theorem value1279 (q : Snake 81) : valuation q 1279 = decide (1 ≤ count1279 (baseVal q)) := rfl
theorem value1282 (q : Snake 81) : valuation q 1282 = decide (1 ≤ count1282 (baseVal q)) := rfl
theorem value1284 (q : Snake 81) : valuation q 1284 = decide (1 ≤ count1284 (baseVal q)) := rfl
theorem value1285 (q : Snake 81) : valuation q 1285 = decide (2 ≤ count1284 (baseVal q)) := rfl
theorem value1286 (q : Snake 81) : valuation q 1286 = decide (1 ≤ count1286 (baseVal q)) := rfl
theorem value1287 (q : Snake 81) : valuation q 1287 = decide (2 ≤ count1286 (baseVal q)) := rfl
theorem value1290 (q : Snake 81) : valuation q 1290 = decide (1 ≤ count1290 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (2 ≤ count1290 (baseVal q)) := rfl
theorem value1292 (q : Snake 81) : valuation q 1292 = decide (3 ≤ count1290 (baseVal q)) := rfl
theorem value1298 (q : Snake 81) : valuation q 1298 = decide (2 ≤ count1297 (baseVal q)) := rfl
theorem value1299 (q : Snake 81) : valuation q 1299 = decide (3 ≤ count1297 (baseVal q)) := rfl
theorem value1300 (q : Snake 81) : valuation q 1300 = decide (4 ≤ count1297 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (5 ≤ count1297 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (1 ≤ count1309 (baseVal q)) := rfl
theorem value1310 (q : Snake 81) : valuation q 1310 = decide (2 ≤ count1309 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (1 ≤ count1311 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (2 ≤ count1311 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (1 ≤ count1314 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (2 ≤ count1314 (baseVal q)) := rfl
theorem value1316 (q : Snake 81) : valuation q 1316 = decide (1 ≤ count1316 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (2 ≤ count1316 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (1 ≤ count1319 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (2 ≤ count1319 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (3 ≤ count1319 (baseVal q)) := rfl
theorem value1325 (q : Snake 81) : valuation q 1325 = decide (1 ≤ count1325 (baseVal q)) := rfl
theorem value1326 (q : Snake 81) : valuation q 1326 = decide (2 ≤ count1325 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (1 ≤ count1327 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (2 ≤ count1327 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (1 ≤ count1330 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (1 ≤ count1332 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (2 ≤ count1332 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (1 ≤ count1334 (baseVal q)) := rfl
theorem value1335 (q : Snake 81) : valuation q 1335 = decide (2 ≤ count1334 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (1 ≤ count1338 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (2 ≤ count1338 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (3 ≤ count1338 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (2 ≤ count1345 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (3 ≤ count1345 (baseVal q)) := rfl
theorem value1348 (q : Snake 81) : valuation q 1348 = decide (4 ≤ count1345 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (5 ≤ count1345 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (5 ≤ count1357 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (6 ≤ count1357 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (7 ≤ count1357 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (1 ≤ count1369 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (1 ≤ count1371 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (1 ≤ count1379 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (2 ≤ count1385 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (1 ≤ count1387 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (3 ≤ count1387 (baseVal q)) := rfl
theorem value1390 (q : Snake 81) : valuation q 1390 = decide (1 ≤ count1390 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (1 ≤ count1392 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (2 ≤ count1392 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (1 ≤ count1394 (baseVal q)) := rfl
theorem value1395 (q : Snake 81) : valuation q 1395 = decide (2 ≤ count1394 (baseVal q)) := rfl
theorem value1396 (q : Snake 81) : valuation q 1396 = decide (3 ≤ count1394 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (1 ≤ count1398 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (2 ≤ count1398 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (3 ≤ count1398 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (4 ≤ count1398 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (1 ≤ count1405 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (2 ≤ count1405 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (3 ≤ count1405 (baseVal q)) := rfl
theorem value1408 (q : Snake 81) : valuation q 1408 = decide (4 ≤ count1405 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (1 ≤ count1417 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (2 ≤ count1417 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (1 ≤ count1419 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (2 ≤ count1419 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (3 ≤ count1419 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (1 ≤ count1422 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (2 ≤ count1422 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (1 ≤ count1424 (baseVal q)) := rfl
theorem value1425 (q : Snake 81) : valuation q 1425 = decide (2 ≤ count1424 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (1 ≤ count1427 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (2 ≤ count1427 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (3 ≤ count1427 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (4 ≤ count1427 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (5 ≤ count1427 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (1 ≤ count1433 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (2 ≤ count1433 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (1 ≤ count1435 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (2 ≤ count1435 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (3 ≤ count1435 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (1 ≤ count1438 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (2 ≤ count1438 (baseVal q)) := rfl
theorem value1440 (q : Snake 81) : valuation q 1440 = decide (1 ≤ count1440 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (2 ≤ count1440 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (1 ≤ count1442 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (2 ≤ count1442 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (3 ≤ count1442 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (1 ≤ count1446 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (2 ≤ count1446 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (3 ≤ count1446 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (4 ≤ count1446 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (3 ≤ count1453 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (4 ≤ count1453 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (5 ≤ count1453 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (6 ≤ count1453 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (7 ≤ count1453 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (5 ≤ count1465 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (6 ≤ count1465 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (7 ≤ count1465 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (12 ≤ count1477 (baseVal q)) := rfl
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
theorem meaningNeg67 (b : Nat → Bool) : literal (valuationOf b) (-67) = decide (1 ≤ countLit b [-67]) := by
  change literal b (-67) = decide (1 ≤ countLit b [-67])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-67) <;> decide
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
theorem meaningNeg46 (b : Nat → Bool) : literal (valuationOf b) (-46) = decide (1 ≤ countLit b [-46]) := by
  change literal b (-46) = decide (1 ≤ countLit b [-46])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-46) <;> decide
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
theorem meaning210 (b : Nat → Bool) : literal (valuationOf b) (210) = decide (1 ≤ countLit b [210]) := by
  change literal b (210) = decide (1 ≤ countLit b [210])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (210) <;> decide
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning418 (b : Nat → Bool) : literal (valuationOf b) 418 = decide (2 ≤ count417 b) := rfl
theorem meaning420 (b : Nat → Bool) : literal (valuationOf b) 420 = decide (2 ≤ count419 b) := rfl
theorem meaning1261 (b : Nat → Bool) : literal (valuationOf b) 1261 = decide (1 ≤ count1261 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (2 ≤ count1261 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (1 ≤ count1263 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (2 ≤ count1263 b) := rfl
theorem meaning1266 (b : Nat → Bool) : literal (valuationOf b) 1266 = decide (1 ≤ count1266 b) := rfl
theorem meaning1267 (b : Nat → Bool) : literal (valuationOf b) 1267 = decide (2 ≤ count1266 b) := rfl
theorem meaning1268 (b : Nat → Bool) : literal (valuationOf b) 1268 = decide (1 ≤ count1268 b) := rfl
theorem meaning1269 (b : Nat → Bool) : literal (valuationOf b) 1269 = decide (2 ≤ count1268 b) := rfl
theorem meaning1270 (b : Nat → Bool) : literal (valuationOf b) 1270 = decide (3 ≤ count1268 b) := rfl
theorem meaning1271 (b : Nat → Bool) : literal (valuationOf b) 1271 = decide (1 ≤ count1271 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (2 ≤ count1271 b) := rfl
theorem meaning1273 (b : Nat → Bool) : literal (valuationOf b) 1273 = decide (3 ≤ count1271 b) := rfl
theorem meaning1274 (b : Nat → Bool) : literal (valuationOf b) 1274 = decide (4 ≤ count1271 b) := rfl
theorem meaning1277 (b : Nat → Bool) : literal (valuationOf b) 1277 = decide (1 ≤ count1277 b) := rfl
theorem meaning1279 (b : Nat → Bool) : literal (valuationOf b) 1279 = decide (1 ≤ count1279 b) := rfl
theorem meaning1282 (b : Nat → Bool) : literal (valuationOf b) 1282 = decide (1 ≤ count1282 b) := rfl
theorem meaning1284 (b : Nat → Bool) : literal (valuationOf b) 1284 = decide (1 ≤ count1284 b) := rfl
theorem meaning1285 (b : Nat → Bool) : literal (valuationOf b) 1285 = decide (2 ≤ count1284 b) := rfl
theorem meaning1286 (b : Nat → Bool) : literal (valuationOf b) 1286 = decide (1 ≤ count1286 b) := rfl
theorem meaning1287 (b : Nat → Bool) : literal (valuationOf b) 1287 = decide (2 ≤ count1286 b) := rfl
theorem meaning1290 (b : Nat → Bool) : literal (valuationOf b) 1290 = decide (1 ≤ count1290 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (2 ≤ count1290 b) := rfl
theorem meaning1292 (b : Nat → Bool) : literal (valuationOf b) 1292 = decide (3 ≤ count1290 b) := rfl
theorem meaning1298 (b : Nat → Bool) : literal (valuationOf b) 1298 = decide (2 ≤ count1297 b) := rfl
theorem meaning1299 (b : Nat → Bool) : literal (valuationOf b) 1299 = decide (3 ≤ count1297 b) := rfl
theorem meaning1300 (b : Nat → Bool) : literal (valuationOf b) 1300 = decide (4 ≤ count1297 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (5 ≤ count1297 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (1 ≤ count1309 b) := rfl
theorem meaning1310 (b : Nat → Bool) : literal (valuationOf b) 1310 = decide (2 ≤ count1309 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (1 ≤ count1311 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (2 ≤ count1311 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (1 ≤ count1314 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (2 ≤ count1314 b) := rfl
theorem meaning1316 (b : Nat → Bool) : literal (valuationOf b) 1316 = decide (1 ≤ count1316 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (2 ≤ count1316 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (1 ≤ count1319 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (2 ≤ count1319 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (3 ≤ count1319 b) := rfl
theorem meaning1325 (b : Nat → Bool) : literal (valuationOf b) 1325 = decide (1 ≤ count1325 b) := rfl
theorem meaning1326 (b : Nat → Bool) : literal (valuationOf b) 1326 = decide (2 ≤ count1325 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (1 ≤ count1327 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (2 ≤ count1327 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (1 ≤ count1330 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (1 ≤ count1332 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (2 ≤ count1332 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (1 ≤ count1334 b) := rfl
theorem meaning1335 (b : Nat → Bool) : literal (valuationOf b) 1335 = decide (2 ≤ count1334 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (1 ≤ count1338 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (2 ≤ count1338 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (3 ≤ count1338 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (2 ≤ count1345 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (3 ≤ count1345 b) := rfl
theorem meaning1348 (b : Nat → Bool) : literal (valuationOf b) 1348 = decide (4 ≤ count1345 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (5 ≤ count1345 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (5 ≤ count1357 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (6 ≤ count1357 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (7 ≤ count1357 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (1 ≤ count1369 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (1 ≤ count1371 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (1 ≤ count1379 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (2 ≤ count1385 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (1 ≤ count1387 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (3 ≤ count1387 b) := rfl
theorem meaning1390 (b : Nat → Bool) : literal (valuationOf b) 1390 = decide (1 ≤ count1390 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (1 ≤ count1392 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (2 ≤ count1392 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (1 ≤ count1394 b) := rfl
theorem meaning1395 (b : Nat → Bool) : literal (valuationOf b) 1395 = decide (2 ≤ count1394 b) := rfl
theorem meaning1396 (b : Nat → Bool) : literal (valuationOf b) 1396 = decide (3 ≤ count1394 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (1 ≤ count1398 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (2 ≤ count1398 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (3 ≤ count1398 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (4 ≤ count1398 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (1 ≤ count1405 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (2 ≤ count1405 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (3 ≤ count1405 b) := rfl
theorem meaning1408 (b : Nat → Bool) : literal (valuationOf b) 1408 = decide (4 ≤ count1405 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (1 ≤ count1417 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (2 ≤ count1417 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (1 ≤ count1419 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (2 ≤ count1419 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (3 ≤ count1419 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (1 ≤ count1422 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (2 ≤ count1422 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (1 ≤ count1424 b) := rfl
theorem meaning1425 (b : Nat → Bool) : literal (valuationOf b) 1425 = decide (2 ≤ count1424 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (1 ≤ count1427 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (2 ≤ count1427 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (3 ≤ count1427 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (4 ≤ count1427 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (5 ≤ count1427 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (1 ≤ count1433 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (2 ≤ count1433 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (1 ≤ count1435 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (2 ≤ count1435 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (3 ≤ count1435 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (1 ≤ count1438 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (2 ≤ count1438 b) := rfl
theorem meaning1440 (b : Nat → Bool) : literal (valuationOf b) 1440 = decide (1 ≤ count1440 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (2 ≤ count1440 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (1 ≤ count1442 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (2 ≤ count1442 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (3 ≤ count1442 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (1 ≤ count1446 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (2 ≤ count1446 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (3 ≤ count1446 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (4 ≤ count1446 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (3 ≤ count1453 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (4 ≤ count1453 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (5 ≤ count1453 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (6 ≤ count1453 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (7 ≤ count1453 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (5 ≤ count1465 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (6 ≤ count1465 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (7 ≤ count1465 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (12 ≤ count1477 b) := rfl
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
end Snake9.Regrowth.E112150
