import E112201Data
namespace Snake9.Regrowth.E112201
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 109 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 4 then decide (InPath q (11 : Vertex)) else (if i < 5 then decide (InPath q (13 : Vertex)) else decide (InPath q (15 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (17 : Vertex)) else (if i < 8 then decide (InPath q (18 : Vertex)) else decide (InPath q (19 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (22 : Vertex)) else decide (InPath q (28 : Vertex))) else (if i < 12 then decide (InPath q (29 : Vertex)) else decide (InPath q (30 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (160 : Vertex)) else (if i < 15 then decide (InPath q (161 : Vertex)) else decide (InPath q (162 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (163 : Vertex)) else decide (InPath q (165 : Vertex))) else (if i < 19 then decide (InPath q (166 : Vertex)) else decide (InPath q (171 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (173 : Vertex)) else (if i < 22 then decide (InPath q (175 : Vertex)) else decide (InPath q (176 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (177 : Vertex)) else decide (InPath q (178 : Vertex))) else (if i < 26 then decide (InPath q (179 : Vertex)) else decide (InPath q (182 : Vertex))))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then decide (InPath q (184 : Vertex)) else (if i < 29 then decide (InPath q (188 : Vertex)) else decide (InPath q (189 : Vertex)))) else (if i < 31 then decide (InPath q (190 : Vertex)) else (if i < 32 then decide (InPath q (191 : Vertex)) else decide (InPath q (226 : Vertex))))) else (if i < 36 then (if i < 34 then decide (InPath q (228 : Vertex)) else (if i < 35 then decide (InPath q (229 : Vertex)) else decide (InPath q (230 : Vertex)))) else (if i < 38 then (if i < 37 then decide (InPath q (235 : Vertex)) else decide (InPath q (238 : Vertex))) else (if i < 39 then decide (InPath q (244 : Vertex)) else decide (InPath q (245 : Vertex)))))) else (if i < 47 then (if i < 43 then (if i < 41 then decide (InPath q (247 : Vertex)) else (if i < 42 then decide (InPath q (249 : Vertex)) else decide (InPath q (250 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (251 : Vertex)) else decide (InPath q (255 : Vertex))) else (if i < 46 then decide (InPath q (259 : Vertex)) else decide (InPath q (261 : Vertex))))) else (if i < 50 then (if i < 48 then decide (InPath q (267 : Vertex)) else (if i < 49 then decide (InPath q (272 : Vertex)) else decide (InPath q (276 : Vertex)))) else (if i < 52 then (if i < 51 then decide (InPath q (277 : Vertex)) else decide (InPath q (279 : Vertex))) else (if i < 53 then decide (InPath q (281 : Vertex)) else decide (InPath q (283 : Vertex)))))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then decide (InPath q (287 : Vertex)) else (if i < 56 then decide (InPath q (288 : Vertex)) else decide (InPath q (291 : Vertex)))) else (if i < 58 then decide (InPath q (304 : Vertex)) else (if i < 59 then decide (InPath q (305 : Vertex)) else decide (InPath q (307 : Vertex))))) else (if i < 63 then (if i < 61 then decide (InPath q (354 : Vertex)) else (if i < 62 then decide (InPath q (355 : Vertex)) else decide (InPath q (356 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (357 : Vertex)) else decide (InPath q (362 : Vertex))) else (if i < 66 then decide (InPath q (363 : Vertex)) else decide (InPath q (364 : Vertex)))))) else (if i < 74 then (if i < 70 then (if i < 68 then decide (InPath q (366 : Vertex)) else (if i < 69 then decide (InPath q (368 : Vertex)) else decide (InPath q (372 : Vertex)))) else (if i < 72 then (if i < 71 then decide (InPath q (373 : Vertex)) else decide (InPath q (375 : Vertex))) else (if i < 73 then decide (InPath q (376 : Vertex)) else decide (InPath q (377 : Vertex))))) else (if i < 77 then (if i < 75 then decide (InPath q (379 : Vertex)) else (if i < 76 then decide (InPath q (383 : Vertex)) else decide (InPath q (418 : Vertex)))) else (if i < 79 then (if i < 78 then decide (InPath q (419 : Vertex)) else decide (InPath q (420 : Vertex))) else (if i < 80 then decide (InPath q (421 : Vertex)) else decide (InPath q (426 : Vertex))))))) else (if i < 95 then (if i < 88 then (if i < 84 then (if i < 82 then decide (InPath q (427 : Vertex)) else (if i < 83 then decide (InPath q (428 : Vertex)) else decide (InPath q (430 : Vertex)))) else (if i < 86 then (if i < 85 then decide (InPath q (432 : Vertex)) else decide (InPath q (436 : Vertex))) else (if i < 87 then decide (InPath q (437 : Vertex)) else decide (InPath q (439 : Vertex))))) else (if i < 91 then (if i < 89 then decide (InPath q (440 : Vertex)) else (if i < 90 then decide (InPath q (441 : Vertex)) else decide (InPath q (442 : Vertex)))) else (if i < 93 then (if i < 92 then decide (InPath q (443 : Vertex)) else decide (InPath q (447 : Vertex))) else (if i < 94 then decide (InPath q (480 : Vertex)) else decide (InPath q (481 : Vertex)))))) else (if i < 102 then (if i < 98 then (if i < 96 then decide (InPath q (486 : Vertex)) else (if i < 97 then decide (InPath q (487 : Vertex)) else decide (InPath q (491 : Vertex)))) else (if i < 100 then (if i < 99 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))) else (if i < 101 then decide (InPath q (496 : Vertex)) else decide (InPath q (497 : Vertex))))) else (if i < 105 then (if i < 103 then decide (InPath q (498 : Vertex)) else (if i < 104 then decide (InPath q (499 : Vertex)) else decide (InPath q (500 : Vertex)))) else (if i < 107 then (if i < 106 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 108 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 164 then (if i < 136 then (if i < 122 then (if i < 115 then (if i < 112 then (if i < 110 then decide (InPath q (510 : Vertex)) else (if i < 111 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 113 then decide (BallClauseLogic.Endpoint q (11 : Vertex)) else (if i < 114 then decide (BallClauseLogic.Endpoint q (13 : Vertex)) else decide (BallClauseLogic.Endpoint q (15 : Vertex))))) else (if i < 118 then (if i < 116 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else (if i < 117 then decide (BallClauseLogic.Endpoint q (18 : Vertex)) else decide (BallClauseLogic.Endpoint q (19 : Vertex)))) else (if i < 120 then (if i < 119 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (28 : Vertex))) else (if i < 121 then decide (BallClauseLogic.Endpoint q (29 : Vertex)) else decide (BallClauseLogic.Endpoint q (30 : Vertex)))))) else (if i < 129 then (if i < 125 then (if i < 123 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (161 : Vertex)) else decide (BallClauseLogic.Endpoint q (162 : Vertex)))) else (if i < 127 then (if i < 126 then decide (BallClauseLogic.Endpoint q (163 : Vertex)) else decide (BallClauseLogic.Endpoint q (165 : Vertex))) else (if i < 128 then decide (BallClauseLogic.Endpoint q (166 : Vertex)) else decide (BallClauseLogic.Endpoint q (171 : Vertex))))) else (if i < 132 then (if i < 130 then decide (BallClauseLogic.Endpoint q (173 : Vertex)) else (if i < 131 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else decide (BallClauseLogic.Endpoint q (176 : Vertex)))) else (if i < 134 then (if i < 133 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else decide (BallClauseLogic.Endpoint q (178 : Vertex))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex))))))) else (if i < 150 then (if i < 143 then (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (184 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (188 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (190 : Vertex)) else decide (BallClauseLogic.Endpoint q (191 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else decide (BallClauseLogic.Endpoint q (228 : Vertex))))) else (if i < 146 then (if i < 144 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (230 : Vertex)) else decide (BallClauseLogic.Endpoint q (235 : Vertex)))) else (if i < 148 then (if i < 147 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else decide (BallClauseLogic.Endpoint q (244 : Vertex))) else (if i < 149 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else decide (BallClauseLogic.Endpoint q (247 : Vertex)))))) else (if i < 157 then (if i < 153 then (if i < 151 then decide (BallClauseLogic.Endpoint q (249 : Vertex)) else (if i < 152 then decide (BallClauseLogic.Endpoint q (250 : Vertex)) else decide (BallClauseLogic.Endpoint q (251 : Vertex)))) else (if i < 155 then (if i < 154 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else decide (BallClauseLogic.Endpoint q (259 : Vertex))) else (if i < 156 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex))))) else (if i < 160 then (if i < 158 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else (if i < 159 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else decide (BallClauseLogic.Endpoint q (277 : Vertex)))) else (if i < 162 then (if i < 161 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else decide (BallClauseLogic.Endpoint q (281 : Vertex))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex)))))))) else (if i < 191 then (if i < 177 then (if i < 170 then (if i < 167 then (if i < 165 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else (if i < 166 then decide (BallClauseLogic.Endpoint q (291 : Vertex)) else decide (BallClauseLogic.Endpoint q (304 : Vertex)))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (305 : Vertex)) else (if i < 169 then decide (BallClauseLogic.Endpoint q (307 : Vertex)) else decide (BallClauseLogic.Endpoint q (354 : Vertex))))) else (if i < 173 then (if i < 171 then decide (BallClauseLogic.Endpoint q (355 : Vertex)) else (if i < 172 then decide (BallClauseLogic.Endpoint q (356 : Vertex)) else decide (BallClauseLogic.Endpoint q (357 : Vertex)))) else (if i < 175 then (if i < 174 then decide (BallClauseLogic.Endpoint q (362 : Vertex)) else decide (BallClauseLogic.Endpoint q (363 : Vertex))) else (if i < 176 then decide (BallClauseLogic.Endpoint q (364 : Vertex)) else decide (BallClauseLogic.Endpoint q (366 : Vertex)))))) else (if i < 184 then (if i < 180 then (if i < 178 then decide (BallClauseLogic.Endpoint q (368 : Vertex)) else (if i < 179 then decide (BallClauseLogic.Endpoint q (372 : Vertex)) else decide (BallClauseLogic.Endpoint q (373 : Vertex)))) else (if i < 182 then (if i < 181 then decide (BallClauseLogic.Endpoint q (375 : Vertex)) else decide (BallClauseLogic.Endpoint q (376 : Vertex))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (377 : Vertex)) else decide (BallClauseLogic.Endpoint q (379 : Vertex))))) else (if i < 187 then (if i < 185 then decide (BallClauseLogic.Endpoint q (383 : Vertex)) else (if i < 186 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (419 : Vertex)))) else (if i < 189 then (if i < 188 then decide (BallClauseLogic.Endpoint q (420 : Vertex)) else decide (BallClauseLogic.Endpoint q (421 : Vertex))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))))))) else (if i < 205 then (if i < 198 then (if i < 194 then (if i < 192 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else (if i < 193 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (432 : Vertex)))) else (if i < 196 then (if i < 195 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (437 : Vertex))) else (if i < 197 then decide (BallClauseLogic.Endpoint q (439 : Vertex)) else decide (BallClauseLogic.Endpoint q (440 : Vertex))))) else (if i < 201 then (if i < 199 then decide (BallClauseLogic.Endpoint q (441 : Vertex)) else (if i < 200 then decide (BallClauseLogic.Endpoint q (442 : Vertex)) else decide (BallClauseLogic.Endpoint q (443 : Vertex)))) else (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (447 : Vertex)) else decide (BallClauseLogic.Endpoint q (480 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (481 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex)))))) else (if i < 212 then (if i < 208 then (if i < 206 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else (if i < 207 then decide (BallClauseLogic.Endpoint q (491 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex)))) else (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (496 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex))))) else (if i < 215 then (if i < 213 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else (if i < 214 then decide (BallClauseLogic.Endpoint q (500 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 217 then (if i < 216 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 218 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count219 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count221 (b : Nat → Bool) : Nat := countLit b [110, 111, 112]
def count223 (b : Nat → Bool) : Nat := countLit b [114, 115]
def count225 (b : Nat → Bool) : Nat := countLit b [113, 114, 115]
def count227 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115]
def count229 (b : Nat → Bool) : Nat := countLit b [117, 118]
def count231 (b : Nat → Bool) : Nat := countLit b [116, 117, 118]
def count233 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count235 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count237 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122]
def count239 (b : Nat → Bool) : Nat := countLit b [116, 117, 118, 119, 120, 121, 122]
def count241 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122]
def count243 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count245 (b : Nat → Bool) : Nat := countLit b [123, 124, 125]
def count247 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [126, 127, 128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [130, 131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count263 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
def count269 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
def count271 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [137, 138, 139]
def count275 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140, 141, 142]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count289 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
def count295 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count303 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156]
def count307 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count313 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163]
def count317 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]
def count323 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]
def count325 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [164, 165, 166]
def count329 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [167, 168, 169]
def count333 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167, 168, 169]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [170, 171, 172]
def count339 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [173, 174, 175, 176]
def count345 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175, 176]
def count347 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]
def count349 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count351 (b : Nat → Bool) : Nat := countLit b [177, 178, 179]
def count353 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183]
def count359 (b : Nat → Bool) : Nat := countLit b [177, 178, 179, 180, 181, 182, 183]
def count361 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [184, 185, 186]
def count365 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count369 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]
def count375 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]
def count377 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count379 (b : Nat → Bool) : Nat := countLit b [191, 192, 193]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count383 (b : Nat → Bool) : Nat := countLit b [194, 195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196]
def count387 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count389 (b : Nat → Bool) : Nat := countLit b [197, 198, 199]
def count391 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count395 (b : Nat → Bool) : Nat := countLit b [200, 201, 203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200, 201, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count403 (b : Nat → Bool) : Nat := countLit b [205, 206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count409 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211]
def count411 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211]
def count413 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count415 (b : Nat → Bool) : Nat := countLit b [212, 213, 214]
def count417 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count419 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count421 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218]
def count423 (b : Nat → Bool) : Nat := countLit b [212, 213, 214, 215, 216, 217, 218]
def count425 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count429 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count431 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count433 (b : Nat → Bool) : Nat := countLit b [5, 6]
def count435 (b : Nat → Bool) : Nat := countLit b [1, 5, 6]
def count438 (b : Nat → Bool) : Nat := countLit b [7, 11]
def count440 (b : Nat → Bool) : Nat := countLit b [12, 13]
def count442 (b : Nat → Bool) : Nat := countLit b [7, 11, 12, 13]
def count446 (b : Nat → Bool) : Nat := countLit b [1, 5, 6, 7, 11, 12, 13]
def count453 (b : Nat → Bool) : Nat := countLit b [17, 18]
def count455 (b : Nat → Bool) : Nat := countLit b [16, 17, 18]
def count458 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count460 (b : Nat → Bool) : Nat := countLit b [24, 27]
def count462 (b : Nat → Bool) : Nat := countLit b [21, 23, 24, 27]
def count466 (b : Nat → Bool) : Nat := countLit b [16, 17, 18, 21, 23, 24, 27]
def count473 (b : Nat → Bool) : Nat := countLit b [1, 5, 6, 7, 11, 12, 13, 16, 17, 18, 21, 23, 24, 27]
def count487 (b : Nat → Bool) : Nat := countLit b [30, 32]
def count489 (b : Nat → Bool) : Nat := countLit b [29, 30, 32]
def count492 (b : Nat → Bool) : Nat := countLit b [33, 36]
def count494 (b : Nat → Bool) : Nat := countLit b [37, 39]
def count496 (b : Nat → Bool) : Nat := countLit b [33, 36, 37, 39]
def count500 (b : Nat → Bool) : Nat := countLit b [29, 30, 32, 33, 36, 37, 39]
def count507 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count509 (b : Nat → Bool) : Nat := countLit b [41, 42, 44]
def count512 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count514 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count516 (b : Nat → Bool) : Nat := countLit b [47, 48, 50, 52]
def count520 (b : Nat → Bool) : Nat := countLit b [41, 42, 44, 47, 48, 50, 52]
def count527 (b : Nat → Bool) : Nat := countLit b [29, 30, 32, 33, 36, 37, 39, 41, 42, 44, 47, 48, 50, 52]
def count541 (b : Nat → Bool) : Nat := countLit b [1, 5, 6, 7, 11, 12, 13, 16, 17, 18, 21, 23, 24, 27, 29, 30, 32, 33, 36, 37, 39, 41, 42, 44, 47, 48, 50, 52]
def count569 (b : Nat → Bool) : Nat := countLit b [55, 56]
def count571 (b : Nat → Bool) : Nat := countLit b [54, 55, 56]
def count574 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count576 (b : Nat → Bool) : Nat := countLit b [62, 65]
def count578 (b : Nat → Bool) : Nat := countLit b [58, 60, 62, 65]
def count582 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 58, 60, 62, 65]
def count589 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count591 (b : Nat → Bool) : Nat := countLit b [67, 68, 70]
def count594 (b : Nat → Bool) : Nat := countLit b [73, 75]
def count596 (b : Nat → Bool) : Nat := countLit b [76, 78]
def count598 (b : Nat → Bool) : Nat := countLit b [73, 75, 76, 78]
def count602 (b : Nat → Bool) : Nat := countLit b [67, 68, 70, 73, 75, 76, 78]
def count609 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 58, 60, 62, 65, 67, 68, 70, 73, 75, 76, 78]
def count623 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count625 (b : Nat → Bool) : Nat := countLit b [81, 83, 84]
def count628 (b : Nat → Bool) : Nat := countLit b [86, 89]
def count630 (b : Nat → Bool) : Nat := countLit b [90, 92]
def count632 (b : Nat → Bool) : Nat := countLit b [86, 89, 90, 92]
def count636 (b : Nat → Bool) : Nat := countLit b [81, 83, 84, 86, 89, 90, 92]
def count643 (b : Nat → Bool) : Nat := countLit b [93, 95]
def count645 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count647 (b : Nat → Bool) : Nat := countLit b [93, 95, 99, 101]
def count651 (b : Nat → Bool) : Nat := countLit b [102, 104]
def count653 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count655 (b : Nat → Bool) : Nat := countLit b [102, 104, 108, 109]
def count659 (b : Nat → Bool) : Nat := countLit b [93, 95, 99, 101, 102, 104, 108, 109]
def count667 (b : Nat → Bool) : Nat := countLit b [81, 83, 84, 86, 89, 90, 92, 93, 95, 99, 101, 102, 104, 108, 109]
def count682 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 58, 60, 62, 65, 67, 68, 70, 73, 75, 76, 78, 81, 83, 84, 86, 89, 90, 92, 93, 95, 99, 101, 102, 104, 108, 109]
def count711 (b : Nat → Bool) : Nat := countLit b [1, 5, 6, 7, 11, 12, 13, 16, 17, 18, 21, 23, 24, 27, 29, 30, 32, 33, 36, 37, 39, 41, 42, 44, 47, 48, 50, 52, 54, 55, 56, 58, 60, 62, 65, 67, 68, 70, 73, 75, 76, 78, 81, 83, 84, 86, 89, 90, 92, 93, 95, 99, 101, 102, 104, 108, 109]
def count753 (b : Nat → Bool) : Nat := countLit b [-5, -6]
def count755 (b : Nat → Bool) : Nat := countLit b [-1, -5, -6]
def count758 (b : Nat → Bool) : Nat := countLit b [-7, -11]
def count760 (b : Nat → Bool) : Nat := countLit b [-12, -13]
def count762 (b : Nat → Bool) : Nat := countLit b [-7, -11, -12, -13]
def count766 (b : Nat → Bool) : Nat := countLit b [-1, -5, -6, -7, -11, -12, -13]
def count773 (b : Nat → Bool) : Nat := countLit b [-17, -18]
def count775 (b : Nat → Bool) : Nat := countLit b [-16, -17, -18]
def count778 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count780 (b : Nat → Bool) : Nat := countLit b [-24, -27]
def count782 (b : Nat → Bool) : Nat := countLit b [-21, -23, -24, -27]
def count786 (b : Nat → Bool) : Nat := countLit b [-16, -17, -18, -21, -23, -24, -27]
def count793 (b : Nat → Bool) : Nat := countLit b [-1, -5, -6, -7, -11, -12, -13, -16, -17, -18, -21, -23, -24, -27]
def count807 (b : Nat → Bool) : Nat := countLit b [-30, -32]
def count809 (b : Nat → Bool) : Nat := countLit b [-29, -30, -32]
def count812 (b : Nat → Bool) : Nat := countLit b [-33, -36]
def count814 (b : Nat → Bool) : Nat := countLit b [-37, -39]
def count816 (b : Nat → Bool) : Nat := countLit b [-33, -36, -37, -39]
def count820 (b : Nat → Bool) : Nat := countLit b [-29, -30, -32, -33, -36, -37, -39]
def count827 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count829 (b : Nat → Bool) : Nat := countLit b [-41, -42, -44]
def count832 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count834 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count836 (b : Nat → Bool) : Nat := countLit b [-47, -48, -50, -52]
def count840 (b : Nat → Bool) : Nat := countLit b [-41, -42, -44, -47, -48, -50, -52]
def count847 (b : Nat → Bool) : Nat := countLit b [-29, -30, -32, -33, -36, -37, -39, -41, -42, -44, -47, -48, -50, -52]
def count861 (b : Nat → Bool) : Nat := countLit b [-1, -5, -6, -7, -11, -12, -13, -16, -17, -18, -21, -23, -24, -27, -29, -30, -32, -33, -36, -37, -39, -41, -42, -44, -47, -48, -50, -52]
def count878 (b : Nat → Bool) : Nat := countLit b [-55, -56]
def count880 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56]
def count883 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count885 (b : Nat → Bool) : Nat := countLit b [-62, -65]
def count887 (b : Nat → Bool) : Nat := countLit b [-58, -60, -62, -65]
def count891 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -58, -60, -62, -65]
def count898 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count900 (b : Nat → Bool) : Nat := countLit b [-67, -68, -70]
def count903 (b : Nat → Bool) : Nat := countLit b [-73, -75]
def count905 (b : Nat → Bool) : Nat := countLit b [-76, -78]
def count907 (b : Nat → Bool) : Nat := countLit b [-73, -75, -76, -78]
def count911 (b : Nat → Bool) : Nat := countLit b [-67, -68, -70, -73, -75, -76, -78]
def count918 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -58, -60, -62, -65, -67, -68, -70, -73, -75, -76, -78]
def count932 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count934 (b : Nat → Bool) : Nat := countLit b [-81, -83, -84]
def count937 (b : Nat → Bool) : Nat := countLit b [-86, -89]
def count939 (b : Nat → Bool) : Nat := countLit b [-90, -92]
def count941 (b : Nat → Bool) : Nat := countLit b [-86, -89, -90, -92]
def count945 (b : Nat → Bool) : Nat := countLit b [-81, -83, -84, -86, -89, -90, -92]
def count952 (b : Nat → Bool) : Nat := countLit b [-93, -95]
def count954 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count956 (b : Nat → Bool) : Nat := countLit b [-93, -95, -99, -101]
def count960 (b : Nat → Bool) : Nat := countLit b [-102, -104]
def count962 (b : Nat → Bool) : Nat := countLit b [-108, -109]
def count964 (b : Nat → Bool) : Nat := countLit b [-102, -104, -108, -109]
def count968 (b : Nat → Bool) : Nat := countLit b [-93, -95, -99, -101, -102, -104, -108, -109]
def count976 (b : Nat → Bool) : Nat := countLit b [-81, -83, -84, -86, -89, -90, -92, -93, -95, -99, -101, -102, -104, -108, -109]
def count991 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -58, -60, -62, -65, -67, -68, -70, -73, -75, -76, -78, -81, -83, -84, -86, -89, -90, -92, -93, -95, -99, -101, -102, -104, -108, -109]
def count1008 (b : Nat → Bool) : Nat := countLit b [-1, -5, -6, -7, -11, -12, -13, -16, -17, -18, -21, -23, -24, -27, -29, -30, -32, -33, -36, -37, -39, -41, -42, -44, -47, -48, -50, -52, -54, -55, -56, -58, -60, -62, -65, -67, -68, -70, -73, -75, -76, -78, -81, -83, -84, -86, -89, -90, -92, -93, -95, -99, -101, -102, -104, -108, -109]
def count1025 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count1027 (b : Nat → Bool) : Nat := countLit b [2, 3, 4]
def count1030 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count1032 (b : Nat → Bool) : Nat := countLit b [8, 9, 10]
def count1035 (b : Nat → Bool) : Nat := countLit b [2, 3, 4, 8, 9, 10]
def count1041 (b : Nat → Bool) : Nat := countLit b [15, 19]
def count1043 (b : Nat → Bool) : Nat := countLit b [14, 15, 19]
def count1046 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count1048 (b : Nat → Bool) : Nat := countLit b [25, 26]
def count1050 (b : Nat → Bool) : Nat := countLit b [20, 22, 25, 26]
def count1054 (b : Nat → Bool) : Nat := countLit b [14, 15, 19, 20, 22, 25, 26]
def count1061 (b : Nat → Bool) : Nat := countLit b [2, 3, 4, 8, 9, 10, 14, 15, 19, 20, 22, 25, 26]
def count1074 (b : Nat → Bool) : Nat := countLit b [31, 34]
def count1076 (b : Nat → Bool) : Nat := countLit b [28, 31, 34]
def count1079 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count1081 (b : Nat → Bool) : Nat := countLit b [35, 38, 40]
def count1084 (b : Nat → Bool) : Nat := countLit b [28, 31, 34, 35, 38, 40]
def count1090 (b : Nat → Bool) : Nat := countLit b [45, 46]
def count1092 (b : Nat → Bool) : Nat := countLit b [43, 45, 46]
def count1095 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count1097 (b : Nat → Bool) : Nat := countLit b [53, 57]
def count1099 (b : Nat → Bool) : Nat := countLit b [49, 51, 53, 57]
def count1103 (b : Nat → Bool) : Nat := countLit b [43, 45, 46, 49, 51, 53, 57]
def count1110 (b : Nat → Bool) : Nat := countLit b [28, 31, 34, 35, 38, 40, 43, 45, 46, 49, 51, 53, 57]
def count1123 (b : Nat → Bool) : Nat := countLit b [2, 3, 4, 8, 9, 10, 14, 15, 19, 20, 22, 25, 26, 28, 31, 34, 35, 38, 40, 43, 45, 46, 49, 51, 53, 57]
def count1149 (b : Nat → Bool) : Nat := countLit b [61, 63]
def count1151 (b : Nat → Bool) : Nat := countLit b [59, 61, 63]
def count1154 (b : Nat → Bool) : Nat := countLit b [66, 69]
def count1156 (b : Nat → Bool) : Nat := countLit b [64, 66, 69]
def count1159 (b : Nat → Bool) : Nat := countLit b [59, 61, 63, 64, 66, 69]
def count1165 (b : Nat → Bool) : Nat := countLit b [72, 74]
def count1167 (b : Nat → Bool) : Nat := countLit b [71, 72, 74]
def count1170 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count1172 (b : Nat → Bool) : Nat := countLit b [80, 82]
def count1174 (b : Nat → Bool) : Nat := countLit b [77, 79, 80, 82]
def count1178 (b : Nat → Bool) : Nat := countLit b [71, 72, 74, 77, 79, 80, 82]
def count1185 (b : Nat → Bool) : Nat := countLit b [59, 61, 63, 64, 66, 69, 71, 72, 74, 77, 79, 80, 82]
def count1198 (b : Nat → Bool) : Nat := countLit b [87, 88]
def count1200 (b : Nat → Bool) : Nat := countLit b [85, 87, 88]
def count1203 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count1205 (b : Nat → Bool) : Nat := countLit b [91, 94, 96]
def count1208 (b : Nat → Bool) : Nat := countLit b [85, 87, 88, 91, 94, 96]
def count1214 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count1216 (b : Nat → Bool) : Nat := countLit b [97, 98, 100]
def count1219 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count1221 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count1223 (b : Nat → Bool) : Nat := countLit b [103, 105, 106, 107]
def count1227 (b : Nat → Bool) : Nat := countLit b [97, 98, 100, 103, 105, 106, 107]
def count1234 (b : Nat → Bool) : Nat := countLit b [85, 87, 88, 91, 94, 96, 97, 98, 100, 103, 105, 106, 107]
def count1247 (b : Nat → Bool) : Nat := countLit b [59, 61, 63, 64, 66, 69, 71, 72, 74, 77, 79, 80, 82, 85, 87, 88, 91, 94, 96, 97, 98, 100, 103, 105, 106, 107]
def count1273 (b : Nat → Bool) : Nat := countLit b [2, 3, 4, 8, 9, 10, 14, 15, 19, 20, 22, 25, 26, 28, 31, 34, 35, 38, 40, 43, 45, 46, 49, 51, 53, 57, 59, 61, 63, 64, 66, 69, 71, 72, 74, 77, 79, 80, 82, 85, 87, 88, 91, 94, 96, 97, 98, 100, 103, 105, 106, 107]
def count1315 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count1317 (b : Nat → Bool) : Nat := countLit b [-2, -3, -4]
def count1320 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count1322 (b : Nat → Bool) : Nat := countLit b [-8, -9, -10]
def count1325 (b : Nat → Bool) : Nat := countLit b [-2, -3, -4, -8, -9, -10]
def count1331 (b : Nat → Bool) : Nat := countLit b [-15, -19]
def count1333 (b : Nat → Bool) : Nat := countLit b [-14, -15, -19]
def count1336 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count1338 (b : Nat → Bool) : Nat := countLit b [-25, -26]
def count1340 (b : Nat → Bool) : Nat := countLit b [-20, -22, -25, -26]
def count1344 (b : Nat → Bool) : Nat := countLit b [-14, -15, -19, -20, -22, -25, -26]
def count1351 (b : Nat → Bool) : Nat := countLit b [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26]
def count1363 (b : Nat → Bool) : Nat := countLit b [-31, -34]
def count1365 (b : Nat → Bool) : Nat := countLit b [-28, -31, -34]
def count1368 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1370 (b : Nat → Bool) : Nat := countLit b [-35, -38, -40]
def count1373 (b : Nat → Bool) : Nat := countLit b [-28, -31, -34, -35, -38, -40]
def count1379 (b : Nat → Bool) : Nat := countLit b [-45, -46]
def count1381 (b : Nat → Bool) : Nat := countLit b [-43, -45, -46]
def count1384 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count1386 (b : Nat → Bool) : Nat := countLit b [-53, -57]
def count1388 (b : Nat → Bool) : Nat := countLit b [-49, -51, -53, -57]
def count1392 (b : Nat → Bool) : Nat := countLit b [-43, -45, -46, -49, -51, -53, -57]
def count1399 (b : Nat → Bool) : Nat := countLit b [-28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]
def count1411 (b : Nat → Bool) : Nat := countLit b [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57]
def count1423 (b : Nat → Bool) : Nat := countLit b [-61, -63]
def count1425 (b : Nat → Bool) : Nat := countLit b [-59, -61, -63]
def count1428 (b : Nat → Bool) : Nat := countLit b [-66, -69]
def count1430 (b : Nat → Bool) : Nat := countLit b [-64, -66, -69]
def count1433 (b : Nat → Bool) : Nat := countLit b [-59, -61, -63, -64, -66, -69]
def count1439 (b : Nat → Bool) : Nat := countLit b [-72, -74]
def count1441 (b : Nat → Bool) : Nat := countLit b [-71, -72, -74]
def count1444 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count1446 (b : Nat → Bool) : Nat := countLit b [-80, -82]
def count1448 (b : Nat → Bool) : Nat := countLit b [-77, -79, -80, -82]
def count1452 (b : Nat → Bool) : Nat := countLit b [-71, -72, -74, -77, -79, -80, -82]
def count1459 (b : Nat → Bool) : Nat := countLit b [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82]
def count1471 (b : Nat → Bool) : Nat := countLit b [-87, -88]
def count1473 (b : Nat → Bool) : Nat := countLit b [-85, -87, -88]
def count1476 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1478 (b : Nat → Bool) : Nat := countLit b [-91, -94, -96]
def count1481 (b : Nat → Bool) : Nat := countLit b [-85, -87, -88, -91, -94, -96]
def count1487 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count1489 (b : Nat → Bool) : Nat := countLit b [-97, -98, -100]
def count1492 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count1494 (b : Nat → Bool) : Nat := countLit b [-106, -107]
def count1496 (b : Nat → Bool) : Nat := countLit b [-103, -105, -106, -107]
def count1500 (b : Nat → Bool) : Nat := countLit b [-97, -98, -100, -103, -105, -106, -107]
def count1507 (b : Nat → Bool) : Nat := countLit b [-85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]
def count1519 (b : Nat → Bool) : Nat := countLit b [-59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]
def count1531 (b : Nat → Bool) : Nat := countLit b [-2, -3, -4, -8, -9, -10, -14, -15, -19, -20, -22, -25, -26, -28, -31, -34, -35, -38, -40, -43, -45, -46, -49, -51, -53, -57, -59, -61, -63, -64, -66, -69, -71, -72, -74, -77, -79, -80, -82, -85, -87, -88, -91, -94, -96, -97, -98, -100, -103, -105, -106, -107]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 771 then (if i < 385 then (if i < 192 then (if i < 96 then (if i < 48 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 10 then b 9 else (if i < 11 then b 10 else b 11)))) else (if i < 18 then (if i < 15 then (if i < 13 then b 12 else (if i < 14 then b 13 else b 14)) else (if i < 16 then b 15 else (if i < 17 then b 16 else b 17))) else (if i < 21 then (if i < 19 then b 18 else (if i < 20 then b 19 else b 20)) else (if i < 22 then b 21 else (if i < 23 then b 22 else b 23))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then b 24 else (if i < 26 then b 25 else b 26)) else (if i < 28 then b 27 else (if i < 29 then b 28 else b 29))) else (if i < 33 then (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)) else (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)))) else (if i < 42 then (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 40 then b 39 else (if i < 41 then b 40 else b 41))) else (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)))))) else (if i < 72 then (if i < 60 then (if i < 54 then (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 52 then b 51 else (if i < 53 then b 52 else b 53))) else (if i < 57 then (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)) else (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)))) else (if i < 66 then (if i < 63 then (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)) else (if i < 64 then b 63 else (if i < 65 then b 64 else b 65))) else (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))))) else (if i < 84 then (if i < 78 then (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77))) else (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)))) else (if i < 90 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))) else (if i < 93 then (if i < 91 then b 90 else (if i < 92 then b 91 else b 92)) else (if i < 94 then b 93 else (if i < 95 then b 94 else b 95))))))) else (if i < 144 then (if i < 120 then (if i < 108 then (if i < 102 then (if i < 99 then (if i < 97 then b 96 else (if i < 98 then b 97 else b 98)) else (if i < 100 then b 99 else (if i < 101 then b 100 else b 101))) else (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 106 then b 105 else (if i < 107 then b 106 else b 107)))) else (if i < 114 then (if i < 111 then (if i < 109 then b 108 else (if i < 110 then b 109 else b 110)) else (if i < 112 then b 111 else (if i < 113 then b 112 else b 113))) else (if i < 117 then (if i < 115 then b 114 else (if i < 116 then b 115 else b 116)) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119))))) else (if i < 132 then (if i < 126 then (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 124 then b 123 else (if i < 125 then b 124 else b 125))) else (if i < 129 then (if i < 127 then b 126 else (if i < 128 then b 127 else b 128)) else (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)))) else (if i < 138 then (if i < 135 then (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)) else (if i < 136 then b 135 else (if i < 137 then b 136 else b 137))) else (if i < 141 then (if i < 139 then b 138 else (if i < 140 then b 139 else b 140)) else (if i < 142 then b 141 else (if i < 143 then b 142 else b 143)))))) else (if i < 168 then (if i < 156 then (if i < 150 then (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 148 then b 147 else (if i < 149 then b 148 else b 149))) else (if i < 153 then (if i < 151 then b 150 else (if i < 152 then b 151 else b 152)) else (if i < 154 then b 153 else (if i < 155 then b 154 else b 155)))) else (if i < 162 then (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 166 then b 165 else (if i < 167 then b 166 else b 167))))) else (if i < 180 then (if i < 174 then (if i < 171 then (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)) else (if i < 172 then b 171 else (if i < 173 then b 172 else b 173))) else (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)))) else (if i < 186 then (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185))) else (if i < 189 then (if i < 187 then b 186 else (if i < 188 then b 187 else b 188)) else (if i < 190 then b 189 else (if i < 191 then b 190 else b 191)))))))) else (if i < 288 then (if i < 240 then (if i < 216 then (if i < 204 then (if i < 198 then (if i < 195 then (if i < 193 then b 192 else (if i < 194 then b 193 else b 194)) else (if i < 196 then b 195 else (if i < 197 then b 196 else b 197))) else (if i < 201 then (if i < 199 then b 198 else (if i < 200 then b 199 else b 200)) else (if i < 202 then b 201 else (if i < 203 then b 202 else b 203)))) else (if i < 210 then (if i < 207 then (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)) else (if i < 208 then b 207 else (if i < 209 then b 208 else b 209))) else (if i < 213 then (if i < 211 then b 210 else (if i < 212 then b 211 else b 212)) else (if i < 214 then b 213 else (if i < 215 then b 214 else b 215))))) else (if i < 228 then (if i < 222 then (if i < 219 then (if i < 217 then b 216 else (if i < 218 then b 217 else b 218)) else (if i < 220 then decide (1 ≤ count219 b) else (if i < 221 then decide (2 ≤ count219 b) else decide (1 ≤ count221 b)))) else (if i < 225 then (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b))) else (if i < 226 then decide (1 ≤ count225 b) else (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b))))) else (if i < 234 then (if i < 231 then (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b))) else (if i < 232 then decide (1 ≤ count231 b) else (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b)))) else (if i < 237 then (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b))) else (if i < 238 then decide (1 ≤ count237 b) else (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b))))))) else (if i < 264 then (if i < 252 then (if i < 246 then (if i < 243 then (if i < 241 then decide (2 ≤ count239 b) else (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b))) else (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b)))) else (if i < 249 then (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b))) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))))) else (if i < 258 then (if i < 255 then (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))) else (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b)))) else (if i < 261 then (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)))))) else (if i < 276 then (if i < 270 then (if i < 267 then (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))) else (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)))) else (if i < 273 then (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b))) else (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))))) else (if i < 282 then (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b)))) else (if i < 285 then (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))) else (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b)))))))) else (if i < 336 then (if i < 312 then (if i < 300 then (if i < 294 then (if i < 291 then (if i < 289 then decide (2 ≤ count287 b) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))) else (if i < 292 then decide (1 ≤ count291 b) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b)))) else (if i < 297 then (if i < 295 then decide (2 ≤ count293 b) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b))) else (if i < 298 then decide (1 ≤ count297 b) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))))) else (if i < 306 then (if i < 303 then (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b))) else (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)))) else (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)))))) else (if i < 324 then (if i < 318 then (if i < 315 then (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b))) else (if i < 316 then decide (1 ≤ count315 b) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)))) else (if i < 321 then (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))) else (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b))))) else (if i < 330 then (if i < 327 then (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))) else (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)))) else (if i < 333 then (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b))) else (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))))))) else (if i < 360 then (if i < 348 then (if i < 342 then (if i < 339 then (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))) else (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)))) else (if i < 345 then (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b))) else (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b))))) else (if i < 354 then (if i < 351 then (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b))) else (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))) else (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b)))))) else (if i < 372 then (if i < 366 then (if i < 363 then (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b))) else (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))) else (if i < 369 then (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b))))) else (if i < 378 then (if i < 375 then (if i < 373 then decide (2 ≤ count371 b) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b))) else (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b)))) else (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 383 then (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b)))))))))) else (if i < 578 then (if i < 481 then (if i < 433 then (if i < 409 then (if i < 397 then (if i < 391 then (if i < 388 then (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b))) else (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)))) else (if i < 394 then (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))))) else (if i < 403 then (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b)))) else (if i < 406 then (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))) else (if i < 407 then decide (2 ≤ count405 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)))))) else (if i < 421 then (if i < 415 then (if i < 412 then (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b))) else (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))) else (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))))) else (if i < 427 then (if i < 424 then (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b))) else (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)))) else (if i < 430 then (if i < 428 then decide (1 ≤ count427 b) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b))) else (if i < 431 then decide (2 ≤ count429 b) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b))))))) else (if i < 457 then (if i < 445 then (if i < 439 then (if i < 436 then (if i < 434 then decide (1 ≤ count433 b) else (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b))) else (if i < 437 then decide (2 ≤ count435 b) else (if i < 438 then decide (3 ≤ count435 b) else decide (1 ≤ count438 b)))) else (if i < 442 then (if i < 440 then decide (2 ≤ count438 b) else (if i < 441 then decide (1 ≤ count440 b) else decide (2 ≤ count440 b))) else (if i < 443 then decide (1 ≤ count442 b) else (if i < 444 then decide (2 ≤ count442 b) else decide (3 ≤ count442 b))))) else (if i < 451 then (if i < 448 then (if i < 446 then decide (4 ≤ count442 b) else (if i < 447 then decide (1 ≤ count446 b) else decide (2 ≤ count446 b))) else (if i < 449 then decide (3 ≤ count446 b) else (if i < 450 then decide (4 ≤ count446 b) else decide (5 ≤ count446 b)))) else (if i < 454 then (if i < 452 then decide (6 ≤ count446 b) else (if i < 453 then decide (7 ≤ count446 b) else decide (1 ≤ count453 b))) else (if i < 455 then decide (2 ≤ count453 b) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b)))))) else (if i < 469 then (if i < 463 then (if i < 460 then (if i < 458 then decide (3 ≤ count455 b) else (if i < 459 then decide (1 ≤ count458 b) else decide (2 ≤ count458 b))) else (if i < 461 then decide (1 ≤ count460 b) else (if i < 462 then decide (2 ≤ count460 b) else decide (1 ≤ count462 b)))) else (if i < 466 then (if i < 464 then decide (2 ≤ count462 b) else (if i < 465 then decide (3 ≤ count462 b) else decide (4 ≤ count462 b))) else (if i < 467 then decide (1 ≤ count466 b) else (if i < 468 then decide (2 ≤ count466 b) else decide (3 ≤ count466 b))))) else (if i < 475 then (if i < 472 then (if i < 470 then decide (4 ≤ count466 b) else (if i < 471 then decide (5 ≤ count466 b) else decide (6 ≤ count466 b))) else (if i < 473 then decide (7 ≤ count466 b) else (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)))) else (if i < 478 then (if i < 476 then decide (3 ≤ count473 b) else (if i < 477 then decide (4 ≤ count473 b) else decide (5 ≤ count473 b))) else (if i < 479 then decide (6 ≤ count473 b) else (if i < 480 then decide (7 ≤ count473 b) else decide (8 ≤ count473 b)))))))) else (if i < 529 then (if i < 505 then (if i < 493 then (if i < 487 then (if i < 484 then (if i < 482 then decide (9 ≤ count473 b) else (if i < 483 then decide (10 ≤ count473 b) else decide (11 ≤ count473 b))) else (if i < 485 then decide (12 ≤ count473 b) else (if i < 486 then decide (13 ≤ count473 b) else decide (14 ≤ count473 b)))) else (if i < 490 then (if i < 488 then decide (1 ≤ count487 b) else (if i < 489 then decide (2 ≤ count487 b) else decide (1 ≤ count489 b))) else (if i < 491 then decide (2 ≤ count489 b) else (if i < 492 then decide (3 ≤ count489 b) else decide (1 ≤ count492 b))))) else (if i < 499 then (if i < 496 then (if i < 494 then decide (2 ≤ count492 b) else (if i < 495 then decide (1 ≤ count494 b) else decide (2 ≤ count494 b))) else (if i < 497 then decide (1 ≤ count496 b) else (if i < 498 then decide (2 ≤ count496 b) else decide (3 ≤ count496 b)))) else (if i < 502 then (if i < 500 then decide (4 ≤ count496 b) else (if i < 501 then decide (1 ≤ count500 b) else decide (2 ≤ count500 b))) else (if i < 503 then decide (3 ≤ count500 b) else (if i < 504 then decide (4 ≤ count500 b) else decide (5 ≤ count500 b)))))) else (if i < 517 then (if i < 511 then (if i < 508 then (if i < 506 then decide (6 ≤ count500 b) else (if i < 507 then decide (7 ≤ count500 b) else decide (1 ≤ count507 b))) else (if i < 509 then decide (2 ≤ count507 b) else (if i < 510 then decide (1 ≤ count509 b) else decide (2 ≤ count509 b)))) else (if i < 514 then (if i < 512 then decide (3 ≤ count509 b) else (if i < 513 then decide (1 ≤ count512 b) else decide (2 ≤ count512 b))) else (if i < 515 then decide (1 ≤ count514 b) else (if i < 516 then decide (2 ≤ count514 b) else decide (1 ≤ count516 b))))) else (if i < 523 then (if i < 520 then (if i < 518 then decide (2 ≤ count516 b) else (if i < 519 then decide (3 ≤ count516 b) else decide (4 ≤ count516 b))) else (if i < 521 then decide (1 ≤ count520 b) else (if i < 522 then decide (2 ≤ count520 b) else decide (3 ≤ count520 b)))) else (if i < 526 then (if i < 524 then decide (4 ≤ count520 b) else (if i < 525 then decide (5 ≤ count520 b) else decide (6 ≤ count520 b))) else (if i < 527 then decide (7 ≤ count520 b) else (if i < 528 then decide (1 ≤ count527 b) else decide (2 ≤ count527 b))))))) else (if i < 553 then (if i < 541 then (if i < 535 then (if i < 532 then (if i < 530 then decide (3 ≤ count527 b) else (if i < 531 then decide (4 ≤ count527 b) else decide (5 ≤ count527 b))) else (if i < 533 then decide (6 ≤ count527 b) else (if i < 534 then decide (7 ≤ count527 b) else decide (8 ≤ count527 b)))) else (if i < 538 then (if i < 536 then decide (9 ≤ count527 b) else (if i < 537 then decide (10 ≤ count527 b) else decide (11 ≤ count527 b))) else (if i < 539 then decide (12 ≤ count527 b) else (if i < 540 then decide (13 ≤ count527 b) else decide (14 ≤ count527 b))))) else (if i < 547 then (if i < 544 then (if i < 542 then decide (1 ≤ count541 b) else (if i < 543 then decide (2 ≤ count541 b) else decide (3 ≤ count541 b))) else (if i < 545 then decide (4 ≤ count541 b) else (if i < 546 then decide (5 ≤ count541 b) else decide (6 ≤ count541 b)))) else (if i < 550 then (if i < 548 then decide (7 ≤ count541 b) else (if i < 549 then decide (8 ≤ count541 b) else decide (9 ≤ count541 b))) else (if i < 551 then decide (10 ≤ count541 b) else (if i < 552 then decide (11 ≤ count541 b) else decide (12 ≤ count541 b)))))) else (if i < 565 then (if i < 559 then (if i < 556 then (if i < 554 then decide (13 ≤ count541 b) else (if i < 555 then decide (14 ≤ count541 b) else decide (15 ≤ count541 b))) else (if i < 557 then decide (16 ≤ count541 b) else (if i < 558 then decide (17 ≤ count541 b) else decide (18 ≤ count541 b)))) else (if i < 562 then (if i < 560 then decide (19 ≤ count541 b) else (if i < 561 then decide (20 ≤ count541 b) else decide (21 ≤ count541 b))) else (if i < 563 then decide (22 ≤ count541 b) else (if i < 564 then decide (23 ≤ count541 b) else decide (24 ≤ count541 b))))) else (if i < 571 then (if i < 568 then (if i < 566 then decide (25 ≤ count541 b) else (if i < 567 then decide (26 ≤ count541 b) else decide (27 ≤ count541 b))) else (if i < 569 then decide (28 ≤ count541 b) else (if i < 570 then decide (1 ≤ count569 b) else decide (2 ≤ count569 b)))) else (if i < 574 then (if i < 572 then decide (1 ≤ count571 b) else (if i < 573 then decide (2 ≤ count571 b) else decide (3 ≤ count571 b))) else (if i < 576 then (if i < 575 then decide (1 ≤ count574 b) else decide (2 ≤ count574 b)) else (if i < 577 then decide (1 ≤ count576 b) else decide (2 ≤ count576 b))))))))) else (if i < 674 then (if i < 626 then (if i < 602 then (if i < 590 then (if i < 584 then (if i < 581 then (if i < 579 then decide (1 ≤ count578 b) else (if i < 580 then decide (2 ≤ count578 b) else decide (3 ≤ count578 b))) else (if i < 582 then decide (4 ≤ count578 b) else (if i < 583 then decide (1 ≤ count582 b) else decide (2 ≤ count582 b)))) else (if i < 587 then (if i < 585 then decide (3 ≤ count582 b) else (if i < 586 then decide (4 ≤ count582 b) else decide (5 ≤ count582 b))) else (if i < 588 then decide (6 ≤ count582 b) else (if i < 589 then decide (7 ≤ count582 b) else decide (1 ≤ count589 b))))) else (if i < 596 then (if i < 593 then (if i < 591 then decide (2 ≤ count589 b) else (if i < 592 then decide (1 ≤ count591 b) else decide (2 ≤ count591 b))) else (if i < 594 then decide (3 ≤ count591 b) else (if i < 595 then decide (1 ≤ count594 b) else decide (2 ≤ count594 b)))) else (if i < 599 then (if i < 597 then decide (1 ≤ count596 b) else (if i < 598 then decide (2 ≤ count596 b) else decide (1 ≤ count598 b))) else (if i < 600 then decide (2 ≤ count598 b) else (if i < 601 then decide (3 ≤ count598 b) else decide (4 ≤ count598 b)))))) else (if i < 614 then (if i < 608 then (if i < 605 then (if i < 603 then decide (1 ≤ count602 b) else (if i < 604 then decide (2 ≤ count602 b) else decide (3 ≤ count602 b))) else (if i < 606 then decide (4 ≤ count602 b) else (if i < 607 then decide (5 ≤ count602 b) else decide (6 ≤ count602 b)))) else (if i < 611 then (if i < 609 then decide (7 ≤ count602 b) else (if i < 610 then decide (1 ≤ count609 b) else decide (2 ≤ count609 b))) else (if i < 612 then decide (3 ≤ count609 b) else (if i < 613 then decide (4 ≤ count609 b) else decide (5 ≤ count609 b))))) else (if i < 620 then (if i < 617 then (if i < 615 then decide (6 ≤ count609 b) else (if i < 616 then decide (7 ≤ count609 b) else decide (8 ≤ count609 b))) else (if i < 618 then decide (9 ≤ count609 b) else (if i < 619 then decide (10 ≤ count609 b) else decide (11 ≤ count609 b)))) else (if i < 623 then (if i < 621 then decide (12 ≤ count609 b) else (if i < 622 then decide (13 ≤ count609 b) else decide (14 ≤ count609 b))) else (if i < 624 then decide (1 ≤ count623 b) else (if i < 625 then decide (2 ≤ count623 b) else decide (1 ≤ count625 b))))))) else (if i < 650 then (if i < 638 then (if i < 632 then (if i < 629 then (if i < 627 then decide (2 ≤ count625 b) else (if i < 628 then decide (3 ≤ count625 b) else decide (1 ≤ count628 b))) else (if i < 630 then decide (2 ≤ count628 b) else (if i < 631 then decide (1 ≤ count630 b) else decide (2 ≤ count630 b)))) else (if i < 635 then (if i < 633 then decide (1 ≤ count632 b) else (if i < 634 then decide (2 ≤ count632 b) else decide (3 ≤ count632 b))) else (if i < 636 then decide (4 ≤ count632 b) else (if i < 637 then decide (1 ≤ count636 b) else decide (2 ≤ count636 b))))) else (if i < 644 then (if i < 641 then (if i < 639 then decide (3 ≤ count636 b) else (if i < 640 then decide (4 ≤ count636 b) else decide (5 ≤ count636 b))) else (if i < 642 then decide (6 ≤ count636 b) else (if i < 643 then decide (7 ≤ count636 b) else decide (1 ≤ count643 b)))) else (if i < 647 then (if i < 645 then decide (2 ≤ count643 b) else (if i < 646 then decide (1 ≤ count645 b) else decide (2 ≤ count645 b))) else (if i < 648 then decide (1 ≤ count647 b) else (if i < 649 then decide (2 ≤ count647 b) else decide (3 ≤ count647 b)))))) else (if i < 662 then (if i < 656 then (if i < 653 then (if i < 651 then decide (4 ≤ count647 b) else (if i < 652 then decide (1 ≤ count651 b) else decide (2 ≤ count651 b))) else (if i < 654 then decide (1 ≤ count653 b) else (if i < 655 then decide (2 ≤ count653 b) else decide (1 ≤ count655 b)))) else (if i < 659 then (if i < 657 then decide (2 ≤ count655 b) else (if i < 658 then decide (3 ≤ count655 b) else decide (4 ≤ count655 b))) else (if i < 660 then decide (1 ≤ count659 b) else (if i < 661 then decide (2 ≤ count659 b) else decide (3 ≤ count659 b))))) else (if i < 668 then (if i < 665 then (if i < 663 then decide (4 ≤ count659 b) else (if i < 664 then decide (5 ≤ count659 b) else decide (6 ≤ count659 b))) else (if i < 666 then decide (7 ≤ count659 b) else (if i < 667 then decide (8 ≤ count659 b) else decide (1 ≤ count667 b)))) else (if i < 671 then (if i < 669 then decide (2 ≤ count667 b) else (if i < 670 then decide (3 ≤ count667 b) else decide (4 ≤ count667 b))) else (if i < 672 then decide (5 ≤ count667 b) else (if i < 673 then decide (6 ≤ count667 b) else decide (7 ≤ count667 b)))))))) else (if i < 722 then (if i < 698 then (if i < 686 then (if i < 680 then (if i < 677 then (if i < 675 then decide (8 ≤ count667 b) else (if i < 676 then decide (9 ≤ count667 b) else decide (10 ≤ count667 b))) else (if i < 678 then decide (11 ≤ count667 b) else (if i < 679 then decide (12 ≤ count667 b) else decide (13 ≤ count667 b)))) else (if i < 683 then (if i < 681 then decide (14 ≤ count667 b) else (if i < 682 then decide (15 ≤ count667 b) else decide (1 ≤ count682 b))) else (if i < 684 then decide (2 ≤ count682 b) else (if i < 685 then decide (3 ≤ count682 b) else decide (4 ≤ count682 b))))) else (if i < 692 then (if i < 689 then (if i < 687 then decide (5 ≤ count682 b) else (if i < 688 then decide (6 ≤ count682 b) else decide (7 ≤ count682 b))) else (if i < 690 then decide (8 ≤ count682 b) else (if i < 691 then decide (9 ≤ count682 b) else decide (10 ≤ count682 b)))) else (if i < 695 then (if i < 693 then decide (11 ≤ count682 b) else (if i < 694 then decide (12 ≤ count682 b) else decide (13 ≤ count682 b))) else (if i < 696 then decide (14 ≤ count682 b) else (if i < 697 then decide (15 ≤ count682 b) else decide (16 ≤ count682 b)))))) else (if i < 710 then (if i < 704 then (if i < 701 then (if i < 699 then decide (17 ≤ count682 b) else (if i < 700 then decide (18 ≤ count682 b) else decide (19 ≤ count682 b))) else (if i < 702 then decide (20 ≤ count682 b) else (if i < 703 then decide (21 ≤ count682 b) else decide (22 ≤ count682 b)))) else (if i < 707 then (if i < 705 then decide (23 ≤ count682 b) else (if i < 706 then decide (24 ≤ count682 b) else decide (25 ≤ count682 b))) else (if i < 708 then decide (26 ≤ count682 b) else (if i < 709 then decide (27 ≤ count682 b) else decide (28 ≤ count682 b))))) else (if i < 716 then (if i < 713 then (if i < 711 then decide (29 ≤ count682 b) else (if i < 712 then decide (1 ≤ count711 b) else decide (2 ≤ count711 b))) else (if i < 714 then decide (3 ≤ count711 b) else (if i < 715 then decide (4 ≤ count711 b) else decide (5 ≤ count711 b)))) else (if i < 719 then (if i < 717 then decide (6 ≤ count711 b) else (if i < 718 then decide (7 ≤ count711 b) else decide (8 ≤ count711 b))) else (if i < 720 then decide (9 ≤ count711 b) else (if i < 721 then decide (10 ≤ count711 b) else decide (11 ≤ count711 b))))))) else (if i < 746 then (if i < 734 then (if i < 728 then (if i < 725 then (if i < 723 then decide (12 ≤ count711 b) else (if i < 724 then decide (13 ≤ count711 b) else decide (14 ≤ count711 b))) else (if i < 726 then decide (15 ≤ count711 b) else (if i < 727 then decide (16 ≤ count711 b) else decide (17 ≤ count711 b)))) else (if i < 731 then (if i < 729 then decide (18 ≤ count711 b) else (if i < 730 then decide (19 ≤ count711 b) else decide (20 ≤ count711 b))) else (if i < 732 then decide (21 ≤ count711 b) else (if i < 733 then decide (22 ≤ count711 b) else decide (23 ≤ count711 b))))) else (if i < 740 then (if i < 737 then (if i < 735 then decide (24 ≤ count711 b) else (if i < 736 then decide (25 ≤ count711 b) else decide (26 ≤ count711 b))) else (if i < 738 then decide (27 ≤ count711 b) else (if i < 739 then decide (28 ≤ count711 b) else decide (29 ≤ count711 b)))) else (if i < 743 then (if i < 741 then decide (30 ≤ count711 b) else (if i < 742 then decide (31 ≤ count711 b) else decide (32 ≤ count711 b))) else (if i < 744 then decide (33 ≤ count711 b) else (if i < 745 then decide (34 ≤ count711 b) else decide (35 ≤ count711 b)))))) else (if i < 758 then (if i < 752 then (if i < 749 then (if i < 747 then decide (36 ≤ count711 b) else (if i < 748 then decide (37 ≤ count711 b) else decide (38 ≤ count711 b))) else (if i < 750 then decide (39 ≤ count711 b) else (if i < 751 then decide (40 ≤ count711 b) else decide (41 ≤ count711 b)))) else (if i < 755 then (if i < 753 then decide (42 ≤ count711 b) else (if i < 754 then decide (1 ≤ count753 b) else decide (2 ≤ count753 b))) else (if i < 756 then decide (1 ≤ count755 b) else (if i < 757 then decide (2 ≤ count755 b) else decide (3 ≤ count755 b))))) else (if i < 764 then (if i < 761 then (if i < 759 then decide (1 ≤ count758 b) else (if i < 760 then decide (2 ≤ count758 b) else decide (1 ≤ count760 b))) else (if i < 762 then decide (2 ≤ count760 b) else (if i < 763 then decide (1 ≤ count762 b) else decide (2 ≤ count762 b)))) else (if i < 767 then (if i < 765 then decide (3 ≤ count762 b) else (if i < 766 then decide (4 ≤ count762 b) else decide (1 ≤ count766 b))) else (if i < 769 then (if i < 768 then decide (2 ≤ count766 b) else decide (3 ≤ count766 b)) else (if i < 770 then decide (4 ≤ count766 b) else decide (5 ≤ count766 b))))))))))) else (if i < 1157 then (if i < 964 then (if i < 867 then (if i < 819 then (if i < 795 then (if i < 783 then (if i < 777 then (if i < 774 then (if i < 772 then decide (6 ≤ count766 b) else (if i < 773 then decide (7 ≤ count766 b) else decide (1 ≤ count773 b))) else (if i < 775 then decide (2 ≤ count773 b) else (if i < 776 then decide (1 ≤ count775 b) else decide (2 ≤ count775 b)))) else (if i < 780 then (if i < 778 then decide (3 ≤ count775 b) else (if i < 779 then decide (1 ≤ count778 b) else decide (2 ≤ count778 b))) else (if i < 781 then decide (1 ≤ count780 b) else (if i < 782 then decide (2 ≤ count780 b) else decide (1 ≤ count782 b))))) else (if i < 789 then (if i < 786 then (if i < 784 then decide (2 ≤ count782 b) else (if i < 785 then decide (3 ≤ count782 b) else decide (4 ≤ count782 b))) else (if i < 787 then decide (1 ≤ count786 b) else (if i < 788 then decide (2 ≤ count786 b) else decide (3 ≤ count786 b)))) else (if i < 792 then (if i < 790 then decide (4 ≤ count786 b) else (if i < 791 then decide (5 ≤ count786 b) else decide (6 ≤ count786 b))) else (if i < 793 then decide (7 ≤ count786 b) else (if i < 794 then decide (1 ≤ count793 b) else decide (2 ≤ count793 b)))))) else (if i < 807 then (if i < 801 then (if i < 798 then (if i < 796 then decide (3 ≤ count793 b) else (if i < 797 then decide (4 ≤ count793 b) else decide (5 ≤ count793 b))) else (if i < 799 then decide (6 ≤ count793 b) else (if i < 800 then decide (7 ≤ count793 b) else decide (8 ≤ count793 b)))) else (if i < 804 then (if i < 802 then decide (9 ≤ count793 b) else (if i < 803 then decide (10 ≤ count793 b) else decide (11 ≤ count793 b))) else (if i < 805 then decide (12 ≤ count793 b) else (if i < 806 then decide (13 ≤ count793 b) else decide (14 ≤ count793 b))))) else (if i < 813 then (if i < 810 then (if i < 808 then decide (1 ≤ count807 b) else (if i < 809 then decide (2 ≤ count807 b) else decide (1 ≤ count809 b))) else (if i < 811 then decide (2 ≤ count809 b) else (if i < 812 then decide (3 ≤ count809 b) else decide (1 ≤ count812 b)))) else (if i < 816 then (if i < 814 then decide (2 ≤ count812 b) else (if i < 815 then decide (1 ≤ count814 b) else decide (2 ≤ count814 b))) else (if i < 817 then decide (1 ≤ count816 b) else (if i < 818 then decide (2 ≤ count816 b) else decide (3 ≤ count816 b))))))) else (if i < 843 then (if i < 831 then (if i < 825 then (if i < 822 then (if i < 820 then decide (4 ≤ count816 b) else (if i < 821 then decide (1 ≤ count820 b) else decide (2 ≤ count820 b))) else (if i < 823 then decide (3 ≤ count820 b) else (if i < 824 then decide (4 ≤ count820 b) else decide (5 ≤ count820 b)))) else (if i < 828 then (if i < 826 then decide (6 ≤ count820 b) else (if i < 827 then decide (7 ≤ count820 b) else decide (1 ≤ count827 b))) else (if i < 829 then decide (2 ≤ count827 b) else (if i < 830 then decide (1 ≤ count829 b) else decide (2 ≤ count829 b))))) else (if i < 837 then (if i < 834 then (if i < 832 then decide (3 ≤ count829 b) else (if i < 833 then decide (1 ≤ count832 b) else decide (2 ≤ count832 b))) else (if i < 835 then decide (1 ≤ count834 b) else (if i < 836 then decide (2 ≤ count834 b) else decide (1 ≤ count836 b)))) else (if i < 840 then (if i < 838 then decide (2 ≤ count836 b) else (if i < 839 then decide (3 ≤ count836 b) else decide (4 ≤ count836 b))) else (if i < 841 then decide (1 ≤ count840 b) else (if i < 842 then decide (2 ≤ count840 b) else decide (3 ≤ count840 b)))))) else (if i < 855 then (if i < 849 then (if i < 846 then (if i < 844 then decide (4 ≤ count840 b) else (if i < 845 then decide (5 ≤ count840 b) else decide (6 ≤ count840 b))) else (if i < 847 then decide (7 ≤ count840 b) else (if i < 848 then decide (1 ≤ count847 b) else decide (2 ≤ count847 b)))) else (if i < 852 then (if i < 850 then decide (3 ≤ count847 b) else (if i < 851 then decide (4 ≤ count847 b) else decide (5 ≤ count847 b))) else (if i < 853 then decide (6 ≤ count847 b) else (if i < 854 then decide (7 ≤ count847 b) else decide (8 ≤ count847 b))))) else (if i < 861 then (if i < 858 then (if i < 856 then decide (9 ≤ count847 b) else (if i < 857 then decide (10 ≤ count847 b) else decide (11 ≤ count847 b))) else (if i < 859 then decide (12 ≤ count847 b) else (if i < 860 then decide (13 ≤ count847 b) else decide (14 ≤ count847 b)))) else (if i < 864 then (if i < 862 then decide (1 ≤ count861 b) else (if i < 863 then decide (2 ≤ count861 b) else decide (3 ≤ count861 b))) else (if i < 865 then decide (4 ≤ count861 b) else (if i < 866 then decide (5 ≤ count861 b) else decide (6 ≤ count861 b)))))))) else (if i < 915 then (if i < 891 then (if i < 879 then (if i < 873 then (if i < 870 then (if i < 868 then decide (7 ≤ count861 b) else (if i < 869 then decide (8 ≤ count861 b) else decide (9 ≤ count861 b))) else (if i < 871 then decide (10 ≤ count861 b) else (if i < 872 then decide (11 ≤ count861 b) else decide (12 ≤ count861 b)))) else (if i < 876 then (if i < 874 then decide (13 ≤ count861 b) else (if i < 875 then decide (14 ≤ count861 b) else decide (15 ≤ count861 b))) else (if i < 877 then decide (16 ≤ count861 b) else (if i < 878 then decide (17 ≤ count861 b) else decide (1 ≤ count878 b))))) else (if i < 885 then (if i < 882 then (if i < 880 then decide (2 ≤ count878 b) else (if i < 881 then decide (1 ≤ count880 b) else decide (2 ≤ count880 b))) else (if i < 883 then decide (3 ≤ count880 b) else (if i < 884 then decide (1 ≤ count883 b) else decide (2 ≤ count883 b)))) else (if i < 888 then (if i < 886 then decide (1 ≤ count885 b) else (if i < 887 then decide (2 ≤ count885 b) else decide (1 ≤ count887 b))) else (if i < 889 then decide (2 ≤ count887 b) else (if i < 890 then decide (3 ≤ count887 b) else decide (4 ≤ count887 b)))))) else (if i < 903 then (if i < 897 then (if i < 894 then (if i < 892 then decide (1 ≤ count891 b) else (if i < 893 then decide (2 ≤ count891 b) else decide (3 ≤ count891 b))) else (if i < 895 then decide (4 ≤ count891 b) else (if i < 896 then decide (5 ≤ count891 b) else decide (6 ≤ count891 b)))) else (if i < 900 then (if i < 898 then decide (7 ≤ count891 b) else (if i < 899 then decide (1 ≤ count898 b) else decide (2 ≤ count898 b))) else (if i < 901 then decide (1 ≤ count900 b) else (if i < 902 then decide (2 ≤ count900 b) else decide (3 ≤ count900 b))))) else (if i < 909 then (if i < 906 then (if i < 904 then decide (1 ≤ count903 b) else (if i < 905 then decide (2 ≤ count903 b) else decide (1 ≤ count905 b))) else (if i < 907 then decide (2 ≤ count905 b) else (if i < 908 then decide (1 ≤ count907 b) else decide (2 ≤ count907 b)))) else (if i < 912 then (if i < 910 then decide (3 ≤ count907 b) else (if i < 911 then decide (4 ≤ count907 b) else decide (1 ≤ count911 b))) else (if i < 913 then decide (2 ≤ count911 b) else (if i < 914 then decide (3 ≤ count911 b) else decide (4 ≤ count911 b))))))) else (if i < 939 then (if i < 927 then (if i < 921 then (if i < 918 then (if i < 916 then decide (5 ≤ count911 b) else (if i < 917 then decide (6 ≤ count911 b) else decide (7 ≤ count911 b))) else (if i < 919 then decide (1 ≤ count918 b) else (if i < 920 then decide (2 ≤ count918 b) else decide (3 ≤ count918 b)))) else (if i < 924 then (if i < 922 then decide (4 ≤ count918 b) else (if i < 923 then decide (5 ≤ count918 b) else decide (6 ≤ count918 b))) else (if i < 925 then decide (7 ≤ count918 b) else (if i < 926 then decide (8 ≤ count918 b) else decide (9 ≤ count918 b))))) else (if i < 933 then (if i < 930 then (if i < 928 then decide (10 ≤ count918 b) else (if i < 929 then decide (11 ≤ count918 b) else decide (12 ≤ count918 b))) else (if i < 931 then decide (13 ≤ count918 b) else (if i < 932 then decide (14 ≤ count918 b) else decide (1 ≤ count932 b)))) else (if i < 936 then (if i < 934 then decide (2 ≤ count932 b) else (if i < 935 then decide (1 ≤ count934 b) else decide (2 ≤ count934 b))) else (if i < 937 then decide (3 ≤ count934 b) else (if i < 938 then decide (1 ≤ count937 b) else decide (2 ≤ count937 b)))))) else (if i < 951 then (if i < 945 then (if i < 942 then (if i < 940 then decide (1 ≤ count939 b) else (if i < 941 then decide (2 ≤ count939 b) else decide (1 ≤ count941 b))) else (if i < 943 then decide (2 ≤ count941 b) else (if i < 944 then decide (3 ≤ count941 b) else decide (4 ≤ count941 b)))) else (if i < 948 then (if i < 946 then decide (1 ≤ count945 b) else (if i < 947 then decide (2 ≤ count945 b) else decide (3 ≤ count945 b))) else (if i < 949 then decide (4 ≤ count945 b) else (if i < 950 then decide (5 ≤ count945 b) else decide (6 ≤ count945 b))))) else (if i < 957 then (if i < 954 then (if i < 952 then decide (7 ≤ count945 b) else (if i < 953 then decide (1 ≤ count952 b) else decide (2 ≤ count952 b))) else (if i < 955 then decide (1 ≤ count954 b) else (if i < 956 then decide (2 ≤ count954 b) else decide (1 ≤ count956 b)))) else (if i < 960 then (if i < 958 then decide (2 ≤ count956 b) else (if i < 959 then decide (3 ≤ count956 b) else decide (4 ≤ count956 b))) else (if i < 962 then (if i < 961 then decide (1 ≤ count960 b) else decide (2 ≤ count960 b)) else (if i < 963 then decide (1 ≤ count962 b) else decide (2 ≤ count962 b))))))))) else (if i < 1060 then (if i < 1012 then (if i < 988 then (if i < 976 then (if i < 970 then (if i < 967 then (if i < 965 then decide (1 ≤ count964 b) else (if i < 966 then decide (2 ≤ count964 b) else decide (3 ≤ count964 b))) else (if i < 968 then decide (4 ≤ count964 b) else (if i < 969 then decide (1 ≤ count968 b) else decide (2 ≤ count968 b)))) else (if i < 973 then (if i < 971 then decide (3 ≤ count968 b) else (if i < 972 then decide (4 ≤ count968 b) else decide (5 ≤ count968 b))) else (if i < 974 then decide (6 ≤ count968 b) else (if i < 975 then decide (7 ≤ count968 b) else decide (8 ≤ count968 b))))) else (if i < 982 then (if i < 979 then (if i < 977 then decide (1 ≤ count976 b) else (if i < 978 then decide (2 ≤ count976 b) else decide (3 ≤ count976 b))) else (if i < 980 then decide (4 ≤ count976 b) else (if i < 981 then decide (5 ≤ count976 b) else decide (6 ≤ count976 b)))) else (if i < 985 then (if i < 983 then decide (7 ≤ count976 b) else (if i < 984 then decide (8 ≤ count976 b) else decide (9 ≤ count976 b))) else (if i < 986 then decide (10 ≤ count976 b) else (if i < 987 then decide (11 ≤ count976 b) else decide (12 ≤ count976 b)))))) else (if i < 1000 then (if i < 994 then (if i < 991 then (if i < 989 then decide (13 ≤ count976 b) else (if i < 990 then decide (14 ≤ count976 b) else decide (15 ≤ count976 b))) else (if i < 992 then decide (1 ≤ count991 b) else (if i < 993 then decide (2 ≤ count991 b) else decide (3 ≤ count991 b)))) else (if i < 997 then (if i < 995 then decide (4 ≤ count991 b) else (if i < 996 then decide (5 ≤ count991 b) else decide (6 ≤ count991 b))) else (if i < 998 then decide (7 ≤ count991 b) else (if i < 999 then decide (8 ≤ count991 b) else decide (9 ≤ count991 b))))) else (if i < 1006 then (if i < 1003 then (if i < 1001 then decide (10 ≤ count991 b) else (if i < 1002 then decide (11 ≤ count991 b) else decide (12 ≤ count991 b))) else (if i < 1004 then decide (13 ≤ count991 b) else (if i < 1005 then decide (14 ≤ count991 b) else decide (15 ≤ count991 b)))) else (if i < 1009 then (if i < 1007 then decide (16 ≤ count991 b) else (if i < 1008 then decide (17 ≤ count991 b) else decide (1 ≤ count1008 b))) else (if i < 1010 then decide (2 ≤ count1008 b) else (if i < 1011 then decide (3 ≤ count1008 b) else decide (4 ≤ count1008 b))))))) else (if i < 1036 then (if i < 1024 then (if i < 1018 then (if i < 1015 then (if i < 1013 then decide (5 ≤ count1008 b) else (if i < 1014 then decide (6 ≤ count1008 b) else decide (7 ≤ count1008 b))) else (if i < 1016 then decide (8 ≤ count1008 b) else (if i < 1017 then decide (9 ≤ count1008 b) else decide (10 ≤ count1008 b)))) else (if i < 1021 then (if i < 1019 then decide (11 ≤ count1008 b) else (if i < 1020 then decide (12 ≤ count1008 b) else decide (13 ≤ count1008 b))) else (if i < 1022 then decide (14 ≤ count1008 b) else (if i < 1023 then decide (15 ≤ count1008 b) else decide (16 ≤ count1008 b))))) else (if i < 1030 then (if i < 1027 then (if i < 1025 then decide (17 ≤ count1008 b) else (if i < 1026 then decide (1 ≤ count1025 b) else decide (2 ≤ count1025 b))) else (if i < 1028 then decide (1 ≤ count1027 b) else (if i < 1029 then decide (2 ≤ count1027 b) else decide (3 ≤ count1027 b)))) else (if i < 1033 then (if i < 1031 then decide (1 ≤ count1030 b) else (if i < 1032 then decide (2 ≤ count1030 b) else decide (1 ≤ count1032 b))) else (if i < 1034 then decide (2 ≤ count1032 b) else (if i < 1035 then decide (3 ≤ count1032 b) else decide (1 ≤ count1035 b)))))) else (if i < 1048 then (if i < 1042 then (if i < 1039 then (if i < 1037 then decide (2 ≤ count1035 b) else (if i < 1038 then decide (3 ≤ count1035 b) else decide (4 ≤ count1035 b))) else (if i < 1040 then decide (5 ≤ count1035 b) else (if i < 1041 then decide (6 ≤ count1035 b) else decide (1 ≤ count1041 b)))) else (if i < 1045 then (if i < 1043 then decide (2 ≤ count1041 b) else (if i < 1044 then decide (1 ≤ count1043 b) else decide (2 ≤ count1043 b))) else (if i < 1046 then decide (3 ≤ count1043 b) else (if i < 1047 then decide (1 ≤ count1046 b) else decide (2 ≤ count1046 b))))) else (if i < 1054 then (if i < 1051 then (if i < 1049 then decide (1 ≤ count1048 b) else (if i < 1050 then decide (2 ≤ count1048 b) else decide (1 ≤ count1050 b))) else (if i < 1052 then decide (2 ≤ count1050 b) else (if i < 1053 then decide (3 ≤ count1050 b) else decide (4 ≤ count1050 b)))) else (if i < 1057 then (if i < 1055 then decide (1 ≤ count1054 b) else (if i < 1056 then decide (2 ≤ count1054 b) else decide (3 ≤ count1054 b))) else (if i < 1058 then decide (4 ≤ count1054 b) else (if i < 1059 then decide (5 ≤ count1054 b) else decide (6 ≤ count1054 b)))))))) else (if i < 1108 then (if i < 1084 then (if i < 1072 then (if i < 1066 then (if i < 1063 then (if i < 1061 then decide (7 ≤ count1054 b) else (if i < 1062 then decide (1 ≤ count1061 b) else decide (2 ≤ count1061 b))) else (if i < 1064 then decide (3 ≤ count1061 b) else (if i < 1065 then decide (4 ≤ count1061 b) else decide (5 ≤ count1061 b)))) else (if i < 1069 then (if i < 1067 then decide (6 ≤ count1061 b) else (if i < 1068 then decide (7 ≤ count1061 b) else decide (8 ≤ count1061 b))) else (if i < 1070 then decide (9 ≤ count1061 b) else (if i < 1071 then decide (10 ≤ count1061 b) else decide (11 ≤ count1061 b))))) else (if i < 1078 then (if i < 1075 then (if i < 1073 then decide (12 ≤ count1061 b) else (if i < 1074 then decide (13 ≤ count1061 b) else decide (1 ≤ count1074 b))) else (if i < 1076 then decide (2 ≤ count1074 b) else (if i < 1077 then decide (1 ≤ count1076 b) else decide (2 ≤ count1076 b)))) else (if i < 1081 then (if i < 1079 then decide (3 ≤ count1076 b) else (if i < 1080 then decide (1 ≤ count1079 b) else decide (2 ≤ count1079 b))) else (if i < 1082 then decide (1 ≤ count1081 b) else (if i < 1083 then decide (2 ≤ count1081 b) else decide (3 ≤ count1081 b)))))) else (if i < 1096 then (if i < 1090 then (if i < 1087 then (if i < 1085 then decide (1 ≤ count1084 b) else (if i < 1086 then decide (2 ≤ count1084 b) else decide (3 ≤ count1084 b))) else (if i < 1088 then decide (4 ≤ count1084 b) else (if i < 1089 then decide (5 ≤ count1084 b) else decide (6 ≤ count1084 b)))) else (if i < 1093 then (if i < 1091 then decide (1 ≤ count1090 b) else (if i < 1092 then decide (2 ≤ count1090 b) else decide (1 ≤ count1092 b))) else (if i < 1094 then decide (2 ≤ count1092 b) else (if i < 1095 then decide (3 ≤ count1092 b) else decide (1 ≤ count1095 b))))) else (if i < 1102 then (if i < 1099 then (if i < 1097 then decide (2 ≤ count1095 b) else (if i < 1098 then decide (1 ≤ count1097 b) else decide (2 ≤ count1097 b))) else (if i < 1100 then decide (1 ≤ count1099 b) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (3 ≤ count1099 b)))) else (if i < 1105 then (if i < 1103 then decide (4 ≤ count1099 b) else (if i < 1104 then decide (1 ≤ count1103 b) else decide (2 ≤ count1103 b))) else (if i < 1106 then decide (3 ≤ count1103 b) else (if i < 1107 then decide (4 ≤ count1103 b) else decide (5 ≤ count1103 b))))))) else (if i < 1132 then (if i < 1120 then (if i < 1114 then (if i < 1111 then (if i < 1109 then decide (6 ≤ count1103 b) else (if i < 1110 then decide (7 ≤ count1103 b) else decide (1 ≤ count1110 b))) else (if i < 1112 then decide (2 ≤ count1110 b) else (if i < 1113 then decide (3 ≤ count1110 b) else decide (4 ≤ count1110 b)))) else (if i < 1117 then (if i < 1115 then decide (5 ≤ count1110 b) else (if i < 1116 then decide (6 ≤ count1110 b) else decide (7 ≤ count1110 b))) else (if i < 1118 then decide (8 ≤ count1110 b) else (if i < 1119 then decide (9 ≤ count1110 b) else decide (10 ≤ count1110 b))))) else (if i < 1126 then (if i < 1123 then (if i < 1121 then decide (11 ≤ count1110 b) else (if i < 1122 then decide (12 ≤ count1110 b) else decide (13 ≤ count1110 b))) else (if i < 1124 then decide (1 ≤ count1123 b) else (if i < 1125 then decide (2 ≤ count1123 b) else decide (3 ≤ count1123 b)))) else (if i < 1129 then (if i < 1127 then decide (4 ≤ count1123 b) else (if i < 1128 then decide (5 ≤ count1123 b) else decide (6 ≤ count1123 b))) else (if i < 1130 then decide (7 ≤ count1123 b) else (if i < 1131 then decide (8 ≤ count1123 b) else decide (9 ≤ count1123 b)))))) else (if i < 1144 then (if i < 1138 then (if i < 1135 then (if i < 1133 then decide (10 ≤ count1123 b) else (if i < 1134 then decide (11 ≤ count1123 b) else decide (12 ≤ count1123 b))) else (if i < 1136 then decide (13 ≤ count1123 b) else (if i < 1137 then decide (14 ≤ count1123 b) else decide (15 ≤ count1123 b)))) else (if i < 1141 then (if i < 1139 then decide (16 ≤ count1123 b) else (if i < 1140 then decide (17 ≤ count1123 b) else decide (18 ≤ count1123 b))) else (if i < 1142 then decide (19 ≤ count1123 b) else (if i < 1143 then decide (20 ≤ count1123 b) else decide (21 ≤ count1123 b))))) else (if i < 1150 then (if i < 1147 then (if i < 1145 then decide (22 ≤ count1123 b) else (if i < 1146 then decide (23 ≤ count1123 b) else decide (24 ≤ count1123 b))) else (if i < 1148 then decide (25 ≤ count1123 b) else (if i < 1149 then decide (26 ≤ count1123 b) else decide (1 ≤ count1149 b)))) else (if i < 1153 then (if i < 1151 then decide (2 ≤ count1149 b) else (if i < 1152 then decide (1 ≤ count1151 b) else decide (2 ≤ count1151 b))) else (if i < 1155 then (if i < 1154 then decide (3 ≤ count1151 b) else decide (1 ≤ count1154 b)) else (if i < 1156 then decide (2 ≤ count1154 b) else decide (1 ≤ count1156 b)))))))))) else (if i < 1350 then (if i < 1253 then (if i < 1205 then (if i < 1181 then (if i < 1169 then (if i < 1163 then (if i < 1160 then (if i < 1158 then decide (2 ≤ count1156 b) else (if i < 1159 then decide (3 ≤ count1156 b) else decide (1 ≤ count1159 b))) else (if i < 1161 then decide (2 ≤ count1159 b) else (if i < 1162 then decide (3 ≤ count1159 b) else decide (4 ≤ count1159 b)))) else (if i < 1166 then (if i < 1164 then decide (5 ≤ count1159 b) else (if i < 1165 then decide (6 ≤ count1159 b) else decide (1 ≤ count1165 b))) else (if i < 1167 then decide (2 ≤ count1165 b) else (if i < 1168 then decide (1 ≤ count1167 b) else decide (2 ≤ count1167 b))))) else (if i < 1175 then (if i < 1172 then (if i < 1170 then decide (3 ≤ count1167 b) else (if i < 1171 then decide (1 ≤ count1170 b) else decide (2 ≤ count1170 b))) else (if i < 1173 then decide (1 ≤ count1172 b) else (if i < 1174 then decide (2 ≤ count1172 b) else decide (1 ≤ count1174 b)))) else (if i < 1178 then (if i < 1176 then decide (2 ≤ count1174 b) else (if i < 1177 then decide (3 ≤ count1174 b) else decide (4 ≤ count1174 b))) else (if i < 1179 then decide (1 ≤ count1178 b) else (if i < 1180 then decide (2 ≤ count1178 b) else decide (3 ≤ count1178 b)))))) else (if i < 1193 then (if i < 1187 then (if i < 1184 then (if i < 1182 then decide (4 ≤ count1178 b) else (if i < 1183 then decide (5 ≤ count1178 b) else decide (6 ≤ count1178 b))) else (if i < 1185 then decide (7 ≤ count1178 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b)))) else (if i < 1190 then (if i < 1188 then decide (3 ≤ count1185 b) else (if i < 1189 then decide (4 ≤ count1185 b) else decide (5 ≤ count1185 b))) else (if i < 1191 then decide (6 ≤ count1185 b) else (if i < 1192 then decide (7 ≤ count1185 b) else decide (8 ≤ count1185 b))))) else (if i < 1199 then (if i < 1196 then (if i < 1194 then decide (9 ≤ count1185 b) else (if i < 1195 then decide (10 ≤ count1185 b) else decide (11 ≤ count1185 b))) else (if i < 1197 then decide (12 ≤ count1185 b) else (if i < 1198 then decide (13 ≤ count1185 b) else decide (1 ≤ count1198 b)))) else (if i < 1202 then (if i < 1200 then decide (2 ≤ count1198 b) else (if i < 1201 then decide (1 ≤ count1200 b) else decide (2 ≤ count1200 b))) else (if i < 1203 then decide (3 ≤ count1200 b) else (if i < 1204 then decide (1 ≤ count1203 b) else decide (2 ≤ count1203 b))))))) else (if i < 1229 then (if i < 1217 then (if i < 1211 then (if i < 1208 then (if i < 1206 then decide (1 ≤ count1205 b) else (if i < 1207 then decide (2 ≤ count1205 b) else decide (3 ≤ count1205 b))) else (if i < 1209 then decide (1 ≤ count1208 b) else (if i < 1210 then decide (2 ≤ count1208 b) else decide (3 ≤ count1208 b)))) else (if i < 1214 then (if i < 1212 then decide (4 ≤ count1208 b) else (if i < 1213 then decide (5 ≤ count1208 b) else decide (6 ≤ count1208 b))) else (if i < 1215 then decide (1 ≤ count1214 b) else (if i < 1216 then decide (2 ≤ count1214 b) else decide (1 ≤ count1216 b))))) else (if i < 1223 then (if i < 1220 then (if i < 1218 then decide (2 ≤ count1216 b) else (if i < 1219 then decide (3 ≤ count1216 b) else decide (1 ≤ count1219 b))) else (if i < 1221 then decide (2 ≤ count1219 b) else (if i < 1222 then decide (1 ≤ count1221 b) else decide (2 ≤ count1221 b)))) else (if i < 1226 then (if i < 1224 then decide (1 ≤ count1223 b) else (if i < 1225 then decide (2 ≤ count1223 b) else decide (3 ≤ count1223 b))) else (if i < 1227 then decide (4 ≤ count1223 b) else (if i < 1228 then decide (1 ≤ count1227 b) else decide (2 ≤ count1227 b)))))) else (if i < 1241 then (if i < 1235 then (if i < 1232 then (if i < 1230 then decide (3 ≤ count1227 b) else (if i < 1231 then decide (4 ≤ count1227 b) else decide (5 ≤ count1227 b))) else (if i < 1233 then decide (6 ≤ count1227 b) else (if i < 1234 then decide (7 ≤ count1227 b) else decide (1 ≤ count1234 b)))) else (if i < 1238 then (if i < 1236 then decide (2 ≤ count1234 b) else (if i < 1237 then decide (3 ≤ count1234 b) else decide (4 ≤ count1234 b))) else (if i < 1239 then decide (5 ≤ count1234 b) else (if i < 1240 then decide (6 ≤ count1234 b) else decide (7 ≤ count1234 b))))) else (if i < 1247 then (if i < 1244 then (if i < 1242 then decide (8 ≤ count1234 b) else (if i < 1243 then decide (9 ≤ count1234 b) else decide (10 ≤ count1234 b))) else (if i < 1245 then decide (11 ≤ count1234 b) else (if i < 1246 then decide (12 ≤ count1234 b) else decide (13 ≤ count1234 b)))) else (if i < 1250 then (if i < 1248 then decide (1 ≤ count1247 b) else (if i < 1249 then decide (2 ≤ count1247 b) else decide (3 ≤ count1247 b))) else (if i < 1251 then decide (4 ≤ count1247 b) else (if i < 1252 then decide (5 ≤ count1247 b) else decide (6 ≤ count1247 b)))))))) else (if i < 1301 then (if i < 1277 then (if i < 1265 then (if i < 1259 then (if i < 1256 then (if i < 1254 then decide (7 ≤ count1247 b) else (if i < 1255 then decide (8 ≤ count1247 b) else decide (9 ≤ count1247 b))) else (if i < 1257 then decide (10 ≤ count1247 b) else (if i < 1258 then decide (11 ≤ count1247 b) else decide (12 ≤ count1247 b)))) else (if i < 1262 then (if i < 1260 then decide (13 ≤ count1247 b) else (if i < 1261 then decide (14 ≤ count1247 b) else decide (15 ≤ count1247 b))) else (if i < 1263 then decide (16 ≤ count1247 b) else (if i < 1264 then decide (17 ≤ count1247 b) else decide (18 ≤ count1247 b))))) else (if i < 1271 then (if i < 1268 then (if i < 1266 then decide (19 ≤ count1247 b) else (if i < 1267 then decide (20 ≤ count1247 b) else decide (21 ≤ count1247 b))) else (if i < 1269 then decide (22 ≤ count1247 b) else (if i < 1270 then decide (23 ≤ count1247 b) else decide (24 ≤ count1247 b)))) else (if i < 1274 then (if i < 1272 then decide (25 ≤ count1247 b) else (if i < 1273 then decide (26 ≤ count1247 b) else decide (1 ≤ count1273 b))) else (if i < 1275 then decide (2 ≤ count1273 b) else (if i < 1276 then decide (3 ≤ count1273 b) else decide (4 ≤ count1273 b)))))) else (if i < 1289 then (if i < 1283 then (if i < 1280 then (if i < 1278 then decide (5 ≤ count1273 b) else (if i < 1279 then decide (6 ≤ count1273 b) else decide (7 ≤ count1273 b))) else (if i < 1281 then decide (8 ≤ count1273 b) else (if i < 1282 then decide (9 ≤ count1273 b) else decide (10 ≤ count1273 b)))) else (if i < 1286 then (if i < 1284 then decide (11 ≤ count1273 b) else (if i < 1285 then decide (12 ≤ count1273 b) else decide (13 ≤ count1273 b))) else (if i < 1287 then decide (14 ≤ count1273 b) else (if i < 1288 then decide (15 ≤ count1273 b) else decide (16 ≤ count1273 b))))) else (if i < 1295 then (if i < 1292 then (if i < 1290 then decide (17 ≤ count1273 b) else (if i < 1291 then decide (18 ≤ count1273 b) else decide (19 ≤ count1273 b))) else (if i < 1293 then decide (20 ≤ count1273 b) else (if i < 1294 then decide (21 ≤ count1273 b) else decide (22 ≤ count1273 b)))) else (if i < 1298 then (if i < 1296 then decide (23 ≤ count1273 b) else (if i < 1297 then decide (24 ≤ count1273 b) else decide (25 ≤ count1273 b))) else (if i < 1299 then decide (26 ≤ count1273 b) else (if i < 1300 then decide (27 ≤ count1273 b) else decide (28 ≤ count1273 b))))))) else (if i < 1325 then (if i < 1313 then (if i < 1307 then (if i < 1304 then (if i < 1302 then decide (29 ≤ count1273 b) else (if i < 1303 then decide (30 ≤ count1273 b) else decide (31 ≤ count1273 b))) else (if i < 1305 then decide (32 ≤ count1273 b) else (if i < 1306 then decide (33 ≤ count1273 b) else decide (34 ≤ count1273 b)))) else (if i < 1310 then (if i < 1308 then decide (35 ≤ count1273 b) else (if i < 1309 then decide (36 ≤ count1273 b) else decide (37 ≤ count1273 b))) else (if i < 1311 then decide (38 ≤ count1273 b) else (if i < 1312 then decide (39 ≤ count1273 b) else decide (40 ≤ count1273 b))))) else (if i < 1319 then (if i < 1316 then (if i < 1314 then decide (41 ≤ count1273 b) else (if i < 1315 then decide (42 ≤ count1273 b) else decide (1 ≤ count1315 b))) else (if i < 1317 then decide (2 ≤ count1315 b) else (if i < 1318 then decide (1 ≤ count1317 b) else decide (2 ≤ count1317 b)))) else (if i < 1322 then (if i < 1320 then decide (3 ≤ count1317 b) else (if i < 1321 then decide (1 ≤ count1320 b) else decide (2 ≤ count1320 b))) else (if i < 1323 then decide (1 ≤ count1322 b) else (if i < 1324 then decide (2 ≤ count1322 b) else decide (3 ≤ count1322 b)))))) else (if i < 1337 then (if i < 1331 then (if i < 1328 then (if i < 1326 then decide (1 ≤ count1325 b) else (if i < 1327 then decide (2 ≤ count1325 b) else decide (3 ≤ count1325 b))) else (if i < 1329 then decide (4 ≤ count1325 b) else (if i < 1330 then decide (5 ≤ count1325 b) else decide (6 ≤ count1325 b)))) else (if i < 1334 then (if i < 1332 then decide (1 ≤ count1331 b) else (if i < 1333 then decide (2 ≤ count1331 b) else decide (1 ≤ count1333 b))) else (if i < 1335 then decide (2 ≤ count1333 b) else (if i < 1336 then decide (3 ≤ count1333 b) else decide (1 ≤ count1336 b))))) else (if i < 1343 then (if i < 1340 then (if i < 1338 then decide (2 ≤ count1336 b) else (if i < 1339 then decide (1 ≤ count1338 b) else decide (2 ≤ count1338 b))) else (if i < 1341 then decide (1 ≤ count1340 b) else (if i < 1342 then decide (2 ≤ count1340 b) else decide (3 ≤ count1340 b)))) else (if i < 1346 then (if i < 1344 then decide (4 ≤ count1340 b) else (if i < 1345 then decide (1 ≤ count1344 b) else decide (2 ≤ count1344 b))) else (if i < 1348 then (if i < 1347 then decide (3 ≤ count1344 b) else decide (4 ≤ count1344 b)) else (if i < 1349 then decide (5 ≤ count1344 b) else decide (6 ≤ count1344 b))))))))) else (if i < 1446 then (if i < 1398 then (if i < 1374 then (if i < 1362 then (if i < 1356 then (if i < 1353 then (if i < 1351 then decide (7 ≤ count1344 b) else (if i < 1352 then decide (1 ≤ count1351 b) else decide (2 ≤ count1351 b))) else (if i < 1354 then decide (3 ≤ count1351 b) else (if i < 1355 then decide (4 ≤ count1351 b) else decide (5 ≤ count1351 b)))) else (if i < 1359 then (if i < 1357 then decide (6 ≤ count1351 b) else (if i < 1358 then decide (7 ≤ count1351 b) else decide (8 ≤ count1351 b))) else (if i < 1360 then decide (9 ≤ count1351 b) else (if i < 1361 then decide (10 ≤ count1351 b) else decide (11 ≤ count1351 b))))) else (if i < 1368 then (if i < 1365 then (if i < 1363 then decide (12 ≤ count1351 b) else (if i < 1364 then decide (1 ≤ count1363 b) else decide (2 ≤ count1363 b))) else (if i < 1366 then decide (1 ≤ count1365 b) else (if i < 1367 then decide (2 ≤ count1365 b) else decide (3 ≤ count1365 b)))) else (if i < 1371 then (if i < 1369 then decide (1 ≤ count1368 b) else (if i < 1370 then decide (2 ≤ count1368 b) else decide (1 ≤ count1370 b))) else (if i < 1372 then decide (2 ≤ count1370 b) else (if i < 1373 then decide (3 ≤ count1370 b) else decide (1 ≤ count1373 b)))))) else (if i < 1386 then (if i < 1380 then (if i < 1377 then (if i < 1375 then decide (2 ≤ count1373 b) else (if i < 1376 then decide (3 ≤ count1373 b) else decide (4 ≤ count1373 b))) else (if i < 1378 then decide (5 ≤ count1373 b) else (if i < 1379 then decide (6 ≤ count1373 b) else decide (1 ≤ count1379 b)))) else (if i < 1383 then (if i < 1381 then decide (2 ≤ count1379 b) else (if i < 1382 then decide (1 ≤ count1381 b) else decide (2 ≤ count1381 b))) else (if i < 1384 then decide (3 ≤ count1381 b) else (if i < 1385 then decide (1 ≤ count1384 b) else decide (2 ≤ count1384 b))))) else (if i < 1392 then (if i < 1389 then (if i < 1387 then decide (1 ≤ count1386 b) else (if i < 1388 then decide (2 ≤ count1386 b) else decide (1 ≤ count1388 b))) else (if i < 1390 then decide (2 ≤ count1388 b) else (if i < 1391 then decide (3 ≤ count1388 b) else decide (4 ≤ count1388 b)))) else (if i < 1395 then (if i < 1393 then decide (1 ≤ count1392 b) else (if i < 1394 then decide (2 ≤ count1392 b) else decide (3 ≤ count1392 b))) else (if i < 1396 then decide (4 ≤ count1392 b) else (if i < 1397 then decide (5 ≤ count1392 b) else decide (6 ≤ count1392 b))))))) else (if i < 1422 then (if i < 1410 then (if i < 1404 then (if i < 1401 then (if i < 1399 then decide (7 ≤ count1392 b) else (if i < 1400 then decide (1 ≤ count1399 b) else decide (2 ≤ count1399 b))) else (if i < 1402 then decide (3 ≤ count1399 b) else (if i < 1403 then decide (4 ≤ count1399 b) else decide (5 ≤ count1399 b)))) else (if i < 1407 then (if i < 1405 then decide (6 ≤ count1399 b) else (if i < 1406 then decide (7 ≤ count1399 b) else decide (8 ≤ count1399 b))) else (if i < 1408 then decide (9 ≤ count1399 b) else (if i < 1409 then decide (10 ≤ count1399 b) else decide (11 ≤ count1399 b))))) else (if i < 1416 then (if i < 1413 then (if i < 1411 then decide (12 ≤ count1399 b) else (if i < 1412 then decide (1 ≤ count1411 b) else decide (2 ≤ count1411 b))) else (if i < 1414 then decide (3 ≤ count1411 b) else (if i < 1415 then decide (4 ≤ count1411 b) else decide (5 ≤ count1411 b)))) else (if i < 1419 then (if i < 1417 then decide (6 ≤ count1411 b) else (if i < 1418 then decide (7 ≤ count1411 b) else decide (8 ≤ count1411 b))) else (if i < 1420 then decide (9 ≤ count1411 b) else (if i < 1421 then decide (10 ≤ count1411 b) else decide (11 ≤ count1411 b)))))) else (if i < 1434 then (if i < 1428 then (if i < 1425 then (if i < 1423 then decide (12 ≤ count1411 b) else (if i < 1424 then decide (1 ≤ count1423 b) else decide (2 ≤ count1423 b))) else (if i < 1426 then decide (1 ≤ count1425 b) else (if i < 1427 then decide (2 ≤ count1425 b) else decide (3 ≤ count1425 b)))) else (if i < 1431 then (if i < 1429 then decide (1 ≤ count1428 b) else (if i < 1430 then decide (2 ≤ count1428 b) else decide (1 ≤ count1430 b))) else (if i < 1432 then decide (2 ≤ count1430 b) else (if i < 1433 then decide (3 ≤ count1430 b) else decide (1 ≤ count1433 b))))) else (if i < 1440 then (if i < 1437 then (if i < 1435 then decide (2 ≤ count1433 b) else (if i < 1436 then decide (3 ≤ count1433 b) else decide (4 ≤ count1433 b))) else (if i < 1438 then decide (5 ≤ count1433 b) else (if i < 1439 then decide (6 ≤ count1433 b) else decide (1 ≤ count1439 b)))) else (if i < 1443 then (if i < 1441 then decide (2 ≤ count1439 b) else (if i < 1442 then decide (1 ≤ count1441 b) else decide (2 ≤ count1441 b))) else (if i < 1444 then decide (3 ≤ count1441 b) else (if i < 1445 then decide (1 ≤ count1444 b) else decide (2 ≤ count1444 b)))))))) else (if i < 1494 then (if i < 1470 then (if i < 1458 then (if i < 1452 then (if i < 1449 then (if i < 1447 then decide (1 ≤ count1446 b) else (if i < 1448 then decide (2 ≤ count1446 b) else decide (1 ≤ count1448 b))) else (if i < 1450 then decide (2 ≤ count1448 b) else (if i < 1451 then decide (3 ≤ count1448 b) else decide (4 ≤ count1448 b)))) else (if i < 1455 then (if i < 1453 then decide (1 ≤ count1452 b) else (if i < 1454 then decide (2 ≤ count1452 b) else decide (3 ≤ count1452 b))) else (if i < 1456 then decide (4 ≤ count1452 b) else (if i < 1457 then decide (5 ≤ count1452 b) else decide (6 ≤ count1452 b))))) else (if i < 1464 then (if i < 1461 then (if i < 1459 then decide (7 ≤ count1452 b) else (if i < 1460 then decide (1 ≤ count1459 b) else decide (2 ≤ count1459 b))) else (if i < 1462 then decide (3 ≤ count1459 b) else (if i < 1463 then decide (4 ≤ count1459 b) else decide (5 ≤ count1459 b)))) else (if i < 1467 then (if i < 1465 then decide (6 ≤ count1459 b) else (if i < 1466 then decide (7 ≤ count1459 b) else decide (8 ≤ count1459 b))) else (if i < 1468 then decide (9 ≤ count1459 b) else (if i < 1469 then decide (10 ≤ count1459 b) else decide (11 ≤ count1459 b)))))) else (if i < 1482 then (if i < 1476 then (if i < 1473 then (if i < 1471 then decide (12 ≤ count1459 b) else (if i < 1472 then decide (1 ≤ count1471 b) else decide (2 ≤ count1471 b))) else (if i < 1474 then decide (1 ≤ count1473 b) else (if i < 1475 then decide (2 ≤ count1473 b) else decide (3 ≤ count1473 b)))) else (if i < 1479 then (if i < 1477 then decide (1 ≤ count1476 b) else (if i < 1478 then decide (2 ≤ count1476 b) else decide (1 ≤ count1478 b))) else (if i < 1480 then decide (2 ≤ count1478 b) else (if i < 1481 then decide (3 ≤ count1478 b) else decide (1 ≤ count1481 b))))) else (if i < 1488 then (if i < 1485 then (if i < 1483 then decide (2 ≤ count1481 b) else (if i < 1484 then decide (3 ≤ count1481 b) else decide (4 ≤ count1481 b))) else (if i < 1486 then decide (5 ≤ count1481 b) else (if i < 1487 then decide (6 ≤ count1481 b) else decide (1 ≤ count1487 b)))) else (if i < 1491 then (if i < 1489 then decide (2 ≤ count1487 b) else (if i < 1490 then decide (1 ≤ count1489 b) else decide (2 ≤ count1489 b))) else (if i < 1492 then decide (3 ≤ count1489 b) else (if i < 1493 then decide (1 ≤ count1492 b) else decide (2 ≤ count1492 b))))))) else (if i < 1518 then (if i < 1506 then (if i < 1500 then (if i < 1497 then (if i < 1495 then decide (1 ≤ count1494 b) else (if i < 1496 then decide (2 ≤ count1494 b) else decide (1 ≤ count1496 b))) else (if i < 1498 then decide (2 ≤ count1496 b) else (if i < 1499 then decide (3 ≤ count1496 b) else decide (4 ≤ count1496 b)))) else (if i < 1503 then (if i < 1501 then decide (1 ≤ count1500 b) else (if i < 1502 then decide (2 ≤ count1500 b) else decide (3 ≤ count1500 b))) else (if i < 1504 then decide (4 ≤ count1500 b) else (if i < 1505 then decide (5 ≤ count1500 b) else decide (6 ≤ count1500 b))))) else (if i < 1512 then (if i < 1509 then (if i < 1507 then decide (7 ≤ count1500 b) else (if i < 1508 then decide (1 ≤ count1507 b) else decide (2 ≤ count1507 b))) else (if i < 1510 then decide (3 ≤ count1507 b) else (if i < 1511 then decide (4 ≤ count1507 b) else decide (5 ≤ count1507 b)))) else (if i < 1515 then (if i < 1513 then decide (6 ≤ count1507 b) else (if i < 1514 then decide (7 ≤ count1507 b) else decide (8 ≤ count1507 b))) else (if i < 1516 then decide (9 ≤ count1507 b) else (if i < 1517 then decide (10 ≤ count1507 b) else decide (11 ≤ count1507 b)))))) else (if i < 1530 then (if i < 1524 then (if i < 1521 then (if i < 1519 then decide (12 ≤ count1507 b) else (if i < 1520 then decide (1 ≤ count1519 b) else decide (2 ≤ count1519 b))) else (if i < 1522 then decide (3 ≤ count1519 b) else (if i < 1523 then decide (4 ≤ count1519 b) else decide (5 ≤ count1519 b)))) else (if i < 1527 then (if i < 1525 then decide (6 ≤ count1519 b) else (if i < 1526 then decide (7 ≤ count1519 b) else decide (8 ≤ count1519 b))) else (if i < 1528 then decide (9 ≤ count1519 b) else (if i < 1529 then decide (10 ≤ count1519 b) else decide (11 ≤ count1519 b))))) else (if i < 1536 then (if i < 1533 then (if i < 1531 then decide (12 ≤ count1519 b) else (if i < 1532 then decide (1 ≤ count1531 b) else decide (2 ≤ count1531 b))) else (if i < 1534 then decide (3 ≤ count1531 b) else (if i < 1535 then decide (4 ≤ count1531 b) else decide (5 ≤ count1531 b)))) else (if i < 1539 then (if i < 1537 then decide (6 ≤ count1531 b) else (if i < 1538 then decide (7 ≤ count1531 b) else decide (8 ≤ count1531 b))) else (if i < 1541 then (if i < 1540 then decide (9 ≤ count1531 b) else decide (10 ≤ count1531 b)) else (if i < 1542 then decide (11 ≤ count1531 b) else decide (12 ≤ count1531 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (11 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (13 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (15 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (17 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (18 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (19 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (22 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (28 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (29 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (30 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (160 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (161 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (162 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (163 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (165 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (166 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (171 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (173 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (175 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (176 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (177 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (178 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (179 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (182 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (184 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (188 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (189 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (190 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (191 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (226 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (228 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (229 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (230 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (235 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (244 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (245 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (247 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (249 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (250 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (251 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (255 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (259 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (261 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (267 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (272 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (276 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (277 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (279 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (281 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (283 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (287 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (288 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (291 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (304 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (305 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (307 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (355 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (356 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (357 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (362 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (363 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (364 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (368 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (372 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (373 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (375 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (376 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (377 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (379 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (383 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (418 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (419 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (420 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (421 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (426 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (427 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (428 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (430 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (432 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (436 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (437 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (439 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (440 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (441 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (442 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (443 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (447 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (481 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (487 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (491 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (493 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (495 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (496 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (498 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (499 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (500 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (502 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (506 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (508 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (510 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (30 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (163 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (165 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (166 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (176 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (178 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (184 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (190 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (191 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (226 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (228 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (235 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (250 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (291 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (304 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (307 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (354 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (356 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (362 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (363 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (364 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (366 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (372 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (373 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (375 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (377 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (379 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (383 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (418 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (420 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (437 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (441 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (442 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (496 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (500 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (510 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (2 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (2 ≤ count221 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (2 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (2 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (2 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (2 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (2 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value292 (q : Snake 81) : valuation q 292 = decide (2 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
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
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value322 (q : Snake 81) : valuation q 322 = decide (2 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value324 (q : Snake 81) : valuation q 324 = decide (2 ≤ count323 (baseVal q)) := rfl
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
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
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
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value430 (q : Snake 81) : valuation q 430 = decide (2 ≤ count429 (baseVal q)) := rfl
theorem value432 (q : Snake 81) : valuation q 432 = decide (2 ≤ count431 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (1 ≤ count1315 (baseVal q)) := rfl
theorem value1316 (q : Snake 81) : valuation q 1316 = decide (2 ≤ count1315 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (1 ≤ count1317 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (2 ≤ count1317 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (3 ≤ count1317 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (1 ≤ count1320 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (2 ≤ count1320 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (1 ≤ count1322 (baseVal q)) := rfl
theorem value1324 (q : Snake 81) : valuation q 1324 = decide (3 ≤ count1322 (baseVal q)) := rfl
theorem value1325 (q : Snake 81) : valuation q 1325 = decide (1 ≤ count1325 (baseVal q)) := rfl
theorem value1326 (q : Snake 81) : valuation q 1326 = decide (2 ≤ count1325 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (4 ≤ count1325 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (6 ≤ count1325 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (1 ≤ count1331 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (2 ≤ count1331 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (1 ≤ count1333 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (2 ≤ count1333 (baseVal q)) := rfl
theorem value1336 (q : Snake 81) : valuation q 1336 = decide (1 ≤ count1336 (baseVal q)) := rfl
theorem value1337 (q : Snake 81) : valuation q 1337 = decide (2 ≤ count1336 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (1 ≤ count1338 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (2 ≤ count1338 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (1 ≤ count1340 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (2 ≤ count1340 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (3 ≤ count1340 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (1 ≤ count1344 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (2 ≤ count1344 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (3 ≤ count1344 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (1 ≤ count1351 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (2 ≤ count1351 (baseVal q)) := rfl
theorem value1353 (q : Snake 81) : valuation q 1353 = decide (3 ≤ count1351 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (5 ≤ count1351 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (7 ≤ count1351 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (1 ≤ count1363 (baseVal q)) := rfl
theorem value1364 (q : Snake 81) : valuation q 1364 = decide (2 ≤ count1363 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (1 ≤ count1365 (baseVal q)) := rfl
theorem value1366 (q : Snake 81) : valuation q 1366 = decide (2 ≤ count1365 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (3 ≤ count1365 (baseVal q)) := rfl
theorem value1368 (q : Snake 81) : valuation q 1368 = decide (1 ≤ count1368 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (2 ≤ count1368 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (1 ≤ count1370 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (2 ≤ count1370 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (1 ≤ count1373 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (2 ≤ count1373 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (3 ≤ count1373 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (1 ≤ count1379 (baseVal q)) := rfl
theorem value1380 (q : Snake 81) : valuation q 1380 = decide (2 ≤ count1379 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (1 ≤ count1381 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (2 ≤ count1381 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (3 ≤ count1381 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (1 ≤ count1384 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (2 ≤ count1384 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (1 ≤ count1386 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (2 ≤ count1386 (baseVal q)) := rfl
theorem value1388 (q : Snake 81) : valuation q 1388 = decide (1 ≤ count1388 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (2 ≤ count1388 (baseVal q)) := rfl
theorem value1390 (q : Snake 81) : valuation q 1390 = decide (3 ≤ count1388 (baseVal q)) := rfl
theorem value1391 (q : Snake 81) : valuation q 1391 = decide (4 ≤ count1388 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (1 ≤ count1392 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (2 ≤ count1392 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (3 ≤ count1392 (baseVal q)) := rfl
theorem value1395 (q : Snake 81) : valuation q 1395 = decide (4 ≤ count1392 (baseVal q)) := rfl
theorem value1396 (q : Snake 81) : valuation q 1396 = decide (5 ≤ count1392 (baseVal q)) := rfl
theorem value1397 (q : Snake 81) : valuation q 1397 = decide (6 ≤ count1392 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (2 ≤ count1399 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (3 ≤ count1399 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (4 ≤ count1399 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (5 ≤ count1399 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (6 ≤ count1399 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (7 ≤ count1399 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (4 ≤ count1411 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (5 ≤ count1411 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (6 ≤ count1411 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (7 ≤ count1411 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (8 ≤ count1411 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (9 ≤ count1411 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (1 ≤ count1423 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (2 ≤ count1423 (baseVal q)) := rfl
theorem value1425 (q : Snake 81) : valuation q 1425 = decide (1 ≤ count1425 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (2 ≤ count1425 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (1 ≤ count1428 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (1 ≤ count1430 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (2 ≤ count1430 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (1 ≤ count1433 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (2 ≤ count1433 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (1 ≤ count1439 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (1 ≤ count1441 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (1 ≤ count1444 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (2 ≤ count1444 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (1 ≤ count1446 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (2 ≤ count1446 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (1 ≤ count1448 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (2 ≤ count1448 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (3 ≤ count1448 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (1 ≤ count1452 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (2 ≤ count1452 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (3 ≤ count1452 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (2 ≤ count1459 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (3 ≤ count1459 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (4 ≤ count1459 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (1 ≤ count1471 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (2 ≤ count1471 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (1 ≤ count1473 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (2 ≤ count1473 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (3 ≤ count1473 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (1 ≤ count1476 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (2 ≤ count1476 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (1 ≤ count1478 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (2 ≤ count1478 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (3 ≤ count1478 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (1 ≤ count1481 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (2 ≤ count1481 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (3 ≤ count1481 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (4 ≤ count1481 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (1 ≤ count1487 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (2 ≤ count1487 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (1 ≤ count1489 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (2 ≤ count1489 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (1 ≤ count1492 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (1 ≤ count1494 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (1 ≤ count1496 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (2 ≤ count1496 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (1 ≤ count1500 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (2 ≤ count1500 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (3 ≤ count1500 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (1 ≤ count1507 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (2 ≤ count1507 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (3 ≤ count1507 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (4 ≤ count1507 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (5 ≤ count1507 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (3 ≤ count1519 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (4 ≤ count1519 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (5 ≤ count1519 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (6 ≤ count1519 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (7 ≤ count1519 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (8 ≤ count1519 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (12 ≤ count1531 (baseVal q)) := rfl
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
theorem meaningNeg77 (b : Nat → Bool) : literal (valuationOf b) (-77) = decide (1 ≤ countLit b [-77]) := by
  change literal b (-77) = decide (1 ≤ countLit b [-77])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-77) <;> decide
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
theorem meaningNeg61 (b : Nat → Bool) : literal (valuationOf b) (-61) = decide (1 ≤ countLit b [-61]) := by
  change literal b (-61) = decide (1 ≤ countLit b [-61])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-61) <;> decide
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
theorem meaningNeg31 (b : Nat → Bool) : literal (valuationOf b) (-31) = decide (1 ≤ countLit b [-31]) := by
  change literal b (-31) = decide (1 ≤ countLit b [-31])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-31) <;> decide
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
theorem meaningNeg22 (b : Nat → Bool) : literal (valuationOf b) (-22) = decide (1 ≤ countLit b [-22]) := by
  change literal b (-22) = decide (1 ≤ countLit b [-22])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-22) <;> decide
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
theorem meaning111 (b : Nat → Bool) : literal (valuationOf b) (111) = decide (1 ≤ countLit b [111]) := by
  change literal b (111) = decide (1 ≤ countLit b [111])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (111) <;> decide
theorem meaning112 (b : Nat → Bool) : literal (valuationOf b) (112) = decide (1 ≤ countLit b [112]) := by
  change literal b (112) = decide (1 ≤ countLit b [112])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (112) <;> decide
theorem meaning113 (b : Nat → Bool) : literal (valuationOf b) (113) = decide (1 ≤ countLit b [113]) := by
  change literal b (113) = decide (1 ≤ countLit b [113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (113) <;> decide
theorem meaning117 (b : Nat → Bool) : literal (valuationOf b) (117) = decide (1 ≤ countLit b [117]) := by
  change literal b (117) = decide (1 ≤ countLit b [117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (117) <;> decide
theorem meaning118 (b : Nat → Bool) : literal (valuationOf b) (118) = decide (1 ≤ countLit b [118]) := by
  change literal b (118) = decide (1 ≤ countLit b [118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (118) <;> decide
theorem meaning119 (b : Nat → Bool) : literal (valuationOf b) (119) = decide (1 ≤ countLit b [119]) := by
  change literal b (119) = decide (1 ≤ countLit b [119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (119) <;> decide
theorem meaning123 (b : Nat → Bool) : literal (valuationOf b) (123) = decide (1 ≤ countLit b [123]) := by
  change literal b (123) = decide (1 ≤ countLit b [123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (123) <;> decide
theorem meaning124 (b : Nat → Bool) : literal (valuationOf b) (124) = decide (1 ≤ countLit b [124]) := by
  change literal b (124) = decide (1 ≤ countLit b [124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (124) <;> decide
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
theorem meaning131 (b : Nat → Bool) : literal (valuationOf b) (131) = decide (1 ≤ countLit b [131]) := by
  change literal b (131) = decide (1 ≤ countLit b [131])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (131) <;> decide
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
theorem meaning149 (b : Nat → Bool) : literal (valuationOf b) (149) = decide (1 ≤ countLit b [149]) := by
  change literal b (149) = decide (1 ≤ countLit b [149])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (149) <;> decide
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
theorem meaning194 (b : Nat → Bool) : literal (valuationOf b) (194) = decide (1 ≤ countLit b [194]) := by
  change literal b (194) = decide (1 ≤ countLit b [194])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (194) <;> decide
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
theorem meaning212 (b : Nat → Bool) : literal (valuationOf b) (212) = decide (1 ≤ countLit b [212]) := by
  change literal b (212) = decide (1 ≤ countLit b [212])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (212) <;> decide
theorem meaning214 (b : Nat → Bool) : literal (valuationOf b) (214) = decide (1 ≤ countLit b [214]) := by
  change literal b (214) = decide (1 ≤ countLit b [214])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (214) <;> decide
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
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning220 (b : Nat → Bool) : literal (valuationOf b) 220 = decide (2 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) 222 = decide (2 ≤ count221 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) 228 = decide (2 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) 230 = decide (2 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) 232 = decide (2 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) 240 = decide (2 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) 242 = decide (2 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning292 (b : Nat → Bool) : literal (valuationOf b) 292 = decide (2 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
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
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning322 (b : Nat → Bool) : literal (valuationOf b) 322 = decide (2 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning324 (b : Nat → Bool) : literal (valuationOf b) 324 = decide (2 ≤ count323 b) := rfl
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
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
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
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning430 (b : Nat → Bool) : literal (valuationOf b) 430 = decide (2 ≤ count429 b) := rfl
theorem meaning432 (b : Nat → Bool) : literal (valuationOf b) 432 = decide (2 ≤ count431 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (1 ≤ count1315 b) := rfl
theorem meaning1316 (b : Nat → Bool) : literal (valuationOf b) 1316 = decide (2 ≤ count1315 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (1 ≤ count1317 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (2 ≤ count1317 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (3 ≤ count1317 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (1 ≤ count1320 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (2 ≤ count1320 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (1 ≤ count1322 b) := rfl
theorem meaning1324 (b : Nat → Bool) : literal (valuationOf b) 1324 = decide (3 ≤ count1322 b) := rfl
theorem meaning1325 (b : Nat → Bool) : literal (valuationOf b) 1325 = decide (1 ≤ count1325 b) := rfl
theorem meaning1326 (b : Nat → Bool) : literal (valuationOf b) 1326 = decide (2 ≤ count1325 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (4 ≤ count1325 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (6 ≤ count1325 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (1 ≤ count1331 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (2 ≤ count1331 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (1 ≤ count1333 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (2 ≤ count1333 b) := rfl
theorem meaning1336 (b : Nat → Bool) : literal (valuationOf b) 1336 = decide (1 ≤ count1336 b) := rfl
theorem meaning1337 (b : Nat → Bool) : literal (valuationOf b) 1337 = decide (2 ≤ count1336 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (1 ≤ count1338 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (2 ≤ count1338 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (1 ≤ count1340 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (2 ≤ count1340 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (3 ≤ count1340 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (1 ≤ count1344 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (2 ≤ count1344 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (3 ≤ count1344 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (1 ≤ count1351 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (2 ≤ count1351 b) := rfl
theorem meaning1353 (b : Nat → Bool) : literal (valuationOf b) 1353 = decide (3 ≤ count1351 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (5 ≤ count1351 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (7 ≤ count1351 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (1 ≤ count1363 b) := rfl
theorem meaning1364 (b : Nat → Bool) : literal (valuationOf b) 1364 = decide (2 ≤ count1363 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (1 ≤ count1365 b) := rfl
theorem meaning1366 (b : Nat → Bool) : literal (valuationOf b) 1366 = decide (2 ≤ count1365 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (3 ≤ count1365 b) := rfl
theorem meaning1368 (b : Nat → Bool) : literal (valuationOf b) 1368 = decide (1 ≤ count1368 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (2 ≤ count1368 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (1 ≤ count1370 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (2 ≤ count1370 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (1 ≤ count1373 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (2 ≤ count1373 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (3 ≤ count1373 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (1 ≤ count1379 b) := rfl
theorem meaning1380 (b : Nat → Bool) : literal (valuationOf b) 1380 = decide (2 ≤ count1379 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (1 ≤ count1381 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (2 ≤ count1381 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (3 ≤ count1381 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (1 ≤ count1384 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (2 ≤ count1384 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (1 ≤ count1386 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (2 ≤ count1386 b) := rfl
theorem meaning1388 (b : Nat → Bool) : literal (valuationOf b) 1388 = decide (1 ≤ count1388 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (2 ≤ count1388 b) := rfl
theorem meaning1390 (b : Nat → Bool) : literal (valuationOf b) 1390 = decide (3 ≤ count1388 b) := rfl
theorem meaning1391 (b : Nat → Bool) : literal (valuationOf b) 1391 = decide (4 ≤ count1388 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (1 ≤ count1392 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (2 ≤ count1392 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (3 ≤ count1392 b) := rfl
theorem meaning1395 (b : Nat → Bool) : literal (valuationOf b) 1395 = decide (4 ≤ count1392 b) := rfl
theorem meaning1396 (b : Nat → Bool) : literal (valuationOf b) 1396 = decide (5 ≤ count1392 b) := rfl
theorem meaning1397 (b : Nat → Bool) : literal (valuationOf b) 1397 = decide (6 ≤ count1392 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (2 ≤ count1399 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (3 ≤ count1399 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (4 ≤ count1399 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (5 ≤ count1399 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (6 ≤ count1399 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (7 ≤ count1399 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (4 ≤ count1411 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (5 ≤ count1411 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (6 ≤ count1411 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (7 ≤ count1411 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (8 ≤ count1411 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (9 ≤ count1411 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (1 ≤ count1423 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (2 ≤ count1423 b) := rfl
theorem meaning1425 (b : Nat → Bool) : literal (valuationOf b) 1425 = decide (1 ≤ count1425 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (2 ≤ count1425 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (1 ≤ count1428 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (1 ≤ count1430 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (2 ≤ count1430 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (1 ≤ count1433 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (2 ≤ count1433 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (1 ≤ count1439 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (1 ≤ count1441 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (1 ≤ count1444 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (2 ≤ count1444 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (1 ≤ count1446 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (2 ≤ count1446 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (1 ≤ count1448 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (2 ≤ count1448 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (3 ≤ count1448 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (1 ≤ count1452 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (2 ≤ count1452 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (3 ≤ count1452 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (2 ≤ count1459 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (3 ≤ count1459 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (4 ≤ count1459 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (1 ≤ count1471 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (2 ≤ count1471 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (1 ≤ count1473 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (2 ≤ count1473 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (3 ≤ count1473 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (1 ≤ count1476 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (2 ≤ count1476 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (1 ≤ count1478 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (2 ≤ count1478 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (3 ≤ count1478 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (1 ≤ count1481 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (2 ≤ count1481 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (3 ≤ count1481 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (4 ≤ count1481 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (1 ≤ count1487 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (2 ≤ count1487 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (1 ≤ count1489 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (2 ≤ count1489 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (1 ≤ count1492 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (1 ≤ count1494 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (1 ≤ count1496 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (2 ≤ count1496 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (1 ≤ count1500 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (2 ≤ count1500 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (3 ≤ count1500 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (1 ≤ count1507 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (2 ≤ count1507 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (3 ≤ count1507 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (4 ≤ count1507 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (5 ≤ count1507 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (3 ≤ count1519 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (4 ≤ count1519 b) := rfl
theorem meaning1523 (b : Nat → Bool) : literal (valuationOf b) 1523 = decide (5 ≤ count1519 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (6 ≤ count1519 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (7 ≤ count1519 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (8 ≤ count1519 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (12 ≤ count1531 b) := rfl
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
end Snake9.Regrowth.E112201
