import E112234Data
namespace Snake9.Regrowth.E112234
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 102 then (if i < 51 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (11 : Vertex)) else decide (InPath q (13 : Vertex)))) else (if i < 4 then decide (InPath q (15 : Vertex)) else (if i < 5 then decide (InPath q (24 : Vertex)) else decide (InPath q (28 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (29 : Vertex)) else (if i < 8 then decide (InPath q (99 : Vertex)) else decide (InPath q (160 : Vertex)))) else (if i < 10 then decide (InPath q (161 : Vertex)) else (if i < 11 then decide (InPath q (162 : Vertex)) else decide (InPath q (163 : Vertex)))))) else (if i < 18 then (if i < 15 then (if i < 13 then decide (InPath q (165 : Vertex)) else (if i < 14 then decide (InPath q (171 : Vertex)) else decide (InPath q (173 : Vertex)))) else (if i < 16 then decide (InPath q (175 : Vertex)) else (if i < 17 then decide (InPath q (176 : Vertex)) else decide (InPath q (177 : Vertex))))) else (if i < 21 then (if i < 19 then decide (InPath q (178 : Vertex)) else (if i < 20 then decide (InPath q (179 : Vertex)) else decide (InPath q (182 : Vertex)))) else (if i < 23 then (if i < 22 then decide (InPath q (184 : Vertex)) else decide (InPath q (188 : Vertex))) else (if i < 24 then decide (InPath q (189 : Vertex)) else decide (InPath q (190 : Vertex))))))) else (if i < 38 then (if i < 31 then (if i < 28 then (if i < 26 then decide (InPath q (191 : Vertex)) else (if i < 27 then decide (InPath q (226 : Vertex)) else decide (InPath q (227 : Vertex)))) else (if i < 29 then decide (InPath q (228 : Vertex)) else (if i < 30 then decide (InPath q (229 : Vertex)) else decide (InPath q (234 : Vertex))))) else (if i < 34 then (if i < 32 then decide (InPath q (235 : Vertex)) else (if i < 33 then decide (InPath q (236 : Vertex)) else decide (InPath q (238 : Vertex)))) else (if i < 36 then (if i < 35 then decide (InPath q (244 : Vertex)) else decide (InPath q (245 : Vertex))) else (if i < 37 then decide (InPath q (247 : Vertex)) else decide (InPath q (248 : Vertex)))))) else (if i < 44 then (if i < 41 then (if i < 39 then decide (InPath q (249 : Vertex)) else (if i < 40 then decide (InPath q (251 : Vertex)) else decide (InPath q (255 : Vertex)))) else (if i < 42 then decide (InPath q (258 : Vertex)) else (if i < 43 then decide (InPath q (259 : Vertex)) else decide (InPath q (260 : Vertex))))) else (if i < 47 then (if i < 45 then decide (InPath q (261 : Vertex)) else (if i < 46 then decide (InPath q (266 : Vertex)) else decide (InPath q (267 : Vertex)))) else (if i < 49 then (if i < 48 then decide (InPath q (268 : Vertex)) else decide (InPath q (270 : Vertex))) else (if i < 50 then decide (InPath q (272 : Vertex)) else decide (InPath q (276 : Vertex)))))))) else (if i < 76 then (if i < 63 then (if i < 57 then (if i < 54 then (if i < 52 then decide (InPath q (277 : Vertex)) else (if i < 53 then decide (InPath q (279 : Vertex)) else decide (InPath q (280 : Vertex)))) else (if i < 55 then decide (InPath q (281 : Vertex)) else (if i < 56 then decide (InPath q (283 : Vertex)) else decide (InPath q (287 : Vertex))))) else (if i < 60 then (if i < 58 then decide (InPath q (354 : Vertex)) else (if i < 59 then decide (InPath q (355 : Vertex)) else decide (InPath q (356 : Vertex)))) else (if i < 61 then decide (InPath q (357 : Vertex)) else (if i < 62 then decide (InPath q (362 : Vertex)) else decide (InPath q (363 : Vertex)))))) else (if i < 69 then (if i < 66 then (if i < 64 then decide (InPath q (364 : Vertex)) else (if i < 65 then decide (InPath q (366 : Vertex)) else decide (InPath q (372 : Vertex)))) else (if i < 67 then decide (InPath q (373 : Vertex)) else (if i < 68 then decide (InPath q (375 : Vertex)) else decide (InPath q (376 : Vertex))))) else (if i < 72 then (if i < 70 then decide (InPath q (377 : Vertex)) else (if i < 71 then decide (InPath q (379 : Vertex)) else decide (InPath q (383 : Vertex)))) else (if i < 74 then (if i < 73 then decide (InPath q (384 : Vertex)) else decide (InPath q (387 : Vertex))) else (if i < 75 then decide (InPath q (400 : Vertex)) else decide (InPath q (401 : Vertex))))))) else (if i < 89 then (if i < 82 then (if i < 79 then (if i < 77 then decide (InPath q (403 : Vertex)) else (if i < 78 then decide (InPath q (419 : Vertex)) else decide (InPath q (421 : Vertex)))) else (if i < 80 then decide (InPath q (427 : Vertex)) else (if i < 81 then decide (InPath q (432 : Vertex)) else decide (InPath q (436 : Vertex))))) else (if i < 85 then (if i < 83 then decide (InPath q (437 : Vertex)) else (if i < 84 then decide (InPath q (439 : Vertex)) else decide (InPath q (441 : Vertex)))) else (if i < 87 then (if i < 86 then decide (InPath q (443 : Vertex)) else decide (InPath q (447 : Vertex))) else (if i < 88 then decide (InPath q (450 : Vertex)) else decide (InPath q (451 : Vertex)))))) else (if i < 95 then (if i < 92 then (if i < 90 then decide (InPath q (452 : Vertex)) else (if i < 91 then decide (InPath q (453 : Vertex)) else decide (InPath q (458 : Vertex)))) else (if i < 93 then decide (InPath q (459 : Vertex)) else (if i < 94 then decide (InPath q (460 : Vertex)) else decide (InPath q (462 : Vertex))))) else (if i < 98 then (if i < 96 then decide (InPath q (464 : Vertex)) else (if i < 97 then decide (InPath q (468 : Vertex)) else decide (InPath q (469 : Vertex)))) else (if i < 100 then (if i < 99 then decide (InPath q (471 : Vertex)) else decide (InPath q (472 : Vertex))) else (if i < 101 then decide (InPath q (473 : Vertex)) else decide (InPath q (475 : Vertex))))))))) else (if i < 153 then (if i < 127 then (if i < 114 then (if i < 108 then (if i < 105 then (if i < 103 then decide (InPath q (479 : Vertex)) else (if i < 104 then decide (BallClauseLogic.Endpoint q (11 : Vertex)) else decide (BallClauseLogic.Endpoint q (13 : Vertex)))) else (if i < 106 then decide (BallClauseLogic.Endpoint q (15 : Vertex)) else (if i < 107 then decide (BallClauseLogic.Endpoint q (24 : Vertex)) else decide (BallClauseLogic.Endpoint q (28 : Vertex))))) else (if i < 111 then (if i < 109 then decide (BallClauseLogic.Endpoint q (29 : Vertex)) else (if i < 110 then decide (BallClauseLogic.Endpoint q (99 : Vertex)) else decide (BallClauseLogic.Endpoint q (160 : Vertex)))) else (if i < 112 then decide (BallClauseLogic.Endpoint q (161 : Vertex)) else (if i < 113 then decide (BallClauseLogic.Endpoint q (162 : Vertex)) else decide (BallClauseLogic.Endpoint q (163 : Vertex)))))) else (if i < 120 then (if i < 117 then (if i < 115 then decide (BallClauseLogic.Endpoint q (165 : Vertex)) else (if i < 116 then decide (BallClauseLogic.Endpoint q (171 : Vertex)) else decide (BallClauseLogic.Endpoint q (173 : Vertex)))) else (if i < 118 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else (if i < 119 then decide (BallClauseLogic.Endpoint q (176 : Vertex)) else decide (BallClauseLogic.Endpoint q (177 : Vertex))))) else (if i < 123 then (if i < 121 then decide (BallClauseLogic.Endpoint q (178 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex)))) else (if i < 125 then (if i < 124 then decide (BallClauseLogic.Endpoint q (184 : Vertex)) else decide (BallClauseLogic.Endpoint q (188 : Vertex))) else (if i < 126 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (190 : Vertex))))))) else (if i < 140 then (if i < 133 then (if i < 130 then (if i < 128 then decide (BallClauseLogic.Endpoint q (191 : Vertex)) else (if i < 129 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else decide (BallClauseLogic.Endpoint q (227 : Vertex)))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (228 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (234 : Vertex))))) else (if i < 136 then (if i < 134 then decide (BallClauseLogic.Endpoint q (235 : Vertex)) else (if i < 135 then decide (BallClauseLogic.Endpoint q (236 : Vertex)) else decide (BallClauseLogic.Endpoint q (238 : Vertex)))) else (if i < 138 then (if i < 137 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (245 : Vertex))) else (if i < 139 then decide (BallClauseLogic.Endpoint q (247 : Vertex)) else decide (BallClauseLogic.Endpoint q (248 : Vertex)))))) else (if i < 146 then (if i < 143 then (if i < 141 then decide (BallClauseLogic.Endpoint q (249 : Vertex)) else (if i < 142 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex)))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (259 : Vertex)) else decide (BallClauseLogic.Endpoint q (260 : Vertex))))) else (if i < 149 then (if i < 147 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else (if i < 148 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex)))) else (if i < 151 then (if i < 150 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else decide (BallClauseLogic.Endpoint q (270 : Vertex))) else (if i < 152 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (276 : Vertex)))))))) else (if i < 179 then (if i < 166 then (if i < 159 then (if i < 156 then (if i < 154 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else (if i < 155 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else decide (BallClauseLogic.Endpoint q (280 : Vertex)))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex))))) else (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (354 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (355 : Vertex)) else decide (BallClauseLogic.Endpoint q (356 : Vertex)))) else (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else decide (BallClauseLogic.Endpoint q (362 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (363 : Vertex)) else decide (BallClauseLogic.Endpoint q (364 : Vertex)))))) else (if i < 172 then (if i < 169 then (if i < 167 then decide (BallClauseLogic.Endpoint q (366 : Vertex)) else (if i < 168 then decide (BallClauseLogic.Endpoint q (372 : Vertex)) else decide (BallClauseLogic.Endpoint q (373 : Vertex)))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (375 : Vertex)) else (if i < 171 then decide (BallClauseLogic.Endpoint q (376 : Vertex)) else decide (BallClauseLogic.Endpoint q (377 : Vertex))))) else (if i < 175 then (if i < 173 then decide (BallClauseLogic.Endpoint q (379 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (383 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex)))) else (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (387 : Vertex)) else decide (BallClauseLogic.Endpoint q (400 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else decide (BallClauseLogic.Endpoint q (403 : Vertex))))))) else (if i < 192 then (if i < 185 then (if i < 182 then (if i < 180 then decide (BallClauseLogic.Endpoint q (419 : Vertex)) else (if i < 181 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex)))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (437 : Vertex))))) else (if i < 188 then (if i < 186 then decide (BallClauseLogic.Endpoint q (439 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (441 : Vertex)) else decide (BallClauseLogic.Endpoint q (443 : Vertex)))) else (if i < 190 then (if i < 189 then decide (BallClauseLogic.Endpoint q (447 : Vertex)) else decide (BallClauseLogic.Endpoint q (450 : Vertex))) else (if i < 191 then decide (BallClauseLogic.Endpoint q (451 : Vertex)) else decide (BallClauseLogic.Endpoint q (452 : Vertex)))))) else (if i < 198 then (if i < 195 then (if i < 193 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else (if i < 194 then decide (BallClauseLogic.Endpoint q (458 : Vertex)) else decide (BallClauseLogic.Endpoint q (459 : Vertex)))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (460 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))))) else (if i < 201 then (if i < 199 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else (if i < 200 then decide (BallClauseLogic.Endpoint q (469 : Vertex)) else decide (BallClauseLogic.Endpoint q (471 : Vertex)))) else (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (472 : Vertex)) else decide (BallClauseLogic.Endpoint q (473 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (475 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count205 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count207 (b : Nat → Bool) : Nat := countLit b [104, 105, 106]
def count209 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count211 (b : Nat → Bool) : Nat := countLit b [107, 108, 109]
def count213 (b : Nat → Bool) : Nat := countLit b [104, 105, 106, 107, 108, 109]
def count215 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count217 (b : Nat → Bool) : Nat := countLit b [110, 111, 112]
def count219 (b : Nat → Bool) : Nat := countLit b [114, 115]
def count221 (b : Nat → Bool) : Nat := countLit b [113, 114, 115]
def count223 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115]
def count225 (b : Nat → Bool) : Nat := countLit b [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]
def count227 (b : Nat → Bool) : Nat := countLit b [117, 118]
def count229 (b : Nat → Bool) : Nat := countLit b [116, 117, 118]
def count231 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count233 (b : Nat → Bool) : Nat := countLit b [119, 120, 121]
def count235 (b : Nat → Bool) : Nat := countLit b [116, 117, 118, 119, 120, 121]
def count237 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count239 (b : Nat → Bool) : Nat := countLit b [122, 123, 124]
def count241 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count243 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count245 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128]
def count247 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128]
def count249 (b : Nat → Bool) : Nat := countLit b [116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
def count251 (b : Nat → Bool) : Nat := countLit b [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
def count253 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count255 (b : Nat → Bool) : Nat := countLit b [129, 130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count259 (b : Nat → Bool) : Nat := countLit b [132, 133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count265 (b : Nat → Bool) : Nat := countLit b [135, 136, 137]
def count267 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count269 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count271 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count277 (b : Nat → Bool) : Nat := countLit b [141, 142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145, 146]
def count283 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148, 149]
def count289 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count291 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count293 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153]
def count295 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150, 151, 152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153]
def count299 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153]
def count301 (b : Nat → Bool) : Nat := countLit b [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153]
def count303 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [154, 155, 156]
def count307 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count331 (b : Nat → Bool) : Nat := countLit b [169, 170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count337 (b : Nat → Bool) : Nat := countLit b [172, 173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count341 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count343 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]
def count351 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [179, 180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count357 (b : Nat → Bool) : Nat := countLit b [182, 183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count363 (b : Nat → Bool) : Nat := countLit b [185, 186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count367 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188, 189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count377 (b : Nat → Bool) : Nat := countLit b [192, 193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196, 197]
def count383 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count387 (b : Nat → Bool) : Nat := countLit b [198, 199, 200]
def count389 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count391 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count395 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count403 (b : Nat → Bool) : Nat := countLit b [104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count405 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count407 (b : Nat → Bool) : Nat := countLit b [3, 4, 6]
def count410 (b : Nat → Bool) : Nat := countLit b [8, 11]
def count412 (b : Nat → Bool) : Nat := countLit b [7, 8, 11]
def count415 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 8, 11]
def count421 (b : Nat → Bool) : Nat := countLit b [15, 17]
def count423 (b : Nat → Bool) : Nat := countLit b [12, 15, 17]
def count426 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count428 (b : Nat → Bool) : Nat := countLit b [18, 21, 23]
def count431 (b : Nat → Bool) : Nat := countLit b [12, 15, 17, 18, 21, 23]
def count437 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 8, 11, 12, 15, 17, 18, 21, 23]
def count449 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count451 (b : Nat → Bool) : Nat := countLit b [24, 26, 28]
def count454 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count456 (b : Nat → Bool) : Nat := countLit b [31, 33, 35]
def count459 (b : Nat → Bool) : Nat := countLit b [24, 26, 28, 31, 33, 35]
def count465 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count467 (b : Nat → Bool) : Nat := countLit b [38, 40, 41]
def count470 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count472 (b : Nat → Bool) : Nat := countLit b [48, 49]
def count474 (b : Nat → Bool) : Nat := countLit b [43, 46, 48, 49]
def count478 (b : Nat → Bool) : Nat := countLit b [38, 40, 41, 43, 46, 48, 49]
def count485 (b : Nat → Bool) : Nat := countLit b [24, 26, 28, 31, 33, 35, 38, 40, 41, 43, 46, 48, 49]
def count498 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 8, 11, 12, 15, 17, 18, 21, 23, 24, 26, 28, 31, 33, 35, 38, 40, 41, 43, 46, 48, 49]
def count523 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count525 (b : Nat → Bool) : Nat := countLit b [51, 54, 56]
def count528 (b : Nat → Bool) : Nat := countLit b [59, 62]
def count530 (b : Nat → Bool) : Nat := countLit b [57, 59, 62]
def count533 (b : Nat → Bool) : Nat := countLit b [51, 54, 56, 57, 59, 62]
def count539 (b : Nat → Bool) : Nat := countLit b [66, 69]
def count541 (b : Nat → Bool) : Nat := countLit b [64, 66, 69]
def count544 (b : Nat → Bool) : Nat := countLit b [71, 72]
def count546 (b : Nat → Bool) : Nat := countLit b [73, 75]
def count548 (b : Nat → Bool) : Nat := countLit b [71, 72, 73, 75]
def count552 (b : Nat → Bool) : Nat := countLit b [64, 66, 69, 71, 72, 73, 75]
def count559 (b : Nat → Bool) : Nat := countLit b [51, 54, 56, 57, 59, 62, 64, 66, 69, 71, 72, 73, 75]
def count572 (b : Nat → Bool) : Nat := countLit b [80, 82]
def count574 (b : Nat → Bool) : Nat := countLit b [79, 80, 82]
def count577 (b : Nat → Bool) : Nat := countLit b [86, 87]
def count579 (b : Nat → Bool) : Nat := countLit b [84, 86, 87]
def count582 (b : Nat → Bool) : Nat := countLit b [79, 80, 82, 84, 86, 87]
def count588 (b : Nat → Bool) : Nat := countLit b [92, 94]
def count590 (b : Nat → Bool) : Nat := countLit b [89, 92, 94]
def count593 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count595 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count597 (b : Nat → Bool) : Nat := countLit b [95, 97, 100, 102]
def count601 (b : Nat → Bool) : Nat := countLit b [89, 92, 94, 95, 97, 100, 102]
def count608 (b : Nat → Bool) : Nat := countLit b [79, 80, 82, 84, 86, 87, 89, 92, 94, 95, 97, 100, 102]
def count621 (b : Nat → Bool) : Nat := countLit b [51, 54, 56, 57, 59, 62, 64, 66, 69, 71, 72, 73, 75, 79, 80, 82, 84, 86, 87, 89, 92, 94, 95, 97, 100, 102]
def count647 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 8, 11, 12, 15, 17, 18, 21, 23, 24, 26, 28, 31, 33, 35, 38, 40, 41, 43, 46, 48, 49, 51, 54, 56, 57, 59, 62, 64, 66, 69, 71, 72, 73, 75, 79, 80, 82, 84, 86, 87, 89, 92, 94, 95, 97, 100, 102]
def count689 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count691 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6]
def count694 (b : Nat → Bool) : Nat := countLit b [-8, -11]
def count696 (b : Nat → Bool) : Nat := countLit b [-7, -8, -11]
def count699 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -8, -11]
def count705 (b : Nat → Bool) : Nat := countLit b [-15, -17]
def count707 (b : Nat → Bool) : Nat := countLit b [-12, -15, -17]
def count710 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count712 (b : Nat → Bool) : Nat := countLit b [-18, -21, -23]
def count715 (b : Nat → Bool) : Nat := countLit b [-12, -15, -17, -18, -21, -23]
def count721 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -8, -11, -12, -15, -17, -18, -21, -23]
def count732 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count734 (b : Nat → Bool) : Nat := countLit b [-24, -26, -28]
def count737 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count739 (b : Nat → Bool) : Nat := countLit b [-31, -33, -35]
def count742 (b : Nat → Bool) : Nat := countLit b [-24, -26, -28, -31, -33, -35]
def count748 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count750 (b : Nat → Bool) : Nat := countLit b [-38, -40, -41]
def count753 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count755 (b : Nat → Bool) : Nat := countLit b [-48, -49]
def count757 (b : Nat → Bool) : Nat := countLit b [-43, -46, -48, -49]
def count761 (b : Nat → Bool) : Nat := countLit b [-38, -40, -41, -43, -46, -48, -49]
def count768 (b : Nat → Bool) : Nat := countLit b [-24, -26, -28, -31, -33, -35, -38, -40, -41, -43, -46, -48, -49]
def count779 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -8, -11, -12, -15, -17, -18, -21, -23, -24, -26, -28, -31, -33, -35, -38, -40, -41, -43, -46, -48, -49]
def count790 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count792 (b : Nat → Bool) : Nat := countLit b [-51, -54, -56]
def count795 (b : Nat → Bool) : Nat := countLit b [-59, -62]
def count797 (b : Nat → Bool) : Nat := countLit b [-57, -59, -62]
def count800 (b : Nat → Bool) : Nat := countLit b [-51, -54, -56, -57, -59, -62]
def count806 (b : Nat → Bool) : Nat := countLit b [-66, -69]
def count808 (b : Nat → Bool) : Nat := countLit b [-64, -66, -69]
def count811 (b : Nat → Bool) : Nat := countLit b [-71, -72]
def count813 (b : Nat → Bool) : Nat := countLit b [-73, -75]
def count815 (b : Nat → Bool) : Nat := countLit b [-71, -72, -73, -75]
def count819 (b : Nat → Bool) : Nat := countLit b [-64, -66, -69, -71, -72, -73, -75]
def count826 (b : Nat → Bool) : Nat := countLit b [-51, -54, -56, -57, -59, -62, -64, -66, -69, -71, -72, -73, -75]
def count837 (b : Nat → Bool) : Nat := countLit b [-80, -82]
def count839 (b : Nat → Bool) : Nat := countLit b [-79, -80, -82]
def count842 (b : Nat → Bool) : Nat := countLit b [-86, -87]
def count844 (b : Nat → Bool) : Nat := countLit b [-84, -86, -87]
def count847 (b : Nat → Bool) : Nat := countLit b [-79, -80, -82, -84, -86, -87]
def count853 (b : Nat → Bool) : Nat := countLit b [-92, -94]
def count855 (b : Nat → Bool) : Nat := countLit b [-89, -92, -94]
def count858 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count860 (b : Nat → Bool) : Nat := countLit b [-100, -102]
def count862 (b : Nat → Bool) : Nat := countLit b [-95, -97, -100, -102]
def count866 (b : Nat → Bool) : Nat := countLit b [-89, -92, -94, -95, -97, -100, -102]
def count873 (b : Nat → Bool) : Nat := countLit b [-79, -80, -82, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102]
def count884 (b : Nat → Bool) : Nat := countLit b [-51, -54, -56, -57, -59, -62, -64, -66, -69, -71, -72, -73, -75, -79, -80, -82, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102]
def count895 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -8, -11, -12, -15, -17, -18, -21, -23, -24, -26, -28, -31, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54, -56, -57, -59, -62, -64, -66, -69, -71, -72, -73, -75, -79, -80, -82, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102]
def count906 (b : Nat → Bool) : Nat := countLit b [2, 5]
def count908 (b : Nat → Bool) : Nat := countLit b [1, 2, 5]
def count911 (b : Nat → Bool) : Nat := countLit b [10, 13]
def count913 (b : Nat → Bool) : Nat := countLit b [9, 10, 13]
def count916 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 9, 10, 13]
def count922 (b : Nat → Bool) : Nat := countLit b [16, 19]
def count924 (b : Nat → Bool) : Nat := countLit b [14, 16, 19]
def count927 (b : Nat → Bool) : Nat := countLit b [22, 25]
def count929 (b : Nat → Bool) : Nat := countLit b [20, 22, 25]
def count932 (b : Nat → Bool) : Nat := countLit b [14, 16, 19, 20, 22, 25]
def count938 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 9, 10, 13, 14, 16, 19, 20, 22, 25]
def count950 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count952 (b : Nat → Bool) : Nat := countLit b [27, 29, 30]
def count955 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count957 (b : Nat → Bool) : Nat := countLit b [32, 34, 36]
def count960 (b : Nat → Bool) : Nat := countLit b [27, 29, 30, 32, 34, 36]
def count966 (b : Nat → Bool) : Nat := countLit b [39, 42]
def count968 (b : Nat → Bool) : Nat := countLit b [37, 39, 42]
def count971 (b : Nat → Bool) : Nat := countLit b [44, 45]
def count973 (b : Nat → Bool) : Nat := countLit b [47, 50]
def count975 (b : Nat → Bool) : Nat := countLit b [44, 45, 47, 50]
def count979 (b : Nat → Bool) : Nat := countLit b [37, 39, 42, 44, 45, 47, 50]
def count986 (b : Nat → Bool) : Nat := countLit b [27, 29, 30, 32, 34, 36, 37, 39, 42, 44, 45, 47, 50]
def count999 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 9, 10, 13, 14, 16, 19, 20, 22, 25, 27, 29, 30, 32, 34, 36, 37, 39, 42, 44, 45, 47, 50]
def count1024 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count1026 (b : Nat → Bool) : Nat := countLit b [52, 53, 55]
def count1029 (b : Nat → Bool) : Nat := countLit b [60, 61]
def count1031 (b : Nat → Bool) : Nat := countLit b [58, 60, 61]
def count1034 (b : Nat → Bool) : Nat := countLit b [52, 53, 55, 58, 60, 61]
def count1040 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count1042 (b : Nat → Bool) : Nat := countLit b [63, 65, 67]
def count1045 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count1047 (b : Nat → Bool) : Nat := countLit b [74, 76]
def count1049 (b : Nat → Bool) : Nat := countLit b [68, 70, 74, 76]
def count1053 (b : Nat → Bool) : Nat := countLit b [63, 65, 67, 68, 70, 74, 76]
def count1060 (b : Nat → Bool) : Nat := countLit b [52, 53, 55, 58, 60, 61, 63, 65, 67, 68, 70, 74, 76]
def count1073 (b : Nat → Bool) : Nat := countLit b [78, 81]
def count1075 (b : Nat → Bool) : Nat := countLit b [77, 78, 81]
def count1078 (b : Nat → Bool) : Nat := countLit b [85, 88]
def count1080 (b : Nat → Bool) : Nat := countLit b [83, 85, 88]
def count1083 (b : Nat → Bool) : Nat := countLit b [77, 78, 81, 83, 85, 88]
def count1089 (b : Nat → Bool) : Nat := countLit b [91, 93]
def count1091 (b : Nat → Bool) : Nat := countLit b [90, 91, 93]
def count1094 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count1096 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count1098 (b : Nat → Bool) : Nat := countLit b [96, 98, 99, 101]
def count1102 (b : Nat → Bool) : Nat := countLit b [90, 91, 93, 96, 98, 99, 101]
def count1109 (b : Nat → Bool) : Nat := countLit b [77, 78, 81, 83, 85, 88, 90, 91, 93, 96, 98, 99, 101]
def count1122 (b : Nat → Bool) : Nat := countLit b [52, 53, 55, 58, 60, 61, 63, 65, 67, 68, 70, 74, 76, 77, 78, 81, 83, 85, 88, 90, 91, 93, 96, 98, 99, 101]
def count1148 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 9, 10, 13, 14, 16, 19, 20, 22, 25, 27, 29, 30, 32, 34, 36, 37, 39, 42, 44, 45, 47, 50, 52, 53, 55, 58, 60, 61, 63, 65, 67, 68, 70, 74, 76, 77, 78, 81, 83, 85, 88, 90, 91, 93, 96, 98, 99, 101]
def count1190 (b : Nat → Bool) : Nat := countLit b [-2, -5]
def count1192 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5]
def count1195 (b : Nat → Bool) : Nat := countLit b [-10, -13]
def count1197 (b : Nat → Bool) : Nat := countLit b [-9, -10, -13]
def count1200 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -9, -10, -13]
def count1206 (b : Nat → Bool) : Nat := countLit b [-16, -19]
def count1208 (b : Nat → Bool) : Nat := countLit b [-14, -16, -19]
def count1211 (b : Nat → Bool) : Nat := countLit b [-22, -25]
def count1213 (b : Nat → Bool) : Nat := countLit b [-20, -22, -25]
def count1216 (b : Nat → Bool) : Nat := countLit b [-14, -16, -19, -20, -22, -25]
def count1222 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25]
def count1233 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count1235 (b : Nat → Bool) : Nat := countLit b [-27, -29, -30]
def count1238 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count1240 (b : Nat → Bool) : Nat := countLit b [-32, -34, -36]
def count1243 (b : Nat → Bool) : Nat := countLit b [-27, -29, -30, -32, -34, -36]
def count1249 (b : Nat → Bool) : Nat := countLit b [-39, -42]
def count1251 (b : Nat → Bool) : Nat := countLit b [-37, -39, -42]
def count1254 (b : Nat → Bool) : Nat := countLit b [-44, -45]
def count1256 (b : Nat → Bool) : Nat := countLit b [-47, -50]
def count1258 (b : Nat → Bool) : Nat := countLit b [-44, -45, -47, -50]
def count1262 (b : Nat → Bool) : Nat := countLit b [-37, -39, -42, -44, -45, -47, -50]
def count1269 (b : Nat → Bool) : Nat := countLit b [-27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]
def count1280 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50]
def count1291 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count1293 (b : Nat → Bool) : Nat := countLit b [-52, -53, -55]
def count1296 (b : Nat → Bool) : Nat := countLit b [-60, -61]
def count1298 (b : Nat → Bool) : Nat := countLit b [-58, -60, -61]
def count1301 (b : Nat → Bool) : Nat := countLit b [-52, -53, -55, -58, -60, -61]
def count1307 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count1309 (b : Nat → Bool) : Nat := countLit b [-63, -65, -67]
def count1312 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count1314 (b : Nat → Bool) : Nat := countLit b [-74, -76]
def count1316 (b : Nat → Bool) : Nat := countLit b [-68, -70, -74, -76]
def count1320 (b : Nat → Bool) : Nat := countLit b [-63, -65, -67, -68, -70, -74, -76]
def count1327 (b : Nat → Bool) : Nat := countLit b [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76]
def count1338 (b : Nat → Bool) : Nat := countLit b [-78, -81]
def count1340 (b : Nat → Bool) : Nat := countLit b [-77, -78, -81]
def count1343 (b : Nat → Bool) : Nat := countLit b [-85, -88]
def count1345 (b : Nat → Bool) : Nat := countLit b [-83, -85, -88]
def count1348 (b : Nat → Bool) : Nat := countLit b [-77, -78, -81, -83, -85, -88]
def count1354 (b : Nat → Bool) : Nat := countLit b [-91, -93]
def count1356 (b : Nat → Bool) : Nat := countLit b [-90, -91, -93]
def count1359 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count1361 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count1363 (b : Nat → Bool) : Nat := countLit b [-96, -98, -99, -101]
def count1367 (b : Nat → Bool) : Nat := countLit b [-90, -91, -93, -96, -98, -99, -101]
def count1374 (b : Nat → Bool) : Nat := countLit b [-77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]
def count1385 (b : Nat → Bool) : Nat := countLit b [-52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]
def count1396 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -9, -10, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -34, -36, -37, -39, -42, -44, -45, -47, -50, -52, -53, -55, -58, -60, -61, -63, -65, -67, -68, -70, -74, -76, -77, -78, -81, -83, -85, -88, -90, -91, -93, -96, -98, -99, -101]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 703 then (if i < 351 then (if i < 175 then (if i < 87 then (if i < 43 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 7 then (if i < 6 then b 5 else b 6) else (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)))) else (if i < 15 then (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else (if i < 14 then b 13 else b 14))) else (if i < 18 then (if i < 16 then b 15 else (if i < 17 then b 16 else b 17)) else (if i < 19 then b 18 else (if i < 20 then b 19 else b 20))))) else (if i < 32 then (if i < 26 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else (if i < 25 then b 24 else b 25))) else (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)))) else (if i < 37 then (if i < 34 then (if i < 33 then b 32 else b 33) else (if i < 35 then b 34 else (if i < 36 then b 35 else b 36))) else (if i < 40 then (if i < 38 then b 37 else (if i < 39 then b 38 else b 39)) else (if i < 41 then b 40 else (if i < 42 then b 41 else b 42)))))) else (if i < 65 then (if i < 54 then (if i < 48 then (if i < 45 then (if i < 44 then b 43 else b 44) else (if i < 46 then b 45 else (if i < 47 then b 46 else b 47))) else (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 52 then b 51 else (if i < 53 then b 52 else b 53)))) else (if i < 59 then (if i < 56 then (if i < 55 then b 54 else b 55) else (if i < 57 then b 56 else (if i < 58 then b 57 else b 58))) else (if i < 62 then (if i < 60 then b 59 else (if i < 61 then b 60 else b 61)) else (if i < 63 then b 62 else (if i < 64 then b 63 else b 64))))) else (if i < 76 then (if i < 70 then (if i < 67 then (if i < 66 then b 65 else b 66) else (if i < 68 then b 67 else (if i < 69 then b 68 else b 69))) else (if i < 73 then (if i < 71 then b 70 else (if i < 72 then b 71 else b 72)) else (if i < 74 then b 73 else (if i < 75 then b 74 else b 75)))) else (if i < 81 then (if i < 78 then (if i < 77 then b 76 else b 77) else (if i < 79 then b 78 else (if i < 80 then b 79 else b 80))) else (if i < 84 then (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)) else (if i < 85 then b 84 else (if i < 86 then b 85 else b 86))))))) else (if i < 131 then (if i < 109 then (if i < 98 then (if i < 92 then (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else (if i < 91 then b 90 else b 91))) else (if i < 95 then (if i < 93 then b 92 else (if i < 94 then b 93 else b 94)) else (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)))) else (if i < 103 then (if i < 100 then (if i < 99 then b 98 else b 99) else (if i < 101 then b 100 else (if i < 102 then b 101 else b 102))) else (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 107 then b 106 else (if i < 108 then b 107 else b 108))))) else (if i < 120 then (if i < 114 then (if i < 111 then (if i < 110 then b 109 else b 110) else (if i < 112 then b 111 else (if i < 113 then b 112 else b 113))) else (if i < 117 then (if i < 115 then b 114 else (if i < 116 then b 115 else b 116)) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)))) else (if i < 125 then (if i < 122 then (if i < 121 then b 120 else b 121) else (if i < 123 then b 122 else (if i < 124 then b 123 else b 124))) else (if i < 128 then (if i < 126 then b 125 else (if i < 127 then b 126 else b 127)) else (if i < 129 then b 128 else (if i < 130 then b 129 else b 130)))))) else (if i < 153 then (if i < 142 then (if i < 136 then (if i < 133 then (if i < 132 then b 131 else b 132) else (if i < 134 then b 133 else (if i < 135 then b 134 else b 135))) else (if i < 139 then (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)) else (if i < 140 then b 139 else (if i < 141 then b 140 else b 141)))) else (if i < 147 then (if i < 144 then (if i < 143 then b 142 else b 143) else (if i < 145 then b 144 else (if i < 146 then b 145 else b 146))) else (if i < 150 then (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)) else (if i < 151 then b 150 else (if i < 152 then b 151 else b 152))))) else (if i < 164 then (if i < 158 then (if i < 155 then (if i < 154 then b 153 else b 154) else (if i < 156 then b 155 else (if i < 157 then b 156 else b 157))) else (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 162 then b 161 else (if i < 163 then b 162 else b 163)))) else (if i < 169 then (if i < 166 then (if i < 165 then b 164 else b 165) else (if i < 167 then b 166 else (if i < 168 then b 167 else b 168))) else (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174)))))))) else (if i < 263 then (if i < 219 then (if i < 197 then (if i < 186 then (if i < 180 then (if i < 177 then (if i < 176 then b 175 else b 176) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179))) else (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185)))) else (if i < 191 then (if i < 188 then (if i < 187 then b 186 else b 187) else (if i < 189 then b 188 else (if i < 190 then b 189 else b 190))) else (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 195 then b 194 else (if i < 196 then b 195 else b 196))))) else (if i < 208 then (if i < 202 then (if i < 199 then (if i < 198 then b 197 else b 198) else (if i < 200 then b 199 else (if i < 201 then b 200 else b 201))) else (if i < 205 then (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)) else (if i < 206 then decide (1 ≤ count205 b) else (if i < 207 then decide (2 ≤ count205 b) else decide (1 ≤ count207 b))))) else (if i < 213 then (if i < 210 then (if i < 209 then decide (2 ≤ count207 b) else decide (1 ≤ count209 b)) else (if i < 211 then decide (2 ≤ count209 b) else (if i < 212 then decide (1 ≤ count211 b) else decide (2 ≤ count211 b)))) else (if i < 216 then (if i < 214 then decide (1 ≤ count213 b) else (if i < 215 then decide (2 ≤ count213 b) else decide (1 ≤ count215 b))) else (if i < 217 then decide (2 ≤ count215 b) else (if i < 218 then decide (1 ≤ count217 b) else decide (2 ≤ count217 b))))))) else (if i < 241 then (if i < 230 then (if i < 224 then (if i < 221 then (if i < 220 then decide (1 ≤ count219 b) else decide (2 ≤ count219 b)) else (if i < 222 then decide (1 ≤ count221 b) else (if i < 223 then decide (2 ≤ count221 b) else decide (1 ≤ count223 b)))) else (if i < 227 then (if i < 225 then decide (2 ≤ count223 b) else (if i < 226 then decide (1 ≤ count225 b) else decide (2 ≤ count225 b))) else (if i < 228 then decide (1 ≤ count227 b) else (if i < 229 then decide (2 ≤ count227 b) else decide (1 ≤ count229 b))))) else (if i < 235 then (if i < 232 then (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b)) else (if i < 233 then decide (2 ≤ count231 b) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))) else (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b)))))) else (if i < 252 then (if i < 246 then (if i < 243 then (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b)) else (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b)))) else (if i < 249 then (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b))) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))))) else (if i < 257 then (if i < 254 then (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)) else (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b)))) else (if i < 260 then (if i < 258 then decide (1 ≤ count257 b) else (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b))) else (if i < 261 then decide (2 ≤ count259 b) else (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b)))))))) else (if i < 307 then (if i < 285 then (if i < 274 then (if i < 268 then (if i < 265 then (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)) else (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)))) else (if i < 271 then (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b))) else (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))))) else (if i < 279 then (if i < 276 then (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)) else (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)))) else (if i < 282 then (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))) else (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)))))) else (if i < 296 then (if i < 290 then (if i < 287 then (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)) else (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)))) else (if i < 293 then (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))) else (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))))) else (if i < 301 then (if i < 298 then (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)) else (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b)))) else (if i < 304 then (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))) else (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))))))) else (if i < 329 then (if i < 318 then (if i < 312 then (if i < 309 then (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)) else (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)))) else (if i < 315 then (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b))) else (if i < 316 then decide (1 ≤ count315 b) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b))))) else (if i < 323 then (if i < 320 then (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)) else (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)))) else (if i < 326 then (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))) else (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)))))) else (if i < 340 then (if i < 334 then (if i < 331 then (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)) else (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)))) else (if i < 337 then (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b))) else (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))))) else (if i < 345 then (if i < 342 then (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)) else (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)))) else (if i < 348 then (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b))) else (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b)))))))))) else (if i < 527 then (if i < 439 then (if i < 395 then (if i < 373 then (if i < 362 then (if i < 356 then (if i < 353 then (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b)) else (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b)))) else (if i < 359 then (if i < 357 then decide (2 ≤ count355 b) else (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b))) else (if i < 360 then decide (1 ≤ count359 b) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b))))) else (if i < 367 then (if i < 364 then (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)) else (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b)))) else (if i < 370 then (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))) else (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)))))) else (if i < 384 then (if i < 378 then (if i < 375 then (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)) else (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b)))) else (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b))))) else (if i < 389 then (if i < 386 then (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)) else (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 392 then (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))) else (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b))))))) else (if i < 417 then (if i < 406 then (if i < 400 then (if i < 397 then (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)) else (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))) else (if i < 403 then (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))) else (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))))) else (if i < 411 then (if i < 408 then (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b)) else (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (3 ≤ count407 b) else decide (1 ≤ count410 b)))) else (if i < 414 then (if i < 412 then decide (2 ≤ count410 b) else (if i < 413 then decide (1 ≤ count412 b) else decide (2 ≤ count412 b))) else (if i < 415 then decide (3 ≤ count412 b) else (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b)))))) else (if i < 428 then (if i < 422 then (if i < 419 then (if i < 418 then decide (3 ≤ count415 b) else decide (4 ≤ count415 b)) else (if i < 420 then decide (5 ≤ count415 b) else (if i < 421 then decide (6 ≤ count415 b) else decide (1 ≤ count421 b)))) else (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 426 then decide (3 ≤ count423 b) else (if i < 427 then decide (1 ≤ count426 b) else decide (2 ≤ count426 b))))) else (if i < 433 then (if i < 430 then (if i < 429 then decide (1 ≤ count428 b) else decide (2 ≤ count428 b)) else (if i < 431 then decide (3 ≤ count428 b) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)))) else (if i < 436 then (if i < 434 then decide (3 ≤ count431 b) else (if i < 435 then decide (4 ≤ count431 b) else decide (5 ≤ count431 b))) else (if i < 437 then decide (6 ≤ count431 b) else (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b)))))))) else (if i < 483 then (if i < 461 then (if i < 450 then (if i < 444 then (if i < 441 then (if i < 440 then decide (3 ≤ count437 b) else decide (4 ≤ count437 b)) else (if i < 442 then decide (5 ≤ count437 b) else (if i < 443 then decide (6 ≤ count437 b) else decide (7 ≤ count437 b)))) else (if i < 447 then (if i < 445 then decide (8 ≤ count437 b) else (if i < 446 then decide (9 ≤ count437 b) else decide (10 ≤ count437 b))) else (if i < 448 then decide (11 ≤ count437 b) else (if i < 449 then decide (12 ≤ count437 b) else decide (1 ≤ count449 b))))) else (if i < 455 then (if i < 452 then (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b)) else (if i < 453 then decide (2 ≤ count451 b) else (if i < 454 then decide (3 ≤ count451 b) else decide (1 ≤ count454 b)))) else (if i < 458 then (if i < 456 then decide (2 ≤ count454 b) else (if i < 457 then decide (1 ≤ count456 b) else decide (2 ≤ count456 b))) else (if i < 459 then decide (3 ≤ count456 b) else (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)))))) else (if i < 472 then (if i < 466 then (if i < 463 then (if i < 462 then decide (3 ≤ count459 b) else decide (4 ≤ count459 b)) else (if i < 464 then decide (5 ≤ count459 b) else (if i < 465 then decide (6 ≤ count459 b) else decide (1 ≤ count465 b)))) else (if i < 469 then (if i < 467 then decide (2 ≤ count465 b) else (if i < 468 then decide (1 ≤ count467 b) else decide (2 ≤ count467 b))) else (if i < 470 then decide (3 ≤ count467 b) else (if i < 471 then decide (1 ≤ count470 b) else decide (2 ≤ count470 b))))) else (if i < 477 then (if i < 474 then (if i < 473 then decide (1 ≤ count472 b) else decide (2 ≤ count472 b)) else (if i < 475 then decide (1 ≤ count474 b) else (if i < 476 then decide (2 ≤ count474 b) else decide (3 ≤ count474 b)))) else (if i < 480 then (if i < 478 then decide (4 ≤ count474 b) else (if i < 479 then decide (1 ≤ count478 b) else decide (2 ≤ count478 b))) else (if i < 481 then decide (3 ≤ count478 b) else (if i < 482 then decide (4 ≤ count478 b) else decide (5 ≤ count478 b))))))) else (if i < 505 then (if i < 494 then (if i < 488 then (if i < 485 then (if i < 484 then decide (6 ≤ count478 b) else decide (7 ≤ count478 b)) else (if i < 486 then decide (1 ≤ count485 b) else (if i < 487 then decide (2 ≤ count485 b) else decide (3 ≤ count485 b)))) else (if i < 491 then (if i < 489 then decide (4 ≤ count485 b) else (if i < 490 then decide (5 ≤ count485 b) else decide (6 ≤ count485 b))) else (if i < 492 then decide (7 ≤ count485 b) else (if i < 493 then decide (8 ≤ count485 b) else decide (9 ≤ count485 b))))) else (if i < 499 then (if i < 496 then (if i < 495 then decide (10 ≤ count485 b) else decide (11 ≤ count485 b)) else (if i < 497 then decide (12 ≤ count485 b) else (if i < 498 then decide (13 ≤ count485 b) else decide (1 ≤ count498 b)))) else (if i < 502 then (if i < 500 then decide (2 ≤ count498 b) else (if i < 501 then decide (3 ≤ count498 b) else decide (4 ≤ count498 b))) else (if i < 503 then decide (5 ≤ count498 b) else (if i < 504 then decide (6 ≤ count498 b) else decide (7 ≤ count498 b)))))) else (if i < 516 then (if i < 510 then (if i < 507 then (if i < 506 then decide (8 ≤ count498 b) else decide (9 ≤ count498 b)) else (if i < 508 then decide (10 ≤ count498 b) else (if i < 509 then decide (11 ≤ count498 b) else decide (12 ≤ count498 b)))) else (if i < 513 then (if i < 511 then decide (13 ≤ count498 b) else (if i < 512 then decide (14 ≤ count498 b) else decide (15 ≤ count498 b))) else (if i < 514 then decide (16 ≤ count498 b) else (if i < 515 then decide (17 ≤ count498 b) else decide (18 ≤ count498 b))))) else (if i < 521 then (if i < 518 then (if i < 517 then decide (19 ≤ count498 b) else decide (20 ≤ count498 b)) else (if i < 519 then decide (21 ≤ count498 b) else (if i < 520 then decide (22 ≤ count498 b) else decide (23 ≤ count498 b)))) else (if i < 524 then (if i < 522 then decide (24 ≤ count498 b) else (if i < 523 then decide (25 ≤ count498 b) else decide (1 ≤ count523 b))) else (if i < 525 then decide (2 ≤ count523 b) else (if i < 526 then decide (1 ≤ count525 b) else decide (2 ≤ count525 b))))))))) else (if i < 615 then (if i < 571 then (if i < 549 then (if i < 538 then (if i < 532 then (if i < 529 then (if i < 528 then decide (3 ≤ count525 b) else decide (1 ≤ count528 b)) else (if i < 530 then decide (2 ≤ count528 b) else (if i < 531 then decide (1 ≤ count530 b) else decide (2 ≤ count530 b)))) else (if i < 535 then (if i < 533 then decide (3 ≤ count530 b) else (if i < 534 then decide (1 ≤ count533 b) else decide (2 ≤ count533 b))) else (if i < 536 then decide (3 ≤ count533 b) else (if i < 537 then decide (4 ≤ count533 b) else decide (5 ≤ count533 b))))) else (if i < 543 then (if i < 540 then (if i < 539 then decide (6 ≤ count533 b) else decide (1 ≤ count539 b)) else (if i < 541 then decide (2 ≤ count539 b) else (if i < 542 then decide (1 ≤ count541 b) else decide (2 ≤ count541 b)))) else (if i < 546 then (if i < 544 then decide (3 ≤ count541 b) else (if i < 545 then decide (1 ≤ count544 b) else decide (2 ≤ count544 b))) else (if i < 547 then decide (1 ≤ count546 b) else (if i < 548 then decide (2 ≤ count546 b) else decide (1 ≤ count548 b)))))) else (if i < 560 then (if i < 554 then (if i < 551 then (if i < 550 then decide (2 ≤ count548 b) else decide (3 ≤ count548 b)) else (if i < 552 then decide (4 ≤ count548 b) else (if i < 553 then decide (1 ≤ count552 b) else decide (2 ≤ count552 b)))) else (if i < 557 then (if i < 555 then decide (3 ≤ count552 b) else (if i < 556 then decide (4 ≤ count552 b) else decide (5 ≤ count552 b))) else (if i < 558 then decide (6 ≤ count552 b) else (if i < 559 then decide (7 ≤ count552 b) else decide (1 ≤ count559 b))))) else (if i < 565 then (if i < 562 then (if i < 561 then decide (2 ≤ count559 b) else decide (3 ≤ count559 b)) else (if i < 563 then decide (4 ≤ count559 b) else (if i < 564 then decide (5 ≤ count559 b) else decide (6 ≤ count559 b)))) else (if i < 568 then (if i < 566 then decide (7 ≤ count559 b) else (if i < 567 then decide (8 ≤ count559 b) else decide (9 ≤ count559 b))) else (if i < 569 then decide (10 ≤ count559 b) else (if i < 570 then decide (11 ≤ count559 b) else decide (12 ≤ count559 b))))))) else (if i < 593 then (if i < 582 then (if i < 576 then (if i < 573 then (if i < 572 then decide (13 ≤ count559 b) else decide (1 ≤ count572 b)) else (if i < 574 then decide (2 ≤ count572 b) else (if i < 575 then decide (1 ≤ count574 b) else decide (2 ≤ count574 b)))) else (if i < 579 then (if i < 577 then decide (3 ≤ count574 b) else (if i < 578 then decide (1 ≤ count577 b) else decide (2 ≤ count577 b))) else (if i < 580 then decide (1 ≤ count579 b) else (if i < 581 then decide (2 ≤ count579 b) else decide (3 ≤ count579 b))))) else (if i < 587 then (if i < 584 then (if i < 583 then decide (1 ≤ count582 b) else decide (2 ≤ count582 b)) else (if i < 585 then decide (3 ≤ count582 b) else (if i < 586 then decide (4 ≤ count582 b) else decide (5 ≤ count582 b)))) else (if i < 590 then (if i < 588 then decide (6 ≤ count582 b) else (if i < 589 then decide (1 ≤ count588 b) else decide (2 ≤ count588 b))) else (if i < 591 then decide (1 ≤ count590 b) else (if i < 592 then decide (2 ≤ count590 b) else decide (3 ≤ count590 b)))))) else (if i < 604 then (if i < 598 then (if i < 595 then (if i < 594 then decide (1 ≤ count593 b) else decide (2 ≤ count593 b)) else (if i < 596 then decide (1 ≤ count595 b) else (if i < 597 then decide (2 ≤ count595 b) else decide (1 ≤ count597 b)))) else (if i < 601 then (if i < 599 then decide (2 ≤ count597 b) else (if i < 600 then decide (3 ≤ count597 b) else decide (4 ≤ count597 b))) else (if i < 602 then decide (1 ≤ count601 b) else (if i < 603 then decide (2 ≤ count601 b) else decide (3 ≤ count601 b))))) else (if i < 609 then (if i < 606 then (if i < 605 then decide (4 ≤ count601 b) else decide (5 ≤ count601 b)) else (if i < 607 then decide (6 ≤ count601 b) else (if i < 608 then decide (7 ≤ count601 b) else decide (1 ≤ count608 b)))) else (if i < 612 then (if i < 610 then decide (2 ≤ count608 b) else (if i < 611 then decide (3 ≤ count608 b) else decide (4 ≤ count608 b))) else (if i < 613 then decide (5 ≤ count608 b) else (if i < 614 then decide (6 ≤ count608 b) else decide (7 ≤ count608 b)))))))) else (if i < 659 then (if i < 637 then (if i < 626 then (if i < 620 then (if i < 617 then (if i < 616 then decide (8 ≤ count608 b) else decide (9 ≤ count608 b)) else (if i < 618 then decide (10 ≤ count608 b) else (if i < 619 then decide (11 ≤ count608 b) else decide (12 ≤ count608 b)))) else (if i < 623 then (if i < 621 then decide (13 ≤ count608 b) else (if i < 622 then decide (1 ≤ count621 b) else decide (2 ≤ count621 b))) else (if i < 624 then decide (3 ≤ count621 b) else (if i < 625 then decide (4 ≤ count621 b) else decide (5 ≤ count621 b))))) else (if i < 631 then (if i < 628 then (if i < 627 then decide (6 ≤ count621 b) else decide (7 ≤ count621 b)) else (if i < 629 then decide (8 ≤ count621 b) else (if i < 630 then decide (9 ≤ count621 b) else decide (10 ≤ count621 b)))) else (if i < 634 then (if i < 632 then decide (11 ≤ count621 b) else (if i < 633 then decide (12 ≤ count621 b) else decide (13 ≤ count621 b))) else (if i < 635 then decide (14 ≤ count621 b) else (if i < 636 then decide (15 ≤ count621 b) else decide (16 ≤ count621 b)))))) else (if i < 648 then (if i < 642 then (if i < 639 then (if i < 638 then decide (17 ≤ count621 b) else decide (18 ≤ count621 b)) else (if i < 640 then decide (19 ≤ count621 b) else (if i < 641 then decide (20 ≤ count621 b) else decide (21 ≤ count621 b)))) else (if i < 645 then (if i < 643 then decide (22 ≤ count621 b) else (if i < 644 then decide (23 ≤ count621 b) else decide (24 ≤ count621 b))) else (if i < 646 then decide (25 ≤ count621 b) else (if i < 647 then decide (26 ≤ count621 b) else decide (1 ≤ count647 b))))) else (if i < 653 then (if i < 650 then (if i < 649 then decide (2 ≤ count647 b) else decide (3 ≤ count647 b)) else (if i < 651 then decide (4 ≤ count647 b) else (if i < 652 then decide (5 ≤ count647 b) else decide (6 ≤ count647 b)))) else (if i < 656 then (if i < 654 then decide (7 ≤ count647 b) else (if i < 655 then decide (8 ≤ count647 b) else decide (9 ≤ count647 b))) else (if i < 657 then decide (10 ≤ count647 b) else (if i < 658 then decide (11 ≤ count647 b) else decide (12 ≤ count647 b))))))) else (if i < 681 then (if i < 670 then (if i < 664 then (if i < 661 then (if i < 660 then decide (13 ≤ count647 b) else decide (14 ≤ count647 b)) else (if i < 662 then decide (15 ≤ count647 b) else (if i < 663 then decide (16 ≤ count647 b) else decide (17 ≤ count647 b)))) else (if i < 667 then (if i < 665 then decide (18 ≤ count647 b) else (if i < 666 then decide (19 ≤ count647 b) else decide (20 ≤ count647 b))) else (if i < 668 then decide (21 ≤ count647 b) else (if i < 669 then decide (22 ≤ count647 b) else decide (23 ≤ count647 b))))) else (if i < 675 then (if i < 672 then (if i < 671 then decide (24 ≤ count647 b) else decide (25 ≤ count647 b)) else (if i < 673 then decide (26 ≤ count647 b) else (if i < 674 then decide (27 ≤ count647 b) else decide (28 ≤ count647 b)))) else (if i < 678 then (if i < 676 then decide (29 ≤ count647 b) else (if i < 677 then decide (30 ≤ count647 b) else decide (31 ≤ count647 b))) else (if i < 679 then decide (32 ≤ count647 b) else (if i < 680 then decide (33 ≤ count647 b) else decide (34 ≤ count647 b)))))) else (if i < 692 then (if i < 686 then (if i < 683 then (if i < 682 then decide (35 ≤ count647 b) else decide (36 ≤ count647 b)) else (if i < 684 then decide (37 ≤ count647 b) else (if i < 685 then decide (38 ≤ count647 b) else decide (39 ≤ count647 b)))) else (if i < 689 then (if i < 687 then decide (40 ≤ count647 b) else (if i < 688 then decide (41 ≤ count647 b) else decide (42 ≤ count647 b))) else (if i < 690 then decide (1 ≤ count689 b) else (if i < 691 then decide (2 ≤ count689 b) else decide (1 ≤ count691 b))))) else (if i < 697 then (if i < 694 then (if i < 693 then decide (2 ≤ count691 b) else decide (3 ≤ count691 b)) else (if i < 695 then decide (1 ≤ count694 b) else (if i < 696 then decide (2 ≤ count694 b) else decide (1 ≤ count696 b)))) else (if i < 700 then (if i < 698 then decide (2 ≤ count696 b) else (if i < 699 then decide (3 ≤ count696 b) else decide (1 ≤ count699 b))) else (if i < 701 then decide (2 ≤ count699 b) else (if i < 702 then decide (3 ≤ count699 b) else decide (4 ≤ count699 b))))))))))) else (if i < 1055 then (if i < 879 then (if i < 791 then (if i < 747 then (if i < 725 then (if i < 714 then (if i < 708 then (if i < 705 then (if i < 704 then decide (5 ≤ count699 b) else decide (6 ≤ count699 b)) else (if i < 706 then decide (1 ≤ count705 b) else (if i < 707 then decide (2 ≤ count705 b) else decide (1 ≤ count707 b)))) else (if i < 711 then (if i < 709 then decide (2 ≤ count707 b) else (if i < 710 then decide (3 ≤ count707 b) else decide (1 ≤ count710 b))) else (if i < 712 then decide (2 ≤ count710 b) else (if i < 713 then decide (1 ≤ count712 b) else decide (2 ≤ count712 b))))) else (if i < 719 then (if i < 716 then (if i < 715 then decide (3 ≤ count712 b) else decide (1 ≤ count715 b)) else (if i < 717 then decide (2 ≤ count715 b) else (if i < 718 then decide (3 ≤ count715 b) else decide (4 ≤ count715 b)))) else (if i < 722 then (if i < 720 then decide (5 ≤ count715 b) else (if i < 721 then decide (6 ≤ count715 b) else decide (1 ≤ count721 b))) else (if i < 723 then decide (2 ≤ count721 b) else (if i < 724 then decide (3 ≤ count721 b) else decide (4 ≤ count721 b)))))) else (if i < 736 then (if i < 730 then (if i < 727 then (if i < 726 then decide (5 ≤ count721 b) else decide (6 ≤ count721 b)) else (if i < 728 then decide (7 ≤ count721 b) else (if i < 729 then decide (8 ≤ count721 b) else decide (9 ≤ count721 b)))) else (if i < 733 then (if i < 731 then decide (10 ≤ count721 b) else (if i < 732 then decide (11 ≤ count721 b) else decide (1 ≤ count732 b))) else (if i < 734 then decide (2 ≤ count732 b) else (if i < 735 then decide (1 ≤ count734 b) else decide (2 ≤ count734 b))))) else (if i < 741 then (if i < 738 then (if i < 737 then decide (3 ≤ count734 b) else decide (1 ≤ count737 b)) else (if i < 739 then decide (2 ≤ count737 b) else (if i < 740 then decide (1 ≤ count739 b) else decide (2 ≤ count739 b)))) else (if i < 744 then (if i < 742 then decide (3 ≤ count739 b) else (if i < 743 then decide (1 ≤ count742 b) else decide (2 ≤ count742 b))) else (if i < 745 then decide (3 ≤ count742 b) else (if i < 746 then decide (4 ≤ count742 b) else decide (5 ≤ count742 b))))))) else (if i < 769 then (if i < 758 then (if i < 752 then (if i < 749 then (if i < 748 then decide (6 ≤ count742 b) else decide (1 ≤ count748 b)) else (if i < 750 then decide (2 ≤ count748 b) else (if i < 751 then decide (1 ≤ count750 b) else decide (2 ≤ count750 b)))) else (if i < 755 then (if i < 753 then decide (3 ≤ count750 b) else (if i < 754 then decide (1 ≤ count753 b) else decide (2 ≤ count753 b))) else (if i < 756 then decide (1 ≤ count755 b) else (if i < 757 then decide (2 ≤ count755 b) else decide (1 ≤ count757 b))))) else (if i < 763 then (if i < 760 then (if i < 759 then decide (2 ≤ count757 b) else decide (3 ≤ count757 b)) else (if i < 761 then decide (4 ≤ count757 b) else (if i < 762 then decide (1 ≤ count761 b) else decide (2 ≤ count761 b)))) else (if i < 766 then (if i < 764 then decide (3 ≤ count761 b) else (if i < 765 then decide (4 ≤ count761 b) else decide (5 ≤ count761 b))) else (if i < 767 then decide (6 ≤ count761 b) else (if i < 768 then decide (7 ≤ count761 b) else decide (1 ≤ count768 b)))))) else (if i < 780 then (if i < 774 then (if i < 771 then (if i < 770 then decide (2 ≤ count768 b) else decide (3 ≤ count768 b)) else (if i < 772 then decide (4 ≤ count768 b) else (if i < 773 then decide (5 ≤ count768 b) else decide (6 ≤ count768 b)))) else (if i < 777 then (if i < 775 then decide (7 ≤ count768 b) else (if i < 776 then decide (8 ≤ count768 b) else decide (9 ≤ count768 b))) else (if i < 778 then decide (10 ≤ count768 b) else (if i < 779 then decide (11 ≤ count768 b) else decide (1 ≤ count779 b))))) else (if i < 785 then (if i < 782 then (if i < 781 then decide (2 ≤ count779 b) else decide (3 ≤ count779 b)) else (if i < 783 then decide (4 ≤ count779 b) else (if i < 784 then decide (5 ≤ count779 b) else decide (6 ≤ count779 b)))) else (if i < 788 then (if i < 786 then decide (7 ≤ count779 b) else (if i < 787 then decide (8 ≤ count779 b) else decide (9 ≤ count779 b))) else (if i < 789 then decide (10 ≤ count779 b) else (if i < 790 then decide (11 ≤ count779 b) else decide (1 ≤ count790 b)))))))) else (if i < 835 then (if i < 813 then (if i < 802 then (if i < 796 then (if i < 793 then (if i < 792 then decide (2 ≤ count790 b) else decide (1 ≤ count792 b)) else (if i < 794 then decide (2 ≤ count792 b) else (if i < 795 then decide (3 ≤ count792 b) else decide (1 ≤ count795 b)))) else (if i < 799 then (if i < 797 then decide (2 ≤ count795 b) else (if i < 798 then decide (1 ≤ count797 b) else decide (2 ≤ count797 b))) else (if i < 800 then decide (3 ≤ count797 b) else (if i < 801 then decide (1 ≤ count800 b) else decide (2 ≤ count800 b))))) else (if i < 807 then (if i < 804 then (if i < 803 then decide (3 ≤ count800 b) else decide (4 ≤ count800 b)) else (if i < 805 then decide (5 ≤ count800 b) else (if i < 806 then decide (6 ≤ count800 b) else decide (1 ≤ count806 b)))) else (if i < 810 then (if i < 808 then decide (2 ≤ count806 b) else (if i < 809 then decide (1 ≤ count808 b) else decide (2 ≤ count808 b))) else (if i < 811 then decide (3 ≤ count808 b) else (if i < 812 then decide (1 ≤ count811 b) else decide (2 ≤ count811 b)))))) else (if i < 824 then (if i < 818 then (if i < 815 then (if i < 814 then decide (1 ≤ count813 b) else decide (2 ≤ count813 b)) else (if i < 816 then decide (1 ≤ count815 b) else (if i < 817 then decide (2 ≤ count815 b) else decide (3 ≤ count815 b)))) else (if i < 821 then (if i < 819 then decide (4 ≤ count815 b) else (if i < 820 then decide (1 ≤ count819 b) else decide (2 ≤ count819 b))) else (if i < 822 then decide (3 ≤ count819 b) else (if i < 823 then decide (4 ≤ count819 b) else decide (5 ≤ count819 b))))) else (if i < 829 then (if i < 826 then (if i < 825 then decide (6 ≤ count819 b) else decide (7 ≤ count819 b)) else (if i < 827 then decide (1 ≤ count826 b) else (if i < 828 then decide (2 ≤ count826 b) else decide (3 ≤ count826 b)))) else (if i < 832 then (if i < 830 then decide (4 ≤ count826 b) else (if i < 831 then decide (5 ≤ count826 b) else decide (6 ≤ count826 b))) else (if i < 833 then decide (7 ≤ count826 b) else (if i < 834 then decide (8 ≤ count826 b) else decide (9 ≤ count826 b))))))) else (if i < 857 then (if i < 846 then (if i < 840 then (if i < 837 then (if i < 836 then decide (10 ≤ count826 b) else decide (11 ≤ count826 b)) else (if i < 838 then decide (1 ≤ count837 b) else (if i < 839 then decide (2 ≤ count837 b) else decide (1 ≤ count839 b)))) else (if i < 843 then (if i < 841 then decide (2 ≤ count839 b) else (if i < 842 then decide (3 ≤ count839 b) else decide (1 ≤ count842 b))) else (if i < 844 then decide (2 ≤ count842 b) else (if i < 845 then decide (1 ≤ count844 b) else decide (2 ≤ count844 b))))) else (if i < 851 then (if i < 848 then (if i < 847 then decide (3 ≤ count844 b) else decide (1 ≤ count847 b)) else (if i < 849 then decide (2 ≤ count847 b) else (if i < 850 then decide (3 ≤ count847 b) else decide (4 ≤ count847 b)))) else (if i < 854 then (if i < 852 then decide (5 ≤ count847 b) else (if i < 853 then decide (6 ≤ count847 b) else decide (1 ≤ count853 b))) else (if i < 855 then decide (2 ≤ count853 b) else (if i < 856 then decide (1 ≤ count855 b) else decide (2 ≤ count855 b)))))) else (if i < 868 then (if i < 862 then (if i < 859 then (if i < 858 then decide (3 ≤ count855 b) else decide (1 ≤ count858 b)) else (if i < 860 then decide (2 ≤ count858 b) else (if i < 861 then decide (1 ≤ count860 b) else decide (2 ≤ count860 b)))) else (if i < 865 then (if i < 863 then decide (1 ≤ count862 b) else (if i < 864 then decide (2 ≤ count862 b) else decide (3 ≤ count862 b))) else (if i < 866 then decide (4 ≤ count862 b) else (if i < 867 then decide (1 ≤ count866 b) else decide (2 ≤ count866 b))))) else (if i < 873 then (if i < 870 then (if i < 869 then decide (3 ≤ count866 b) else decide (4 ≤ count866 b)) else (if i < 871 then decide (5 ≤ count866 b) else (if i < 872 then decide (6 ≤ count866 b) else decide (7 ≤ count866 b)))) else (if i < 876 then (if i < 874 then decide (1 ≤ count873 b) else (if i < 875 then decide (2 ≤ count873 b) else decide (3 ≤ count873 b))) else (if i < 877 then decide (4 ≤ count873 b) else (if i < 878 then decide (5 ≤ count873 b) else decide (6 ≤ count873 b))))))))) else (if i < 967 then (if i < 923 then (if i < 901 then (if i < 890 then (if i < 884 then (if i < 881 then (if i < 880 then decide (7 ≤ count873 b) else decide (8 ≤ count873 b)) else (if i < 882 then decide (9 ≤ count873 b) else (if i < 883 then decide (10 ≤ count873 b) else decide (11 ≤ count873 b)))) else (if i < 887 then (if i < 885 then decide (1 ≤ count884 b) else (if i < 886 then decide (2 ≤ count884 b) else decide (3 ≤ count884 b))) else (if i < 888 then decide (4 ≤ count884 b) else (if i < 889 then decide (5 ≤ count884 b) else decide (6 ≤ count884 b))))) else (if i < 895 then (if i < 892 then (if i < 891 then decide (7 ≤ count884 b) else decide (8 ≤ count884 b)) else (if i < 893 then decide (9 ≤ count884 b) else (if i < 894 then decide (10 ≤ count884 b) else decide (11 ≤ count884 b)))) else (if i < 898 then (if i < 896 then decide (1 ≤ count895 b) else (if i < 897 then decide (2 ≤ count895 b) else decide (3 ≤ count895 b))) else (if i < 899 then decide (4 ≤ count895 b) else (if i < 900 then decide (5 ≤ count895 b) else decide (6 ≤ count895 b)))))) else (if i < 912 then (if i < 906 then (if i < 903 then (if i < 902 then decide (7 ≤ count895 b) else decide (8 ≤ count895 b)) else (if i < 904 then decide (9 ≤ count895 b) else (if i < 905 then decide (10 ≤ count895 b) else decide (11 ≤ count895 b)))) else (if i < 909 then (if i < 907 then decide (1 ≤ count906 b) else (if i < 908 then decide (2 ≤ count906 b) else decide (1 ≤ count908 b))) else (if i < 910 then decide (2 ≤ count908 b) else (if i < 911 then decide (3 ≤ count908 b) else decide (1 ≤ count911 b))))) else (if i < 917 then (if i < 914 then (if i < 913 then decide (2 ≤ count911 b) else decide (1 ≤ count913 b)) else (if i < 915 then decide (2 ≤ count913 b) else (if i < 916 then decide (3 ≤ count913 b) else decide (1 ≤ count916 b)))) else (if i < 920 then (if i < 918 then decide (2 ≤ count916 b) else (if i < 919 then decide (3 ≤ count916 b) else decide (4 ≤ count916 b))) else (if i < 921 then decide (5 ≤ count916 b) else (if i < 922 then decide (6 ≤ count916 b) else decide (1 ≤ count922 b))))))) else (if i < 945 then (if i < 934 then (if i < 928 then (if i < 925 then (if i < 924 then decide (2 ≤ count922 b) else decide (1 ≤ count924 b)) else (if i < 926 then decide (2 ≤ count924 b) else (if i < 927 then decide (3 ≤ count924 b) else decide (1 ≤ count927 b)))) else (if i < 931 then (if i < 929 then decide (2 ≤ count927 b) else (if i < 930 then decide (1 ≤ count929 b) else decide (2 ≤ count929 b))) else (if i < 932 then decide (3 ≤ count929 b) else (if i < 933 then decide (1 ≤ count932 b) else decide (2 ≤ count932 b))))) else (if i < 939 then (if i < 936 then (if i < 935 then decide (3 ≤ count932 b) else decide (4 ≤ count932 b)) else (if i < 937 then decide (5 ≤ count932 b) else (if i < 938 then decide (6 ≤ count932 b) else decide (1 ≤ count938 b)))) else (if i < 942 then (if i < 940 then decide (2 ≤ count938 b) else (if i < 941 then decide (3 ≤ count938 b) else decide (4 ≤ count938 b))) else (if i < 943 then decide (5 ≤ count938 b) else (if i < 944 then decide (6 ≤ count938 b) else decide (7 ≤ count938 b)))))) else (if i < 956 then (if i < 950 then (if i < 947 then (if i < 946 then decide (8 ≤ count938 b) else decide (9 ≤ count938 b)) else (if i < 948 then decide (10 ≤ count938 b) else (if i < 949 then decide (11 ≤ count938 b) else decide (12 ≤ count938 b)))) else (if i < 953 then (if i < 951 then decide (1 ≤ count950 b) else (if i < 952 then decide (2 ≤ count950 b) else decide (1 ≤ count952 b))) else (if i < 954 then decide (2 ≤ count952 b) else (if i < 955 then decide (3 ≤ count952 b) else decide (1 ≤ count955 b))))) else (if i < 961 then (if i < 958 then (if i < 957 then decide (2 ≤ count955 b) else decide (1 ≤ count957 b)) else (if i < 959 then decide (2 ≤ count957 b) else (if i < 960 then decide (3 ≤ count957 b) else decide (1 ≤ count960 b)))) else (if i < 964 then (if i < 962 then decide (2 ≤ count960 b) else (if i < 963 then decide (3 ≤ count960 b) else decide (4 ≤ count960 b))) else (if i < 965 then decide (5 ≤ count960 b) else (if i < 966 then decide (6 ≤ count960 b) else decide (1 ≤ count966 b)))))))) else (if i < 1011 then (if i < 989 then (if i < 978 then (if i < 972 then (if i < 969 then (if i < 968 then decide (2 ≤ count966 b) else decide (1 ≤ count968 b)) else (if i < 970 then decide (2 ≤ count968 b) else (if i < 971 then decide (3 ≤ count968 b) else decide (1 ≤ count971 b)))) else (if i < 975 then (if i < 973 then decide (2 ≤ count971 b) else (if i < 974 then decide (1 ≤ count973 b) else decide (2 ≤ count973 b))) else (if i < 976 then decide (1 ≤ count975 b) else (if i < 977 then decide (2 ≤ count975 b) else decide (3 ≤ count975 b))))) else (if i < 983 then (if i < 980 then (if i < 979 then decide (4 ≤ count975 b) else decide (1 ≤ count979 b)) else (if i < 981 then decide (2 ≤ count979 b) else (if i < 982 then decide (3 ≤ count979 b) else decide (4 ≤ count979 b)))) else (if i < 986 then (if i < 984 then decide (5 ≤ count979 b) else (if i < 985 then decide (6 ≤ count979 b) else decide (7 ≤ count979 b))) else (if i < 987 then decide (1 ≤ count986 b) else (if i < 988 then decide (2 ≤ count986 b) else decide (3 ≤ count986 b)))))) else (if i < 1000 then (if i < 994 then (if i < 991 then (if i < 990 then decide (4 ≤ count986 b) else decide (5 ≤ count986 b)) else (if i < 992 then decide (6 ≤ count986 b) else (if i < 993 then decide (7 ≤ count986 b) else decide (8 ≤ count986 b)))) else (if i < 997 then (if i < 995 then decide (9 ≤ count986 b) else (if i < 996 then decide (10 ≤ count986 b) else decide (11 ≤ count986 b))) else (if i < 998 then decide (12 ≤ count986 b) else (if i < 999 then decide (13 ≤ count986 b) else decide (1 ≤ count999 b))))) else (if i < 1005 then (if i < 1002 then (if i < 1001 then decide (2 ≤ count999 b) else decide (3 ≤ count999 b)) else (if i < 1003 then decide (4 ≤ count999 b) else (if i < 1004 then decide (5 ≤ count999 b) else decide (6 ≤ count999 b)))) else (if i < 1008 then (if i < 1006 then decide (7 ≤ count999 b) else (if i < 1007 then decide (8 ≤ count999 b) else decide (9 ≤ count999 b))) else (if i < 1009 then decide (10 ≤ count999 b) else (if i < 1010 then decide (11 ≤ count999 b) else decide (12 ≤ count999 b))))))) else (if i < 1033 then (if i < 1022 then (if i < 1016 then (if i < 1013 then (if i < 1012 then decide (13 ≤ count999 b) else decide (14 ≤ count999 b)) else (if i < 1014 then decide (15 ≤ count999 b) else (if i < 1015 then decide (16 ≤ count999 b) else decide (17 ≤ count999 b)))) else (if i < 1019 then (if i < 1017 then decide (18 ≤ count999 b) else (if i < 1018 then decide (19 ≤ count999 b) else decide (20 ≤ count999 b))) else (if i < 1020 then decide (21 ≤ count999 b) else (if i < 1021 then decide (22 ≤ count999 b) else decide (23 ≤ count999 b))))) else (if i < 1027 then (if i < 1024 then (if i < 1023 then decide (24 ≤ count999 b) else decide (25 ≤ count999 b)) else (if i < 1025 then decide (1 ≤ count1024 b) else (if i < 1026 then decide (2 ≤ count1024 b) else decide (1 ≤ count1026 b)))) else (if i < 1030 then (if i < 1028 then decide (2 ≤ count1026 b) else (if i < 1029 then decide (3 ≤ count1026 b) else decide (1 ≤ count1029 b))) else (if i < 1031 then decide (2 ≤ count1029 b) else (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b)))))) else (if i < 1044 then (if i < 1038 then (if i < 1035 then (if i < 1034 then decide (3 ≤ count1031 b) else decide (1 ≤ count1034 b)) else (if i < 1036 then decide (2 ≤ count1034 b) else (if i < 1037 then decide (3 ≤ count1034 b) else decide (4 ≤ count1034 b)))) else (if i < 1041 then (if i < 1039 then decide (5 ≤ count1034 b) else (if i < 1040 then decide (6 ≤ count1034 b) else decide (1 ≤ count1040 b))) else (if i < 1042 then decide (2 ≤ count1040 b) else (if i < 1043 then decide (1 ≤ count1042 b) else decide (2 ≤ count1042 b))))) else (if i < 1049 then (if i < 1046 then (if i < 1045 then decide (3 ≤ count1042 b) else decide (1 ≤ count1045 b)) else (if i < 1047 then decide (2 ≤ count1045 b) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b)))) else (if i < 1052 then (if i < 1050 then decide (1 ≤ count1049 b) else (if i < 1051 then decide (2 ≤ count1049 b) else decide (3 ≤ count1049 b))) else (if i < 1053 then decide (4 ≤ count1049 b) else (if i < 1054 then decide (1 ≤ count1053 b) else decide (2 ≤ count1053 b)))))))))) else (if i < 1231 then (if i < 1143 then (if i < 1099 then (if i < 1077 then (if i < 1066 then (if i < 1060 then (if i < 1057 then (if i < 1056 then decide (3 ≤ count1053 b) else decide (4 ≤ count1053 b)) else (if i < 1058 then decide (5 ≤ count1053 b) else (if i < 1059 then decide (6 ≤ count1053 b) else decide (7 ≤ count1053 b)))) else (if i < 1063 then (if i < 1061 then decide (1 ≤ count1060 b) else (if i < 1062 then decide (2 ≤ count1060 b) else decide (3 ≤ count1060 b))) else (if i < 1064 then decide (4 ≤ count1060 b) else (if i < 1065 then decide (5 ≤ count1060 b) else decide (6 ≤ count1060 b))))) else (if i < 1071 then (if i < 1068 then (if i < 1067 then decide (7 ≤ count1060 b) else decide (8 ≤ count1060 b)) else (if i < 1069 then decide (9 ≤ count1060 b) else (if i < 1070 then decide (10 ≤ count1060 b) else decide (11 ≤ count1060 b)))) else (if i < 1074 then (if i < 1072 then decide (12 ≤ count1060 b) else (if i < 1073 then decide (13 ≤ count1060 b) else decide (1 ≤ count1073 b))) else (if i < 1075 then decide (2 ≤ count1073 b) else (if i < 1076 then decide (1 ≤ count1075 b) else decide (2 ≤ count1075 b)))))) else (if i < 1088 then (if i < 1082 then (if i < 1079 then (if i < 1078 then decide (3 ≤ count1075 b) else decide (1 ≤ count1078 b)) else (if i < 1080 then decide (2 ≤ count1078 b) else (if i < 1081 then decide (1 ≤ count1080 b) else decide (2 ≤ count1080 b)))) else (if i < 1085 then (if i < 1083 then decide (3 ≤ count1080 b) else (if i < 1084 then decide (1 ≤ count1083 b) else decide (2 ≤ count1083 b))) else (if i < 1086 then decide (3 ≤ count1083 b) else (if i < 1087 then decide (4 ≤ count1083 b) else decide (5 ≤ count1083 b))))) else (if i < 1093 then (if i < 1090 then (if i < 1089 then decide (6 ≤ count1083 b) else decide (1 ≤ count1089 b)) else (if i < 1091 then decide (2 ≤ count1089 b) else (if i < 1092 then decide (1 ≤ count1091 b) else decide (2 ≤ count1091 b)))) else (if i < 1096 then (if i < 1094 then decide (3 ≤ count1091 b) else (if i < 1095 then decide (1 ≤ count1094 b) else decide (2 ≤ count1094 b))) else (if i < 1097 then decide (1 ≤ count1096 b) else (if i < 1098 then decide (2 ≤ count1096 b) else decide (1 ≤ count1098 b))))))) else (if i < 1121 then (if i < 1110 then (if i < 1104 then (if i < 1101 then (if i < 1100 then decide (2 ≤ count1098 b) else decide (3 ≤ count1098 b)) else (if i < 1102 then decide (4 ≤ count1098 b) else (if i < 1103 then decide (1 ≤ count1102 b) else decide (2 ≤ count1102 b)))) else (if i < 1107 then (if i < 1105 then decide (3 ≤ count1102 b) else (if i < 1106 then decide (4 ≤ count1102 b) else decide (5 ≤ count1102 b))) else (if i < 1108 then decide (6 ≤ count1102 b) else (if i < 1109 then decide (7 ≤ count1102 b) else decide (1 ≤ count1109 b))))) else (if i < 1115 then (if i < 1112 then (if i < 1111 then decide (2 ≤ count1109 b) else decide (3 ≤ count1109 b)) else (if i < 1113 then decide (4 ≤ count1109 b) else (if i < 1114 then decide (5 ≤ count1109 b) else decide (6 ≤ count1109 b)))) else (if i < 1118 then (if i < 1116 then decide (7 ≤ count1109 b) else (if i < 1117 then decide (8 ≤ count1109 b) else decide (9 ≤ count1109 b))) else (if i < 1119 then decide (10 ≤ count1109 b) else (if i < 1120 then decide (11 ≤ count1109 b) else decide (12 ≤ count1109 b)))))) else (if i < 1132 then (if i < 1126 then (if i < 1123 then (if i < 1122 then decide (13 ≤ count1109 b) else decide (1 ≤ count1122 b)) else (if i < 1124 then decide (2 ≤ count1122 b) else (if i < 1125 then decide (3 ≤ count1122 b) else decide (4 ≤ count1122 b)))) else (if i < 1129 then (if i < 1127 then decide (5 ≤ count1122 b) else (if i < 1128 then decide (6 ≤ count1122 b) else decide (7 ≤ count1122 b))) else (if i < 1130 then decide (8 ≤ count1122 b) else (if i < 1131 then decide (9 ≤ count1122 b) else decide (10 ≤ count1122 b))))) else (if i < 1137 then (if i < 1134 then (if i < 1133 then decide (11 ≤ count1122 b) else decide (12 ≤ count1122 b)) else (if i < 1135 then decide (13 ≤ count1122 b) else (if i < 1136 then decide (14 ≤ count1122 b) else decide (15 ≤ count1122 b)))) else (if i < 1140 then (if i < 1138 then decide (16 ≤ count1122 b) else (if i < 1139 then decide (17 ≤ count1122 b) else decide (18 ≤ count1122 b))) else (if i < 1141 then decide (19 ≤ count1122 b) else (if i < 1142 then decide (20 ≤ count1122 b) else decide (21 ≤ count1122 b)))))))) else (if i < 1187 then (if i < 1165 then (if i < 1154 then (if i < 1148 then (if i < 1145 then (if i < 1144 then decide (22 ≤ count1122 b) else decide (23 ≤ count1122 b)) else (if i < 1146 then decide (24 ≤ count1122 b) else (if i < 1147 then decide (25 ≤ count1122 b) else decide (26 ≤ count1122 b)))) else (if i < 1151 then (if i < 1149 then decide (1 ≤ count1148 b) else (if i < 1150 then decide (2 ≤ count1148 b) else decide (3 ≤ count1148 b))) else (if i < 1152 then decide (4 ≤ count1148 b) else (if i < 1153 then decide (5 ≤ count1148 b) else decide (6 ≤ count1148 b))))) else (if i < 1159 then (if i < 1156 then (if i < 1155 then decide (7 ≤ count1148 b) else decide (8 ≤ count1148 b)) else (if i < 1157 then decide (9 ≤ count1148 b) else (if i < 1158 then decide (10 ≤ count1148 b) else decide (11 ≤ count1148 b)))) else (if i < 1162 then (if i < 1160 then decide (12 ≤ count1148 b) else (if i < 1161 then decide (13 ≤ count1148 b) else decide (14 ≤ count1148 b))) else (if i < 1163 then decide (15 ≤ count1148 b) else (if i < 1164 then decide (16 ≤ count1148 b) else decide (17 ≤ count1148 b)))))) else (if i < 1176 then (if i < 1170 then (if i < 1167 then (if i < 1166 then decide (18 ≤ count1148 b) else decide (19 ≤ count1148 b)) else (if i < 1168 then decide (20 ≤ count1148 b) else (if i < 1169 then decide (21 ≤ count1148 b) else decide (22 ≤ count1148 b)))) else (if i < 1173 then (if i < 1171 then decide (23 ≤ count1148 b) else (if i < 1172 then decide (24 ≤ count1148 b) else decide (25 ≤ count1148 b))) else (if i < 1174 then decide (26 ≤ count1148 b) else (if i < 1175 then decide (27 ≤ count1148 b) else decide (28 ≤ count1148 b))))) else (if i < 1181 then (if i < 1178 then (if i < 1177 then decide (29 ≤ count1148 b) else decide (30 ≤ count1148 b)) else (if i < 1179 then decide (31 ≤ count1148 b) else (if i < 1180 then decide (32 ≤ count1148 b) else decide (33 ≤ count1148 b)))) else (if i < 1184 then (if i < 1182 then decide (34 ≤ count1148 b) else (if i < 1183 then decide (35 ≤ count1148 b) else decide (36 ≤ count1148 b))) else (if i < 1185 then decide (37 ≤ count1148 b) else (if i < 1186 then decide (38 ≤ count1148 b) else decide (39 ≤ count1148 b))))))) else (if i < 1209 then (if i < 1198 then (if i < 1192 then (if i < 1189 then (if i < 1188 then decide (40 ≤ count1148 b) else decide (41 ≤ count1148 b)) else (if i < 1190 then decide (42 ≤ count1148 b) else (if i < 1191 then decide (1 ≤ count1190 b) else decide (2 ≤ count1190 b)))) else (if i < 1195 then (if i < 1193 then decide (1 ≤ count1192 b) else (if i < 1194 then decide (2 ≤ count1192 b) else decide (3 ≤ count1192 b))) else (if i < 1196 then decide (1 ≤ count1195 b) else (if i < 1197 then decide (2 ≤ count1195 b) else decide (1 ≤ count1197 b))))) else (if i < 1203 then (if i < 1200 then (if i < 1199 then decide (2 ≤ count1197 b) else decide (3 ≤ count1197 b)) else (if i < 1201 then decide (1 ≤ count1200 b) else (if i < 1202 then decide (2 ≤ count1200 b) else decide (3 ≤ count1200 b)))) else (if i < 1206 then (if i < 1204 then decide (4 ≤ count1200 b) else (if i < 1205 then decide (5 ≤ count1200 b) else decide (6 ≤ count1200 b))) else (if i < 1207 then decide (1 ≤ count1206 b) else (if i < 1208 then decide (2 ≤ count1206 b) else decide (1 ≤ count1208 b)))))) else (if i < 1220 then (if i < 1214 then (if i < 1211 then (if i < 1210 then decide (2 ≤ count1208 b) else decide (3 ≤ count1208 b)) else (if i < 1212 then decide (1 ≤ count1211 b) else (if i < 1213 then decide (2 ≤ count1211 b) else decide (1 ≤ count1213 b)))) else (if i < 1217 then (if i < 1215 then decide (2 ≤ count1213 b) else (if i < 1216 then decide (3 ≤ count1213 b) else decide (1 ≤ count1216 b))) else (if i < 1218 then decide (2 ≤ count1216 b) else (if i < 1219 then decide (3 ≤ count1216 b) else decide (4 ≤ count1216 b))))) else (if i < 1225 then (if i < 1222 then (if i < 1221 then decide (5 ≤ count1216 b) else decide (6 ≤ count1216 b)) else (if i < 1223 then decide (1 ≤ count1222 b) else (if i < 1224 then decide (2 ≤ count1222 b) else decide (3 ≤ count1222 b)))) else (if i < 1228 then (if i < 1226 then decide (4 ≤ count1222 b) else (if i < 1227 then decide (5 ≤ count1222 b) else decide (6 ≤ count1222 b))) else (if i < 1229 then decide (7 ≤ count1222 b) else (if i < 1230 then decide (8 ≤ count1222 b) else decide (9 ≤ count1222 b))))))))) else (if i < 1319 then (if i < 1275 then (if i < 1253 then (if i < 1242 then (if i < 1236 then (if i < 1233 then (if i < 1232 then decide (10 ≤ count1222 b) else decide (11 ≤ count1222 b)) else (if i < 1234 then decide (1 ≤ count1233 b) else (if i < 1235 then decide (2 ≤ count1233 b) else decide (1 ≤ count1235 b)))) else (if i < 1239 then (if i < 1237 then decide (2 ≤ count1235 b) else (if i < 1238 then decide (3 ≤ count1235 b) else decide (1 ≤ count1238 b))) else (if i < 1240 then decide (2 ≤ count1238 b) else (if i < 1241 then decide (1 ≤ count1240 b) else decide (2 ≤ count1240 b))))) else (if i < 1247 then (if i < 1244 then (if i < 1243 then decide (3 ≤ count1240 b) else decide (1 ≤ count1243 b)) else (if i < 1245 then decide (2 ≤ count1243 b) else (if i < 1246 then decide (3 ≤ count1243 b) else decide (4 ≤ count1243 b)))) else (if i < 1250 then (if i < 1248 then decide (5 ≤ count1243 b) else (if i < 1249 then decide (6 ≤ count1243 b) else decide (1 ≤ count1249 b))) else (if i < 1251 then decide (2 ≤ count1249 b) else (if i < 1252 then decide (1 ≤ count1251 b) else decide (2 ≤ count1251 b)))))) else (if i < 1264 then (if i < 1258 then (if i < 1255 then (if i < 1254 then decide (3 ≤ count1251 b) else decide (1 ≤ count1254 b)) else (if i < 1256 then decide (2 ≤ count1254 b) else (if i < 1257 then decide (1 ≤ count1256 b) else decide (2 ≤ count1256 b)))) else (if i < 1261 then (if i < 1259 then decide (1 ≤ count1258 b) else (if i < 1260 then decide (2 ≤ count1258 b) else decide (3 ≤ count1258 b))) else (if i < 1262 then decide (4 ≤ count1258 b) else (if i < 1263 then decide (1 ≤ count1262 b) else decide (2 ≤ count1262 b))))) else (if i < 1269 then (if i < 1266 then (if i < 1265 then decide (3 ≤ count1262 b) else decide (4 ≤ count1262 b)) else (if i < 1267 then decide (5 ≤ count1262 b) else (if i < 1268 then decide (6 ≤ count1262 b) else decide (7 ≤ count1262 b)))) else (if i < 1272 then (if i < 1270 then decide (1 ≤ count1269 b) else (if i < 1271 then decide (2 ≤ count1269 b) else decide (3 ≤ count1269 b))) else (if i < 1273 then decide (4 ≤ count1269 b) else (if i < 1274 then decide (5 ≤ count1269 b) else decide (6 ≤ count1269 b))))))) else (if i < 1297 then (if i < 1286 then (if i < 1280 then (if i < 1277 then (if i < 1276 then decide (7 ≤ count1269 b) else decide (8 ≤ count1269 b)) else (if i < 1278 then decide (9 ≤ count1269 b) else (if i < 1279 then decide (10 ≤ count1269 b) else decide (11 ≤ count1269 b)))) else (if i < 1283 then (if i < 1281 then decide (1 ≤ count1280 b) else (if i < 1282 then decide (2 ≤ count1280 b) else decide (3 ≤ count1280 b))) else (if i < 1284 then decide (4 ≤ count1280 b) else (if i < 1285 then decide (5 ≤ count1280 b) else decide (6 ≤ count1280 b))))) else (if i < 1291 then (if i < 1288 then (if i < 1287 then decide (7 ≤ count1280 b) else decide (8 ≤ count1280 b)) else (if i < 1289 then decide (9 ≤ count1280 b) else (if i < 1290 then decide (10 ≤ count1280 b) else decide (11 ≤ count1280 b)))) else (if i < 1294 then (if i < 1292 then decide (1 ≤ count1291 b) else (if i < 1293 then decide (2 ≤ count1291 b) else decide (1 ≤ count1293 b))) else (if i < 1295 then decide (2 ≤ count1293 b) else (if i < 1296 then decide (3 ≤ count1293 b) else decide (1 ≤ count1296 b)))))) else (if i < 1308 then (if i < 1302 then (if i < 1299 then (if i < 1298 then decide (2 ≤ count1296 b) else decide (1 ≤ count1298 b)) else (if i < 1300 then decide (2 ≤ count1298 b) else (if i < 1301 then decide (3 ≤ count1298 b) else decide (1 ≤ count1301 b)))) else (if i < 1305 then (if i < 1303 then decide (2 ≤ count1301 b) else (if i < 1304 then decide (3 ≤ count1301 b) else decide (4 ≤ count1301 b))) else (if i < 1306 then decide (5 ≤ count1301 b) else (if i < 1307 then decide (6 ≤ count1301 b) else decide (1 ≤ count1307 b))))) else (if i < 1313 then (if i < 1310 then (if i < 1309 then decide (2 ≤ count1307 b) else decide (1 ≤ count1309 b)) else (if i < 1311 then decide (2 ≤ count1309 b) else (if i < 1312 then decide (3 ≤ count1309 b) else decide (1 ≤ count1312 b)))) else (if i < 1316 then (if i < 1314 then decide (2 ≤ count1312 b) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b))) else (if i < 1317 then decide (1 ≤ count1316 b) else (if i < 1318 then decide (2 ≤ count1316 b) else decide (3 ≤ count1316 b)))))))) else (if i < 1363 then (if i < 1341 then (if i < 1330 then (if i < 1324 then (if i < 1321 then (if i < 1320 then decide (4 ≤ count1316 b) else decide (1 ≤ count1320 b)) else (if i < 1322 then decide (2 ≤ count1320 b) else (if i < 1323 then decide (3 ≤ count1320 b) else decide (4 ≤ count1320 b)))) else (if i < 1327 then (if i < 1325 then decide (5 ≤ count1320 b) else (if i < 1326 then decide (6 ≤ count1320 b) else decide (7 ≤ count1320 b))) else (if i < 1328 then decide (1 ≤ count1327 b) else (if i < 1329 then decide (2 ≤ count1327 b) else decide (3 ≤ count1327 b))))) else (if i < 1335 then (if i < 1332 then (if i < 1331 then decide (4 ≤ count1327 b) else decide (5 ≤ count1327 b)) else (if i < 1333 then decide (6 ≤ count1327 b) else (if i < 1334 then decide (7 ≤ count1327 b) else decide (8 ≤ count1327 b)))) else (if i < 1338 then (if i < 1336 then decide (9 ≤ count1327 b) else (if i < 1337 then decide (10 ≤ count1327 b) else decide (11 ≤ count1327 b))) else (if i < 1339 then decide (1 ≤ count1338 b) else (if i < 1340 then decide (2 ≤ count1338 b) else decide (1 ≤ count1340 b)))))) else (if i < 1352 then (if i < 1346 then (if i < 1343 then (if i < 1342 then decide (2 ≤ count1340 b) else decide (3 ≤ count1340 b)) else (if i < 1344 then decide (1 ≤ count1343 b) else (if i < 1345 then decide (2 ≤ count1343 b) else decide (1 ≤ count1345 b)))) else (if i < 1349 then (if i < 1347 then decide (2 ≤ count1345 b) else (if i < 1348 then decide (3 ≤ count1345 b) else decide (1 ≤ count1348 b))) else (if i < 1350 then decide (2 ≤ count1348 b) else (if i < 1351 then decide (3 ≤ count1348 b) else decide (4 ≤ count1348 b))))) else (if i < 1357 then (if i < 1354 then (if i < 1353 then decide (5 ≤ count1348 b) else decide (6 ≤ count1348 b)) else (if i < 1355 then decide (1 ≤ count1354 b) else (if i < 1356 then decide (2 ≤ count1354 b) else decide (1 ≤ count1356 b)))) else (if i < 1360 then (if i < 1358 then decide (2 ≤ count1356 b) else (if i < 1359 then decide (3 ≤ count1356 b) else decide (1 ≤ count1359 b))) else (if i < 1361 then decide (2 ≤ count1359 b) else (if i < 1362 then decide (1 ≤ count1361 b) else decide (2 ≤ count1361 b))))))) else (if i < 1385 then (if i < 1374 then (if i < 1368 then (if i < 1365 then (if i < 1364 then decide (1 ≤ count1363 b) else decide (2 ≤ count1363 b)) else (if i < 1366 then decide (3 ≤ count1363 b) else (if i < 1367 then decide (4 ≤ count1363 b) else decide (1 ≤ count1367 b)))) else (if i < 1371 then (if i < 1369 then decide (2 ≤ count1367 b) else (if i < 1370 then decide (3 ≤ count1367 b) else decide (4 ≤ count1367 b))) else (if i < 1372 then decide (5 ≤ count1367 b) else (if i < 1373 then decide (6 ≤ count1367 b) else decide (7 ≤ count1367 b))))) else (if i < 1379 then (if i < 1376 then (if i < 1375 then decide (1 ≤ count1374 b) else decide (2 ≤ count1374 b)) else (if i < 1377 then decide (3 ≤ count1374 b) else (if i < 1378 then decide (4 ≤ count1374 b) else decide (5 ≤ count1374 b)))) else (if i < 1382 then (if i < 1380 then decide (6 ≤ count1374 b) else (if i < 1381 then decide (7 ≤ count1374 b) else decide (8 ≤ count1374 b))) else (if i < 1383 then decide (9 ≤ count1374 b) else (if i < 1384 then decide (10 ≤ count1374 b) else decide (11 ≤ count1374 b)))))) else (if i < 1396 then (if i < 1390 then (if i < 1387 then (if i < 1386 then decide (1 ≤ count1385 b) else decide (2 ≤ count1385 b)) else (if i < 1388 then decide (3 ≤ count1385 b) else (if i < 1389 then decide (4 ≤ count1385 b) else decide (5 ≤ count1385 b)))) else (if i < 1393 then (if i < 1391 then decide (6 ≤ count1385 b) else (if i < 1392 then decide (7 ≤ count1385 b) else decide (8 ≤ count1385 b))) else (if i < 1394 then decide (9 ≤ count1385 b) else (if i < 1395 then decide (10 ≤ count1385 b) else decide (11 ≤ count1385 b))))) else (if i < 1401 then (if i < 1398 then (if i < 1397 then decide (1 ≤ count1396 b) else decide (2 ≤ count1396 b)) else (if i < 1399 then decide (3 ≤ count1396 b) else (if i < 1400 then decide (4 ≤ count1396 b) else decide (5 ≤ count1396 b)))) else (if i < 1404 then (if i < 1402 then decide (6 ≤ count1396 b) else (if i < 1403 then decide (7 ≤ count1396 b) else decide (8 ≤ count1396 b))) else (if i < 1405 then decide (9 ≤ count1396 b) else (if i < 1406 then decide (10 ≤ count1396 b) else decide (11 ≤ count1396 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (13 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (15 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (160 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (161 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (162 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (163 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (165 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (171 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (173 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (175 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (176 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (177 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (178 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (179 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (182 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (184 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (188 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (189 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (190 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (191 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (226 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (227 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (228 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (229 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (234 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (235 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (236 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (244 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (245 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (247 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (248 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (249 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (251 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (255 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (259 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (260 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (261 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (267 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (268 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (276 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (356 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (357 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (364 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (372 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (376 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (387 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (400 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (403 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (419 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (421 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (427 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (432 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (436 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (437 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (439 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (443 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (447 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (451 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (453 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (468 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (469 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (471 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (178 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (184 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (236 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (364 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (2 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (2 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value250 (q : Snake 81) : valuation q 250 = decide (2 ≤ count249 (baseVal q)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (2 ≤ count251 (baseVal q)) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value1190 (q : Snake 81) : valuation q 1190 = decide (1 ≤ count1190 (baseVal q)) := rfl
theorem value1192 (q : Snake 81) : valuation q 1192 = decide (1 ≤ count1192 (baseVal q)) := rfl
theorem value1195 (q : Snake 81) : valuation q 1195 = decide (1 ≤ count1195 (baseVal q)) := rfl
theorem value1196 (q : Snake 81) : valuation q 1196 = decide (2 ≤ count1195 (baseVal q)) := rfl
theorem value1197 (q : Snake 81) : valuation q 1197 = decide (1 ≤ count1197 (baseVal q)) := rfl
theorem value1198 (q : Snake 81) : valuation q 1198 = decide (2 ≤ count1197 (baseVal q)) := rfl
theorem value1199 (q : Snake 81) : valuation q 1199 = decide (3 ≤ count1197 (baseVal q)) := rfl
theorem value1200 (q : Snake 81) : valuation q 1200 = decide (1 ≤ count1200 (baseVal q)) := rfl
theorem value1201 (q : Snake 81) : valuation q 1201 = decide (2 ≤ count1200 (baseVal q)) := rfl
theorem value1202 (q : Snake 81) : valuation q 1202 = decide (3 ≤ count1200 (baseVal q)) := rfl
theorem value1206 (q : Snake 81) : valuation q 1206 = decide (1 ≤ count1206 (baseVal q)) := rfl
theorem value1207 (q : Snake 81) : valuation q 1207 = decide (2 ≤ count1206 (baseVal q)) := rfl
theorem value1208 (q : Snake 81) : valuation q 1208 = decide (1 ≤ count1208 (baseVal q)) := rfl
theorem value1209 (q : Snake 81) : valuation q 1209 = decide (2 ≤ count1208 (baseVal q)) := rfl
theorem value1210 (q : Snake 81) : valuation q 1210 = decide (3 ≤ count1208 (baseVal q)) := rfl
theorem value1211 (q : Snake 81) : valuation q 1211 = decide (1 ≤ count1211 (baseVal q)) := rfl
theorem value1212 (q : Snake 81) : valuation q 1212 = decide (2 ≤ count1211 (baseVal q)) := rfl
theorem value1213 (q : Snake 81) : valuation q 1213 = decide (1 ≤ count1213 (baseVal q)) := rfl
theorem value1214 (q : Snake 81) : valuation q 1214 = decide (2 ≤ count1213 (baseVal q)) := rfl
theorem value1216 (q : Snake 81) : valuation q 1216 = decide (1 ≤ count1216 (baseVal q)) := rfl
theorem value1217 (q : Snake 81) : valuation q 1217 = decide (2 ≤ count1216 (baseVal q)) := rfl
theorem value1218 (q : Snake 81) : valuation q 1218 = decide (3 ≤ count1216 (baseVal q)) := rfl
theorem value1219 (q : Snake 81) : valuation q 1219 = decide (4 ≤ count1216 (baseVal q)) := rfl
theorem value1223 (q : Snake 81) : valuation q 1223 = decide (2 ≤ count1222 (baseVal q)) := rfl
theorem value1224 (q : Snake 81) : valuation q 1224 = decide (3 ≤ count1222 (baseVal q)) := rfl
theorem value1225 (q : Snake 81) : valuation q 1225 = decide (4 ≤ count1222 (baseVal q)) := rfl
theorem value1226 (q : Snake 81) : valuation q 1226 = decide (5 ≤ count1222 (baseVal q)) := rfl
theorem value1233 (q : Snake 81) : valuation q 1233 = decide (1 ≤ count1233 (baseVal q)) := rfl
theorem value1234 (q : Snake 81) : valuation q 1234 = decide (2 ≤ count1233 (baseVal q)) := rfl
theorem value1235 (q : Snake 81) : valuation q 1235 = decide (1 ≤ count1235 (baseVal q)) := rfl
theorem value1236 (q : Snake 81) : valuation q 1236 = decide (2 ≤ count1235 (baseVal q)) := rfl
theorem value1238 (q : Snake 81) : valuation q 1238 = decide (1 ≤ count1238 (baseVal q)) := rfl
theorem value1239 (q : Snake 81) : valuation q 1239 = decide (2 ≤ count1238 (baseVal q)) := rfl
theorem value1240 (q : Snake 81) : valuation q 1240 = decide (1 ≤ count1240 (baseVal q)) := rfl
theorem value1241 (q : Snake 81) : valuation q 1241 = decide (2 ≤ count1240 (baseVal q)) := rfl
theorem value1243 (q : Snake 81) : valuation q 1243 = decide (1 ≤ count1243 (baseVal q)) := rfl
theorem value1244 (q : Snake 81) : valuation q 1244 = decide (2 ≤ count1243 (baseVal q)) := rfl
theorem value1245 (q : Snake 81) : valuation q 1245 = decide (3 ≤ count1243 (baseVal q)) := rfl
theorem value1249 (q : Snake 81) : valuation q 1249 = decide (1 ≤ count1249 (baseVal q)) := rfl
theorem value1251 (q : Snake 81) : valuation q 1251 = decide (1 ≤ count1251 (baseVal q)) := rfl
theorem value1252 (q : Snake 81) : valuation q 1252 = decide (2 ≤ count1251 (baseVal q)) := rfl
theorem value1254 (q : Snake 81) : valuation q 1254 = decide (1 ≤ count1254 (baseVal q)) := rfl
theorem value1256 (q : Snake 81) : valuation q 1256 = decide (1 ≤ count1256 (baseVal q)) := rfl
theorem value1258 (q : Snake 81) : valuation q 1258 = decide (1 ≤ count1258 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (1 ≤ count1262 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (2 ≤ count1262 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (3 ≤ count1262 (baseVal q)) := rfl
theorem value1269 (q : Snake 81) : valuation q 1269 = decide (1 ≤ count1269 (baseVal q)) := rfl
theorem value1270 (q : Snake 81) : valuation q 1270 = decide (2 ≤ count1269 (baseVal q)) := rfl
theorem value1271 (q : Snake 81) : valuation q 1271 = decide (3 ≤ count1269 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (4 ≤ count1269 (baseVal q)) := rfl
theorem value1284 (q : Snake 81) : valuation q 1284 = decide (5 ≤ count1280 (baseVal q)) := rfl
theorem value1285 (q : Snake 81) : valuation q 1285 = decide (6 ≤ count1280 (baseVal q)) := rfl
theorem value1286 (q : Snake 81) : valuation q 1286 = decide (7 ≤ count1280 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (1 ≤ count1296 (baseVal q)) := rfl
theorem value1298 (q : Snake 81) : valuation q 1298 = decide (1 ≤ count1298 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (1 ≤ count1301 (baseVal q)) := rfl
theorem value1307 (q : Snake 81) : valuation q 1307 = decide (1 ≤ count1307 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (1 ≤ count1309 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (1 ≤ count1312 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (1 ≤ count1314 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (2 ≤ count1314 (baseVal q)) := rfl
theorem value1316 (q : Snake 81) : valuation q 1316 = decide (1 ≤ count1316 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (2 ≤ count1316 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (3 ≤ count1316 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (1 ≤ count1320 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (2 ≤ count1320 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (3 ≤ count1320 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (2 ≤ count1327 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (3 ≤ count1327 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (1 ≤ count1338 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (2 ≤ count1338 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (1 ≤ count1340 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (2 ≤ count1340 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (1 ≤ count1343 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (2 ≤ count1343 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (1 ≤ count1345 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (2 ≤ count1345 (baseVal q)) := rfl
theorem value1348 (q : Snake 81) : valuation q 1348 = decide (1 ≤ count1348 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (2 ≤ count1348 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (3 ≤ count1348 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (1 ≤ count1356 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (1 ≤ count1359 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (1 ≤ count1363 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (1 ≤ count1367 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (2 ≤ count1374 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (3 ≤ count1374 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (4 ≤ count1374 (baseVal q)) := rfl
theorem value1388 (q : Snake 81) : valuation q 1388 = decide (4 ≤ count1385 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (5 ≤ count1385 (baseVal q)) := rfl
theorem value1390 (q : Snake 81) : valuation q 1390 = decide (6 ≤ count1385 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (11 ≤ count1396 (baseVal q)) := rfl
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
theorem meaningNeg83 (b : Nat → Bool) : literal (valuationOf b) (-83) = decide (1 ≤ countLit b [-83]) := by
  change literal b (-83) = decide (1 ≤ countLit b [-83])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-83) <;> decide
theorem meaningNeg81 (b : Nat → Bool) : literal (valuationOf b) (-81) = decide (1 ≤ countLit b [-81]) := by
  change literal b (-81) = decide (1 ≤ countLit b [-81])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-81) <;> decide
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
theorem meaningNeg74 (b : Nat → Bool) : literal (valuationOf b) (-74) = decide (1 ≤ countLit b [-74]) := by
  change literal b (-74) = decide (1 ≤ countLit b [-74])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-74) <;> decide
theorem meaningNeg68 (b : Nat → Bool) : literal (valuationOf b) (-68) = decide (1 ≤ countLit b [-68]) := by
  change literal b (-68) = decide (1 ≤ countLit b [-68])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-68) <;> decide
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
theorem meaningNeg60 (b : Nat → Bool) : literal (valuationOf b) (-60) = decide (1 ≤ countLit b [-60]) := by
  change literal b (-60) = decide (1 ≤ countLit b [-60])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-60) <;> decide
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
theorem meaningNeg39 (b : Nat → Bool) : literal (valuationOf b) (-39) = decide (1 ≤ countLit b [-39]) := by
  change literal b (-39) = decide (1 ≤ countLit b [-39])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-39) <;> decide
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
theorem meaning120 (b : Nat → Bool) : literal (valuationOf b) (120) = decide (1 ≤ countLit b [120]) := by
  change literal b (120) = decide (1 ≤ countLit b [120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (120) <;> decide
theorem meaning123 (b : Nat → Bool) : literal (valuationOf b) (123) = decide (1 ≤ countLit b [123]) := by
  change literal b (123) = decide (1 ≤ countLit b [123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (123) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning234 (b : Nat → Bool) : literal (valuationOf b) 234 = decide (2 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning236 (b : Nat → Bool) : literal (valuationOf b) 236 = decide (2 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning250 (b : Nat → Bool) : literal (valuationOf b) 250 = decide (2 ≤ count249 b) := rfl
theorem meaning252 (b : Nat → Bool) : literal (valuationOf b) 252 = decide (2 ≤ count251 b) := rfl
theorem meaning302 (b : Nat → Bool) : literal (valuationOf b) 302 = decide (2 ≤ count301 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning1190 (b : Nat → Bool) : literal (valuationOf b) 1190 = decide (1 ≤ count1190 b) := rfl
theorem meaning1192 (b : Nat → Bool) : literal (valuationOf b) 1192 = decide (1 ≤ count1192 b) := rfl
theorem meaning1195 (b : Nat → Bool) : literal (valuationOf b) 1195 = decide (1 ≤ count1195 b) := rfl
theorem meaning1196 (b : Nat → Bool) : literal (valuationOf b) 1196 = decide (2 ≤ count1195 b) := rfl
theorem meaning1197 (b : Nat → Bool) : literal (valuationOf b) 1197 = decide (1 ≤ count1197 b) := rfl
theorem meaning1198 (b : Nat → Bool) : literal (valuationOf b) 1198 = decide (2 ≤ count1197 b) := rfl
theorem meaning1199 (b : Nat → Bool) : literal (valuationOf b) 1199 = decide (3 ≤ count1197 b) := rfl
theorem meaning1200 (b : Nat → Bool) : literal (valuationOf b) 1200 = decide (1 ≤ count1200 b) := rfl
theorem meaning1201 (b : Nat → Bool) : literal (valuationOf b) 1201 = decide (2 ≤ count1200 b) := rfl
theorem meaning1202 (b : Nat → Bool) : literal (valuationOf b) 1202 = decide (3 ≤ count1200 b) := rfl
theorem meaning1206 (b : Nat → Bool) : literal (valuationOf b) 1206 = decide (1 ≤ count1206 b) := rfl
theorem meaning1207 (b : Nat → Bool) : literal (valuationOf b) 1207 = decide (2 ≤ count1206 b) := rfl
theorem meaning1208 (b : Nat → Bool) : literal (valuationOf b) 1208 = decide (1 ≤ count1208 b) := rfl
theorem meaning1209 (b : Nat → Bool) : literal (valuationOf b) 1209 = decide (2 ≤ count1208 b) := rfl
theorem meaning1210 (b : Nat → Bool) : literal (valuationOf b) 1210 = decide (3 ≤ count1208 b) := rfl
theorem meaning1211 (b : Nat → Bool) : literal (valuationOf b) 1211 = decide (1 ≤ count1211 b) := rfl
theorem meaning1212 (b : Nat → Bool) : literal (valuationOf b) 1212 = decide (2 ≤ count1211 b) := rfl
theorem meaning1213 (b : Nat → Bool) : literal (valuationOf b) 1213 = decide (1 ≤ count1213 b) := rfl
theorem meaning1214 (b : Nat → Bool) : literal (valuationOf b) 1214 = decide (2 ≤ count1213 b) := rfl
theorem meaning1216 (b : Nat → Bool) : literal (valuationOf b) 1216 = decide (1 ≤ count1216 b) := rfl
theorem meaning1217 (b : Nat → Bool) : literal (valuationOf b) 1217 = decide (2 ≤ count1216 b) := rfl
theorem meaning1218 (b : Nat → Bool) : literal (valuationOf b) 1218 = decide (3 ≤ count1216 b) := rfl
theorem meaning1219 (b : Nat → Bool) : literal (valuationOf b) 1219 = decide (4 ≤ count1216 b) := rfl
theorem meaning1223 (b : Nat → Bool) : literal (valuationOf b) 1223 = decide (2 ≤ count1222 b) := rfl
theorem meaning1224 (b : Nat → Bool) : literal (valuationOf b) 1224 = decide (3 ≤ count1222 b) := rfl
theorem meaning1225 (b : Nat → Bool) : literal (valuationOf b) 1225 = decide (4 ≤ count1222 b) := rfl
theorem meaning1226 (b : Nat → Bool) : literal (valuationOf b) 1226 = decide (5 ≤ count1222 b) := rfl
theorem meaning1233 (b : Nat → Bool) : literal (valuationOf b) 1233 = decide (1 ≤ count1233 b) := rfl
theorem meaning1234 (b : Nat → Bool) : literal (valuationOf b) 1234 = decide (2 ≤ count1233 b) := rfl
theorem meaning1235 (b : Nat → Bool) : literal (valuationOf b) 1235 = decide (1 ≤ count1235 b) := rfl
theorem meaning1236 (b : Nat → Bool) : literal (valuationOf b) 1236 = decide (2 ≤ count1235 b) := rfl
theorem meaning1238 (b : Nat → Bool) : literal (valuationOf b) 1238 = decide (1 ≤ count1238 b) := rfl
theorem meaning1239 (b : Nat → Bool) : literal (valuationOf b) 1239 = decide (2 ≤ count1238 b) := rfl
theorem meaning1240 (b : Nat → Bool) : literal (valuationOf b) 1240 = decide (1 ≤ count1240 b) := rfl
theorem meaning1241 (b : Nat → Bool) : literal (valuationOf b) 1241 = decide (2 ≤ count1240 b) := rfl
theorem meaning1243 (b : Nat → Bool) : literal (valuationOf b) 1243 = decide (1 ≤ count1243 b) := rfl
theorem meaning1244 (b : Nat → Bool) : literal (valuationOf b) 1244 = decide (2 ≤ count1243 b) := rfl
theorem meaning1245 (b : Nat → Bool) : literal (valuationOf b) 1245 = decide (3 ≤ count1243 b) := rfl
theorem meaning1249 (b : Nat → Bool) : literal (valuationOf b) 1249 = decide (1 ≤ count1249 b) := rfl
theorem meaning1251 (b : Nat → Bool) : literal (valuationOf b) 1251 = decide (1 ≤ count1251 b) := rfl
theorem meaning1252 (b : Nat → Bool) : literal (valuationOf b) 1252 = decide (2 ≤ count1251 b) := rfl
theorem meaning1254 (b : Nat → Bool) : literal (valuationOf b) 1254 = decide (1 ≤ count1254 b) := rfl
theorem meaning1256 (b : Nat → Bool) : literal (valuationOf b) 1256 = decide (1 ≤ count1256 b) := rfl
theorem meaning1258 (b : Nat → Bool) : literal (valuationOf b) 1258 = decide (1 ≤ count1258 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (1 ≤ count1262 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (2 ≤ count1262 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (3 ≤ count1262 b) := rfl
theorem meaning1269 (b : Nat → Bool) : literal (valuationOf b) 1269 = decide (1 ≤ count1269 b) := rfl
theorem meaning1270 (b : Nat → Bool) : literal (valuationOf b) 1270 = decide (2 ≤ count1269 b) := rfl
theorem meaning1271 (b : Nat → Bool) : literal (valuationOf b) 1271 = decide (3 ≤ count1269 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (4 ≤ count1269 b) := rfl
theorem meaning1284 (b : Nat → Bool) : literal (valuationOf b) 1284 = decide (5 ≤ count1280 b) := rfl
theorem meaning1285 (b : Nat → Bool) : literal (valuationOf b) 1285 = decide (6 ≤ count1280 b) := rfl
theorem meaning1286 (b : Nat → Bool) : literal (valuationOf b) 1286 = decide (7 ≤ count1280 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (1 ≤ count1296 b) := rfl
theorem meaning1298 (b : Nat → Bool) : literal (valuationOf b) 1298 = decide (1 ≤ count1298 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (1 ≤ count1301 b) := rfl
theorem meaning1307 (b : Nat → Bool) : literal (valuationOf b) 1307 = decide (1 ≤ count1307 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (1 ≤ count1309 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (1 ≤ count1312 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (1 ≤ count1314 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (2 ≤ count1314 b) := rfl
theorem meaning1316 (b : Nat → Bool) : literal (valuationOf b) 1316 = decide (1 ≤ count1316 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (2 ≤ count1316 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (3 ≤ count1316 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (1 ≤ count1320 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (2 ≤ count1320 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (3 ≤ count1320 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (2 ≤ count1327 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (3 ≤ count1327 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (1 ≤ count1338 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (2 ≤ count1338 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (1 ≤ count1340 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (2 ≤ count1340 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (1 ≤ count1343 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (2 ≤ count1343 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (1 ≤ count1345 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (2 ≤ count1345 b) := rfl
theorem meaning1348 (b : Nat → Bool) : literal (valuationOf b) 1348 = decide (1 ≤ count1348 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (2 ≤ count1348 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (3 ≤ count1348 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (1 ≤ count1356 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (1 ≤ count1359 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (1 ≤ count1363 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (1 ≤ count1367 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (2 ≤ count1374 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (3 ≤ count1374 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (4 ≤ count1374 b) := rfl
theorem meaning1388 (b : Nat → Bool) : literal (valuationOf b) 1388 = decide (4 ≤ count1385 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (5 ≤ count1385 b) := rfl
theorem meaning1390 (b : Nat → Bool) : literal (valuationOf b) 1390 = decide (6 ≤ count1385 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (11 ≤ count1396 b) := rfl
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
end Snake9.Regrowth.E112234
