import E112149Data
namespace Snake9.Regrowth.E112149
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 99 then (if i < 49 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (2 : Vertex)))) else (if i < 4 then decide (InPath q (4 : Vertex)) else (if i < 5 then decide (InPath q (5 : Vertex)) else decide (InPath q (6 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (8 : Vertex)) else (if i < 8 then decide (InPath q (12 : Vertex)) else decide (InPath q (14 : Vertex)))) else (if i < 10 then decide (InPath q (21 : Vertex)) else (if i < 11 then decide (InPath q (22 : Vertex)) else decide (InPath q (23 : Vertex)))))) else (if i < 18 then (if i < 15 then (if i < 13 then decide (InPath q (106 : Vertex)) else (if i < 14 then decide (InPath q (160 : Vertex)) else decide (InPath q (162 : Vertex)))) else (if i < 16 then decide (InPath q (164 : Vertex)) else (if i < 17 then decide (InPath q (165 : Vertex)) else decide (InPath q (166 : Vertex))))) else (if i < 21 then (if i < 19 then decide (InPath q (168 : Vertex)) else (if i < 20 then decide (InPath q (170 : Vertex)) else decide (InPath q (171 : Vertex)))) else (if i < 22 then decide (InPath q (172 : Vertex)) else (if i < 23 then decide (InPath q (174 : Vertex)) else decide (InPath q (181 : Vertex))))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then decide (InPath q (182 : Vertex)) else (if i < 26 then decide (InPath q (183 : Vertex)) else decide (InPath q (184 : Vertex)))) else (if i < 28 then decide (InPath q (185 : Vertex)) else (if i < 29 then decide (InPath q (187 : Vertex)) else decide (InPath q (189 : Vertex))))) else (if i < 33 then (if i < 31 then decide (InPath q (191 : Vertex)) else (if i < 32 then decide (InPath q (226 : Vertex)) else decide (InPath q (227 : Vertex)))) else (if i < 34 then decide (InPath q (229 : Vertex)) else (if i < 35 then decide (InPath q (234 : Vertex)) else decide (InPath q (235 : Vertex)))))) else (if i < 42 then (if i < 39 then (if i < 37 then decide (InPath q (237 : Vertex)) else (if i < 38 then decide (InPath q (239 : Vertex)) else decide (InPath q (240 : Vertex)))) else (if i < 40 then decide (InPath q (241 : Vertex)) else (if i < 41 then decide (InPath q (243 : Vertex)) else decide (InPath q (244 : Vertex))))) else (if i < 45 then (if i < 43 then decide (InPath q (248 : Vertex)) else (if i < 44 then decide (InPath q (252 : Vertex)) else decide (InPath q (254 : Vertex)))) else (if i < 47 then (if i < 46 then decide (InPath q (255 : Vertex)) else decide (InPath q (258 : Vertex))) else (if i < 48 then decide (InPath q (259 : Vertex)) else decide (InPath q (260 : Vertex)))))))) else (if i < 74 then (if i < 61 then (if i < 55 then (if i < 52 then (if i < 50 then decide (InPath q (261 : Vertex)) else (if i < 51 then decide (InPath q (266 : Vertex)) else decide (InPath q (269 : Vertex)))) else (if i < 53 then decide (InPath q (271 : Vertex)) else (if i < 54 then decide (InPath q (272 : Vertex)) else decide (InPath q (273 : Vertex))))) else (if i < 58 then (if i < 56 then decide (InPath q (275 : Vertex)) else (if i < 57 then decide (InPath q (280 : Vertex)) else decide (InPath q (284 : Vertex)))) else (if i < 59 then decide (InPath q (286 : Vertex)) else (if i < 60 then decide (InPath q (287 : Vertex)) else decide (InPath q (354 : Vertex)))))) else (if i < 67 then (if i < 64 then (if i < 62 then decide (InPath q (355 : Vertex)) else (if i < 63 then decide (InPath q (362 : Vertex)) else decide (InPath q (368 : Vertex)))) else (if i < 65 then decide (InPath q (369 : Vertex)) else (if i < 66 then decide (InPath q (371 : Vertex)) else decide (InPath q (376 : Vertex))))) else (if i < 70 then (if i < 68 then decide (InPath q (380 : Vertex)) else (if i < 69 then decide (InPath q (382 : Vertex)) else decide (InPath q (383 : Vertex)))) else (if i < 72 then (if i < 71 then decide (InPath q (384 : Vertex)) else decide (InPath q (388 : Vertex))) else (if i < 73 then decide (InPath q (394 : Vertex)) else decide (InPath q (396 : Vertex))))))) else (if i < 86 then (if i < 80 then (if i < 77 then (if i < 75 then decide (InPath q (398 : Vertex)) else (if i < 76 then decide (InPath q (420 : Vertex)) else decide (InPath q (426 : Vertex)))) else (if i < 78 then decide (InPath q (427 : Vertex)) else (if i < 79 then decide (InPath q (429 : Vertex)) else decide (InPath q (431 : Vertex))))) else (if i < 83 then (if i < 81 then decide (InPath q (436 : Vertex)) else (if i < 82 then decide (InPath q (440 : Vertex)) else decide (InPath q (444 : Vertex)))) else (if i < 84 then decide (InPath q (446 : Vertex)) else (if i < 85 then decide (InPath q (447 : Vertex)) else decide (InPath q (450 : Vertex)))))) else (if i < 92 then (if i < 89 then (if i < 87 then decide (InPath q (451 : Vertex)) else (if i < 88 then decide (InPath q (452 : Vertex)) else decide (InPath q (453 : Vertex)))) else (if i < 90 then decide (InPath q (458 : Vertex)) else (if i < 91 then decide (InPath q (459 : Vertex)) else decide (InPath q (461 : Vertex))))) else (if i < 95 then (if i < 93 then decide (InPath q (463 : Vertex)) else (if i < 94 then decide (InPath q (464 : Vertex)) else decide (InPath q (465 : Vertex)))) else (if i < 97 then (if i < 96 then decide (InPath q (467 : Vertex)) else decide (InPath q (472 : Vertex))) else (if i < 98 then decide (InPath q (476 : Vertex)) else decide (InPath q (478 : Vertex))))))))) else (if i < 149 then (if i < 124 then (if i < 111 then (if i < 105 then (if i < 102 then (if i < 100 then decide (InPath q (479 : Vertex)) else (if i < 101 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (2 : Vertex)))) else (if i < 103 then decide (BallClauseLogic.Endpoint q (4 : Vertex)) else (if i < 104 then decide (BallClauseLogic.Endpoint q (5 : Vertex)) else decide (BallClauseLogic.Endpoint q (6 : Vertex))))) else (if i < 108 then (if i < 106 then decide (BallClauseLogic.Endpoint q (8 : Vertex)) else (if i < 107 then decide (BallClauseLogic.Endpoint q (12 : Vertex)) else decide (BallClauseLogic.Endpoint q (14 : Vertex)))) else (if i < 109 then decide (BallClauseLogic.Endpoint q (21 : Vertex)) else (if i < 110 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (23 : Vertex)))))) else (if i < 117 then (if i < 114 then (if i < 112 then decide (BallClauseLogic.Endpoint q (106 : Vertex)) else (if i < 113 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (162 : Vertex)))) else (if i < 115 then decide (BallClauseLogic.Endpoint q (164 : Vertex)) else (if i < 116 then decide (BallClauseLogic.Endpoint q (165 : Vertex)) else decide (BallClauseLogic.Endpoint q (166 : Vertex))))) else (if i < 120 then (if i < 118 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else (if i < 119 then decide (BallClauseLogic.Endpoint q (170 : Vertex)) else decide (BallClauseLogic.Endpoint q (171 : Vertex)))) else (if i < 122 then (if i < 121 then decide (BallClauseLogic.Endpoint q (172 : Vertex)) else decide (BallClauseLogic.Endpoint q (174 : Vertex))) else (if i < 123 then decide (BallClauseLogic.Endpoint q (181 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex))))))) else (if i < 136 then (if i < 130 then (if i < 127 then (if i < 125 then decide (BallClauseLogic.Endpoint q (183 : Vertex)) else (if i < 126 then decide (BallClauseLogic.Endpoint q (184 : Vertex)) else decide (BallClauseLogic.Endpoint q (185 : Vertex)))) else (if i < 128 then decide (BallClauseLogic.Endpoint q (187 : Vertex)) else (if i < 129 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (191 : Vertex))))) else (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (227 : Vertex)) else decide (BallClauseLogic.Endpoint q (229 : Vertex)))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (234 : Vertex)) else (if i < 135 then decide (BallClauseLogic.Endpoint q (235 : Vertex)) else decide (BallClauseLogic.Endpoint q (237 : Vertex)))))) else (if i < 142 then (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (239 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (240 : Vertex)) else decide (BallClauseLogic.Endpoint q (241 : Vertex)))) else (if i < 140 then decide (BallClauseLogic.Endpoint q (243 : Vertex)) else (if i < 141 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (248 : Vertex))))) else (if i < 145 then (if i < 143 then decide (BallClauseLogic.Endpoint q (252 : Vertex)) else (if i < 144 then decide (BallClauseLogic.Endpoint q (254 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex)))) else (if i < 147 then (if i < 146 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else decide (BallClauseLogic.Endpoint q (259 : Vertex))) else (if i < 148 then decide (BallClauseLogic.Endpoint q (260 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex)))))))) else (if i < 174 then (if i < 161 then (if i < 155 then (if i < 152 then (if i < 150 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else (if i < 151 then decide (BallClauseLogic.Endpoint q (269 : Vertex)) else decide (BallClauseLogic.Endpoint q (271 : Vertex)))) else (if i < 153 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (273 : Vertex)) else decide (BallClauseLogic.Endpoint q (275 : Vertex))))) else (if i < 158 then (if i < 156 then decide (BallClauseLogic.Endpoint q (280 : Vertex)) else (if i < 157 then decide (BallClauseLogic.Endpoint q (284 : Vertex)) else decide (BallClauseLogic.Endpoint q (286 : Vertex)))) else (if i < 159 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else (if i < 160 then decide (BallClauseLogic.Endpoint q (354 : Vertex)) else decide (BallClauseLogic.Endpoint q (355 : Vertex)))))) else (if i < 167 then (if i < 164 then (if i < 162 then decide (BallClauseLogic.Endpoint q (362 : Vertex)) else (if i < 163 then decide (BallClauseLogic.Endpoint q (368 : Vertex)) else decide (BallClauseLogic.Endpoint q (369 : Vertex)))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (371 : Vertex)) else (if i < 166 then decide (BallClauseLogic.Endpoint q (376 : Vertex)) else decide (BallClauseLogic.Endpoint q (380 : Vertex))))) else (if i < 170 then (if i < 168 then decide (BallClauseLogic.Endpoint q (382 : Vertex)) else (if i < 169 then decide (BallClauseLogic.Endpoint q (383 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex)))) else (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (388 : Vertex)) else decide (BallClauseLogic.Endpoint q (394 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (396 : Vertex)) else decide (BallClauseLogic.Endpoint q (398 : Vertex))))))) else (if i < 186 then (if i < 180 then (if i < 177 then (if i < 175 then decide (BallClauseLogic.Endpoint q (420 : Vertex)) else (if i < 176 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex)))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (429 : Vertex)) else (if i < 179 then decide (BallClauseLogic.Endpoint q (431 : Vertex)) else decide (BallClauseLogic.Endpoint q (436 : Vertex))))) else (if i < 183 then (if i < 181 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else (if i < 182 then decide (BallClauseLogic.Endpoint q (444 : Vertex)) else decide (BallClauseLogic.Endpoint q (446 : Vertex)))) else (if i < 184 then decide (BallClauseLogic.Endpoint q (447 : Vertex)) else (if i < 185 then decide (BallClauseLogic.Endpoint q (450 : Vertex)) else decide (BallClauseLogic.Endpoint q (451 : Vertex)))))) else (if i < 192 then (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (452 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else decide (BallClauseLogic.Endpoint q (458 : Vertex)))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (459 : Vertex)) else (if i < 191 then decide (BallClauseLogic.Endpoint q (461 : Vertex)) else decide (BallClauseLogic.Endpoint q (463 : Vertex))))) else (if i < 195 then (if i < 193 then decide (BallClauseLogic.Endpoint q (464 : Vertex)) else (if i < 194 then decide (BallClauseLogic.Endpoint q (465 : Vertex)) else decide (BallClauseLogic.Endpoint q (467 : Vertex)))) else (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (472 : Vertex)) else decide (BallClauseLogic.Endpoint q (476 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (478 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count199 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count201 (b : Nat → Bool) : Nat := countLit b [100, 101, 102]
def count203 (b : Nat → Bool) : Nat := countLit b [104, 105]
def count205 (b : Nat → Bool) : Nat := countLit b [103, 104, 105]
def count207 (b : Nat → Bool) : Nat := countLit b [100, 101, 102, 103, 104, 105]
def count209 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count211 (b : Nat → Bool) : Nat := countLit b [106, 107, 108]
def count213 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count215 (b : Nat → Bool) : Nat := countLit b [109, 110, 111]
def count217 (b : Nat → Bool) : Nat := countLit b [106, 107, 108, 109, 110, 111]
def count219 (b : Nat → Bool) : Nat := countLit b [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
def count221 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count223 (b : Nat → Bool) : Nat := countLit b [112, 113, 114]
def count225 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count227 (b : Nat → Bool) : Nat := countLit b [115, 116, 117]
def count229 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117]
def count231 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count233 (b : Nat → Bool) : Nat := countLit b [118, 119, 120]
def count235 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count237 (b : Nat → Bool) : Nat := countLit b [121, 122, 123]
def count239 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123]
def count241 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
def count243 (b : Nat → Bool) : Nat := countLit b [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
def count245 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count247 (b : Nat → Bool) : Nat := countLit b [124, 125, 126]
def count249 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [127, 128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [130, 131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count273 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count283 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count285 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148]
def count287 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145, 146, 147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
def count293 (b : Nat → Bool) : Nat := countLit b [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
def count295 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [149, 150, 151]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [152, 153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154]
def count305 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [155, 156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count311 (b : Nat → Bool) : Nat := countLit b [158, 159, 160]
def count313 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 159, 160]
def count315 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [161, 162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count323 (b : Nat → Bool) : Nat := countLit b [164, 165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164, 165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count329 (b : Nat → Bool) : Nat := countLit b [167, 169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count333 (b : Nat → Bool) : Nat := countLit b [171, 172, 173]
def count335 (b : Nat → Bool) : Nat := countLit b [167, 169, 170, 171, 172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]
def count341 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [174, 175, 176]
def count345 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count347 (b : Nat → Bool) : Nat := countLit b [177, 178, 179]
def count349 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179]
def count351 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [180, 181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count357 (b : Nat → Bool) : Nat := countLit b [183, 184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count365 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count369 (b : Nat → Bool) : Nat := countLit b [189, 190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count375 (b : Nat → Bool) : Nat := countLit b [192, 193, 194]
def count377 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count379 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198]
def count383 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]
def count391 (b : Nat → Bool) : Nat := countLit b [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]
def count393 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count395 (b : Nat → Bool) : Nat := countLit b [1, 4, 5]
def count398 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count400 (b : Nat → Bool) : Nat := countLit b [7, 11, 12]
def count403 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 7, 11, 12]
def count409 (b : Nat → Bool) : Nat := countLit b [16, 17]
def count411 (b : Nat → Bool) : Nat := countLit b [13, 16, 17]
def count414 (b : Nat → Bool) : Nat := countLit b [21, 25]
def count416 (b : Nat → Bool) : Nat := countLit b [19, 21, 25]
def count419 (b : Nat → Bool) : Nat := countLit b [13, 16, 17, 19, 21, 25]
def count425 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 7, 11, 12, 13, 16, 17, 19, 21, 25]
def count437 (b : Nat → Bool) : Nat := countLit b [28, 29]
def count439 (b : Nat → Bool) : Nat := countLit b [26, 28, 29]
def count442 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count444 (b : Nat → Bool) : Nat := countLit b [31, 35, 36]
def count447 (b : Nat → Bool) : Nat := countLit b [26, 28, 29, 31, 35, 36]
def count453 (b : Nat → Bool) : Nat := countLit b [40, 43]
def count455 (b : Nat → Bool) : Nat := countLit b [38, 40, 43]
def count458 (b : Nat → Bool) : Nat := countLit b [45, 46]
def count460 (b : Nat → Bool) : Nat := countLit b [48, 51]
def count462 (b : Nat → Bool) : Nat := countLit b [45, 46, 48, 51]
def count466 (b : Nat → Bool) : Nat := countLit b [38, 40, 43, 45, 46, 48, 51]
def count473 (b : Nat → Bool) : Nat := countLit b [26, 28, 29, 31, 35, 36, 38, 40, 43, 45, 46, 48, 51]
def count486 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 7, 11, 12, 13, 16, 17, 19, 21, 25, 26, 28, 29, 31, 35, 36, 38, 40, 43, 45, 46, 48, 51]
def count511 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count513 (b : Nat → Bool) : Nat := countLit b [53, 55, 57]
def count516 (b : Nat → Bool) : Nat := countLit b [60, 63]
def count518 (b : Nat → Bool) : Nat := countLit b [59, 60, 63]
def count521 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 59, 60, 63]
def count527 (b : Nat → Bool) : Nat := countLit b [67, 69]
def count529 (b : Nat → Bool) : Nat := countLit b [65, 67, 69]
def count532 (b : Nat → Bool) : Nat := countLit b [72, 73]
def count534 (b : Nat → Bool) : Nat := countLit b [70, 72, 73]
def count537 (b : Nat → Bool) : Nat := countLit b [65, 67, 69, 70, 72, 73]
def count543 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 59, 60, 63, 65, 67, 69, 70, 72, 73]
def count555 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count557 (b : Nat → Bool) : Nat := countLit b [75, 77, 78]
def count560 (b : Nat → Bool) : Nat := countLit b [84, 85]
def count562 (b : Nat → Bool) : Nat := countLit b [82, 84, 85]
def count565 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 82, 84, 85]
def count571 (b : Nat → Bool) : Nat := countLit b [90, 91]
def count573 (b : Nat → Bool) : Nat := countLit b [87, 90, 91]
def count576 (b : Nat → Bool) : Nat := countLit b [93, 95]
def count578 (b : Nat → Bool) : Nat := countLit b [97, 99]
def count580 (b : Nat → Bool) : Nat := countLit b [93, 95, 97, 99]
def count584 (b : Nat → Bool) : Nat := countLit b [87, 90, 91, 93, 95, 97, 99]
def count591 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 82, 84, 85, 87, 90, 91, 93, 95, 97, 99]
def count604 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 59, 60, 63, 65, 67, 69, 70, 72, 73, 75, 77, 78, 82, 84, 85, 87, 90, 91, 93, 95, 97, 99]
def count629 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 7, 11, 12, 13, 16, 17, 19, 21, 25, 26, 28, 29, 31, 35, 36, 38, 40, 43, 45, 46, 48, 51, 53, 55, 57, 59, 60, 63, 65, 67, 69, 70, 72, 73, 75, 77, 78, 82, 84, 85, 87, 90, 91, 93, 95, 97, 99]
def count671 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count673 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5]
def count676 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count678 (b : Nat → Bool) : Nat := countLit b [-7, -11, -12]
def count681 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -7, -11, -12]
def count687 (b : Nat → Bool) : Nat := countLit b [-16, -17]
def count689 (b : Nat → Bool) : Nat := countLit b [-13, -16, -17]
def count692 (b : Nat → Bool) : Nat := countLit b [-21, -25]
def count694 (b : Nat → Bool) : Nat := countLit b [-19, -21, -25]
def count697 (b : Nat → Bool) : Nat := countLit b [-13, -16, -17, -19, -21, -25]
def count703 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -7, -11, -12, -13, -16, -17, -19, -21, -25]
def count713 (b : Nat → Bool) : Nat := countLit b [-28, -29]
def count715 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29]
def count718 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count720 (b : Nat → Bool) : Nat := countLit b [-31, -35, -36]
def count723 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29, -31, -35, -36]
def count729 (b : Nat → Bool) : Nat := countLit b [-40, -43]
def count731 (b : Nat → Bool) : Nat := countLit b [-38, -40, -43]
def count734 (b : Nat → Bool) : Nat := countLit b [-45, -46]
def count736 (b : Nat → Bool) : Nat := countLit b [-48, -51]
def count738 (b : Nat → Bool) : Nat := countLit b [-45, -46, -48, -51]
def count742 (b : Nat → Bool) : Nat := countLit b [-38, -40, -43, -45, -46, -48, -51]
def count749 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29, -31, -35, -36, -38, -40, -43, -45, -46, -48, -51]
def count759 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -7, -11, -12, -13, -16, -17, -19, -21, -25, -26, -28, -29, -31, -35, -36, -38, -40, -43, -45, -46, -48, -51]
def count769 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count771 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57]
def count774 (b : Nat → Bool) : Nat := countLit b [-60, -63]
def count776 (b : Nat → Bool) : Nat := countLit b [-59, -60, -63]
def count779 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -59, -60, -63]
def count785 (b : Nat → Bool) : Nat := countLit b [-67, -69]
def count787 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69]
def count790 (b : Nat → Bool) : Nat := countLit b [-72, -73]
def count792 (b : Nat → Bool) : Nat := countLit b [-70, -72, -73]
def count795 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69, -70, -72, -73]
def count801 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -59, -60, -63, -65, -67, -69, -70, -72, -73]
def count811 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count813 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78]
def count816 (b : Nat → Bool) : Nat := countLit b [-84, -85]
def count818 (b : Nat → Bool) : Nat := countLit b [-82, -84, -85]
def count821 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -82, -84, -85]
def count827 (b : Nat → Bool) : Nat := countLit b [-90, -91]
def count829 (b : Nat → Bool) : Nat := countLit b [-87, -90, -91]
def count832 (b : Nat → Bool) : Nat := countLit b [-93, -95]
def count834 (b : Nat → Bool) : Nat := countLit b [-97, -99]
def count836 (b : Nat → Bool) : Nat := countLit b [-93, -95, -97, -99]
def count840 (b : Nat → Bool) : Nat := countLit b [-87, -90, -91, -93, -95, -97, -99]
def count847 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -82, -84, -85, -87, -90, -91, -93, -95, -97, -99]
def count857 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -59, -60, -63, -65, -67, -69, -70, -72, -73, -75, -77, -78, -82, -84, -85, -87, -90, -91, -93, -95, -97, -99]
def count867 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -7, -11, -12, -13, -16, -17, -19, -21, -25, -26, -28, -29, -31, -35, -36, -38, -40, -43, -45, -46, -48, -51, -53, -55, -57, -59, -60, -63, -65, -67, -69, -70, -72, -73, -75, -77, -78, -82, -84, -85, -87, -90, -91, -93, -95, -97, -99]
def count877 (b : Nat → Bool) : Nat := countLit b [3, 6]
def count879 (b : Nat → Bool) : Nat := countLit b [2, 3, 6]
def count882 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count884 (b : Nat → Bool) : Nat := countLit b [8, 9, 10]
def count887 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 8, 9, 10]
def count893 (b : Nat → Bool) : Nat := countLit b [15, 18]
def count895 (b : Nat → Bool) : Nat := countLit b [14, 15, 18]
def count898 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count900 (b : Nat → Bool) : Nat := countLit b [20, 22, 23]
def count903 (b : Nat → Bool) : Nat := countLit b [14, 15, 18, 20, 22, 23]
def count909 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 8, 9, 10, 14, 15, 18, 20, 22, 23]
def count921 (b : Nat → Bool) : Nat := countLit b [27, 30]
def count923 (b : Nat → Bool) : Nat := countLit b [24, 27, 30]
def count926 (b : Nat → Bool) : Nat := countLit b [33, 34]
def count928 (b : Nat → Bool) : Nat := countLit b [32, 33, 34]
def count931 (b : Nat → Bool) : Nat := countLit b [24, 27, 30, 32, 33, 34]
def count937 (b : Nat → Bool) : Nat := countLit b [39, 41]
def count939 (b : Nat → Bool) : Nat := countLit b [37, 39, 41]
def count942 (b : Nat → Bool) : Nat := countLit b [44, 47]
def count944 (b : Nat → Bool) : Nat := countLit b [42, 44, 47]
def count947 (b : Nat → Bool) : Nat := countLit b [37, 39, 41, 42, 44, 47]
def count953 (b : Nat → Bool) : Nat := countLit b [24, 27, 30, 32, 33, 34, 37, 39, 41, 42, 44, 47]
def count965 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 8, 9, 10, 14, 15, 18, 20, 22, 23, 24, 27, 30, 32, 33, 34, 37, 39, 41, 42, 44, 47]
def count989 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count991 (b : Nat → Bool) : Nat := countLit b [49, 50, 52]
def count994 (b : Nat → Bool) : Nat := countLit b [56, 58]
def count996 (b : Nat → Bool) : Nat := countLit b [54, 56, 58]
def count999 (b : Nat → Bool) : Nat := countLit b [49, 50, 52, 54, 56, 58]
def count1005 (b : Nat → Bool) : Nat := countLit b [62, 64]
def count1007 (b : Nat → Bool) : Nat := countLit b [61, 62, 64]
def count1010 (b : Nat → Bool) : Nat := countLit b [68, 71]
def count1012 (b : Nat → Bool) : Nat := countLit b [66, 68, 71]
def count1015 (b : Nat → Bool) : Nat := countLit b [61, 62, 64, 66, 68, 71]
def count1021 (b : Nat → Bool) : Nat := countLit b [49, 50, 52, 54, 56, 58, 61, 62, 64, 66, 68, 71]
def count1033 (b : Nat → Bool) : Nat := countLit b [76, 79]
def count1035 (b : Nat → Bool) : Nat := countLit b [74, 76, 79]
def count1038 (b : Nat → Bool) : Nat := countLit b [81, 83]
def count1040 (b : Nat → Bool) : Nat := countLit b [80, 81, 83]
def count1043 (b : Nat → Bool) : Nat := countLit b [74, 76, 79, 80, 81, 83]
def count1049 (b : Nat → Bool) : Nat := countLit b [88, 89]
def count1051 (b : Nat → Bool) : Nat := countLit b [86, 88, 89]
def count1054 (b : Nat → Bool) : Nat := countLit b [92, 94]
def count1056 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count1058 (b : Nat → Bool) : Nat := countLit b [92, 94, 96, 98]
def count1062 (b : Nat → Bool) : Nat := countLit b [86, 88, 89, 92, 94, 96, 98]
def count1069 (b : Nat → Bool) : Nat := countLit b [74, 76, 79, 80, 81, 83, 86, 88, 89, 92, 94, 96, 98]
def count1082 (b : Nat → Bool) : Nat := countLit b [49, 50, 52, 54, 56, 58, 61, 62, 64, 66, 68, 71, 74, 76, 79, 80, 81, 83, 86, 88, 89, 92, 94, 96, 98]
def count1107 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 8, 9, 10, 14, 15, 18, 20, 22, 23, 24, 27, 30, 32, 33, 34, 37, 39, 41, 42, 44, 47, 49, 50, 52, 54, 56, 58, 61, 62, 64, 66, 68, 71, 74, 76, 79, 80, 81, 83, 86, 88, 89, 92, 94, 96, 98]
def count1149 (b : Nat → Bool) : Nat := countLit b [-3, -6]
def count1151 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6]
def count1154 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count1156 (b : Nat → Bool) : Nat := countLit b [-8, -9, -10]
def count1159 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -8, -9, -10]
def count1165 (b : Nat → Bool) : Nat := countLit b [-15, -18]
def count1167 (b : Nat → Bool) : Nat := countLit b [-14, -15, -18]
def count1170 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count1172 (b : Nat → Bool) : Nat := countLit b [-20, -22, -23]
def count1175 (b : Nat → Bool) : Nat := countLit b [-14, -15, -18, -20, -22, -23]
def count1181 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23]
def count1190 (b : Nat → Bool) : Nat := countLit b [-27, -30]
def count1192 (b : Nat → Bool) : Nat := countLit b [-24, -27, -30]
def count1195 (b : Nat → Bool) : Nat := countLit b [-33, -34]
def count1197 (b : Nat → Bool) : Nat := countLit b [-32, -33, -34]
def count1200 (b : Nat → Bool) : Nat := countLit b [-24, -27, -30, -32, -33, -34]
def count1206 (b : Nat → Bool) : Nat := countLit b [-39, -41]
def count1208 (b : Nat → Bool) : Nat := countLit b [-37, -39, -41]
def count1211 (b : Nat → Bool) : Nat := countLit b [-44, -47]
def count1213 (b : Nat → Bool) : Nat := countLit b [-42, -44, -47]
def count1216 (b : Nat → Bool) : Nat := countLit b [-37, -39, -41, -42, -44, -47]
def count1222 (b : Nat → Bool) : Nat := countLit b [-24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]
def count1231 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23, -24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47]
def count1240 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count1242 (b : Nat → Bool) : Nat := countLit b [-49, -50, -52]
def count1245 (b : Nat → Bool) : Nat := countLit b [-56, -58]
def count1247 (b : Nat → Bool) : Nat := countLit b [-54, -56, -58]
def count1250 (b : Nat → Bool) : Nat := countLit b [-49, -50, -52, -54, -56, -58]
def count1256 (b : Nat → Bool) : Nat := countLit b [-62, -64]
def count1258 (b : Nat → Bool) : Nat := countLit b [-61, -62, -64]
def count1261 (b : Nat → Bool) : Nat := countLit b [-68, -71]
def count1263 (b : Nat → Bool) : Nat := countLit b [-66, -68, -71]
def count1266 (b : Nat → Bool) : Nat := countLit b [-61, -62, -64, -66, -68, -71]
def count1272 (b : Nat → Bool) : Nat := countLit b [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71]
def count1281 (b : Nat → Bool) : Nat := countLit b [-76, -79]
def count1283 (b : Nat → Bool) : Nat := countLit b [-74, -76, -79]
def count1286 (b : Nat → Bool) : Nat := countLit b [-81, -83]
def count1288 (b : Nat → Bool) : Nat := countLit b [-80, -81, -83]
def count1291 (b : Nat → Bool) : Nat := countLit b [-74, -76, -79, -80, -81, -83]
def count1297 (b : Nat → Bool) : Nat := countLit b [-88, -89]
def count1299 (b : Nat → Bool) : Nat := countLit b [-86, -88, -89]
def count1302 (b : Nat → Bool) : Nat := countLit b [-92, -94]
def count1304 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count1306 (b : Nat → Bool) : Nat := countLit b [-92, -94, -96, -98]
def count1310 (b : Nat → Bool) : Nat := countLit b [-86, -88, -89, -92, -94, -96, -98]
def count1317 (b : Nat → Bool) : Nat := countLit b [-74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]
def count1326 (b : Nat → Bool) : Nat := countLit b [-49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71, -74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]
def count1335 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -8, -9, -10, -14, -15, -18, -20, -22, -23, -24, -27, -30, -32, -33, -34, -37, -39, -41, -42, -44, -47, -49, -50, -52, -54, -56, -58, -61, -62, -64, -66, -68, -71, -74, -76, -79, -80, -81, -83, -86, -88, -89, -92, -94, -96, -98]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 672 then (if i < 336 then (if i < 168 then (if i < 84 then (if i < 42 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 7 then (if i < 6 then b 5 else b 6) else (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)))) else (if i < 15 then (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else (if i < 14 then b 13 else b 14))) else (if i < 18 then (if i < 16 then b 15 else (if i < 17 then b 16 else b 17)) else (if i < 19 then b 18 else (if i < 20 then b 19 else b 20))))) else (if i < 31 then (if i < 26 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else (if i < 25 then b 24 else b 25))) else (if i < 28 then (if i < 27 then b 26 else b 27) else (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)))) else (if i < 36 then (if i < 33 then (if i < 32 then b 31 else b 32) else (if i < 34 then b 33 else (if i < 35 then b 34 else b 35))) else (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)))))) else (if i < 63 then (if i < 52 then (if i < 47 then (if i < 44 then (if i < 43 then b 42 else b 43) else (if i < 45 then b 44 else (if i < 46 then b 45 else b 46))) else (if i < 49 then (if i < 48 then b 47 else b 48) else (if i < 50 then b 49 else (if i < 51 then b 50 else b 51)))) else (if i < 57 then (if i < 54 then (if i < 53 then b 52 else b 53) else (if i < 55 then b 54 else (if i < 56 then b 55 else b 56))) else (if i < 60 then (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)) else (if i < 61 then b 60 else (if i < 62 then b 61 else b 62))))) else (if i < 73 then (if i < 68 then (if i < 65 then (if i < 64 then b 63 else b 64) else (if i < 66 then b 65 else (if i < 67 then b 66 else b 67))) else (if i < 70 then (if i < 69 then b 68 else b 69) else (if i < 71 then b 70 else (if i < 72 then b 71 else b 72)))) else (if i < 78 then (if i < 75 then (if i < 74 then b 73 else b 74) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77))) else (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))))))) else (if i < 126 then (if i < 105 then (if i < 94 then (if i < 89 then (if i < 86 then (if i < 85 then b 84 else b 85) else (if i < 87 then b 86 else (if i < 88 then b 87 else b 88))) else (if i < 91 then (if i < 90 then b 89 else b 90) else (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)))) else (if i < 99 then (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else (if i < 98 then b 97 else b 98))) else (if i < 102 then (if i < 100 then b 99 else (if i < 101 then b 100 else b 101)) else (if i < 103 then b 102 else (if i < 104 then b 103 else b 104))))) else (if i < 115 then (if i < 110 then (if i < 107 then (if i < 106 then b 105 else b 106) else (if i < 108 then b 107 else (if i < 109 then b 108 else b 109))) else (if i < 112 then (if i < 111 then b 110 else b 111) else (if i < 113 then b 112 else (if i < 114 then b 113 else b 114)))) else (if i < 120 then (if i < 117 then (if i < 116 then b 115 else b 116) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119))) else (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)))))) else (if i < 147 then (if i < 136 then (if i < 131 then (if i < 128 then (if i < 127 then b 126 else b 127) else (if i < 129 then b 128 else (if i < 130 then b 129 else b 130))) else (if i < 133 then (if i < 132 then b 131 else b 132) else (if i < 134 then b 133 else (if i < 135 then b 134 else b 135)))) else (if i < 141 then (if i < 138 then (if i < 137 then b 136 else b 137) else (if i < 139 then b 138 else (if i < 140 then b 139 else b 140))) else (if i < 144 then (if i < 142 then b 141 else (if i < 143 then b 142 else b 143)) else (if i < 145 then b 144 else (if i < 146 then b 145 else b 146))))) else (if i < 157 then (if i < 152 then (if i < 149 then (if i < 148 then b 147 else b 148) else (if i < 150 then b 149 else (if i < 151 then b 150 else b 151))) else (if i < 154 then (if i < 153 then b 152 else b 153) else (if i < 155 then b 154 else (if i < 156 then b 155 else b 156)))) else (if i < 162 then (if i < 159 then (if i < 158 then b 157 else b 158) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)))))))) else (if i < 252 then (if i < 210 then (if i < 189 then (if i < 178 then (if i < 173 then (if i < 170 then (if i < 169 then b 168 else b 169) else (if i < 171 then b 170 else (if i < 172 then b 171 else b 172))) else (if i < 175 then (if i < 174 then b 173 else b 174) else (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)))) else (if i < 183 then (if i < 180 then (if i < 179 then b 178 else b 179) else (if i < 181 then b 180 else (if i < 182 then b 181 else b 182))) else (if i < 186 then (if i < 184 then b 183 else (if i < 185 then b 184 else b 185)) else (if i < 187 then b 186 else (if i < 188 then b 187 else b 188))))) else (if i < 199 then (if i < 194 then (if i < 191 then (if i < 190 then b 189 else b 190) else (if i < 192 then b 191 else (if i < 193 then b 192 else b 193))) else (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else (if i < 198 then b 197 else b 198)))) else (if i < 204 then (if i < 201 then (if i < 200 then decide (1 ≤ count199 b) else decide (2 ≤ count199 b)) else (if i < 202 then decide (1 ≤ count201 b) else (if i < 203 then decide (2 ≤ count201 b) else decide (1 ≤ count203 b)))) else (if i < 207 then (if i < 205 then decide (2 ≤ count203 b) else (if i < 206 then decide (1 ≤ count205 b) else decide (2 ≤ count205 b))) else (if i < 208 then decide (1 ≤ count207 b) else (if i < 209 then decide (2 ≤ count207 b) else decide (1 ≤ count209 b))))))) else (if i < 231 then (if i < 220 then (if i < 215 then (if i < 212 then (if i < 211 then decide (2 ≤ count209 b) else decide (1 ≤ count211 b)) else (if i < 213 then decide (2 ≤ count211 b) else (if i < 214 then decide (1 ≤ count213 b) else decide (2 ≤ count213 b)))) else (if i < 217 then (if i < 216 then decide (1 ≤ count215 b) else decide (2 ≤ count215 b)) else (if i < 218 then decide (1 ≤ count217 b) else (if i < 219 then decide (2 ≤ count217 b) else decide (1 ≤ count219 b))))) else (if i < 225 then (if i < 222 then (if i < 221 then decide (2 ≤ count219 b) else decide (1 ≤ count221 b)) else (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b)))) else (if i < 228 then (if i < 226 then decide (1 ≤ count225 b) else (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b))) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b)))))) else (if i < 241 then (if i < 236 then (if i < 233 then (if i < 232 then decide (1 ≤ count231 b) else decide (2 ≤ count231 b)) else (if i < 234 then decide (1 ≤ count233 b) else (if i < 235 then decide (2 ≤ count233 b) else decide (1 ≤ count235 b)))) else (if i < 238 then (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b)) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b))))) else (if i < 246 then (if i < 243 then (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b)) else (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b)))) else (if i < 249 then (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b))) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)))))))) else (if i < 294 then (if i < 273 then (if i < 262 then (if i < 257 then (if i < 254 then (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)) else (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b)))) else (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))))) else (if i < 267 then (if i < 264 then (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)))) else (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)))))) else (if i < 283 then (if i < 278 then (if i < 275 then (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b)) else (if i < 276 then decide (1 ≤ count275 b) else (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)))) else (if i < 280 then (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)) else (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))))) else (if i < 288 then (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b)))) else (if i < 291 then (if i < 289 then decide (2 ≤ count287 b) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))) else (if i < 292 then decide (1 ≤ count291 b) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b))))))) else (if i < 315 then (if i < 304 then (if i < 299 then (if i < 296 then (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)) else (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))) else (if i < 301 then (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b)) else (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))))) else (if i < 309 then (if i < 306 then (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)) else (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)))) else (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b)))))) else (if i < 325 then (if i < 320 then (if i < 317 then (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b)) else (if i < 318 then decide (1 ≤ count317 b) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))) else (if i < 322 then (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b)) else (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))))) else (if i < 330 then (if i < 327 then (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)) else (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)))) else (if i < 333 then (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b))) else (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b)))))))))) else (if i < 504 then (if i < 420 then (if i < 378 then (if i < 357 then (if i < 346 then (if i < 341 then (if i < 338 then (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)) else (if i < 339 then decide (2 ≤ count337 b) else (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)))) else (if i < 343 then (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)) else (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))))) else (if i < 351 then (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b)))) else (if i < 354 then (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))) else (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)))))) else (if i < 367 then (if i < 362 then (if i < 359 then (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)) else (if i < 360 then decide (1 ≤ count359 b) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)))) else (if i < 364 then (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)) else (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))))) else (if i < 372 then (if i < 369 then (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b)) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)))) else (if i < 375 then (if i < 373 then decide (2 ≤ count371 b) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b))) else (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))))))) else (if i < 399 then (if i < 388 then (if i < 383 then (if i < 380 then (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b)) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))) else (if i < 385 then (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b)) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b))))) else (if i < 393 then (if i < 390 then (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b)) else (if i < 391 then decide (2 ≤ count389 b) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b)))) else (if i < 396 then (if i < 394 then decide (1 ≤ count393 b) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b))) else (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (3 ≤ count395 b) else decide (1 ≤ count398 b)))))) else (if i < 409 then (if i < 404 then (if i < 401 then (if i < 400 then decide (2 ≤ count398 b) else decide (1 ≤ count400 b)) else (if i < 402 then decide (2 ≤ count400 b) else (if i < 403 then decide (3 ≤ count400 b) else decide (1 ≤ count403 b)))) else (if i < 406 then (if i < 405 then decide (2 ≤ count403 b) else decide (3 ≤ count403 b)) else (if i < 407 then decide (4 ≤ count403 b) else (if i < 408 then decide (5 ≤ count403 b) else decide (6 ≤ count403 b))))) else (if i < 414 then (if i < 411 then (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)) else (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (3 ≤ count411 b)))) else (if i < 417 then (if i < 415 then decide (1 ≤ count414 b) else (if i < 416 then decide (2 ≤ count414 b) else decide (1 ≤ count416 b))) else (if i < 418 then decide (2 ≤ count416 b) else (if i < 419 then decide (3 ≤ count416 b) else decide (1 ≤ count419 b)))))))) else (if i < 462 then (if i < 441 then (if i < 430 then (if i < 425 then (if i < 422 then (if i < 421 then decide (2 ≤ count419 b) else decide (3 ≤ count419 b)) else (if i < 423 then decide (4 ≤ count419 b) else (if i < 424 then decide (5 ≤ count419 b) else decide (6 ≤ count419 b)))) else (if i < 427 then (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)) else (if i < 428 then decide (3 ≤ count425 b) else (if i < 429 then decide (4 ≤ count425 b) else decide (5 ≤ count425 b))))) else (if i < 435 then (if i < 432 then (if i < 431 then decide (6 ≤ count425 b) else decide (7 ≤ count425 b)) else (if i < 433 then decide (8 ≤ count425 b) else (if i < 434 then decide (9 ≤ count425 b) else decide (10 ≤ count425 b)))) else (if i < 438 then (if i < 436 then decide (11 ≤ count425 b) else (if i < 437 then decide (12 ≤ count425 b) else decide (1 ≤ count437 b))) else (if i < 439 then decide (2 ≤ count437 b) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b)))))) else (if i < 451 then (if i < 446 then (if i < 443 then (if i < 442 then decide (3 ≤ count439 b) else decide (1 ≤ count442 b)) else (if i < 444 then decide (2 ≤ count442 b) else (if i < 445 then decide (1 ≤ count444 b) else decide (2 ≤ count444 b)))) else (if i < 448 then (if i < 447 then decide (3 ≤ count444 b) else decide (1 ≤ count447 b)) else (if i < 449 then decide (2 ≤ count447 b) else (if i < 450 then decide (3 ≤ count447 b) else decide (4 ≤ count447 b))))) else (if i < 456 then (if i < 453 then (if i < 452 then decide (5 ≤ count447 b) else decide (6 ≤ count447 b)) else (if i < 454 then decide (1 ≤ count453 b) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b)))) else (if i < 459 then (if i < 457 then decide (2 ≤ count455 b) else (if i < 458 then decide (3 ≤ count455 b) else decide (1 ≤ count458 b))) else (if i < 460 then decide (2 ≤ count458 b) else (if i < 461 then decide (1 ≤ count460 b) else decide (2 ≤ count460 b))))))) else (if i < 483 then (if i < 472 then (if i < 467 then (if i < 464 then (if i < 463 then decide (1 ≤ count462 b) else decide (2 ≤ count462 b)) else (if i < 465 then decide (3 ≤ count462 b) else (if i < 466 then decide (4 ≤ count462 b) else decide (1 ≤ count466 b)))) else (if i < 469 then (if i < 468 then decide (2 ≤ count466 b) else decide (3 ≤ count466 b)) else (if i < 470 then decide (4 ≤ count466 b) else (if i < 471 then decide (5 ≤ count466 b) else decide (6 ≤ count466 b))))) else (if i < 477 then (if i < 474 then (if i < 473 then decide (7 ≤ count466 b) else decide (1 ≤ count473 b)) else (if i < 475 then decide (2 ≤ count473 b) else (if i < 476 then decide (3 ≤ count473 b) else decide (4 ≤ count473 b)))) else (if i < 480 then (if i < 478 then decide (5 ≤ count473 b) else (if i < 479 then decide (6 ≤ count473 b) else decide (7 ≤ count473 b))) else (if i < 481 then decide (8 ≤ count473 b) else (if i < 482 then decide (9 ≤ count473 b) else decide (10 ≤ count473 b)))))) else (if i < 493 then (if i < 488 then (if i < 485 then (if i < 484 then decide (11 ≤ count473 b) else decide (12 ≤ count473 b)) else (if i < 486 then decide (13 ≤ count473 b) else (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b)))) else (if i < 490 then (if i < 489 then decide (3 ≤ count486 b) else decide (4 ≤ count486 b)) else (if i < 491 then decide (5 ≤ count486 b) else (if i < 492 then decide (6 ≤ count486 b) else decide (7 ≤ count486 b))))) else (if i < 498 then (if i < 495 then (if i < 494 then decide (8 ≤ count486 b) else decide (9 ≤ count486 b)) else (if i < 496 then decide (10 ≤ count486 b) else (if i < 497 then decide (11 ≤ count486 b) else decide (12 ≤ count486 b)))) else (if i < 501 then (if i < 499 then decide (13 ≤ count486 b) else (if i < 500 then decide (14 ≤ count486 b) else decide (15 ≤ count486 b))) else (if i < 502 then decide (16 ≤ count486 b) else (if i < 503 then decide (17 ≤ count486 b) else decide (18 ≤ count486 b))))))))) else (if i < 588 then (if i < 546 then (if i < 525 then (if i < 514 then (if i < 509 then (if i < 506 then (if i < 505 then decide (19 ≤ count486 b) else decide (20 ≤ count486 b)) else (if i < 507 then decide (21 ≤ count486 b) else (if i < 508 then decide (22 ≤ count486 b) else decide (23 ≤ count486 b)))) else (if i < 511 then (if i < 510 then decide (24 ≤ count486 b) else decide (25 ≤ count486 b)) else (if i < 512 then decide (1 ≤ count511 b) else (if i < 513 then decide (2 ≤ count511 b) else decide (1 ≤ count513 b))))) else (if i < 519 then (if i < 516 then (if i < 515 then decide (2 ≤ count513 b) else decide (3 ≤ count513 b)) else (if i < 517 then decide (1 ≤ count516 b) else (if i < 518 then decide (2 ≤ count516 b) else decide (1 ≤ count518 b)))) else (if i < 522 then (if i < 520 then decide (2 ≤ count518 b) else (if i < 521 then decide (3 ≤ count518 b) else decide (1 ≤ count521 b))) else (if i < 523 then decide (2 ≤ count521 b) else (if i < 524 then decide (3 ≤ count521 b) else decide (4 ≤ count521 b)))))) else (if i < 535 then (if i < 530 then (if i < 527 then (if i < 526 then decide (5 ≤ count521 b) else decide (6 ≤ count521 b)) else (if i < 528 then decide (1 ≤ count527 b) else (if i < 529 then decide (2 ≤ count527 b) else decide (1 ≤ count529 b)))) else (if i < 532 then (if i < 531 then decide (2 ≤ count529 b) else decide (3 ≤ count529 b)) else (if i < 533 then decide (1 ≤ count532 b) else (if i < 534 then decide (2 ≤ count532 b) else decide (1 ≤ count534 b))))) else (if i < 540 then (if i < 537 then (if i < 536 then decide (2 ≤ count534 b) else decide (3 ≤ count534 b)) else (if i < 538 then decide (1 ≤ count537 b) else (if i < 539 then decide (2 ≤ count537 b) else decide (3 ≤ count537 b)))) else (if i < 543 then (if i < 541 then decide (4 ≤ count537 b) else (if i < 542 then decide (5 ≤ count537 b) else decide (6 ≤ count537 b))) else (if i < 544 then decide (1 ≤ count543 b) else (if i < 545 then decide (2 ≤ count543 b) else decide (3 ≤ count543 b))))))) else (if i < 567 then (if i < 556 then (if i < 551 then (if i < 548 then (if i < 547 then decide (4 ≤ count543 b) else decide (5 ≤ count543 b)) else (if i < 549 then decide (6 ≤ count543 b) else (if i < 550 then decide (7 ≤ count543 b) else decide (8 ≤ count543 b)))) else (if i < 553 then (if i < 552 then decide (9 ≤ count543 b) else decide (10 ≤ count543 b)) else (if i < 554 then decide (11 ≤ count543 b) else (if i < 555 then decide (12 ≤ count543 b) else decide (1 ≤ count555 b))))) else (if i < 561 then (if i < 558 then (if i < 557 then decide (2 ≤ count555 b) else decide (1 ≤ count557 b)) else (if i < 559 then decide (2 ≤ count557 b) else (if i < 560 then decide (3 ≤ count557 b) else decide (1 ≤ count560 b)))) else (if i < 564 then (if i < 562 then decide (2 ≤ count560 b) else (if i < 563 then decide (1 ≤ count562 b) else decide (2 ≤ count562 b))) else (if i < 565 then decide (3 ≤ count562 b) else (if i < 566 then decide (1 ≤ count565 b) else decide (2 ≤ count565 b)))))) else (if i < 577 then (if i < 572 then (if i < 569 then (if i < 568 then decide (3 ≤ count565 b) else decide (4 ≤ count565 b)) else (if i < 570 then decide (5 ≤ count565 b) else (if i < 571 then decide (6 ≤ count565 b) else decide (1 ≤ count571 b)))) else (if i < 574 then (if i < 573 then decide (2 ≤ count571 b) else decide (1 ≤ count573 b)) else (if i < 575 then decide (2 ≤ count573 b) else (if i < 576 then decide (3 ≤ count573 b) else decide (1 ≤ count576 b))))) else (if i < 582 then (if i < 579 then (if i < 578 then decide (2 ≤ count576 b) else decide (1 ≤ count578 b)) else (if i < 580 then decide (2 ≤ count578 b) else (if i < 581 then decide (1 ≤ count580 b) else decide (2 ≤ count580 b)))) else (if i < 585 then (if i < 583 then decide (3 ≤ count580 b) else (if i < 584 then decide (4 ≤ count580 b) else decide (1 ≤ count584 b))) else (if i < 586 then decide (2 ≤ count584 b) else (if i < 587 then decide (3 ≤ count584 b) else decide (4 ≤ count584 b)))))))) else (if i < 630 then (if i < 609 then (if i < 598 then (if i < 593 then (if i < 590 then (if i < 589 then decide (5 ≤ count584 b) else decide (6 ≤ count584 b)) else (if i < 591 then decide (7 ≤ count584 b) else (if i < 592 then decide (1 ≤ count591 b) else decide (2 ≤ count591 b)))) else (if i < 595 then (if i < 594 then decide (3 ≤ count591 b) else decide (4 ≤ count591 b)) else (if i < 596 then decide (5 ≤ count591 b) else (if i < 597 then decide (6 ≤ count591 b) else decide (7 ≤ count591 b))))) else (if i < 603 then (if i < 600 then (if i < 599 then decide (8 ≤ count591 b) else decide (9 ≤ count591 b)) else (if i < 601 then decide (10 ≤ count591 b) else (if i < 602 then decide (11 ≤ count591 b) else decide (12 ≤ count591 b)))) else (if i < 606 then (if i < 604 then decide (13 ≤ count591 b) else (if i < 605 then decide (1 ≤ count604 b) else decide (2 ≤ count604 b))) else (if i < 607 then decide (3 ≤ count604 b) else (if i < 608 then decide (4 ≤ count604 b) else decide (5 ≤ count604 b)))))) else (if i < 619 then (if i < 614 then (if i < 611 then (if i < 610 then decide (6 ≤ count604 b) else decide (7 ≤ count604 b)) else (if i < 612 then decide (8 ≤ count604 b) else (if i < 613 then decide (9 ≤ count604 b) else decide (10 ≤ count604 b)))) else (if i < 616 then (if i < 615 then decide (11 ≤ count604 b) else decide (12 ≤ count604 b)) else (if i < 617 then decide (13 ≤ count604 b) else (if i < 618 then decide (14 ≤ count604 b) else decide (15 ≤ count604 b))))) else (if i < 624 then (if i < 621 then (if i < 620 then decide (16 ≤ count604 b) else decide (17 ≤ count604 b)) else (if i < 622 then decide (18 ≤ count604 b) else (if i < 623 then decide (19 ≤ count604 b) else decide (20 ≤ count604 b)))) else (if i < 627 then (if i < 625 then decide (21 ≤ count604 b) else (if i < 626 then decide (22 ≤ count604 b) else decide (23 ≤ count604 b))) else (if i < 628 then decide (24 ≤ count604 b) else (if i < 629 then decide (25 ≤ count604 b) else decide (1 ≤ count629 b))))))) else (if i < 651 then (if i < 640 then (if i < 635 then (if i < 632 then (if i < 631 then decide (2 ≤ count629 b) else decide (3 ≤ count629 b)) else (if i < 633 then decide (4 ≤ count629 b) else (if i < 634 then decide (5 ≤ count629 b) else decide (6 ≤ count629 b)))) else (if i < 637 then (if i < 636 then decide (7 ≤ count629 b) else decide (8 ≤ count629 b)) else (if i < 638 then decide (9 ≤ count629 b) else (if i < 639 then decide (10 ≤ count629 b) else decide (11 ≤ count629 b))))) else (if i < 645 then (if i < 642 then (if i < 641 then decide (12 ≤ count629 b) else decide (13 ≤ count629 b)) else (if i < 643 then decide (14 ≤ count629 b) else (if i < 644 then decide (15 ≤ count629 b) else decide (16 ≤ count629 b)))) else (if i < 648 then (if i < 646 then decide (17 ≤ count629 b) else (if i < 647 then decide (18 ≤ count629 b) else decide (19 ≤ count629 b))) else (if i < 649 then decide (20 ≤ count629 b) else (if i < 650 then decide (21 ≤ count629 b) else decide (22 ≤ count629 b)))))) else (if i < 661 then (if i < 656 then (if i < 653 then (if i < 652 then decide (23 ≤ count629 b) else decide (24 ≤ count629 b)) else (if i < 654 then decide (25 ≤ count629 b) else (if i < 655 then decide (26 ≤ count629 b) else decide (27 ≤ count629 b)))) else (if i < 658 then (if i < 657 then decide (28 ≤ count629 b) else decide (29 ≤ count629 b)) else (if i < 659 then decide (30 ≤ count629 b) else (if i < 660 then decide (31 ≤ count629 b) else decide (32 ≤ count629 b))))) else (if i < 666 then (if i < 663 then (if i < 662 then decide (33 ≤ count629 b) else decide (34 ≤ count629 b)) else (if i < 664 then decide (35 ≤ count629 b) else (if i < 665 then decide (36 ≤ count629 b) else decide (37 ≤ count629 b)))) else (if i < 669 then (if i < 667 then decide (38 ≤ count629 b) else (if i < 668 then decide (39 ≤ count629 b) else decide (40 ≤ count629 b))) else (if i < 670 then decide (41 ≤ count629 b) else (if i < 671 then decide (42 ≤ count629 b) else decide (1 ≤ count671 b))))))))))) else (if i < 1008 then (if i < 840 then (if i < 756 then (if i < 714 then (if i < 693 then (if i < 682 then (if i < 677 then (if i < 674 then (if i < 673 then decide (2 ≤ count671 b) else decide (1 ≤ count673 b)) else (if i < 675 then decide (2 ≤ count673 b) else (if i < 676 then decide (3 ≤ count673 b) else decide (1 ≤ count676 b)))) else (if i < 679 then (if i < 678 then decide (2 ≤ count676 b) else decide (1 ≤ count678 b)) else (if i < 680 then decide (2 ≤ count678 b) else (if i < 681 then decide (3 ≤ count678 b) else decide (1 ≤ count681 b))))) else (if i < 687 then (if i < 684 then (if i < 683 then decide (2 ≤ count681 b) else decide (3 ≤ count681 b)) else (if i < 685 then decide (4 ≤ count681 b) else (if i < 686 then decide (5 ≤ count681 b) else decide (6 ≤ count681 b)))) else (if i < 690 then (if i < 688 then decide (1 ≤ count687 b) else (if i < 689 then decide (2 ≤ count687 b) else decide (1 ≤ count689 b))) else (if i < 691 then decide (2 ≤ count689 b) else (if i < 692 then decide (3 ≤ count689 b) else decide (1 ≤ count692 b)))))) else (if i < 703 then (if i < 698 then (if i < 695 then (if i < 694 then decide (2 ≤ count692 b) else decide (1 ≤ count694 b)) else (if i < 696 then decide (2 ≤ count694 b) else (if i < 697 then decide (3 ≤ count694 b) else decide (1 ≤ count697 b)))) else (if i < 700 then (if i < 699 then decide (2 ≤ count697 b) else decide (3 ≤ count697 b)) else (if i < 701 then decide (4 ≤ count697 b) else (if i < 702 then decide (5 ≤ count697 b) else decide (6 ≤ count697 b))))) else (if i < 708 then (if i < 705 then (if i < 704 then decide (1 ≤ count703 b) else decide (2 ≤ count703 b)) else (if i < 706 then decide (3 ≤ count703 b) else (if i < 707 then decide (4 ≤ count703 b) else decide (5 ≤ count703 b)))) else (if i < 711 then (if i < 709 then decide (6 ≤ count703 b) else (if i < 710 then decide (7 ≤ count703 b) else decide (8 ≤ count703 b))) else (if i < 712 then decide (9 ≤ count703 b) else (if i < 713 then decide (10 ≤ count703 b) else decide (1 ≤ count713 b))))))) else (if i < 735 then (if i < 724 then (if i < 719 then (if i < 716 then (if i < 715 then decide (2 ≤ count713 b) else decide (1 ≤ count715 b)) else (if i < 717 then decide (2 ≤ count715 b) else (if i < 718 then decide (3 ≤ count715 b) else decide (1 ≤ count718 b)))) else (if i < 721 then (if i < 720 then decide (2 ≤ count718 b) else decide (1 ≤ count720 b)) else (if i < 722 then decide (2 ≤ count720 b) else (if i < 723 then decide (3 ≤ count720 b) else decide (1 ≤ count723 b))))) else (if i < 729 then (if i < 726 then (if i < 725 then decide (2 ≤ count723 b) else decide (3 ≤ count723 b)) else (if i < 727 then decide (4 ≤ count723 b) else (if i < 728 then decide (5 ≤ count723 b) else decide (6 ≤ count723 b)))) else (if i < 732 then (if i < 730 then decide (1 ≤ count729 b) else (if i < 731 then decide (2 ≤ count729 b) else decide (1 ≤ count731 b))) else (if i < 733 then decide (2 ≤ count731 b) else (if i < 734 then decide (3 ≤ count731 b) else decide (1 ≤ count734 b)))))) else (if i < 745 then (if i < 740 then (if i < 737 then (if i < 736 then decide (2 ≤ count734 b) else decide (1 ≤ count736 b)) else (if i < 738 then decide (2 ≤ count736 b) else (if i < 739 then decide (1 ≤ count738 b) else decide (2 ≤ count738 b)))) else (if i < 742 then (if i < 741 then decide (3 ≤ count738 b) else decide (4 ≤ count738 b)) else (if i < 743 then decide (1 ≤ count742 b) else (if i < 744 then decide (2 ≤ count742 b) else decide (3 ≤ count742 b))))) else (if i < 750 then (if i < 747 then (if i < 746 then decide (4 ≤ count742 b) else decide (5 ≤ count742 b)) else (if i < 748 then decide (6 ≤ count742 b) else (if i < 749 then decide (7 ≤ count742 b) else decide (1 ≤ count749 b)))) else (if i < 753 then (if i < 751 then decide (2 ≤ count749 b) else (if i < 752 then decide (3 ≤ count749 b) else decide (4 ≤ count749 b))) else (if i < 754 then decide (5 ≤ count749 b) else (if i < 755 then decide (6 ≤ count749 b) else decide (7 ≤ count749 b)))))))) else (if i < 798 then (if i < 777 then (if i < 766 then (if i < 761 then (if i < 758 then (if i < 757 then decide (8 ≤ count749 b) else decide (9 ≤ count749 b)) else (if i < 759 then decide (10 ≤ count749 b) else (if i < 760 then decide (1 ≤ count759 b) else decide (2 ≤ count759 b)))) else (if i < 763 then (if i < 762 then decide (3 ≤ count759 b) else decide (4 ≤ count759 b)) else (if i < 764 then decide (5 ≤ count759 b) else (if i < 765 then decide (6 ≤ count759 b) else decide (7 ≤ count759 b))))) else (if i < 771 then (if i < 768 then (if i < 767 then decide (8 ≤ count759 b) else decide (9 ≤ count759 b)) else (if i < 769 then decide (10 ≤ count759 b) else (if i < 770 then decide (1 ≤ count769 b) else decide (2 ≤ count769 b)))) else (if i < 774 then (if i < 772 then decide (1 ≤ count771 b) else (if i < 773 then decide (2 ≤ count771 b) else decide (3 ≤ count771 b))) else (if i < 775 then decide (1 ≤ count774 b) else (if i < 776 then decide (2 ≤ count774 b) else decide (1 ≤ count776 b)))))) else (if i < 787 then (if i < 782 then (if i < 779 then (if i < 778 then decide (2 ≤ count776 b) else decide (3 ≤ count776 b)) else (if i < 780 then decide (1 ≤ count779 b) else (if i < 781 then decide (2 ≤ count779 b) else decide (3 ≤ count779 b)))) else (if i < 784 then (if i < 783 then decide (4 ≤ count779 b) else decide (5 ≤ count779 b)) else (if i < 785 then decide (6 ≤ count779 b) else (if i < 786 then decide (1 ≤ count785 b) else decide (2 ≤ count785 b))))) else (if i < 792 then (if i < 789 then (if i < 788 then decide (1 ≤ count787 b) else decide (2 ≤ count787 b)) else (if i < 790 then decide (3 ≤ count787 b) else (if i < 791 then decide (1 ≤ count790 b) else decide (2 ≤ count790 b)))) else (if i < 795 then (if i < 793 then decide (1 ≤ count792 b) else (if i < 794 then decide (2 ≤ count792 b) else decide (3 ≤ count792 b))) else (if i < 796 then decide (1 ≤ count795 b) else (if i < 797 then decide (2 ≤ count795 b) else decide (3 ≤ count795 b))))))) else (if i < 819 then (if i < 808 then (if i < 803 then (if i < 800 then (if i < 799 then decide (4 ≤ count795 b) else decide (5 ≤ count795 b)) else (if i < 801 then decide (6 ≤ count795 b) else (if i < 802 then decide (1 ≤ count801 b) else decide (2 ≤ count801 b)))) else (if i < 805 then (if i < 804 then decide (3 ≤ count801 b) else decide (4 ≤ count801 b)) else (if i < 806 then decide (5 ≤ count801 b) else (if i < 807 then decide (6 ≤ count801 b) else decide (7 ≤ count801 b))))) else (if i < 813 then (if i < 810 then (if i < 809 then decide (8 ≤ count801 b) else decide (9 ≤ count801 b)) else (if i < 811 then decide (10 ≤ count801 b) else (if i < 812 then decide (1 ≤ count811 b) else decide (2 ≤ count811 b)))) else (if i < 816 then (if i < 814 then decide (1 ≤ count813 b) else (if i < 815 then decide (2 ≤ count813 b) else decide (3 ≤ count813 b))) else (if i < 817 then decide (1 ≤ count816 b) else (if i < 818 then decide (2 ≤ count816 b) else decide (1 ≤ count818 b)))))) else (if i < 829 then (if i < 824 then (if i < 821 then (if i < 820 then decide (2 ≤ count818 b) else decide (3 ≤ count818 b)) else (if i < 822 then decide (1 ≤ count821 b) else (if i < 823 then decide (2 ≤ count821 b) else decide (3 ≤ count821 b)))) else (if i < 826 then (if i < 825 then decide (4 ≤ count821 b) else decide (5 ≤ count821 b)) else (if i < 827 then decide (6 ≤ count821 b) else (if i < 828 then decide (1 ≤ count827 b) else decide (2 ≤ count827 b))))) else (if i < 834 then (if i < 831 then (if i < 830 then decide (1 ≤ count829 b) else decide (2 ≤ count829 b)) else (if i < 832 then decide (3 ≤ count829 b) else (if i < 833 then decide (1 ≤ count832 b) else decide (2 ≤ count832 b)))) else (if i < 837 then (if i < 835 then decide (1 ≤ count834 b) else (if i < 836 then decide (2 ≤ count834 b) else decide (1 ≤ count836 b))) else (if i < 838 then decide (2 ≤ count836 b) else (if i < 839 then decide (3 ≤ count836 b) else decide (4 ≤ count836 b))))))))) else (if i < 924 then (if i < 882 then (if i < 861 then (if i < 850 then (if i < 845 then (if i < 842 then (if i < 841 then decide (1 ≤ count840 b) else decide (2 ≤ count840 b)) else (if i < 843 then decide (3 ≤ count840 b) else (if i < 844 then decide (4 ≤ count840 b) else decide (5 ≤ count840 b)))) else (if i < 847 then (if i < 846 then decide (6 ≤ count840 b) else decide (7 ≤ count840 b)) else (if i < 848 then decide (1 ≤ count847 b) else (if i < 849 then decide (2 ≤ count847 b) else decide (3 ≤ count847 b))))) else (if i < 855 then (if i < 852 then (if i < 851 then decide (4 ≤ count847 b) else decide (5 ≤ count847 b)) else (if i < 853 then decide (6 ≤ count847 b) else (if i < 854 then decide (7 ≤ count847 b) else decide (8 ≤ count847 b)))) else (if i < 858 then (if i < 856 then decide (9 ≤ count847 b) else (if i < 857 then decide (10 ≤ count847 b) else decide (1 ≤ count857 b))) else (if i < 859 then decide (2 ≤ count857 b) else (if i < 860 then decide (3 ≤ count857 b) else decide (4 ≤ count857 b)))))) else (if i < 871 then (if i < 866 then (if i < 863 then (if i < 862 then decide (5 ≤ count857 b) else decide (6 ≤ count857 b)) else (if i < 864 then decide (7 ≤ count857 b) else (if i < 865 then decide (8 ≤ count857 b) else decide (9 ≤ count857 b)))) else (if i < 868 then (if i < 867 then decide (10 ≤ count857 b) else decide (1 ≤ count867 b)) else (if i < 869 then decide (2 ≤ count867 b) else (if i < 870 then decide (3 ≤ count867 b) else decide (4 ≤ count867 b))))) else (if i < 876 then (if i < 873 then (if i < 872 then decide (5 ≤ count867 b) else decide (6 ≤ count867 b)) else (if i < 874 then decide (7 ≤ count867 b) else (if i < 875 then decide (8 ≤ count867 b) else decide (9 ≤ count867 b)))) else (if i < 879 then (if i < 877 then decide (10 ≤ count867 b) else (if i < 878 then decide (1 ≤ count877 b) else decide (2 ≤ count877 b))) else (if i < 880 then decide (1 ≤ count879 b) else (if i < 881 then decide (2 ≤ count879 b) else decide (3 ≤ count879 b))))))) else (if i < 903 then (if i < 892 then (if i < 887 then (if i < 884 then (if i < 883 then decide (1 ≤ count882 b) else decide (2 ≤ count882 b)) else (if i < 885 then decide (1 ≤ count884 b) else (if i < 886 then decide (2 ≤ count884 b) else decide (3 ≤ count884 b)))) else (if i < 889 then (if i < 888 then decide (1 ≤ count887 b) else decide (2 ≤ count887 b)) else (if i < 890 then decide (3 ≤ count887 b) else (if i < 891 then decide (4 ≤ count887 b) else decide (5 ≤ count887 b))))) else (if i < 897 then (if i < 894 then (if i < 893 then decide (6 ≤ count887 b) else decide (1 ≤ count893 b)) else (if i < 895 then decide (2 ≤ count893 b) else (if i < 896 then decide (1 ≤ count895 b) else decide (2 ≤ count895 b)))) else (if i < 900 then (if i < 898 then decide (3 ≤ count895 b) else (if i < 899 then decide (1 ≤ count898 b) else decide (2 ≤ count898 b))) else (if i < 901 then decide (1 ≤ count900 b) else (if i < 902 then decide (2 ≤ count900 b) else decide (3 ≤ count900 b)))))) else (if i < 913 then (if i < 908 then (if i < 905 then (if i < 904 then decide (1 ≤ count903 b) else decide (2 ≤ count903 b)) else (if i < 906 then decide (3 ≤ count903 b) else (if i < 907 then decide (4 ≤ count903 b) else decide (5 ≤ count903 b)))) else (if i < 910 then (if i < 909 then decide (6 ≤ count903 b) else decide (1 ≤ count909 b)) else (if i < 911 then decide (2 ≤ count909 b) else (if i < 912 then decide (3 ≤ count909 b) else decide (4 ≤ count909 b))))) else (if i < 918 then (if i < 915 then (if i < 914 then decide (5 ≤ count909 b) else decide (6 ≤ count909 b)) else (if i < 916 then decide (7 ≤ count909 b) else (if i < 917 then decide (8 ≤ count909 b) else decide (9 ≤ count909 b)))) else (if i < 921 then (if i < 919 then decide (10 ≤ count909 b) else (if i < 920 then decide (11 ≤ count909 b) else decide (12 ≤ count909 b))) else (if i < 922 then decide (1 ≤ count921 b) else (if i < 923 then decide (2 ≤ count921 b) else decide (1 ≤ count923 b)))))))) else (if i < 966 then (if i < 945 then (if i < 934 then (if i < 929 then (if i < 926 then (if i < 925 then decide (2 ≤ count923 b) else decide (3 ≤ count923 b)) else (if i < 927 then decide (1 ≤ count926 b) else (if i < 928 then decide (2 ≤ count926 b) else decide (1 ≤ count928 b)))) else (if i < 931 then (if i < 930 then decide (2 ≤ count928 b) else decide (3 ≤ count928 b)) else (if i < 932 then decide (1 ≤ count931 b) else (if i < 933 then decide (2 ≤ count931 b) else decide (3 ≤ count931 b))))) else (if i < 939 then (if i < 936 then (if i < 935 then decide (4 ≤ count931 b) else decide (5 ≤ count931 b)) else (if i < 937 then decide (6 ≤ count931 b) else (if i < 938 then decide (1 ≤ count937 b) else decide (2 ≤ count937 b)))) else (if i < 942 then (if i < 940 then decide (1 ≤ count939 b) else (if i < 941 then decide (2 ≤ count939 b) else decide (3 ≤ count939 b))) else (if i < 943 then decide (1 ≤ count942 b) else (if i < 944 then decide (2 ≤ count942 b) else decide (1 ≤ count944 b)))))) else (if i < 955 then (if i < 950 then (if i < 947 then (if i < 946 then decide (2 ≤ count944 b) else decide (3 ≤ count944 b)) else (if i < 948 then decide (1 ≤ count947 b) else (if i < 949 then decide (2 ≤ count947 b) else decide (3 ≤ count947 b)))) else (if i < 952 then (if i < 951 then decide (4 ≤ count947 b) else decide (5 ≤ count947 b)) else (if i < 953 then decide (6 ≤ count947 b) else (if i < 954 then decide (1 ≤ count953 b) else decide (2 ≤ count953 b))))) else (if i < 960 then (if i < 957 then (if i < 956 then decide (3 ≤ count953 b) else decide (4 ≤ count953 b)) else (if i < 958 then decide (5 ≤ count953 b) else (if i < 959 then decide (6 ≤ count953 b) else decide (7 ≤ count953 b)))) else (if i < 963 then (if i < 961 then decide (8 ≤ count953 b) else (if i < 962 then decide (9 ≤ count953 b) else decide (10 ≤ count953 b))) else (if i < 964 then decide (11 ≤ count953 b) else (if i < 965 then decide (12 ≤ count953 b) else decide (1 ≤ count965 b))))))) else (if i < 987 then (if i < 976 then (if i < 971 then (if i < 968 then (if i < 967 then decide (2 ≤ count965 b) else decide (3 ≤ count965 b)) else (if i < 969 then decide (4 ≤ count965 b) else (if i < 970 then decide (5 ≤ count965 b) else decide (6 ≤ count965 b)))) else (if i < 973 then (if i < 972 then decide (7 ≤ count965 b) else decide (8 ≤ count965 b)) else (if i < 974 then decide (9 ≤ count965 b) else (if i < 975 then decide (10 ≤ count965 b) else decide (11 ≤ count965 b))))) else (if i < 981 then (if i < 978 then (if i < 977 then decide (12 ≤ count965 b) else decide (13 ≤ count965 b)) else (if i < 979 then decide (14 ≤ count965 b) else (if i < 980 then decide (15 ≤ count965 b) else decide (16 ≤ count965 b)))) else (if i < 984 then (if i < 982 then decide (17 ≤ count965 b) else (if i < 983 then decide (18 ≤ count965 b) else decide (19 ≤ count965 b))) else (if i < 985 then decide (20 ≤ count965 b) else (if i < 986 then decide (21 ≤ count965 b) else decide (22 ≤ count965 b)))))) else (if i < 997 then (if i < 992 then (if i < 989 then (if i < 988 then decide (23 ≤ count965 b) else decide (24 ≤ count965 b)) else (if i < 990 then decide (1 ≤ count989 b) else (if i < 991 then decide (2 ≤ count989 b) else decide (1 ≤ count991 b)))) else (if i < 994 then (if i < 993 then decide (2 ≤ count991 b) else decide (3 ≤ count991 b)) else (if i < 995 then decide (1 ≤ count994 b) else (if i < 996 then decide (2 ≤ count994 b) else decide (1 ≤ count996 b))))) else (if i < 1002 then (if i < 999 then (if i < 998 then decide (2 ≤ count996 b) else decide (3 ≤ count996 b)) else (if i < 1000 then decide (1 ≤ count999 b) else (if i < 1001 then decide (2 ≤ count999 b) else decide (3 ≤ count999 b)))) else (if i < 1005 then (if i < 1003 then decide (4 ≤ count999 b) else (if i < 1004 then decide (5 ≤ count999 b) else decide (6 ≤ count999 b))) else (if i < 1006 then decide (1 ≤ count1005 b) else (if i < 1007 then decide (2 ≤ count1005 b) else decide (1 ≤ count1007 b)))))))))) else (if i < 1176 then (if i < 1092 then (if i < 1050 then (if i < 1029 then (if i < 1018 then (if i < 1013 then (if i < 1010 then (if i < 1009 then decide (2 ≤ count1007 b) else decide (3 ≤ count1007 b)) else (if i < 1011 then decide (1 ≤ count1010 b) else (if i < 1012 then decide (2 ≤ count1010 b) else decide (1 ≤ count1012 b)))) else (if i < 1015 then (if i < 1014 then decide (2 ≤ count1012 b) else decide (3 ≤ count1012 b)) else (if i < 1016 then decide (1 ≤ count1015 b) else (if i < 1017 then decide (2 ≤ count1015 b) else decide (3 ≤ count1015 b))))) else (if i < 1023 then (if i < 1020 then (if i < 1019 then decide (4 ≤ count1015 b) else decide (5 ≤ count1015 b)) else (if i < 1021 then decide (6 ≤ count1015 b) else (if i < 1022 then decide (1 ≤ count1021 b) else decide (2 ≤ count1021 b)))) else (if i < 1026 then (if i < 1024 then decide (3 ≤ count1021 b) else (if i < 1025 then decide (4 ≤ count1021 b) else decide (5 ≤ count1021 b))) else (if i < 1027 then decide (6 ≤ count1021 b) else (if i < 1028 then decide (7 ≤ count1021 b) else decide (8 ≤ count1021 b)))))) else (if i < 1039 then (if i < 1034 then (if i < 1031 then (if i < 1030 then decide (9 ≤ count1021 b) else decide (10 ≤ count1021 b)) else (if i < 1032 then decide (11 ≤ count1021 b) else (if i < 1033 then decide (12 ≤ count1021 b) else decide (1 ≤ count1033 b)))) else (if i < 1036 then (if i < 1035 then decide (2 ≤ count1033 b) else decide (1 ≤ count1035 b)) else (if i < 1037 then decide (2 ≤ count1035 b) else (if i < 1038 then decide (3 ≤ count1035 b) else decide (1 ≤ count1038 b))))) else (if i < 1044 then (if i < 1041 then (if i < 1040 then decide (2 ≤ count1038 b) else decide (1 ≤ count1040 b)) else (if i < 1042 then decide (2 ≤ count1040 b) else (if i < 1043 then decide (3 ≤ count1040 b) else decide (1 ≤ count1043 b)))) else (if i < 1047 then (if i < 1045 then decide (2 ≤ count1043 b) else (if i < 1046 then decide (3 ≤ count1043 b) else decide (4 ≤ count1043 b))) else (if i < 1048 then decide (5 ≤ count1043 b) else (if i < 1049 then decide (6 ≤ count1043 b) else decide (1 ≤ count1049 b))))))) else (if i < 1071 then (if i < 1060 then (if i < 1055 then (if i < 1052 then (if i < 1051 then decide (2 ≤ count1049 b) else decide (1 ≤ count1051 b)) else (if i < 1053 then decide (2 ≤ count1051 b) else (if i < 1054 then decide (3 ≤ count1051 b) else decide (1 ≤ count1054 b)))) else (if i < 1057 then (if i < 1056 then decide (2 ≤ count1054 b) else decide (1 ≤ count1056 b)) else (if i < 1058 then decide (2 ≤ count1056 b) else (if i < 1059 then decide (1 ≤ count1058 b) else decide (2 ≤ count1058 b))))) else (if i < 1065 then (if i < 1062 then (if i < 1061 then decide (3 ≤ count1058 b) else decide (4 ≤ count1058 b)) else (if i < 1063 then decide (1 ≤ count1062 b) else (if i < 1064 then decide (2 ≤ count1062 b) else decide (3 ≤ count1062 b)))) else (if i < 1068 then (if i < 1066 then decide (4 ≤ count1062 b) else (if i < 1067 then decide (5 ≤ count1062 b) else decide (6 ≤ count1062 b))) else (if i < 1069 then decide (7 ≤ count1062 b) else (if i < 1070 then decide (1 ≤ count1069 b) else decide (2 ≤ count1069 b)))))) else (if i < 1081 then (if i < 1076 then (if i < 1073 then (if i < 1072 then decide (3 ≤ count1069 b) else decide (4 ≤ count1069 b)) else (if i < 1074 then decide (5 ≤ count1069 b) else (if i < 1075 then decide (6 ≤ count1069 b) else decide (7 ≤ count1069 b)))) else (if i < 1078 then (if i < 1077 then decide (8 ≤ count1069 b) else decide (9 ≤ count1069 b)) else (if i < 1079 then decide (10 ≤ count1069 b) else (if i < 1080 then decide (11 ≤ count1069 b) else decide (12 ≤ count1069 b))))) else (if i < 1086 then (if i < 1083 then (if i < 1082 then decide (13 ≤ count1069 b) else decide (1 ≤ count1082 b)) else (if i < 1084 then decide (2 ≤ count1082 b) else (if i < 1085 then decide (3 ≤ count1082 b) else decide (4 ≤ count1082 b)))) else (if i < 1089 then (if i < 1087 then decide (5 ≤ count1082 b) else (if i < 1088 then decide (6 ≤ count1082 b) else decide (7 ≤ count1082 b))) else (if i < 1090 then decide (8 ≤ count1082 b) else (if i < 1091 then decide (9 ≤ count1082 b) else decide (10 ≤ count1082 b)))))))) else (if i < 1134 then (if i < 1113 then (if i < 1102 then (if i < 1097 then (if i < 1094 then (if i < 1093 then decide (11 ≤ count1082 b) else decide (12 ≤ count1082 b)) else (if i < 1095 then decide (13 ≤ count1082 b) else (if i < 1096 then decide (14 ≤ count1082 b) else decide (15 ≤ count1082 b)))) else (if i < 1099 then (if i < 1098 then decide (16 ≤ count1082 b) else decide (17 ≤ count1082 b)) else (if i < 1100 then decide (18 ≤ count1082 b) else (if i < 1101 then decide (19 ≤ count1082 b) else decide (20 ≤ count1082 b))))) else (if i < 1107 then (if i < 1104 then (if i < 1103 then decide (21 ≤ count1082 b) else decide (22 ≤ count1082 b)) else (if i < 1105 then decide (23 ≤ count1082 b) else (if i < 1106 then decide (24 ≤ count1082 b) else decide (25 ≤ count1082 b)))) else (if i < 1110 then (if i < 1108 then decide (1 ≤ count1107 b) else (if i < 1109 then decide (2 ≤ count1107 b) else decide (3 ≤ count1107 b))) else (if i < 1111 then decide (4 ≤ count1107 b) else (if i < 1112 then decide (5 ≤ count1107 b) else decide (6 ≤ count1107 b)))))) else (if i < 1123 then (if i < 1118 then (if i < 1115 then (if i < 1114 then decide (7 ≤ count1107 b) else decide (8 ≤ count1107 b)) else (if i < 1116 then decide (9 ≤ count1107 b) else (if i < 1117 then decide (10 ≤ count1107 b) else decide (11 ≤ count1107 b)))) else (if i < 1120 then (if i < 1119 then decide (12 ≤ count1107 b) else decide (13 ≤ count1107 b)) else (if i < 1121 then decide (14 ≤ count1107 b) else (if i < 1122 then decide (15 ≤ count1107 b) else decide (16 ≤ count1107 b))))) else (if i < 1128 then (if i < 1125 then (if i < 1124 then decide (17 ≤ count1107 b) else decide (18 ≤ count1107 b)) else (if i < 1126 then decide (19 ≤ count1107 b) else (if i < 1127 then decide (20 ≤ count1107 b) else decide (21 ≤ count1107 b)))) else (if i < 1131 then (if i < 1129 then decide (22 ≤ count1107 b) else (if i < 1130 then decide (23 ≤ count1107 b) else decide (24 ≤ count1107 b))) else (if i < 1132 then decide (25 ≤ count1107 b) else (if i < 1133 then decide (26 ≤ count1107 b) else decide (27 ≤ count1107 b))))))) else (if i < 1155 then (if i < 1144 then (if i < 1139 then (if i < 1136 then (if i < 1135 then decide (28 ≤ count1107 b) else decide (29 ≤ count1107 b)) else (if i < 1137 then decide (30 ≤ count1107 b) else (if i < 1138 then decide (31 ≤ count1107 b) else decide (32 ≤ count1107 b)))) else (if i < 1141 then (if i < 1140 then decide (33 ≤ count1107 b) else decide (34 ≤ count1107 b)) else (if i < 1142 then decide (35 ≤ count1107 b) else (if i < 1143 then decide (36 ≤ count1107 b) else decide (37 ≤ count1107 b))))) else (if i < 1149 then (if i < 1146 then (if i < 1145 then decide (38 ≤ count1107 b) else decide (39 ≤ count1107 b)) else (if i < 1147 then decide (40 ≤ count1107 b) else (if i < 1148 then decide (41 ≤ count1107 b) else decide (42 ≤ count1107 b)))) else (if i < 1152 then (if i < 1150 then decide (1 ≤ count1149 b) else (if i < 1151 then decide (2 ≤ count1149 b) else decide (1 ≤ count1151 b))) else (if i < 1153 then decide (2 ≤ count1151 b) else (if i < 1154 then decide (3 ≤ count1151 b) else decide (1 ≤ count1154 b)))))) else (if i < 1165 then (if i < 1160 then (if i < 1157 then (if i < 1156 then decide (2 ≤ count1154 b) else decide (1 ≤ count1156 b)) else (if i < 1158 then decide (2 ≤ count1156 b) else (if i < 1159 then decide (3 ≤ count1156 b) else decide (1 ≤ count1159 b)))) else (if i < 1162 then (if i < 1161 then decide (2 ≤ count1159 b) else decide (3 ≤ count1159 b)) else (if i < 1163 then decide (4 ≤ count1159 b) else (if i < 1164 then decide (5 ≤ count1159 b) else decide (6 ≤ count1159 b))))) else (if i < 1170 then (if i < 1167 then (if i < 1166 then decide (1 ≤ count1165 b) else decide (2 ≤ count1165 b)) else (if i < 1168 then decide (1 ≤ count1167 b) else (if i < 1169 then decide (2 ≤ count1167 b) else decide (3 ≤ count1167 b)))) else (if i < 1173 then (if i < 1171 then decide (1 ≤ count1170 b) else (if i < 1172 then decide (2 ≤ count1170 b) else decide (1 ≤ count1172 b))) else (if i < 1174 then decide (2 ≤ count1172 b) else (if i < 1175 then decide (3 ≤ count1172 b) else decide (1 ≤ count1175 b))))))))) else (if i < 1260 then (if i < 1218 then (if i < 1197 then (if i < 1186 then (if i < 1181 then (if i < 1178 then (if i < 1177 then decide (2 ≤ count1175 b) else decide (3 ≤ count1175 b)) else (if i < 1179 then decide (4 ≤ count1175 b) else (if i < 1180 then decide (5 ≤ count1175 b) else decide (6 ≤ count1175 b)))) else (if i < 1183 then (if i < 1182 then decide (1 ≤ count1181 b) else decide (2 ≤ count1181 b)) else (if i < 1184 then decide (3 ≤ count1181 b) else (if i < 1185 then decide (4 ≤ count1181 b) else decide (5 ≤ count1181 b))))) else (if i < 1191 then (if i < 1188 then (if i < 1187 then decide (6 ≤ count1181 b) else decide (7 ≤ count1181 b)) else (if i < 1189 then decide (8 ≤ count1181 b) else (if i < 1190 then decide (9 ≤ count1181 b) else decide (1 ≤ count1190 b)))) else (if i < 1194 then (if i < 1192 then decide (2 ≤ count1190 b) else (if i < 1193 then decide (1 ≤ count1192 b) else decide (2 ≤ count1192 b))) else (if i < 1195 then decide (3 ≤ count1192 b) else (if i < 1196 then decide (1 ≤ count1195 b) else decide (2 ≤ count1195 b)))))) else (if i < 1207 then (if i < 1202 then (if i < 1199 then (if i < 1198 then decide (1 ≤ count1197 b) else decide (2 ≤ count1197 b)) else (if i < 1200 then decide (3 ≤ count1197 b) else (if i < 1201 then decide (1 ≤ count1200 b) else decide (2 ≤ count1200 b)))) else (if i < 1204 then (if i < 1203 then decide (3 ≤ count1200 b) else decide (4 ≤ count1200 b)) else (if i < 1205 then decide (5 ≤ count1200 b) else (if i < 1206 then decide (6 ≤ count1200 b) else decide (1 ≤ count1206 b))))) else (if i < 1212 then (if i < 1209 then (if i < 1208 then decide (2 ≤ count1206 b) else decide (1 ≤ count1208 b)) else (if i < 1210 then decide (2 ≤ count1208 b) else (if i < 1211 then decide (3 ≤ count1208 b) else decide (1 ≤ count1211 b)))) else (if i < 1215 then (if i < 1213 then decide (2 ≤ count1211 b) else (if i < 1214 then decide (1 ≤ count1213 b) else decide (2 ≤ count1213 b))) else (if i < 1216 then decide (3 ≤ count1213 b) else (if i < 1217 then decide (1 ≤ count1216 b) else decide (2 ≤ count1216 b))))))) else (if i < 1239 then (if i < 1228 then (if i < 1223 then (if i < 1220 then (if i < 1219 then decide (3 ≤ count1216 b) else decide (4 ≤ count1216 b)) else (if i < 1221 then decide (5 ≤ count1216 b) else (if i < 1222 then decide (6 ≤ count1216 b) else decide (1 ≤ count1222 b)))) else (if i < 1225 then (if i < 1224 then decide (2 ≤ count1222 b) else decide (3 ≤ count1222 b)) else (if i < 1226 then decide (4 ≤ count1222 b) else (if i < 1227 then decide (5 ≤ count1222 b) else decide (6 ≤ count1222 b))))) else (if i < 1233 then (if i < 1230 then (if i < 1229 then decide (7 ≤ count1222 b) else decide (8 ≤ count1222 b)) else (if i < 1231 then decide (9 ≤ count1222 b) else (if i < 1232 then decide (1 ≤ count1231 b) else decide (2 ≤ count1231 b)))) else (if i < 1236 then (if i < 1234 then decide (3 ≤ count1231 b) else (if i < 1235 then decide (4 ≤ count1231 b) else decide (5 ≤ count1231 b))) else (if i < 1237 then decide (6 ≤ count1231 b) else (if i < 1238 then decide (7 ≤ count1231 b) else decide (8 ≤ count1231 b)))))) else (if i < 1249 then (if i < 1244 then (if i < 1241 then (if i < 1240 then decide (9 ≤ count1231 b) else decide (1 ≤ count1240 b)) else (if i < 1242 then decide (2 ≤ count1240 b) else (if i < 1243 then decide (1 ≤ count1242 b) else decide (2 ≤ count1242 b)))) else (if i < 1246 then (if i < 1245 then decide (3 ≤ count1242 b) else decide (1 ≤ count1245 b)) else (if i < 1247 then decide (2 ≤ count1245 b) else (if i < 1248 then decide (1 ≤ count1247 b) else decide (2 ≤ count1247 b))))) else (if i < 1254 then (if i < 1251 then (if i < 1250 then decide (3 ≤ count1247 b) else decide (1 ≤ count1250 b)) else (if i < 1252 then decide (2 ≤ count1250 b) else (if i < 1253 then decide (3 ≤ count1250 b) else decide (4 ≤ count1250 b)))) else (if i < 1257 then (if i < 1255 then decide (5 ≤ count1250 b) else (if i < 1256 then decide (6 ≤ count1250 b) else decide (1 ≤ count1256 b))) else (if i < 1258 then decide (2 ≤ count1256 b) else (if i < 1259 then decide (1 ≤ count1258 b) else decide (2 ≤ count1258 b)))))))) else (if i < 1302 then (if i < 1281 then (if i < 1270 then (if i < 1265 then (if i < 1262 then (if i < 1261 then decide (3 ≤ count1258 b) else decide (1 ≤ count1261 b)) else (if i < 1263 then decide (2 ≤ count1261 b) else (if i < 1264 then decide (1 ≤ count1263 b) else decide (2 ≤ count1263 b)))) else (if i < 1267 then (if i < 1266 then decide (3 ≤ count1263 b) else decide (1 ≤ count1266 b)) else (if i < 1268 then decide (2 ≤ count1266 b) else (if i < 1269 then decide (3 ≤ count1266 b) else decide (4 ≤ count1266 b))))) else (if i < 1275 then (if i < 1272 then (if i < 1271 then decide (5 ≤ count1266 b) else decide (6 ≤ count1266 b)) else (if i < 1273 then decide (1 ≤ count1272 b) else (if i < 1274 then decide (2 ≤ count1272 b) else decide (3 ≤ count1272 b)))) else (if i < 1278 then (if i < 1276 then decide (4 ≤ count1272 b) else (if i < 1277 then decide (5 ≤ count1272 b) else decide (6 ≤ count1272 b))) else (if i < 1279 then decide (7 ≤ count1272 b) else (if i < 1280 then decide (8 ≤ count1272 b) else decide (9 ≤ count1272 b)))))) else (if i < 1291 then (if i < 1286 then (if i < 1283 then (if i < 1282 then decide (1 ≤ count1281 b) else decide (2 ≤ count1281 b)) else (if i < 1284 then decide (1 ≤ count1283 b) else (if i < 1285 then decide (2 ≤ count1283 b) else decide (3 ≤ count1283 b)))) else (if i < 1288 then (if i < 1287 then decide (1 ≤ count1286 b) else decide (2 ≤ count1286 b)) else (if i < 1289 then decide (1 ≤ count1288 b) else (if i < 1290 then decide (2 ≤ count1288 b) else decide (3 ≤ count1288 b))))) else (if i < 1296 then (if i < 1293 then (if i < 1292 then decide (1 ≤ count1291 b) else decide (2 ≤ count1291 b)) else (if i < 1294 then decide (3 ≤ count1291 b) else (if i < 1295 then decide (4 ≤ count1291 b) else decide (5 ≤ count1291 b)))) else (if i < 1299 then (if i < 1297 then decide (6 ≤ count1291 b) else (if i < 1298 then decide (1 ≤ count1297 b) else decide (2 ≤ count1297 b))) else (if i < 1300 then decide (1 ≤ count1299 b) else (if i < 1301 then decide (2 ≤ count1299 b) else decide (3 ≤ count1299 b))))))) else (if i < 1323 then (if i < 1312 then (if i < 1307 then (if i < 1304 then (if i < 1303 then decide (1 ≤ count1302 b) else decide (2 ≤ count1302 b)) else (if i < 1305 then decide (1 ≤ count1304 b) else (if i < 1306 then decide (2 ≤ count1304 b) else decide (1 ≤ count1306 b)))) else (if i < 1309 then (if i < 1308 then decide (2 ≤ count1306 b) else decide (3 ≤ count1306 b)) else (if i < 1310 then decide (4 ≤ count1306 b) else (if i < 1311 then decide (1 ≤ count1310 b) else decide (2 ≤ count1310 b))))) else (if i < 1317 then (if i < 1314 then (if i < 1313 then decide (3 ≤ count1310 b) else decide (4 ≤ count1310 b)) else (if i < 1315 then decide (5 ≤ count1310 b) else (if i < 1316 then decide (6 ≤ count1310 b) else decide (7 ≤ count1310 b)))) else (if i < 1320 then (if i < 1318 then decide (1 ≤ count1317 b) else (if i < 1319 then decide (2 ≤ count1317 b) else decide (3 ≤ count1317 b))) else (if i < 1321 then decide (4 ≤ count1317 b) else (if i < 1322 then decide (5 ≤ count1317 b) else decide (6 ≤ count1317 b)))))) else (if i < 1333 then (if i < 1328 then (if i < 1325 then (if i < 1324 then decide (7 ≤ count1317 b) else decide (8 ≤ count1317 b)) else (if i < 1326 then decide (9 ≤ count1317 b) else (if i < 1327 then decide (1 ≤ count1326 b) else decide (2 ≤ count1326 b)))) else (if i < 1330 then (if i < 1329 then decide (3 ≤ count1326 b) else decide (4 ≤ count1326 b)) else (if i < 1331 then decide (5 ≤ count1326 b) else (if i < 1332 then decide (6 ≤ count1326 b) else decide (7 ≤ count1326 b))))) else (if i < 1338 then (if i < 1335 then (if i < 1334 then decide (8 ≤ count1326 b) else decide (9 ≤ count1326 b)) else (if i < 1336 then decide (1 ≤ count1335 b) else (if i < 1337 then decide (2 ≤ count1335 b) else decide (3 ≤ count1335 b)))) else (if i < 1341 then (if i < 1339 then decide (4 ≤ count1335 b) else (if i < 1340 then decide (5 ≤ count1335 b) else decide (6 ≤ count1335 b))) else (if i < 1342 then decide (7 ≤ count1335 b) else (if i < 1343 then decide (8 ≤ count1335 b) else decide (9 ≤ count1335 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (2 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (4 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (6 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (8 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (12 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (14 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (22 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (106 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (160 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (162 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (164 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (165 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (166 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (168 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (170 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (171 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (172 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (174 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (181 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (182 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (183 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (184 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (185 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (187 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (189 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (191 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (226 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (227 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (229 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (234 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (235 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (237 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (239 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (240 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (241 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (243 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (244 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (248 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (252 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (254 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (255 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (266 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (354 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (355 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (362 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (368 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (369 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (371 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (376 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (380 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (382 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (383 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (394 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (398 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (426 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (436 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (440 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (444 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (446 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (451 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (458 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (459 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (463 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (BallClauseLogic.Endpoint q (2 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (106 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (174 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (181 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (183 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (226 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (237 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (239 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (241 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (243 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (254 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (354 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (362 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (369 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (371 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (380 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (382 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (398 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (446 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (1 ≤ count199 (baseVal q)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (1 ≤ count201 (baseVal q)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (1 ≤ count203 (baseVal q)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (1 ≤ count205 (baseVal q)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (2 ≤ count207 (baseVal q)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (1 ≤ count209 (baseVal q)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (1 ≤ count211 (baseVal q)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (1 ≤ count215 (baseVal q)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (2 ≤ count217 (baseVal q)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (2 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (2 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (2 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (2 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (2 ≤ count243 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value264 (q : Snake 81) : valuation q 264 = decide (2 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value276 (q : Snake 81) : valuation q 276 = decide (2 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value292 (q : Snake 81) : valuation q 292 = decide (2 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value1149 (q : Snake 81) : valuation q 1149 = decide (1 ≤ count1149 (baseVal q)) := rfl
theorem value1151 (q : Snake 81) : valuation q 1151 = decide (1 ≤ count1151 (baseVal q)) := rfl
theorem value1152 (q : Snake 81) : valuation q 1152 = decide (2 ≤ count1151 (baseVal q)) := rfl
theorem value1154 (q : Snake 81) : valuation q 1154 = decide (1 ≤ count1154 (baseVal q)) := rfl
theorem value1156 (q : Snake 81) : valuation q 1156 = decide (1 ≤ count1156 (baseVal q)) := rfl
theorem value1157 (q : Snake 81) : valuation q 1157 = decide (2 ≤ count1156 (baseVal q)) := rfl
theorem value1160 (q : Snake 81) : valuation q 1160 = decide (2 ≤ count1159 (baseVal q)) := rfl
theorem value1165 (q : Snake 81) : valuation q 1165 = decide (1 ≤ count1165 (baseVal q)) := rfl
theorem value1166 (q : Snake 81) : valuation q 1166 = decide (2 ≤ count1165 (baseVal q)) := rfl
theorem value1167 (q : Snake 81) : valuation q 1167 = decide (1 ≤ count1167 (baseVal q)) := rfl
theorem value1168 (q : Snake 81) : valuation q 1168 = decide (2 ≤ count1167 (baseVal q)) := rfl
theorem value1170 (q : Snake 81) : valuation q 1170 = decide (1 ≤ count1170 (baseVal q)) := rfl
theorem value1172 (q : Snake 81) : valuation q 1172 = decide (1 ≤ count1172 (baseVal q)) := rfl
theorem value1173 (q : Snake 81) : valuation q 1173 = decide (2 ≤ count1172 (baseVal q)) := rfl
theorem value1175 (q : Snake 81) : valuation q 1175 = decide (1 ≤ count1175 (baseVal q)) := rfl
theorem value1176 (q : Snake 81) : valuation q 1176 = decide (2 ≤ count1175 (baseVal q)) := rfl
theorem value1182 (q : Snake 81) : valuation q 1182 = decide (2 ≤ count1181 (baseVal q)) := rfl
theorem value1183 (q : Snake 81) : valuation q 1183 = decide (3 ≤ count1181 (baseVal q)) := rfl
theorem value1184 (q : Snake 81) : valuation q 1184 = decide (4 ≤ count1181 (baseVal q)) := rfl
theorem value1190 (q : Snake 81) : valuation q 1190 = decide (1 ≤ count1190 (baseVal q)) := rfl
theorem value1192 (q : Snake 81) : valuation q 1192 = decide (1 ≤ count1192 (baseVal q)) := rfl
theorem value1193 (q : Snake 81) : valuation q 1193 = decide (2 ≤ count1192 (baseVal q)) := rfl
theorem value1195 (q : Snake 81) : valuation q 1195 = decide (1 ≤ count1195 (baseVal q)) := rfl
theorem value1197 (q : Snake 81) : valuation q 1197 = decide (1 ≤ count1197 (baseVal q)) := rfl
theorem value1200 (q : Snake 81) : valuation q 1200 = decide (1 ≤ count1200 (baseVal q)) := rfl
theorem value1201 (q : Snake 81) : valuation q 1201 = decide (2 ≤ count1200 (baseVal q)) := rfl
theorem value1202 (q : Snake 81) : valuation q 1202 = decide (3 ≤ count1200 (baseVal q)) := rfl
theorem value1206 (q : Snake 81) : valuation q 1206 = decide (1 ≤ count1206 (baseVal q)) := rfl
theorem value1207 (q : Snake 81) : valuation q 1207 = decide (2 ≤ count1206 (baseVal q)) := rfl
theorem value1208 (q : Snake 81) : valuation q 1208 = decide (1 ≤ count1208 (baseVal q)) := rfl
theorem value1209 (q : Snake 81) : valuation q 1209 = decide (2 ≤ count1208 (baseVal q)) := rfl
theorem value1211 (q : Snake 81) : valuation q 1211 = decide (1 ≤ count1211 (baseVal q)) := rfl
theorem value1213 (q : Snake 81) : valuation q 1213 = decide (1 ≤ count1213 (baseVal q)) := rfl
theorem value1214 (q : Snake 81) : valuation q 1214 = decide (2 ≤ count1213 (baseVal q)) := rfl
theorem value1216 (q : Snake 81) : valuation q 1216 = decide (1 ≤ count1216 (baseVal q)) := rfl
theorem value1217 (q : Snake 81) : valuation q 1217 = decide (2 ≤ count1216 (baseVal q)) := rfl
theorem value1223 (q : Snake 81) : valuation q 1223 = decide (2 ≤ count1222 (baseVal q)) := rfl
theorem value1224 (q : Snake 81) : valuation q 1224 = decide (3 ≤ count1222 (baseVal q)) := rfl
theorem value1225 (q : Snake 81) : valuation q 1225 = decide (4 ≤ count1222 (baseVal q)) := rfl
theorem value1236 (q : Snake 81) : valuation q 1236 = decide (6 ≤ count1231 (baseVal q)) := rfl
theorem value1240 (q : Snake 81) : valuation q 1240 = decide (1 ≤ count1240 (baseVal q)) := rfl
theorem value1242 (q : Snake 81) : valuation q 1242 = decide (1 ≤ count1242 (baseVal q)) := rfl
theorem value1250 (q : Snake 81) : valuation q 1250 = decide (1 ≤ count1250 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (1 ≤ count1272 (baseVal q)) := rfl
theorem value1281 (q : Snake 81) : valuation q 1281 = decide (1 ≤ count1281 (baseVal q)) := rfl
theorem value1283 (q : Snake 81) : valuation q 1283 = decide (1 ≤ count1283 (baseVal q)) := rfl
theorem value1284 (q : Snake 81) : valuation q 1284 = decide (2 ≤ count1283 (baseVal q)) := rfl
theorem value1286 (q : Snake 81) : valuation q 1286 = decide (1 ≤ count1286 (baseVal q)) := rfl
theorem value1288 (q : Snake 81) : valuation q 1288 = decide (1 ≤ count1288 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (1 ≤ count1291 (baseVal q)) := rfl
theorem value1292 (q : Snake 81) : valuation q 1292 = decide (2 ≤ count1291 (baseVal q)) := rfl
theorem value1293 (q : Snake 81) : valuation q 1293 = decide (3 ≤ count1291 (baseVal q)) := rfl
theorem value1297 (q : Snake 81) : valuation q 1297 = decide (1 ≤ count1297 (baseVal q)) := rfl
theorem value1299 (q : Snake 81) : valuation q 1299 = decide (1 ≤ count1299 (baseVal q)) := rfl
theorem value1302 (q : Snake 81) : valuation q 1302 = decide (1 ≤ count1302 (baseVal q)) := rfl
theorem value1306 (q : Snake 81) : valuation q 1306 = decide (1 ≤ count1306 (baseVal q)) := rfl
theorem value1310 (q : Snake 81) : valuation q 1310 = decide (1 ≤ count1310 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (2 ≤ count1317 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (3 ≤ count1317 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (3 ≤ count1326 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (9 ≤ count1335 (baseVal q)) := rfl
theorem meaningNeg92 (b : Nat → Bool) : literal (valuationOf b) (-92) = decide (1 ≤ countLit b [-92]) := by
  change literal b (-92) = decide (1 ≤ countLit b [-92])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-92) <;> decide
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
theorem meaningNeg80 (b : Nat → Bool) : literal (valuationOf b) (-80) = decide (1 ≤ countLit b [-80]) := by
  change literal b (-80) = decide (1 ≤ countLit b [-80])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-80) <;> decide
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
theorem meaningNeg50 (b : Nat → Bool) : literal (valuationOf b) (-50) = decide (1 ≤ countLit b [-50]) := by
  change literal b (-50) = decide (1 ≤ countLit b [-50])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-50) <;> decide
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
theorem meaningNeg8 (b : Nat → Bool) : literal (valuationOf b) (-8) = decide (1 ≤ countLit b [-8]) := by
  change literal b (-8) = decide (1 ≤ countLit b [-8])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-8) <;> decide
theorem meaningNeg6 (b : Nat → Bool) : literal (valuationOf b) (-6) = decide (1 ≤ countLit b [-6]) := by
  change literal b (-6) = decide (1 ≤ countLit b [-6])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-6) <;> decide
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
theorem meaning101 (b : Nat → Bool) : literal (valuationOf b) (101) = decide (1 ≤ countLit b [101]) := by
  change literal b (101) = decide (1 ≤ countLit b [101])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (101) <;> decide
theorem meaning105 (b : Nat → Bool) : literal (valuationOf b) (105) = decide (1 ≤ countLit b [105]) := by
  change literal b (105) = decide (1 ≤ countLit b [105])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (105) <;> decide
theorem meaning107 (b : Nat → Bool) : literal (valuationOf b) (107) = decide (1 ≤ countLit b [107]) := by
  change literal b (107) = decide (1 ≤ countLit b [107])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (107) <;> decide
theorem meaning109 (b : Nat → Bool) : literal (valuationOf b) (109) = decide (1 ≤ countLit b [109]) := by
  change literal b (109) = decide (1 ≤ countLit b [109])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (109) <;> decide
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
theorem meaning131 (b : Nat → Bool) : literal (valuationOf b) (131) = decide (1 ≤ countLit b [131]) := by
  change literal b (131) = decide (1 ≤ countLit b [131])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (131) <;> decide
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
theorem meaning136 (b : Nat → Bool) : literal (valuationOf b) (136) = decide (1 ≤ countLit b [136]) := by
  change literal b (136) = decide (1 ≤ countLit b [136])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (136) <;> decide
theorem meaning138 (b : Nat → Bool) : literal (valuationOf b) (138) = decide (1 ≤ countLit b [138]) := by
  change literal b (138) = decide (1 ≤ countLit b [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (138) <;> decide
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
theorem meaning149 (b : Nat → Bool) : literal (valuationOf b) (149) = decide (1 ≤ countLit b [149]) := by
  change literal b (149) = decide (1 ≤ countLit b [149])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (149) <;> decide
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
theorem meaning167 (b : Nat → Bool) : literal (valuationOf b) (167) = decide (1 ≤ countLit b [167]) := by
  change literal b (167) = decide (1 ≤ countLit b [167])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (167) <;> decide
theorem meaning173 (b : Nat → Bool) : literal (valuationOf b) (173) = decide (1 ≤ countLit b [173]) := by
  change literal b (173) = decide (1 ≤ countLit b [173])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (173) <;> decide
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
theorem meaning188 (b : Nat → Bool) : literal (valuationOf b) (188) = decide (1 ≤ countLit b [188]) := by
  change literal b (188) = decide (1 ≤ countLit b [188])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (188) <;> decide
theorem meaning199 (b : Nat → Bool) : literal (valuationOf b) 199 = decide (1 ≤ count199 b) := rfl
theorem meaning201 (b : Nat → Bool) : literal (valuationOf b) 201 = decide (1 ≤ count201 b) := rfl
theorem meaning203 (b : Nat → Bool) : literal (valuationOf b) 203 = decide (1 ≤ count203 b) := rfl
theorem meaning205 (b : Nat → Bool) : literal (valuationOf b) 205 = decide (1 ≤ count205 b) := rfl
theorem meaning208 (b : Nat → Bool) : literal (valuationOf b) 208 = decide (2 ≤ count207 b) := rfl
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) 209 = decide (1 ≤ count209 b) := rfl
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) 211 = decide (1 ≤ count211 b) := rfl
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) 215 = decide (1 ≤ count215 b) := rfl
theorem meaning218 (b : Nat → Bool) : literal (valuationOf b) 218 = decide (2 ≤ count217 b) := rfl
theorem meaning220 (b : Nat → Bool) : literal (valuationOf b) 220 = decide (2 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) 238 = decide (2 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) 240 = decide (2 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) 242 = decide (2 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) 244 = decide (2 ≤ count243 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) 256 = decide (2 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning264 (b : Nat → Bool) : literal (valuationOf b) 264 = decide (2 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning276 (b : Nat → Bool) : literal (valuationOf b) 276 = decide (2 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning292 (b : Nat → Bool) : literal (valuationOf b) 292 = decide (2 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning340 (b : Nat → Bool) : literal (valuationOf b) 340 = decide (2 ≤ count339 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning1149 (b : Nat → Bool) : literal (valuationOf b) 1149 = decide (1 ≤ count1149 b) := rfl
theorem meaning1151 (b : Nat → Bool) : literal (valuationOf b) 1151 = decide (1 ≤ count1151 b) := rfl
theorem meaning1152 (b : Nat → Bool) : literal (valuationOf b) 1152 = decide (2 ≤ count1151 b) := rfl
theorem meaning1154 (b : Nat → Bool) : literal (valuationOf b) 1154 = decide (1 ≤ count1154 b) := rfl
theorem meaning1156 (b : Nat → Bool) : literal (valuationOf b) 1156 = decide (1 ≤ count1156 b) := rfl
theorem meaning1157 (b : Nat → Bool) : literal (valuationOf b) 1157 = decide (2 ≤ count1156 b) := rfl
theorem meaning1160 (b : Nat → Bool) : literal (valuationOf b) 1160 = decide (2 ≤ count1159 b) := rfl
theorem meaning1165 (b : Nat → Bool) : literal (valuationOf b) 1165 = decide (1 ≤ count1165 b) := rfl
theorem meaning1166 (b : Nat → Bool) : literal (valuationOf b) 1166 = decide (2 ≤ count1165 b) := rfl
theorem meaning1167 (b : Nat → Bool) : literal (valuationOf b) 1167 = decide (1 ≤ count1167 b) := rfl
theorem meaning1168 (b : Nat → Bool) : literal (valuationOf b) 1168 = decide (2 ≤ count1167 b) := rfl
theorem meaning1170 (b : Nat → Bool) : literal (valuationOf b) 1170 = decide (1 ≤ count1170 b) := rfl
theorem meaning1172 (b : Nat → Bool) : literal (valuationOf b) 1172 = decide (1 ≤ count1172 b) := rfl
theorem meaning1173 (b : Nat → Bool) : literal (valuationOf b) 1173 = decide (2 ≤ count1172 b) := rfl
theorem meaning1175 (b : Nat → Bool) : literal (valuationOf b) 1175 = decide (1 ≤ count1175 b) := rfl
theorem meaning1176 (b : Nat → Bool) : literal (valuationOf b) 1176 = decide (2 ≤ count1175 b) := rfl
theorem meaning1182 (b : Nat → Bool) : literal (valuationOf b) 1182 = decide (2 ≤ count1181 b) := rfl
theorem meaning1183 (b : Nat → Bool) : literal (valuationOf b) 1183 = decide (3 ≤ count1181 b) := rfl
theorem meaning1184 (b : Nat → Bool) : literal (valuationOf b) 1184 = decide (4 ≤ count1181 b) := rfl
theorem meaning1190 (b : Nat → Bool) : literal (valuationOf b) 1190 = decide (1 ≤ count1190 b) := rfl
theorem meaning1192 (b : Nat → Bool) : literal (valuationOf b) 1192 = decide (1 ≤ count1192 b) := rfl
theorem meaning1193 (b : Nat → Bool) : literal (valuationOf b) 1193 = decide (2 ≤ count1192 b) := rfl
theorem meaning1195 (b : Nat → Bool) : literal (valuationOf b) 1195 = decide (1 ≤ count1195 b) := rfl
theorem meaning1197 (b : Nat → Bool) : literal (valuationOf b) 1197 = decide (1 ≤ count1197 b) := rfl
theorem meaning1200 (b : Nat → Bool) : literal (valuationOf b) 1200 = decide (1 ≤ count1200 b) := rfl
theorem meaning1201 (b : Nat → Bool) : literal (valuationOf b) 1201 = decide (2 ≤ count1200 b) := rfl
theorem meaning1202 (b : Nat → Bool) : literal (valuationOf b) 1202 = decide (3 ≤ count1200 b) := rfl
theorem meaning1206 (b : Nat → Bool) : literal (valuationOf b) 1206 = decide (1 ≤ count1206 b) := rfl
theorem meaning1207 (b : Nat → Bool) : literal (valuationOf b) 1207 = decide (2 ≤ count1206 b) := rfl
theorem meaning1208 (b : Nat → Bool) : literal (valuationOf b) 1208 = decide (1 ≤ count1208 b) := rfl
theorem meaning1209 (b : Nat → Bool) : literal (valuationOf b) 1209 = decide (2 ≤ count1208 b) := rfl
theorem meaning1211 (b : Nat → Bool) : literal (valuationOf b) 1211 = decide (1 ≤ count1211 b) := rfl
theorem meaning1213 (b : Nat → Bool) : literal (valuationOf b) 1213 = decide (1 ≤ count1213 b) := rfl
theorem meaning1214 (b : Nat → Bool) : literal (valuationOf b) 1214 = decide (2 ≤ count1213 b) := rfl
theorem meaning1216 (b : Nat → Bool) : literal (valuationOf b) 1216 = decide (1 ≤ count1216 b) := rfl
theorem meaning1217 (b : Nat → Bool) : literal (valuationOf b) 1217 = decide (2 ≤ count1216 b) := rfl
theorem meaning1223 (b : Nat → Bool) : literal (valuationOf b) 1223 = decide (2 ≤ count1222 b) := rfl
theorem meaning1224 (b : Nat → Bool) : literal (valuationOf b) 1224 = decide (3 ≤ count1222 b) := rfl
theorem meaning1225 (b : Nat → Bool) : literal (valuationOf b) 1225 = decide (4 ≤ count1222 b) := rfl
theorem meaning1236 (b : Nat → Bool) : literal (valuationOf b) 1236 = decide (6 ≤ count1231 b) := rfl
theorem meaning1240 (b : Nat → Bool) : literal (valuationOf b) 1240 = decide (1 ≤ count1240 b) := rfl
theorem meaning1242 (b : Nat → Bool) : literal (valuationOf b) 1242 = decide (1 ≤ count1242 b) := rfl
theorem meaning1250 (b : Nat → Bool) : literal (valuationOf b) 1250 = decide (1 ≤ count1250 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (1 ≤ count1272 b) := rfl
theorem meaning1281 (b : Nat → Bool) : literal (valuationOf b) 1281 = decide (1 ≤ count1281 b) := rfl
theorem meaning1283 (b : Nat → Bool) : literal (valuationOf b) 1283 = decide (1 ≤ count1283 b) := rfl
theorem meaning1284 (b : Nat → Bool) : literal (valuationOf b) 1284 = decide (2 ≤ count1283 b) := rfl
theorem meaning1286 (b : Nat → Bool) : literal (valuationOf b) 1286 = decide (1 ≤ count1286 b) := rfl
theorem meaning1288 (b : Nat → Bool) : literal (valuationOf b) 1288 = decide (1 ≤ count1288 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (1 ≤ count1291 b) := rfl
theorem meaning1292 (b : Nat → Bool) : literal (valuationOf b) 1292 = decide (2 ≤ count1291 b) := rfl
theorem meaning1293 (b : Nat → Bool) : literal (valuationOf b) 1293 = decide (3 ≤ count1291 b) := rfl
theorem meaning1297 (b : Nat → Bool) : literal (valuationOf b) 1297 = decide (1 ≤ count1297 b) := rfl
theorem meaning1299 (b : Nat → Bool) : literal (valuationOf b) 1299 = decide (1 ≤ count1299 b) := rfl
theorem meaning1302 (b : Nat → Bool) : literal (valuationOf b) 1302 = decide (1 ≤ count1302 b) := rfl
theorem meaning1306 (b : Nat → Bool) : literal (valuationOf b) 1306 = decide (1 ≤ count1306 b) := rfl
theorem meaning1310 (b : Nat → Bool) : literal (valuationOf b) 1310 = decide (1 ≤ count1310 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (2 ≤ count1317 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (3 ≤ count1317 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (3 ≤ count1326 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (9 ≤ count1335 b) := rfl
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
end Snake9.Regrowth.E112149
