import E112147Data
namespace Snake9.Regrowth.E112147
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 100 then (if i < 50 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (4 : Vertex)))) else (if i < 4 then decide (InPath q (6 : Vertex)) else (if i < 5 then decide (InPath q (19 : Vertex)) else decide (InPath q (22 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (23 : Vertex)) else (if i < 8 then decide (InPath q (72 : Vertex)) else decide (InPath q (104 : Vertex)))) else (if i < 10 then decide (InPath q (160 : Vertex)) else (if i < 11 then decide (InPath q (164 : Vertex)) else decide (InPath q (166 : Vertex)))))) else (if i < 18 then (if i < 15 then (if i < 13 then decide (InPath q (168 : Vertex)) else (if i < 14 then decide (InPath q (169 : Vertex)) else decide (InPath q (170 : Vertex)))) else (if i < 16 then decide (InPath q (171 : Vertex)) else (if i < 17 then decide (InPath q (174 : Vertex)) else decide (InPath q (179 : Vertex))))) else (if i < 21 then (if i < 19 then decide (InPath q (180 : Vertex)) else (if i < 20 then decide (InPath q (181 : Vertex)) else decide (InPath q (182 : Vertex)))) else (if i < 23 then (if i < 22 then decide (InPath q (183 : Vertex)) else decide (InPath q (184 : Vertex))) else (if i < 24 then decide (InPath q (185 : Vertex)) else decide (InPath q (186 : Vertex))))))) else (if i < 37 then (if i < 31 then (if i < 28 then (if i < 26 then decide (InPath q (187 : Vertex)) else (if i < 27 then decide (InPath q (189 : Vertex)) else decide (InPath q (224 : Vertex)))) else (if i < 29 then decide (InPath q (225 : Vertex)) else (if i < 30 then decide (InPath q (229 : Vertex)) else decide (InPath q (231 : Vertex))))) else (if i < 34 then (if i < 32 then decide (InPath q (232 : Vertex)) else (if i < 33 then decide (InPath q (233 : Vertex)) else decide (InPath q (238 : Vertex)))) else (if i < 35 then decide (InPath q (239 : Vertex)) else (if i < 36 then decide (InPath q (240 : Vertex)) else decide (InPath q (242 : Vertex)))))) else (if i < 43 then (if i < 40 then (if i < 38 then decide (InPath q (243 : Vertex)) else (if i < 39 then decide (InPath q (244 : Vertex)) else decide (InPath q (252 : Vertex)))) else (if i < 41 then decide (InPath q (254 : Vertex)) else (if i < 42 then decide (InPath q (255 : Vertex)) else decide (InPath q (256 : Vertex))))) else (if i < 46 then (if i < 44 then decide (InPath q (257 : Vertex)) else (if i < 45 then decide (InPath q (261 : Vertex)) else decide (InPath q (263 : Vertex)))) else (if i < 48 then (if i < 47 then decide (InPath q (264 : Vertex)) else decide (InPath q (265 : Vertex))) else (if i < 49 then decide (InPath q (270 : Vertex)) else decide (InPath q (271 : Vertex)))))))) else (if i < 75 then (if i < 62 then (if i < 56 then (if i < 53 then (if i < 51 then decide (InPath q (272 : Vertex)) else (if i < 52 then decide (InPath q (274 : Vertex)) else decide (InPath q (275 : Vertex)))) else (if i < 54 then decide (InPath q (276 : Vertex)) else (if i < 55 then decide (InPath q (283 : Vertex)) else decide (InPath q (284 : Vertex))))) else (if i < 59 then (if i < 57 then decide (InPath q (286 : Vertex)) else (if i < 58 then decide (InPath q (352 : Vertex)) else decide (InPath q (353 : Vertex)))) else (if i < 60 then decide (InPath q (357 : Vertex)) else (if i < 61 then decide (InPath q (359 : Vertex)) else decide (InPath q (360 : Vertex)))))) else (if i < 68 then (if i < 65 then (if i < 63 then decide (InPath q (361 : Vertex)) else (if i < 64 then decide (InPath q (366 : Vertex)) else decide (InPath q (367 : Vertex)))) else (if i < 66 then decide (InPath q (368 : Vertex)) else (if i < 67 then decide (InPath q (370 : Vertex)) else decide (InPath q (371 : Vertex))))) else (if i < 71 then (if i < 69 then decide (InPath q (372 : Vertex)) else (if i < 70 then decide (InPath q (380 : Vertex)) else decide (InPath q (382 : Vertex)))) else (if i < 73 then (if i < 72 then decide (InPath q (392 : Vertex)) else decide (InPath q (395 : Vertex))) else (if i < 74 then decide (InPath q (408 : Vertex)) else decide (InPath q (410 : Vertex))))))) else (if i < 87 then (if i < 81 then (if i < 78 then (if i < 76 then decide (InPath q (411 : Vertex)) else (if i < 77 then decide (InPath q (416 : Vertex)) else decide (InPath q (424 : Vertex)))) else (if i < 79 then decide (InPath q (430 : Vertex)) else (if i < 80 then decide (InPath q (432 : Vertex)) else decide (InPath q (434 : Vertex))))) else (if i < 84 then (if i < 82 then decide (InPath q (436 : Vertex)) else (if i < 83 then decide (InPath q (443 : Vertex)) else decide (InPath q (444 : Vertex)))) else (if i < 85 then decide (InPath q (446 : Vertex)) else (if i < 86 then decide (InPath q (447 : Vertex)) else decide (InPath q (448 : Vertex)))))) else (if i < 93 then (if i < 90 then (if i < 88 then decide (InPath q (449 : Vertex)) else (if i < 89 then decide (InPath q (453 : Vertex)) else decide (InPath q (455 : Vertex)))) else (if i < 91 then decide (InPath q (456 : Vertex)) else (if i < 92 then decide (InPath q (457 : Vertex)) else decide (InPath q (462 : Vertex))))) else (if i < 96 then (if i < 94 then decide (InPath q (463 : Vertex)) else (if i < 95 then decide (InPath q (464 : Vertex)) else decide (InPath q (466 : Vertex)))) else (if i < 98 then (if i < 97 then decide (InPath q (467 : Vertex)) else decide (InPath q (468 : Vertex))) else (if i < 99 then decide (InPath q (475 : Vertex)) else decide (InPath q (476 : Vertex))))))))) else (if i < 150 then (if i < 125 then (if i < 112 then (if i < 106 then (if i < 103 then (if i < 101 then decide (InPath q (478 : Vertex)) else (if i < 102 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (4 : Vertex)))) else (if i < 104 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else (if i < 105 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else decide (BallClauseLogic.Endpoint q (22 : Vertex))))) else (if i < 109 then (if i < 107 then decide (BallClauseLogic.Endpoint q (23 : Vertex)) else (if i < 108 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else decide (BallClauseLogic.Endpoint q (104 : Vertex)))) else (if i < 110 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else (if i < 111 then decide (BallClauseLogic.Endpoint q (164 : Vertex)) else decide (BallClauseLogic.Endpoint q (166 : Vertex)))))) else (if i < 118 then (if i < 115 then (if i < 113 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else (if i < 114 then decide (BallClauseLogic.Endpoint q (169 : Vertex)) else decide (BallClauseLogic.Endpoint q (170 : Vertex)))) else (if i < 116 then decide (BallClauseLogic.Endpoint q (171 : Vertex)) else (if i < 117 then decide (BallClauseLogic.Endpoint q (174 : Vertex)) else decide (BallClauseLogic.Endpoint q (179 : Vertex))))) else (if i < 121 then (if i < 119 then decide (BallClauseLogic.Endpoint q (180 : Vertex)) else (if i < 120 then decide (BallClauseLogic.Endpoint q (181 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex)))) else (if i < 123 then (if i < 122 then decide (BallClauseLogic.Endpoint q (183 : Vertex)) else decide (BallClauseLogic.Endpoint q (184 : Vertex))) else (if i < 124 then decide (BallClauseLogic.Endpoint q (185 : Vertex)) else decide (BallClauseLogic.Endpoint q (186 : Vertex))))))) else (if i < 137 then (if i < 131 then (if i < 128 then (if i < 126 then decide (BallClauseLogic.Endpoint q (187 : Vertex)) else (if i < 127 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (224 : Vertex)))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (225 : Vertex)) else (if i < 130 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (231 : Vertex))))) else (if i < 134 then (if i < 132 then decide (BallClauseLogic.Endpoint q (232 : Vertex)) else (if i < 133 then decide (BallClauseLogic.Endpoint q (233 : Vertex)) else decide (BallClauseLogic.Endpoint q (238 : Vertex)))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (239 : Vertex)) else (if i < 136 then decide (BallClauseLogic.Endpoint q (240 : Vertex)) else decide (BallClauseLogic.Endpoint q (242 : Vertex)))))) else (if i < 143 then (if i < 140 then (if i < 138 then decide (BallClauseLogic.Endpoint q (243 : Vertex)) else (if i < 139 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (252 : Vertex)))) else (if i < 141 then decide (BallClauseLogic.Endpoint q (254 : Vertex)) else (if i < 142 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else decide (BallClauseLogic.Endpoint q (256 : Vertex))))) else (if i < 146 then (if i < 144 then decide (BallClauseLogic.Endpoint q (257 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (263 : Vertex)))) else (if i < 148 then (if i < 147 then decide (BallClauseLogic.Endpoint q (264 : Vertex)) else decide (BallClauseLogic.Endpoint q (265 : Vertex))) else (if i < 149 then decide (BallClauseLogic.Endpoint q (270 : Vertex)) else decide (BallClauseLogic.Endpoint q (271 : Vertex)))))))) else (if i < 175 then (if i < 162 then (if i < 156 then (if i < 153 then (if i < 151 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else (if i < 152 then decide (BallClauseLogic.Endpoint q (274 : Vertex)) else decide (BallClauseLogic.Endpoint q (275 : Vertex)))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else (if i < 155 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else decide (BallClauseLogic.Endpoint q (284 : Vertex))))) else (if i < 159 then (if i < 157 then decide (BallClauseLogic.Endpoint q (286 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (352 : Vertex)) else decide (BallClauseLogic.Endpoint q (353 : Vertex)))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (360 : Vertex)))))) else (if i < 168 then (if i < 165 then (if i < 163 then decide (BallClauseLogic.Endpoint q (361 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (366 : Vertex)) else decide (BallClauseLogic.Endpoint q (367 : Vertex)))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (368 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (370 : Vertex)) else decide (BallClauseLogic.Endpoint q (371 : Vertex))))) else (if i < 171 then (if i < 169 then decide (BallClauseLogic.Endpoint q (372 : Vertex)) else (if i < 170 then decide (BallClauseLogic.Endpoint q (380 : Vertex)) else decide (BallClauseLogic.Endpoint q (382 : Vertex)))) else (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (392 : Vertex)) else decide (BallClauseLogic.Endpoint q (395 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (408 : Vertex)) else decide (BallClauseLogic.Endpoint q (410 : Vertex))))))) else (if i < 188 then (if i < 181 then (if i < 178 then (if i < 176 then decide (BallClauseLogic.Endpoint q (411 : Vertex)) else (if i < 177 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex)))) else (if i < 179 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else (if i < 180 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else decide (BallClauseLogic.Endpoint q (434 : Vertex))))) else (if i < 184 then (if i < 182 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else (if i < 183 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (444 : Vertex)))) else (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (446 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (448 : Vertex)) else decide (BallClauseLogic.Endpoint q (449 : Vertex)))))) else (if i < 194 then (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (455 : Vertex)) else decide (BallClauseLogic.Endpoint q (456 : Vertex)))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else (if i < 193 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (463 : Vertex))))) else (if i < 197 then (if i < 195 then decide (BallClauseLogic.Endpoint q (464 : Vertex)) else (if i < 196 then decide (BallClauseLogic.Endpoint q (466 : Vertex)) else decide (BallClauseLogic.Endpoint q (467 : Vertex)))) else (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else decide (BallClauseLogic.Endpoint q (475 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (476 : Vertex)) else decide (BallClauseLogic.Endpoint q (478 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count201 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count203 (b : Nat → Bool) : Nat := countLit b [101, 102, 103]
def count205 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count207 (b : Nat → Bool) : Nat := countLit b [104, 105, 106]
def count209 (b : Nat → Bool) : Nat := countLit b [101, 102, 103, 104, 105, 106]
def count211 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count213 (b : Nat → Bool) : Nat := countLit b [107, 108, 109]
def count215 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count217 (b : Nat → Bool) : Nat := countLit b [110, 111, 112]
def count219 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112]
def count221 (b : Nat → Bool) : Nat := countLit b [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]
def count223 (b : Nat → Bool) : Nat := countLit b [114, 115]
def count225 (b : Nat → Bool) : Nat := countLit b [113, 114, 115]
def count227 (b : Nat → Bool) : Nat := countLit b [117, 118]
def count229 (b : Nat → Bool) : Nat := countLit b [116, 117, 118]
def count231 (b : Nat → Bool) : Nat := countLit b [113, 114, 115, 116, 117, 118]
def count233 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count235 (b : Nat → Bool) : Nat := countLit b [119, 120, 121]
def count237 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count239 (b : Nat → Bool) : Nat := countLit b [122, 123, 124]
def count241 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122, 123, 124]
def count243 (b : Nat → Bool) : Nat := countLit b [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
def count247 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count259 (b : Nat → Bool) : Nat := countLit b [131, 132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
def count269 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count271 (b : Nat → Bool) : Nat := countLit b [137, 138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count275 (b : Nat → Bool) : Nat := countLit b [140, 141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count281 (b : Nat → Bool) : Nat := countLit b [143, 144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count287 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149]
def count289 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
def count295 (b : Nat → Bool) : Nat := countLit b [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [150, 151, 152]
def count301 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155]
def count307 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count313 (b : Nat → Bool) : Nat := countLit b [159, 160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 168]
def count325 (b : Nat → Bool) : Nat := countLit b [165, 166, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165, 166, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count331 (b : Nat → Bool) : Nat := countLit b [169, 170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count335 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count337 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [169, 170, 171, 172, 173, 174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175]
def count345 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count357 (b : Nat → Bool) : Nat := countLit b [182, 183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count361 (b : Nat → Bool) : Nat := countLit b [185, 186, 187]
def count363 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185, 186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count373 (b : Nat → Bool) : Nat := countLit b [191, 192, 193]
def count375 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191, 192, 193]
def count377 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count379 (b : Nat → Bool) : Nat := countLit b [194, 195, 196]
def count381 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count383 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count385 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200]
def count387 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197, 198, 199, 200]
def count389 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]
def count395 (b : Nat → Bool) : Nat := countLit b [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]
def count397 (b : Nat → Bool) : Nat := countLit b [3, 6]
def count399 (b : Nat → Bool) : Nat := countLit b [1, 3, 6]
def count402 (b : Nat → Bool) : Nat := countLit b [9, 11]
def count404 (b : Nat → Bool) : Nat := countLit b [7, 9, 11]
def count407 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 7, 9, 11]
def count413 (b : Nat → Bool) : Nat := countLit b [14, 18]
def count415 (b : Nat → Bool) : Nat := countLit b [13, 14, 18]
def count418 (b : Nat → Bool) : Nat := countLit b [22, 25]
def count420 (b : Nat → Bool) : Nat := countLit b [21, 22, 25]
def count423 (b : Nat → Bool) : Nat := countLit b [13, 14, 18, 21, 22, 25]
def count429 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 7, 9, 11, 13, 14, 18, 21, 22, 25]
def count441 (b : Nat → Bool) : Nat := countLit b [28, 30]
def count443 (b : Nat → Bool) : Nat := countLit b [26, 28, 30]
def count446 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count448 (b : Nat → Bool) : Nat := countLit b [31, 33, 35]
def count451 (b : Nat → Bool) : Nat := countLit b [26, 28, 30, 31, 33, 35]
def count457 (b : Nat → Bool) : Nat := countLit b [39, 41]
def count459 (b : Nat → Bool) : Nat := countLit b [37, 39, 41]
def count462 (b : Nat → Bool) : Nat := countLit b [45, 46]
def count464 (b : Nat → Bool) : Nat := countLit b [43, 45, 46]
def count467 (b : Nat → Bool) : Nat := countLit b [37, 39, 41, 43, 45, 46]
def count473 (b : Nat → Bool) : Nat := countLit b [26, 28, 30, 31, 33, 35, 37, 39, 41, 43, 45, 46]
def count485 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 7, 9, 11, 13, 14, 18, 21, 22, 25, 26, 28, 30, 31, 33, 35, 37, 39, 41, 43, 45, 46]
def count509 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count511 (b : Nat → Bool) : Nat := countLit b [48, 50, 52]
def count514 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count516 (b : Nat → Bool) : Nat := countLit b [55, 58, 60]
def count519 (b : Nat → Bool) : Nat := countLit b [48, 50, 52, 55, 58, 60]
def count525 (b : Nat → Bool) : Nat := countLit b [63, 65]
def count527 (b : Nat → Bool) : Nat := countLit b [61, 63, 65]
def count530 (b : Nat → Bool) : Nat := countLit b [69, 73]
def count532 (b : Nat → Bool) : Nat := countLit b [67, 69, 73]
def count535 (b : Nat → Bool) : Nat := countLit b [61, 63, 65, 67, 69, 73]
def count541 (b : Nat → Bool) : Nat := countLit b [48, 50, 52, 55, 58, 60, 61, 63, 65, 67, 69, 73]
def count553 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count555 (b : Nat → Bool) : Nat := countLit b [75, 77, 78]
def count558 (b : Nat → Bool) : Nat := countLit b [83, 85]
def count560 (b : Nat → Bool) : Nat := countLit b [79, 83, 85]
def count563 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 79, 83, 85]
def count569 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count571 (b : Nat → Bool) : Nat := countLit b [87, 89, 90]
def count574 (b : Nat → Bool) : Nat := countLit b [92, 94]
def count576 (b : Nat → Bool) : Nat := countLit b [96, 99]
def count578 (b : Nat → Bool) : Nat := countLit b [92, 94, 96, 99]
def count582 (b : Nat → Bool) : Nat := countLit b [87, 89, 90, 92, 94, 96, 99]
def count589 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 79, 83, 85, 87, 89, 90, 92, 94, 96, 99]
def count602 (b : Nat → Bool) : Nat := countLit b [48, 50, 52, 55, 58, 60, 61, 63, 65, 67, 69, 73, 75, 77, 78, 79, 83, 85, 87, 89, 90, 92, 94, 96, 99]
def count627 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 7, 9, 11, 13, 14, 18, 21, 22, 25, 26, 28, 30, 31, 33, 35, 37, 39, 41, 43, 45, 46, 48, 50, 52, 55, 58, 60, 61, 63, 65, 67, 69, 73, 75, 77, 78, 79, 83, 85, 87, 89, 90, 92, 94, 96, 99]
def count669 (b : Nat → Bool) : Nat := countLit b [-3, -6]
def count671 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6]
def count674 (b : Nat → Bool) : Nat := countLit b [-9, -11]
def count676 (b : Nat → Bool) : Nat := countLit b [-7, -9, -11]
def count679 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -7, -9, -11]
def count685 (b : Nat → Bool) : Nat := countLit b [-14, -18]
def count687 (b : Nat → Bool) : Nat := countLit b [-13, -14, -18]
def count690 (b : Nat → Bool) : Nat := countLit b [-22, -25]
def count692 (b : Nat → Bool) : Nat := countLit b [-21, -22, -25]
def count695 (b : Nat → Bool) : Nat := countLit b [-13, -14, -18, -21, -22, -25]
def count701 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]
def count710 (b : Nat → Bool) : Nat := countLit b [-28, -30]
def count712 (b : Nat → Bool) : Nat := countLit b [-26, -28, -30]
def count715 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count717 (b : Nat → Bool) : Nat := countLit b [-31, -33, -35]
def count720 (b : Nat → Bool) : Nat := countLit b [-26, -28, -30, -31, -33, -35]
def count726 (b : Nat → Bool) : Nat := countLit b [-39, -41]
def count728 (b : Nat → Bool) : Nat := countLit b [-37, -39, -41]
def count731 (b : Nat → Bool) : Nat := countLit b [-45, -46]
def count733 (b : Nat → Bool) : Nat := countLit b [-43, -45, -46]
def count736 (b : Nat → Bool) : Nat := countLit b [-37, -39, -41, -43, -45, -46]
def count742 (b : Nat → Bool) : Nat := countLit b [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]
def count751 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]
def count760 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count762 (b : Nat → Bool) : Nat := countLit b [-48, -50, -52]
def count765 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count767 (b : Nat → Bool) : Nat := countLit b [-55, -58, -60]
def count770 (b : Nat → Bool) : Nat := countLit b [-48, -50, -52, -55, -58, -60]
def count776 (b : Nat → Bool) : Nat := countLit b [-63, -65]
def count778 (b : Nat → Bool) : Nat := countLit b [-61, -63, -65]
def count781 (b : Nat → Bool) : Nat := countLit b [-69, -73]
def count783 (b : Nat → Bool) : Nat := countLit b [-67, -69, -73]
def count786 (b : Nat → Bool) : Nat := countLit b [-61, -63, -65, -67, -69, -73]
def count792 (b : Nat → Bool) : Nat := countLit b [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73]
def count801 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count803 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78]
def count806 (b : Nat → Bool) : Nat := countLit b [-83, -85]
def count808 (b : Nat → Bool) : Nat := countLit b [-79, -83, -85]
def count811 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -79, -83, -85]
def count817 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count819 (b : Nat → Bool) : Nat := countLit b [-87, -89, -90]
def count822 (b : Nat → Bool) : Nat := countLit b [-92, -94]
def count824 (b : Nat → Bool) : Nat := countLit b [-96, -99]
def count826 (b : Nat → Bool) : Nat := countLit b [-92, -94, -96, -99]
def count830 (b : Nat → Bool) : Nat := countLit b [-87, -89, -90, -92, -94, -96, -99]
def count837 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]
def count846 (b : Nat → Bool) : Nat := countLit b [-48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]
def count855 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25, -26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46, -48, -50, -52, -55, -58, -60, -61, -63, -65, -67, -69, -73, -75, -77, -78, -79, -83, -85, -87, -89, -90, -92, -94, -96, -99]
def count864 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count866 (b : Nat → Bool) : Nat := countLit b [2, 4, 5]
def count869 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count871 (b : Nat → Bool) : Nat := countLit b [8, 10, 12]
def count874 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 8, 10, 12]
def count880 (b : Nat → Bool) : Nat := countLit b [16, 17]
def count882 (b : Nat → Bool) : Nat := countLit b [15, 16, 17]
def count885 (b : Nat → Bool) : Nat := countLit b [20, 23]
def count887 (b : Nat → Bool) : Nat := countLit b [19, 20, 23]
def count890 (b : Nat → Bool) : Nat := countLit b [15, 16, 17, 19, 20, 23]
def count896 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 8, 10, 12, 15, 16, 17, 19, 20, 23]
def count908 (b : Nat → Bool) : Nat := countLit b [27, 29]
def count910 (b : Nat → Bool) : Nat := countLit b [24, 27, 29]
def count913 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count915 (b : Nat → Bool) : Nat := countLit b [32, 34, 36]
def count918 (b : Nat → Bool) : Nat := countLit b [24, 27, 29, 32, 34, 36]
def count924 (b : Nat → Bool) : Nat := countLit b [40, 42]
def count926 (b : Nat → Bool) : Nat := countLit b [38, 40, 42]
def count929 (b : Nat → Bool) : Nat := countLit b [44, 47]
def count931 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count933 (b : Nat → Bool) : Nat := countLit b [44, 47, 49, 51]
def count937 (b : Nat → Bool) : Nat := countLit b [38, 40, 42, 44, 47, 49, 51]
def count944 (b : Nat → Bool) : Nat := countLit b [24, 27, 29, 32, 34, 36, 38, 40, 42, 44, 47, 49, 51]
def count957 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 8, 10, 12, 15, 16, 17, 19, 20, 23, 24, 27, 29, 32, 34, 36, 38, 40, 42, 44, 47, 49, 51]
def count982 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count984 (b : Nat → Bool) : Nat := countLit b [53, 54, 56]
def count987 (b : Nat → Bool) : Nat := countLit b [59, 62]
def count989 (b : Nat → Bool) : Nat := countLit b [57, 59, 62]
def count992 (b : Nat → Bool) : Nat := countLit b [53, 54, 56, 57, 59, 62]
def count998 (b : Nat → Bool) : Nat := countLit b [66, 68]
def count1000 (b : Nat → Bool) : Nat := countLit b [64, 66, 68]
def count1003 (b : Nat → Bool) : Nat := countLit b [70, 71]
def count1005 (b : Nat → Bool) : Nat := countLit b [72, 74]
def count1007 (b : Nat → Bool) : Nat := countLit b [70, 71, 72, 74]
def count1011 (b : Nat → Bool) : Nat := countLit b [64, 66, 68, 70, 71, 72, 74]
def count1018 (b : Nat → Bool) : Nat := countLit b [53, 54, 56, 57, 59, 62, 64, 66, 68, 70, 71, 72, 74]
def count1031 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count1033 (b : Nat → Bool) : Nat := countLit b [76, 80, 81]
def count1036 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count1038 (b : Nat → Bool) : Nat := countLit b [82, 84, 86]
def count1041 (b : Nat → Bool) : Nat := countLit b [76, 80, 81, 82, 84, 86]
def count1047 (b : Nat → Bool) : Nat := countLit b [91, 93]
def count1049 (b : Nat → Bool) : Nat := countLit b [88, 91, 93]
def count1052 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count1054 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count1056 (b : Nat → Bool) : Nat := countLit b [95, 97, 98, 100]
def count1060 (b : Nat → Bool) : Nat := countLit b [88, 91, 93, 95, 97, 98, 100]
def count1067 (b : Nat → Bool) : Nat := countLit b [76, 80, 81, 82, 84, 86, 88, 91, 93, 95, 97, 98, 100]
def count1080 (b : Nat → Bool) : Nat := countLit b [53, 54, 56, 57, 59, 62, 64, 66, 68, 70, 71, 72, 74, 76, 80, 81, 82, 84, 86, 88, 91, 93, 95, 97, 98, 100]
def count1106 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 8, 10, 12, 15, 16, 17, 19, 20, 23, 24, 27, 29, 32, 34, 36, 38, 40, 42, 44, 47, 49, 51, 53, 54, 56, 57, 59, 62, 64, 66, 68, 70, 71, 72, 74, 76, 80, 81, 82, 84, 86, 88, 91, 93, 95, 97, 98, 100]
def count1148 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1150 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5]
def count1153 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count1155 (b : Nat → Bool) : Nat := countLit b [-8, -10, -12]
def count1158 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -8, -10, -12]
def count1164 (b : Nat → Bool) : Nat := countLit b [-16, -17]
def count1166 (b : Nat → Bool) : Nat := countLit b [-15, -16, -17]
def count1169 (b : Nat → Bool) : Nat := countLit b [-20, -23]
def count1171 (b : Nat → Bool) : Nat := countLit b [-19, -20, -23]
def count1174 (b : Nat → Bool) : Nat := countLit b [-15, -16, -17, -19, -20, -23]
def count1180 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -8, -10, -12, -15, -16, -17, -19, -20, -23]
def count1191 (b : Nat → Bool) : Nat := countLit b [-27, -29]
def count1193 (b : Nat → Bool) : Nat := countLit b [-24, -27, -29]
def count1196 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count1198 (b : Nat → Bool) : Nat := countLit b [-32, -34, -36]
def count1201 (b : Nat → Bool) : Nat := countLit b [-24, -27, -29, -32, -34, -36]
def count1207 (b : Nat → Bool) : Nat := countLit b [-40, -42]
def count1209 (b : Nat → Bool) : Nat := countLit b [-38, -40, -42]
def count1212 (b : Nat → Bool) : Nat := countLit b [-44, -47]
def count1214 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count1216 (b : Nat → Bool) : Nat := countLit b [-44, -47, -49, -51]
def count1220 (b : Nat → Bool) : Nat := countLit b [-38, -40, -42, -44, -47, -49, -51]
def count1227 (b : Nat → Bool) : Nat := countLit b [-24, -27, -29, -32, -34, -36, -38, -40, -42, -44, -47, -49, -51]
def count1238 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -8, -10, -12, -15, -16, -17, -19, -20, -23, -24, -27, -29, -32, -34, -36, -38, -40, -42, -44, -47, -49, -51]
def count1249 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count1251 (b : Nat → Bool) : Nat := countLit b [-53, -54, -56]
def count1254 (b : Nat → Bool) : Nat := countLit b [-59, -62]
def count1256 (b : Nat → Bool) : Nat := countLit b [-57, -59, -62]
def count1259 (b : Nat → Bool) : Nat := countLit b [-53, -54, -56, -57, -59, -62]
def count1265 (b : Nat → Bool) : Nat := countLit b [-66, -68]
def count1267 (b : Nat → Bool) : Nat := countLit b [-64, -66, -68]
def count1270 (b : Nat → Bool) : Nat := countLit b [-70, -71]
def count1272 (b : Nat → Bool) : Nat := countLit b [-72, -74]
def count1274 (b : Nat → Bool) : Nat := countLit b [-70, -71, -72, -74]
def count1278 (b : Nat → Bool) : Nat := countLit b [-64, -66, -68, -70, -71, -72, -74]
def count1285 (b : Nat → Bool) : Nat := countLit b [-53, -54, -56, -57, -59, -62, -64, -66, -68, -70, -71, -72, -74]
def count1296 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count1298 (b : Nat → Bool) : Nat := countLit b [-76, -80, -81]
def count1301 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count1303 (b : Nat → Bool) : Nat := countLit b [-82, -84, -86]
def count1306 (b : Nat → Bool) : Nat := countLit b [-76, -80, -81, -82, -84, -86]
def count1312 (b : Nat → Bool) : Nat := countLit b [-91, -93]
def count1314 (b : Nat → Bool) : Nat := countLit b [-88, -91, -93]
def count1317 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count1319 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count1321 (b : Nat → Bool) : Nat := countLit b [-95, -97, -98, -100]
def count1325 (b : Nat → Bool) : Nat := countLit b [-88, -91, -93, -95, -97, -98, -100]
def count1332 (b : Nat → Bool) : Nat := countLit b [-76, -80, -81, -82, -84, -86, -88, -91, -93, -95, -97, -98, -100]
def count1343 (b : Nat → Bool) : Nat := countLit b [-53, -54, -56, -57, -59, -62, -64, -66, -68, -70, -71, -72, -74, -76, -80, -81, -82, -84, -86, -88, -91, -93, -95, -97, -98, -100]
def count1354 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -8, -10, -12, -15, -16, -17, -19, -20, -23, -24, -27, -29, -32, -34, -36, -38, -40, -42, -44, -47, -49, -51, -53, -54, -56, -57, -59, -62, -64, -66, -68, -70, -71, -72, -74, -76, -80, -81, -82, -84, -86, -88, -91, -93, -95, -97, -98, -100]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 682 then (if i < 341 then (if i < 170 then (if i < 85 then (if i < 42 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 7 then (if i < 6 then b 5 else b 6) else (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)))) else (if i < 15 then (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else (if i < 14 then b 13 else b 14))) else (if i < 18 then (if i < 16 then b 15 else (if i < 17 then b 16 else b 17)) else (if i < 19 then b 18 else (if i < 20 then b 19 else b 20))))) else (if i < 31 then (if i < 26 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else (if i < 25 then b 24 else b 25))) else (if i < 28 then (if i < 27 then b 26 else b 27) else (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)))) else (if i < 36 then (if i < 33 then (if i < 32 then b 31 else b 32) else (if i < 34 then b 33 else (if i < 35 then b 34 else b 35))) else (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)))))) else (if i < 63 then (if i < 52 then (if i < 47 then (if i < 44 then (if i < 43 then b 42 else b 43) else (if i < 45 then b 44 else (if i < 46 then b 45 else b 46))) else (if i < 49 then (if i < 48 then b 47 else b 48) else (if i < 50 then b 49 else (if i < 51 then b 50 else b 51)))) else (if i < 57 then (if i < 54 then (if i < 53 then b 52 else b 53) else (if i < 55 then b 54 else (if i < 56 then b 55 else b 56))) else (if i < 60 then (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)) else (if i < 61 then b 60 else (if i < 62 then b 61 else b 62))))) else (if i < 74 then (if i < 68 then (if i < 65 then (if i < 64 then b 63 else b 64) else (if i < 66 then b 65 else (if i < 67 then b 66 else b 67))) else (if i < 71 then (if i < 69 then b 68 else (if i < 70 then b 69 else b 70)) else (if i < 72 then b 71 else (if i < 73 then b 72 else b 73)))) else (if i < 79 then (if i < 76 then (if i < 75 then b 74 else b 75) else (if i < 77 then b 76 else (if i < 78 then b 77 else b 78))) else (if i < 82 then (if i < 80 then b 79 else (if i < 81 then b 80 else b 81)) else (if i < 83 then b 82 else (if i < 84 then b 83 else b 84))))))) else (if i < 127 then (if i < 106 then (if i < 95 then (if i < 90 then (if i < 87 then (if i < 86 then b 85 else b 86) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))) else (if i < 92 then (if i < 91 then b 90 else b 91) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94)))) else (if i < 100 then (if i < 97 then (if i < 96 then b 95 else b 96) else (if i < 98 then b 97 else (if i < 99 then b 98 else b 99))) else (if i < 103 then (if i < 101 then b 100 else (if i < 102 then b 101 else b 102)) else (if i < 104 then b 103 else (if i < 105 then b 104 else b 105))))) else (if i < 116 then (if i < 111 then (if i < 108 then (if i < 107 then b 106 else b 107) else (if i < 109 then b 108 else (if i < 110 then b 109 else b 110))) else (if i < 113 then (if i < 112 then b 111 else b 112) else (if i < 114 then b 113 else (if i < 115 then b 114 else b 115)))) else (if i < 121 then (if i < 118 then (if i < 117 then b 116 else b 117) else (if i < 119 then b 118 else (if i < 120 then b 119 else b 120))) else (if i < 124 then (if i < 122 then b 121 else (if i < 123 then b 122 else b 123)) else (if i < 125 then b 124 else (if i < 126 then b 125 else b 126)))))) else (if i < 148 then (if i < 137 then (if i < 132 then (if i < 129 then (if i < 128 then b 127 else b 128) else (if i < 130 then b 129 else (if i < 131 then b 130 else b 131))) else (if i < 134 then (if i < 133 then b 132 else b 133) else (if i < 135 then b 134 else (if i < 136 then b 135 else b 136)))) else (if i < 142 then (if i < 139 then (if i < 138 then b 137 else b 138) else (if i < 140 then b 139 else (if i < 141 then b 140 else b 141))) else (if i < 145 then (if i < 143 then b 142 else (if i < 144 then b 143 else b 144)) else (if i < 146 then b 145 else (if i < 147 then b 146 else b 147))))) else (if i < 159 then (if i < 153 then (if i < 150 then (if i < 149 then b 148 else b 149) else (if i < 151 then b 150 else (if i < 152 then b 151 else b 152))) else (if i < 156 then (if i < 154 then b 153 else (if i < 155 then b 154 else b 155)) else (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)))) else (if i < 164 then (if i < 161 then (if i < 160 then b 159 else b 160) else (if i < 162 then b 161 else (if i < 163 then b 162 else b 163))) else (if i < 167 then (if i < 165 then b 164 else (if i < 166 then b 165 else b 166)) else (if i < 168 then b 167 else (if i < 169 then b 168 else b 169)))))))) else (if i < 255 then (if i < 212 then (if i < 191 then (if i < 180 then (if i < 175 then (if i < 172 then (if i < 171 then b 170 else b 171) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174))) else (if i < 177 then (if i < 176 then b 175 else b 176) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)))) else (if i < 185 then (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else (if i < 184 then b 183 else b 184))) else (if i < 188 then (if i < 186 then b 185 else (if i < 187 then b 186 else b 187)) else (if i < 189 then b 188 else (if i < 190 then b 189 else b 190))))) else (if i < 201 then (if i < 196 then (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else (if i < 195 then b 194 else b 195))) else (if i < 198 then (if i < 197 then b 196 else b 197) else (if i < 199 then b 198 else (if i < 200 then b 199 else b 200)))) else (if i < 206 then (if i < 203 then (if i < 202 then decide (1 ≤ count201 b) else decide (2 ≤ count201 b)) else (if i < 204 then decide (1 ≤ count203 b) else (if i < 205 then decide (2 ≤ count203 b) else decide (1 ≤ count205 b)))) else (if i < 209 then (if i < 207 then decide (2 ≤ count205 b) else (if i < 208 then decide (1 ≤ count207 b) else decide (2 ≤ count207 b))) else (if i < 210 then decide (1 ≤ count209 b) else (if i < 211 then decide (2 ≤ count209 b) else decide (1 ≤ count211 b))))))) else (if i < 233 then (if i < 222 then (if i < 217 then (if i < 214 then (if i < 213 then decide (2 ≤ count211 b) else decide (1 ≤ count213 b)) else (if i < 215 then decide (2 ≤ count213 b) else (if i < 216 then decide (1 ≤ count215 b) else decide (2 ≤ count215 b)))) else (if i < 219 then (if i < 218 then decide (1 ≤ count217 b) else decide (2 ≤ count217 b)) else (if i < 220 then decide (1 ≤ count219 b) else (if i < 221 then decide (2 ≤ count219 b) else decide (1 ≤ count221 b))))) else (if i < 227 then (if i < 224 then (if i < 223 then decide (2 ≤ count221 b) else decide (1 ≤ count223 b)) else (if i < 225 then decide (2 ≤ count223 b) else (if i < 226 then decide (1 ≤ count225 b) else decide (2 ≤ count225 b)))) else (if i < 230 then (if i < 228 then decide (1 ≤ count227 b) else (if i < 229 then decide (2 ≤ count227 b) else decide (1 ≤ count229 b))) else (if i < 231 then decide (2 ≤ count229 b) else (if i < 232 then decide (1 ≤ count231 b) else decide (2 ≤ count231 b)))))) else (if i < 244 then (if i < 238 then (if i < 235 then (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)) else (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b)))) else (if i < 241 then (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b))) else (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))))) else (if i < 249 then (if i < 246 then (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b)) else (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b)))) else (if i < 252 then (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))) else (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b)))))))) else (if i < 298 then (if i < 276 then (if i < 265 then (if i < 260 then (if i < 257 then (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b)) else (if i < 258 then decide (1 ≤ count257 b) else (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b)))) else (if i < 262 then (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)) else (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))))) else (if i < 270 then (if i < 267 then (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)) else (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)))) else (if i < 273 then (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b))) else (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)))))) else (if i < 287 then (if i < 281 then (if i < 278 then (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)) else (if i < 279 then decide (2 ≤ count277 b) else (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)))) else (if i < 284 then (if i < 282 then decide (1 ≤ count281 b) else (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b))) else (if i < 285 then decide (2 ≤ count283 b) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b))))) else (if i < 292 then (if i < 289 then (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)) else (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b)))) else (if i < 295 then (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b))) else (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))))))) else (if i < 319 then (if i < 308 then (if i < 303 then (if i < 300 then (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b)) else (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b)))) else (if i < 305 then (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b)) else (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))))) else (if i < 313 then (if i < 310 then (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)) else (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)))) else (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)))))) else (if i < 330 then (if i < 324 then (if i < 321 then (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b)) else (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)))) else (if i < 327 then (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))) else (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b))))) else (if i < 335 then (if i < 332 then (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)) else (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b)))) else (if i < 338 then (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b))) else (if i < 339 then decide (2 ≤ count337 b) else (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)))))))))) else (if i < 511 then (if i < 426 then (if i < 383 then (if i < 362 then (if i < 351 then (if i < 346 then (if i < 343 then (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)) else (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b)))) else (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b))))) else (if i < 356 then (if i < 353 then (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b)) else (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b)))) else (if i < 359 then (if i < 357 then decide (2 ≤ count355 b) else (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b))) else (if i < 360 then decide (1 ≤ count359 b) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)))))) else (if i < 372 then (if i < 367 then (if i < 364 then (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)) else (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b)))) else (if i < 369 then (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b)) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b))))) else (if i < 377 then (if i < 374 then (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)))) else (if i < 380 then (if i < 378 then decide (1 ≤ count377 b) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b))) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b))))))) else (if i < 404 then (if i < 393 then (if i < 388 then (if i < 385 then (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b)) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)))) else (if i < 390 then (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b)) else (if i < 391 then decide (2 ≤ count389 b) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))))) else (if i < 398 then (if i < 395 then (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)) else (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b)))) else (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 402 then decide (3 ≤ count399 b) else (if i < 403 then decide (1 ≤ count402 b) else decide (2 ≤ count402 b)))))) else (if i < 415 then (if i < 409 then (if i < 406 then (if i < 405 then decide (1 ≤ count404 b) else decide (2 ≤ count404 b)) else (if i < 407 then decide (3 ≤ count404 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)))) else (if i < 412 then (if i < 410 then decide (3 ≤ count407 b) else (if i < 411 then decide (4 ≤ count407 b) else decide (5 ≤ count407 b))) else (if i < 413 then decide (6 ≤ count407 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))))) else (if i < 420 then (if i < 417 then (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b)) else (if i < 418 then decide (3 ≤ count415 b) else (if i < 419 then decide (1 ≤ count418 b) else decide (2 ≤ count418 b)))) else (if i < 423 then (if i < 421 then decide (1 ≤ count420 b) else (if i < 422 then decide (2 ≤ count420 b) else decide (3 ≤ count420 b))) else (if i < 424 then decide (1 ≤ count423 b) else (if i < 425 then decide (2 ≤ count423 b) else decide (3 ≤ count423 b)))))))) else (if i < 468 then (if i < 447 then (if i < 436 then (if i < 431 then (if i < 428 then (if i < 427 then decide (4 ≤ count423 b) else decide (5 ≤ count423 b)) else (if i < 429 then decide (6 ≤ count423 b) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b)))) else (if i < 433 then (if i < 432 then decide (3 ≤ count429 b) else decide (4 ≤ count429 b)) else (if i < 434 then decide (5 ≤ count429 b) else (if i < 435 then decide (6 ≤ count429 b) else decide (7 ≤ count429 b))))) else (if i < 441 then (if i < 438 then (if i < 437 then decide (8 ≤ count429 b) else decide (9 ≤ count429 b)) else (if i < 439 then decide (10 ≤ count429 b) else (if i < 440 then decide (11 ≤ count429 b) else decide (12 ≤ count429 b)))) else (if i < 444 then (if i < 442 then decide (1 ≤ count441 b) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b))) else (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (3 ≤ count443 b) else decide (1 ≤ count446 b)))))) else (if i < 457 then (if i < 452 then (if i < 449 then (if i < 448 then decide (2 ≤ count446 b) else decide (1 ≤ count448 b)) else (if i < 450 then decide (2 ≤ count448 b) else (if i < 451 then decide (3 ≤ count448 b) else decide (1 ≤ count451 b)))) else (if i < 454 then (if i < 453 then decide (2 ≤ count451 b) else decide (3 ≤ count451 b)) else (if i < 455 then decide (4 ≤ count451 b) else (if i < 456 then decide (5 ≤ count451 b) else decide (6 ≤ count451 b))))) else (if i < 462 then (if i < 459 then (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)) else (if i < 460 then decide (1 ≤ count459 b) else (if i < 461 then decide (2 ≤ count459 b) else decide (3 ≤ count459 b)))) else (if i < 465 then (if i < 463 then decide (1 ≤ count462 b) else (if i < 464 then decide (2 ≤ count462 b) else decide (1 ≤ count464 b))) else (if i < 466 then decide (2 ≤ count464 b) else (if i < 467 then decide (3 ≤ count464 b) else decide (1 ≤ count467 b))))))) else (if i < 489 then (if i < 478 then (if i < 473 then (if i < 470 then (if i < 469 then decide (2 ≤ count467 b) else decide (3 ≤ count467 b)) else (if i < 471 then decide (4 ≤ count467 b) else (if i < 472 then decide (5 ≤ count467 b) else decide (6 ≤ count467 b)))) else (if i < 475 then (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)) else (if i < 476 then decide (3 ≤ count473 b) else (if i < 477 then decide (4 ≤ count473 b) else decide (5 ≤ count473 b))))) else (if i < 483 then (if i < 480 then (if i < 479 then decide (6 ≤ count473 b) else decide (7 ≤ count473 b)) else (if i < 481 then decide (8 ≤ count473 b) else (if i < 482 then decide (9 ≤ count473 b) else decide (10 ≤ count473 b)))) else (if i < 486 then (if i < 484 then decide (11 ≤ count473 b) else (if i < 485 then decide (12 ≤ count473 b) else decide (1 ≤ count485 b))) else (if i < 487 then decide (2 ≤ count485 b) else (if i < 488 then decide (3 ≤ count485 b) else decide (4 ≤ count485 b)))))) else (if i < 500 then (if i < 494 then (if i < 491 then (if i < 490 then decide (5 ≤ count485 b) else decide (6 ≤ count485 b)) else (if i < 492 then decide (7 ≤ count485 b) else (if i < 493 then decide (8 ≤ count485 b) else decide (9 ≤ count485 b)))) else (if i < 497 then (if i < 495 then decide (10 ≤ count485 b) else (if i < 496 then decide (11 ≤ count485 b) else decide (12 ≤ count485 b))) else (if i < 498 then decide (13 ≤ count485 b) else (if i < 499 then decide (14 ≤ count485 b) else decide (15 ≤ count485 b))))) else (if i < 505 then (if i < 502 then (if i < 501 then decide (16 ≤ count485 b) else decide (17 ≤ count485 b)) else (if i < 503 then decide (18 ≤ count485 b) else (if i < 504 then decide (19 ≤ count485 b) else decide (20 ≤ count485 b)))) else (if i < 508 then (if i < 506 then decide (21 ≤ count485 b) else (if i < 507 then decide (22 ≤ count485 b) else decide (23 ≤ count485 b))) else (if i < 509 then decide (24 ≤ count485 b) else (if i < 510 then decide (1 ≤ count509 b) else decide (2 ≤ count509 b))))))))) else (if i < 596 then (if i < 553 then (if i < 532 then (if i < 521 then (if i < 516 then (if i < 513 then (if i < 512 then decide (1 ≤ count511 b) else decide (2 ≤ count511 b)) else (if i < 514 then decide (3 ≤ count511 b) else (if i < 515 then decide (1 ≤ count514 b) else decide (2 ≤ count514 b)))) else (if i < 518 then (if i < 517 then decide (1 ≤ count516 b) else decide (2 ≤ count516 b)) else (if i < 519 then decide (3 ≤ count516 b) else (if i < 520 then decide (1 ≤ count519 b) else decide (2 ≤ count519 b))))) else (if i < 526 then (if i < 523 then (if i < 522 then decide (3 ≤ count519 b) else decide (4 ≤ count519 b)) else (if i < 524 then decide (5 ≤ count519 b) else (if i < 525 then decide (6 ≤ count519 b) else decide (1 ≤ count525 b)))) else (if i < 529 then (if i < 527 then decide (2 ≤ count525 b) else (if i < 528 then decide (1 ≤ count527 b) else decide (2 ≤ count527 b))) else (if i < 530 then decide (3 ≤ count527 b) else (if i < 531 then decide (1 ≤ count530 b) else decide (2 ≤ count530 b)))))) else (if i < 542 then (if i < 537 then (if i < 534 then (if i < 533 then decide (1 ≤ count532 b) else decide (2 ≤ count532 b)) else (if i < 535 then decide (3 ≤ count532 b) else (if i < 536 then decide (1 ≤ count535 b) else decide (2 ≤ count535 b)))) else (if i < 539 then (if i < 538 then decide (3 ≤ count535 b) else decide (4 ≤ count535 b)) else (if i < 540 then decide (5 ≤ count535 b) else (if i < 541 then decide (6 ≤ count535 b) else decide (1 ≤ count541 b))))) else (if i < 547 then (if i < 544 then (if i < 543 then decide (2 ≤ count541 b) else decide (3 ≤ count541 b)) else (if i < 545 then decide (4 ≤ count541 b) else (if i < 546 then decide (5 ≤ count541 b) else decide (6 ≤ count541 b)))) else (if i < 550 then (if i < 548 then decide (7 ≤ count541 b) else (if i < 549 then decide (8 ≤ count541 b) else decide (9 ≤ count541 b))) else (if i < 551 then decide (10 ≤ count541 b) else (if i < 552 then decide (11 ≤ count541 b) else decide (12 ≤ count541 b))))))) else (if i < 574 then (if i < 563 then (if i < 558 then (if i < 555 then (if i < 554 then decide (1 ≤ count553 b) else decide (2 ≤ count553 b)) else (if i < 556 then decide (1 ≤ count555 b) else (if i < 557 then decide (2 ≤ count555 b) else decide (3 ≤ count555 b)))) else (if i < 560 then (if i < 559 then decide (1 ≤ count558 b) else decide (2 ≤ count558 b)) else (if i < 561 then decide (1 ≤ count560 b) else (if i < 562 then decide (2 ≤ count560 b) else decide (3 ≤ count560 b))))) else (if i < 568 then (if i < 565 then (if i < 564 then decide (1 ≤ count563 b) else decide (2 ≤ count563 b)) else (if i < 566 then decide (3 ≤ count563 b) else (if i < 567 then decide (4 ≤ count563 b) else decide (5 ≤ count563 b)))) else (if i < 571 then (if i < 569 then decide (6 ≤ count563 b) else (if i < 570 then decide (1 ≤ count569 b) else decide (2 ≤ count569 b))) else (if i < 572 then decide (1 ≤ count571 b) else (if i < 573 then decide (2 ≤ count571 b) else decide (3 ≤ count571 b)))))) else (if i < 585 then (if i < 579 then (if i < 576 then (if i < 575 then decide (1 ≤ count574 b) else decide (2 ≤ count574 b)) else (if i < 577 then decide (1 ≤ count576 b) else (if i < 578 then decide (2 ≤ count576 b) else decide (1 ≤ count578 b)))) else (if i < 582 then (if i < 580 then decide (2 ≤ count578 b) else (if i < 581 then decide (3 ≤ count578 b) else decide (4 ≤ count578 b))) else (if i < 583 then decide (1 ≤ count582 b) else (if i < 584 then decide (2 ≤ count582 b) else decide (3 ≤ count582 b))))) else (if i < 590 then (if i < 587 then (if i < 586 then decide (4 ≤ count582 b) else decide (5 ≤ count582 b)) else (if i < 588 then decide (6 ≤ count582 b) else (if i < 589 then decide (7 ≤ count582 b) else decide (1 ≤ count589 b)))) else (if i < 593 then (if i < 591 then decide (2 ≤ count589 b) else (if i < 592 then decide (3 ≤ count589 b) else decide (4 ≤ count589 b))) else (if i < 594 then decide (5 ≤ count589 b) else (if i < 595 then decide (6 ≤ count589 b) else decide (7 ≤ count589 b)))))))) else (if i < 639 then (if i < 617 then (if i < 606 then (if i < 601 then (if i < 598 then (if i < 597 then decide (8 ≤ count589 b) else decide (9 ≤ count589 b)) else (if i < 599 then decide (10 ≤ count589 b) else (if i < 600 then decide (11 ≤ count589 b) else decide (12 ≤ count589 b)))) else (if i < 603 then (if i < 602 then decide (13 ≤ count589 b) else decide (1 ≤ count602 b)) else (if i < 604 then decide (2 ≤ count602 b) else (if i < 605 then decide (3 ≤ count602 b) else decide (4 ≤ count602 b))))) else (if i < 611 then (if i < 608 then (if i < 607 then decide (5 ≤ count602 b) else decide (6 ≤ count602 b)) else (if i < 609 then decide (7 ≤ count602 b) else (if i < 610 then decide (8 ≤ count602 b) else decide (9 ≤ count602 b)))) else (if i < 614 then (if i < 612 then decide (10 ≤ count602 b) else (if i < 613 then decide (11 ≤ count602 b) else decide (12 ≤ count602 b))) else (if i < 615 then decide (13 ≤ count602 b) else (if i < 616 then decide (14 ≤ count602 b) else decide (15 ≤ count602 b)))))) else (if i < 628 then (if i < 622 then (if i < 619 then (if i < 618 then decide (16 ≤ count602 b) else decide (17 ≤ count602 b)) else (if i < 620 then decide (18 ≤ count602 b) else (if i < 621 then decide (19 ≤ count602 b) else decide (20 ≤ count602 b)))) else (if i < 625 then (if i < 623 then decide (21 ≤ count602 b) else (if i < 624 then decide (22 ≤ count602 b) else decide (23 ≤ count602 b))) else (if i < 626 then decide (24 ≤ count602 b) else (if i < 627 then decide (25 ≤ count602 b) else decide (1 ≤ count627 b))))) else (if i < 633 then (if i < 630 then (if i < 629 then decide (2 ≤ count627 b) else decide (3 ≤ count627 b)) else (if i < 631 then decide (4 ≤ count627 b) else (if i < 632 then decide (5 ≤ count627 b) else decide (6 ≤ count627 b)))) else (if i < 636 then (if i < 634 then decide (7 ≤ count627 b) else (if i < 635 then decide (8 ≤ count627 b) else decide (9 ≤ count627 b))) else (if i < 637 then decide (10 ≤ count627 b) else (if i < 638 then decide (11 ≤ count627 b) else decide (12 ≤ count627 b))))))) else (if i < 660 then (if i < 649 then (if i < 644 then (if i < 641 then (if i < 640 then decide (13 ≤ count627 b) else decide (14 ≤ count627 b)) else (if i < 642 then decide (15 ≤ count627 b) else (if i < 643 then decide (16 ≤ count627 b) else decide (17 ≤ count627 b)))) else (if i < 646 then (if i < 645 then decide (18 ≤ count627 b) else decide (19 ≤ count627 b)) else (if i < 647 then decide (20 ≤ count627 b) else (if i < 648 then decide (21 ≤ count627 b) else decide (22 ≤ count627 b))))) else (if i < 654 then (if i < 651 then (if i < 650 then decide (23 ≤ count627 b) else decide (24 ≤ count627 b)) else (if i < 652 then decide (25 ≤ count627 b) else (if i < 653 then decide (26 ≤ count627 b) else decide (27 ≤ count627 b)))) else (if i < 657 then (if i < 655 then decide (28 ≤ count627 b) else (if i < 656 then decide (29 ≤ count627 b) else decide (30 ≤ count627 b))) else (if i < 658 then decide (31 ≤ count627 b) else (if i < 659 then decide (32 ≤ count627 b) else decide (33 ≤ count627 b)))))) else (if i < 671 then (if i < 665 then (if i < 662 then (if i < 661 then decide (34 ≤ count627 b) else decide (35 ≤ count627 b)) else (if i < 663 then decide (36 ≤ count627 b) else (if i < 664 then decide (37 ≤ count627 b) else decide (38 ≤ count627 b)))) else (if i < 668 then (if i < 666 then decide (39 ≤ count627 b) else (if i < 667 then decide (40 ≤ count627 b) else decide (41 ≤ count627 b))) else (if i < 669 then decide (42 ≤ count627 b) else (if i < 670 then decide (1 ≤ count669 b) else decide (2 ≤ count669 b))))) else (if i < 676 then (if i < 673 then (if i < 672 then decide (1 ≤ count671 b) else decide (2 ≤ count671 b)) else (if i < 674 then decide (3 ≤ count671 b) else (if i < 675 then decide (1 ≤ count674 b) else decide (2 ≤ count674 b)))) else (if i < 679 then (if i < 677 then decide (1 ≤ count676 b) else (if i < 678 then decide (2 ≤ count676 b) else decide (3 ≤ count676 b))) else (if i < 680 then decide (1 ≤ count679 b) else (if i < 681 then decide (2 ≤ count679 b) else decide (3 ≤ count679 b))))))))))) else (if i < 1023 then (if i < 852 then (if i < 767 then (if i < 724 then (if i < 703 then (if i < 692 then (if i < 687 then (if i < 684 then (if i < 683 then decide (4 ≤ count679 b) else decide (5 ≤ count679 b)) else (if i < 685 then decide (6 ≤ count679 b) else (if i < 686 then decide (1 ≤ count685 b) else decide (2 ≤ count685 b)))) else (if i < 689 then (if i < 688 then decide (1 ≤ count687 b) else decide (2 ≤ count687 b)) else (if i < 690 then decide (3 ≤ count687 b) else (if i < 691 then decide (1 ≤ count690 b) else decide (2 ≤ count690 b))))) else (if i < 697 then (if i < 694 then (if i < 693 then decide (1 ≤ count692 b) else decide (2 ≤ count692 b)) else (if i < 695 then decide (3 ≤ count692 b) else (if i < 696 then decide (1 ≤ count695 b) else decide (2 ≤ count695 b)))) else (if i < 700 then (if i < 698 then decide (3 ≤ count695 b) else (if i < 699 then decide (4 ≤ count695 b) else decide (5 ≤ count695 b))) else (if i < 701 then decide (6 ≤ count695 b) else (if i < 702 then decide (1 ≤ count701 b) else decide (2 ≤ count701 b)))))) else (if i < 713 then (if i < 708 then (if i < 705 then (if i < 704 then decide (3 ≤ count701 b) else decide (4 ≤ count701 b)) else (if i < 706 then decide (5 ≤ count701 b) else (if i < 707 then decide (6 ≤ count701 b) else decide (7 ≤ count701 b)))) else (if i < 710 then (if i < 709 then decide (8 ≤ count701 b) else decide (9 ≤ count701 b)) else (if i < 711 then decide (1 ≤ count710 b) else (if i < 712 then decide (2 ≤ count710 b) else decide (1 ≤ count712 b))))) else (if i < 718 then (if i < 715 then (if i < 714 then decide (2 ≤ count712 b) else decide (3 ≤ count712 b)) else (if i < 716 then decide (1 ≤ count715 b) else (if i < 717 then decide (2 ≤ count715 b) else decide (1 ≤ count717 b)))) else (if i < 721 then (if i < 719 then decide (2 ≤ count717 b) else (if i < 720 then decide (3 ≤ count717 b) else decide (1 ≤ count720 b))) else (if i < 722 then decide (2 ≤ count720 b) else (if i < 723 then decide (3 ≤ count720 b) else decide (4 ≤ count720 b))))))) else (if i < 745 then (if i < 734 then (if i < 729 then (if i < 726 then (if i < 725 then decide (5 ≤ count720 b) else decide (6 ≤ count720 b)) else (if i < 727 then decide (1 ≤ count726 b) else (if i < 728 then decide (2 ≤ count726 b) else decide (1 ≤ count728 b)))) else (if i < 731 then (if i < 730 then decide (2 ≤ count728 b) else decide (3 ≤ count728 b)) else (if i < 732 then decide (1 ≤ count731 b) else (if i < 733 then decide (2 ≤ count731 b) else decide (1 ≤ count733 b))))) else (if i < 739 then (if i < 736 then (if i < 735 then decide (2 ≤ count733 b) else decide (3 ≤ count733 b)) else (if i < 737 then decide (1 ≤ count736 b) else (if i < 738 then decide (2 ≤ count736 b) else decide (3 ≤ count736 b)))) else (if i < 742 then (if i < 740 then decide (4 ≤ count736 b) else (if i < 741 then decide (5 ≤ count736 b) else decide (6 ≤ count736 b))) else (if i < 743 then decide (1 ≤ count742 b) else (if i < 744 then decide (2 ≤ count742 b) else decide (3 ≤ count742 b)))))) else (if i < 756 then (if i < 750 then (if i < 747 then (if i < 746 then decide (4 ≤ count742 b) else decide (5 ≤ count742 b)) else (if i < 748 then decide (6 ≤ count742 b) else (if i < 749 then decide (7 ≤ count742 b) else decide (8 ≤ count742 b)))) else (if i < 753 then (if i < 751 then decide (9 ≤ count742 b) else (if i < 752 then decide (1 ≤ count751 b) else decide (2 ≤ count751 b))) else (if i < 754 then decide (3 ≤ count751 b) else (if i < 755 then decide (4 ≤ count751 b) else decide (5 ≤ count751 b))))) else (if i < 761 then (if i < 758 then (if i < 757 then decide (6 ≤ count751 b) else decide (7 ≤ count751 b)) else (if i < 759 then decide (8 ≤ count751 b) else (if i < 760 then decide (9 ≤ count751 b) else decide (1 ≤ count760 b)))) else (if i < 764 then (if i < 762 then decide (2 ≤ count760 b) else (if i < 763 then decide (1 ≤ count762 b) else decide (2 ≤ count762 b))) else (if i < 765 then decide (3 ≤ count762 b) else (if i < 766 then decide (1 ≤ count765 b) else decide (2 ≤ count765 b)))))))) else (if i < 809 then (if i < 788 then (if i < 777 then (if i < 772 then (if i < 769 then (if i < 768 then decide (1 ≤ count767 b) else decide (2 ≤ count767 b)) else (if i < 770 then decide (3 ≤ count767 b) else (if i < 771 then decide (1 ≤ count770 b) else decide (2 ≤ count770 b)))) else (if i < 774 then (if i < 773 then decide (3 ≤ count770 b) else decide (4 ≤ count770 b)) else (if i < 775 then decide (5 ≤ count770 b) else (if i < 776 then decide (6 ≤ count770 b) else decide (1 ≤ count776 b))))) else (if i < 782 then (if i < 779 then (if i < 778 then decide (2 ≤ count776 b) else decide (1 ≤ count778 b)) else (if i < 780 then decide (2 ≤ count778 b) else (if i < 781 then decide (3 ≤ count778 b) else decide (1 ≤ count781 b)))) else (if i < 785 then (if i < 783 then decide (2 ≤ count781 b) else (if i < 784 then decide (1 ≤ count783 b) else decide (2 ≤ count783 b))) else (if i < 786 then decide (3 ≤ count783 b) else (if i < 787 then decide (1 ≤ count786 b) else decide (2 ≤ count786 b)))))) else (if i < 798 then (if i < 793 then (if i < 790 then (if i < 789 then decide (3 ≤ count786 b) else decide (4 ≤ count786 b)) else (if i < 791 then decide (5 ≤ count786 b) else (if i < 792 then decide (6 ≤ count786 b) else decide (1 ≤ count792 b)))) else (if i < 795 then (if i < 794 then decide (2 ≤ count792 b) else decide (3 ≤ count792 b)) else (if i < 796 then decide (4 ≤ count792 b) else (if i < 797 then decide (5 ≤ count792 b) else decide (6 ≤ count792 b))))) else (if i < 803 then (if i < 800 then (if i < 799 then decide (7 ≤ count792 b) else decide (8 ≤ count792 b)) else (if i < 801 then decide (9 ≤ count792 b) else (if i < 802 then decide (1 ≤ count801 b) else decide (2 ≤ count801 b)))) else (if i < 806 then (if i < 804 then decide (1 ≤ count803 b) else (if i < 805 then decide (2 ≤ count803 b) else decide (3 ≤ count803 b))) else (if i < 807 then decide (1 ≤ count806 b) else (if i < 808 then decide (2 ≤ count806 b) else decide (1 ≤ count808 b))))))) else (if i < 830 then (if i < 819 then (if i < 814 then (if i < 811 then (if i < 810 then decide (2 ≤ count808 b) else decide (3 ≤ count808 b)) else (if i < 812 then decide (1 ≤ count811 b) else (if i < 813 then decide (2 ≤ count811 b) else decide (3 ≤ count811 b)))) else (if i < 816 then (if i < 815 then decide (4 ≤ count811 b) else decide (5 ≤ count811 b)) else (if i < 817 then decide (6 ≤ count811 b) else (if i < 818 then decide (1 ≤ count817 b) else decide (2 ≤ count817 b))))) else (if i < 824 then (if i < 821 then (if i < 820 then decide (1 ≤ count819 b) else decide (2 ≤ count819 b)) else (if i < 822 then decide (3 ≤ count819 b) else (if i < 823 then decide (1 ≤ count822 b) else decide (2 ≤ count822 b)))) else (if i < 827 then (if i < 825 then decide (1 ≤ count824 b) else (if i < 826 then decide (2 ≤ count824 b) else decide (1 ≤ count826 b))) else (if i < 828 then decide (2 ≤ count826 b) else (if i < 829 then decide (3 ≤ count826 b) else decide (4 ≤ count826 b)))))) else (if i < 841 then (if i < 835 then (if i < 832 then (if i < 831 then decide (1 ≤ count830 b) else decide (2 ≤ count830 b)) else (if i < 833 then decide (3 ≤ count830 b) else (if i < 834 then decide (4 ≤ count830 b) else decide (5 ≤ count830 b)))) else (if i < 838 then (if i < 836 then decide (6 ≤ count830 b) else (if i < 837 then decide (7 ≤ count830 b) else decide (1 ≤ count837 b))) else (if i < 839 then decide (2 ≤ count837 b) else (if i < 840 then decide (3 ≤ count837 b) else decide (4 ≤ count837 b))))) else (if i < 846 then (if i < 843 then (if i < 842 then decide (5 ≤ count837 b) else decide (6 ≤ count837 b)) else (if i < 844 then decide (7 ≤ count837 b) else (if i < 845 then decide (8 ≤ count837 b) else decide (9 ≤ count837 b)))) else (if i < 849 then (if i < 847 then decide (1 ≤ count846 b) else (if i < 848 then decide (2 ≤ count846 b) else decide (3 ≤ count846 b))) else (if i < 850 then decide (4 ≤ count846 b) else (if i < 851 then decide (5 ≤ count846 b) else decide (6 ≤ count846 b))))))))) else (if i < 937 then (if i < 894 then (if i < 873 then (if i < 862 then (if i < 857 then (if i < 854 then (if i < 853 then decide (7 ≤ count846 b) else decide (8 ≤ count846 b)) else (if i < 855 then decide (9 ≤ count846 b) else (if i < 856 then decide (1 ≤ count855 b) else decide (2 ≤ count855 b)))) else (if i < 859 then (if i < 858 then decide (3 ≤ count855 b) else decide (4 ≤ count855 b)) else (if i < 860 then decide (5 ≤ count855 b) else (if i < 861 then decide (6 ≤ count855 b) else decide (7 ≤ count855 b))))) else (if i < 867 then (if i < 864 then (if i < 863 then decide (8 ≤ count855 b) else decide (9 ≤ count855 b)) else (if i < 865 then decide (1 ≤ count864 b) else (if i < 866 then decide (2 ≤ count864 b) else decide (1 ≤ count866 b)))) else (if i < 870 then (if i < 868 then decide (2 ≤ count866 b) else (if i < 869 then decide (3 ≤ count866 b) else decide (1 ≤ count869 b))) else (if i < 871 then decide (2 ≤ count869 b) else (if i < 872 then decide (1 ≤ count871 b) else decide (2 ≤ count871 b)))))) else (if i < 883 then (if i < 878 then (if i < 875 then (if i < 874 then decide (3 ≤ count871 b) else decide (1 ≤ count874 b)) else (if i < 876 then decide (2 ≤ count874 b) else (if i < 877 then decide (3 ≤ count874 b) else decide (4 ≤ count874 b)))) else (if i < 880 then (if i < 879 then decide (5 ≤ count874 b) else decide (6 ≤ count874 b)) else (if i < 881 then decide (1 ≤ count880 b) else (if i < 882 then decide (2 ≤ count880 b) else decide (1 ≤ count882 b))))) else (if i < 888 then (if i < 885 then (if i < 884 then decide (2 ≤ count882 b) else decide (3 ≤ count882 b)) else (if i < 886 then decide (1 ≤ count885 b) else (if i < 887 then decide (2 ≤ count885 b) else decide (1 ≤ count887 b)))) else (if i < 891 then (if i < 889 then decide (2 ≤ count887 b) else (if i < 890 then decide (3 ≤ count887 b) else decide (1 ≤ count890 b))) else (if i < 892 then decide (2 ≤ count890 b) else (if i < 893 then decide (3 ≤ count890 b) else decide (4 ≤ count890 b))))))) else (if i < 915 then (if i < 904 then (if i < 899 then (if i < 896 then (if i < 895 then decide (5 ≤ count890 b) else decide (6 ≤ count890 b)) else (if i < 897 then decide (1 ≤ count896 b) else (if i < 898 then decide (2 ≤ count896 b) else decide (3 ≤ count896 b)))) else (if i < 901 then (if i < 900 then decide (4 ≤ count896 b) else decide (5 ≤ count896 b)) else (if i < 902 then decide (6 ≤ count896 b) else (if i < 903 then decide (7 ≤ count896 b) else decide (8 ≤ count896 b))))) else (if i < 909 then (if i < 906 then (if i < 905 then decide (9 ≤ count896 b) else decide (10 ≤ count896 b)) else (if i < 907 then decide (11 ≤ count896 b) else (if i < 908 then decide (12 ≤ count896 b) else decide (1 ≤ count908 b)))) else (if i < 912 then (if i < 910 then decide (2 ≤ count908 b) else (if i < 911 then decide (1 ≤ count910 b) else decide (2 ≤ count910 b))) else (if i < 913 then decide (3 ≤ count910 b) else (if i < 914 then decide (1 ≤ count913 b) else decide (2 ≤ count913 b)))))) else (if i < 926 then (if i < 920 then (if i < 917 then (if i < 916 then decide (1 ≤ count915 b) else decide (2 ≤ count915 b)) else (if i < 918 then decide (3 ≤ count915 b) else (if i < 919 then decide (1 ≤ count918 b) else decide (2 ≤ count918 b)))) else (if i < 923 then (if i < 921 then decide (3 ≤ count918 b) else (if i < 922 then decide (4 ≤ count918 b) else decide (5 ≤ count918 b))) else (if i < 924 then decide (6 ≤ count918 b) else (if i < 925 then decide (1 ≤ count924 b) else decide (2 ≤ count924 b))))) else (if i < 931 then (if i < 928 then (if i < 927 then decide (1 ≤ count926 b) else decide (2 ≤ count926 b)) else (if i < 929 then decide (3 ≤ count926 b) else (if i < 930 then decide (1 ≤ count929 b) else decide (2 ≤ count929 b)))) else (if i < 934 then (if i < 932 then decide (1 ≤ count931 b) else (if i < 933 then decide (2 ≤ count931 b) else decide (1 ≤ count933 b))) else (if i < 935 then decide (2 ≤ count933 b) else (if i < 936 then decide (3 ≤ count933 b) else decide (4 ≤ count933 b)))))))) else (if i < 980 then (if i < 958 then (if i < 947 then (if i < 942 then (if i < 939 then (if i < 938 then decide (1 ≤ count937 b) else decide (2 ≤ count937 b)) else (if i < 940 then decide (3 ≤ count937 b) else (if i < 941 then decide (4 ≤ count937 b) else decide (5 ≤ count937 b)))) else (if i < 944 then (if i < 943 then decide (6 ≤ count937 b) else decide (7 ≤ count937 b)) else (if i < 945 then decide (1 ≤ count944 b) else (if i < 946 then decide (2 ≤ count944 b) else decide (3 ≤ count944 b))))) else (if i < 952 then (if i < 949 then (if i < 948 then decide (4 ≤ count944 b) else decide (5 ≤ count944 b)) else (if i < 950 then decide (6 ≤ count944 b) else (if i < 951 then decide (7 ≤ count944 b) else decide (8 ≤ count944 b)))) else (if i < 955 then (if i < 953 then decide (9 ≤ count944 b) else (if i < 954 then decide (10 ≤ count944 b) else decide (11 ≤ count944 b))) else (if i < 956 then decide (12 ≤ count944 b) else (if i < 957 then decide (13 ≤ count944 b) else decide (1 ≤ count957 b)))))) else (if i < 969 then (if i < 963 then (if i < 960 then (if i < 959 then decide (2 ≤ count957 b) else decide (3 ≤ count957 b)) else (if i < 961 then decide (4 ≤ count957 b) else (if i < 962 then decide (5 ≤ count957 b) else decide (6 ≤ count957 b)))) else (if i < 966 then (if i < 964 then decide (7 ≤ count957 b) else (if i < 965 then decide (8 ≤ count957 b) else decide (9 ≤ count957 b))) else (if i < 967 then decide (10 ≤ count957 b) else (if i < 968 then decide (11 ≤ count957 b) else decide (12 ≤ count957 b))))) else (if i < 974 then (if i < 971 then (if i < 970 then decide (13 ≤ count957 b) else decide (14 ≤ count957 b)) else (if i < 972 then decide (15 ≤ count957 b) else (if i < 973 then decide (16 ≤ count957 b) else decide (17 ≤ count957 b)))) else (if i < 977 then (if i < 975 then decide (18 ≤ count957 b) else (if i < 976 then decide (19 ≤ count957 b) else decide (20 ≤ count957 b))) else (if i < 978 then decide (21 ≤ count957 b) else (if i < 979 then decide (22 ≤ count957 b) else decide (23 ≤ count957 b))))))) else (if i < 1001 then (if i < 990 then (if i < 985 then (if i < 982 then (if i < 981 then decide (24 ≤ count957 b) else decide (25 ≤ count957 b)) else (if i < 983 then decide (1 ≤ count982 b) else (if i < 984 then decide (2 ≤ count982 b) else decide (1 ≤ count984 b)))) else (if i < 987 then (if i < 986 then decide (2 ≤ count984 b) else decide (3 ≤ count984 b)) else (if i < 988 then decide (1 ≤ count987 b) else (if i < 989 then decide (2 ≤ count987 b) else decide (1 ≤ count989 b))))) else (if i < 995 then (if i < 992 then (if i < 991 then decide (2 ≤ count989 b) else decide (3 ≤ count989 b)) else (if i < 993 then decide (1 ≤ count992 b) else (if i < 994 then decide (2 ≤ count992 b) else decide (3 ≤ count992 b)))) else (if i < 998 then (if i < 996 then decide (4 ≤ count992 b) else (if i < 997 then decide (5 ≤ count992 b) else decide (6 ≤ count992 b))) else (if i < 999 then decide (1 ≤ count998 b) else (if i < 1000 then decide (2 ≤ count998 b) else decide (1 ≤ count1000 b)))))) else (if i < 1012 then (if i < 1006 then (if i < 1003 then (if i < 1002 then decide (2 ≤ count1000 b) else decide (3 ≤ count1000 b)) else (if i < 1004 then decide (1 ≤ count1003 b) else (if i < 1005 then decide (2 ≤ count1003 b) else decide (1 ≤ count1005 b)))) else (if i < 1009 then (if i < 1007 then decide (2 ≤ count1005 b) else (if i < 1008 then decide (1 ≤ count1007 b) else decide (2 ≤ count1007 b))) else (if i < 1010 then decide (3 ≤ count1007 b) else (if i < 1011 then decide (4 ≤ count1007 b) else decide (1 ≤ count1011 b))))) else (if i < 1017 then (if i < 1014 then (if i < 1013 then decide (2 ≤ count1011 b) else decide (3 ≤ count1011 b)) else (if i < 1015 then decide (4 ≤ count1011 b) else (if i < 1016 then decide (5 ≤ count1011 b) else decide (6 ≤ count1011 b)))) else (if i < 1020 then (if i < 1018 then decide (7 ≤ count1011 b) else (if i < 1019 then decide (1 ≤ count1018 b) else decide (2 ≤ count1018 b))) else (if i < 1021 then decide (3 ≤ count1018 b) else (if i < 1022 then decide (4 ≤ count1018 b) else decide (5 ≤ count1018 b)))))))))) else (if i < 1194 then (if i < 1108 then (if i < 1065 then (if i < 1044 then (if i < 1033 then (if i < 1028 then (if i < 1025 then (if i < 1024 then decide (6 ≤ count1018 b) else decide (7 ≤ count1018 b)) else (if i < 1026 then decide (8 ≤ count1018 b) else (if i < 1027 then decide (9 ≤ count1018 b) else decide (10 ≤ count1018 b)))) else (if i < 1030 then (if i < 1029 then decide (11 ≤ count1018 b) else decide (12 ≤ count1018 b)) else (if i < 1031 then decide (13 ≤ count1018 b) else (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b))))) else (if i < 1038 then (if i < 1035 then (if i < 1034 then decide (1 ≤ count1033 b) else decide (2 ≤ count1033 b)) else (if i < 1036 then decide (3 ≤ count1033 b) else (if i < 1037 then decide (1 ≤ count1036 b) else decide (2 ≤ count1036 b)))) else (if i < 1041 then (if i < 1039 then decide (1 ≤ count1038 b) else (if i < 1040 then decide (2 ≤ count1038 b) else decide (3 ≤ count1038 b))) else (if i < 1042 then decide (1 ≤ count1041 b) else (if i < 1043 then decide (2 ≤ count1041 b) else decide (3 ≤ count1041 b)))))) else (if i < 1054 then (if i < 1049 then (if i < 1046 then (if i < 1045 then decide (4 ≤ count1041 b) else decide (5 ≤ count1041 b)) else (if i < 1047 then decide (6 ≤ count1041 b) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b)))) else (if i < 1051 then (if i < 1050 then decide (1 ≤ count1049 b) else decide (2 ≤ count1049 b)) else (if i < 1052 then decide (3 ≤ count1049 b) else (if i < 1053 then decide (1 ≤ count1052 b) else decide (2 ≤ count1052 b))))) else (if i < 1059 then (if i < 1056 then (if i < 1055 then decide (1 ≤ count1054 b) else decide (2 ≤ count1054 b)) else (if i < 1057 then decide (1 ≤ count1056 b) else (if i < 1058 then decide (2 ≤ count1056 b) else decide (3 ≤ count1056 b)))) else (if i < 1062 then (if i < 1060 then decide (4 ≤ count1056 b) else (if i < 1061 then decide (1 ≤ count1060 b) else decide (2 ≤ count1060 b))) else (if i < 1063 then decide (3 ≤ count1060 b) else (if i < 1064 then decide (4 ≤ count1060 b) else decide (5 ≤ count1060 b))))))) else (if i < 1086 then (if i < 1075 then (if i < 1070 then (if i < 1067 then (if i < 1066 then decide (6 ≤ count1060 b) else decide (7 ≤ count1060 b)) else (if i < 1068 then decide (1 ≤ count1067 b) else (if i < 1069 then decide (2 ≤ count1067 b) else decide (3 ≤ count1067 b)))) else (if i < 1072 then (if i < 1071 then decide (4 ≤ count1067 b) else decide (5 ≤ count1067 b)) else (if i < 1073 then decide (6 ≤ count1067 b) else (if i < 1074 then decide (7 ≤ count1067 b) else decide (8 ≤ count1067 b))))) else (if i < 1080 then (if i < 1077 then (if i < 1076 then decide (9 ≤ count1067 b) else decide (10 ≤ count1067 b)) else (if i < 1078 then decide (11 ≤ count1067 b) else (if i < 1079 then decide (12 ≤ count1067 b) else decide (13 ≤ count1067 b)))) else (if i < 1083 then (if i < 1081 then decide (1 ≤ count1080 b) else (if i < 1082 then decide (2 ≤ count1080 b) else decide (3 ≤ count1080 b))) else (if i < 1084 then decide (4 ≤ count1080 b) else (if i < 1085 then decide (5 ≤ count1080 b) else decide (6 ≤ count1080 b)))))) else (if i < 1097 then (if i < 1091 then (if i < 1088 then (if i < 1087 then decide (7 ≤ count1080 b) else decide (8 ≤ count1080 b)) else (if i < 1089 then decide (9 ≤ count1080 b) else (if i < 1090 then decide (10 ≤ count1080 b) else decide (11 ≤ count1080 b)))) else (if i < 1094 then (if i < 1092 then decide (12 ≤ count1080 b) else (if i < 1093 then decide (13 ≤ count1080 b) else decide (14 ≤ count1080 b))) else (if i < 1095 then decide (15 ≤ count1080 b) else (if i < 1096 then decide (16 ≤ count1080 b) else decide (17 ≤ count1080 b))))) else (if i < 1102 then (if i < 1099 then (if i < 1098 then decide (18 ≤ count1080 b) else decide (19 ≤ count1080 b)) else (if i < 1100 then decide (20 ≤ count1080 b) else (if i < 1101 then decide (21 ≤ count1080 b) else decide (22 ≤ count1080 b)))) else (if i < 1105 then (if i < 1103 then decide (23 ≤ count1080 b) else (if i < 1104 then decide (24 ≤ count1080 b) else decide (25 ≤ count1080 b))) else (if i < 1106 then decide (26 ≤ count1080 b) else (if i < 1107 then decide (1 ≤ count1106 b) else decide (2 ≤ count1106 b)))))))) else (if i < 1151 then (if i < 1129 then (if i < 1118 then (if i < 1113 then (if i < 1110 then (if i < 1109 then decide (3 ≤ count1106 b) else decide (4 ≤ count1106 b)) else (if i < 1111 then decide (5 ≤ count1106 b) else (if i < 1112 then decide (6 ≤ count1106 b) else decide (7 ≤ count1106 b)))) else (if i < 1115 then (if i < 1114 then decide (8 ≤ count1106 b) else decide (9 ≤ count1106 b)) else (if i < 1116 then decide (10 ≤ count1106 b) else (if i < 1117 then decide (11 ≤ count1106 b) else decide (12 ≤ count1106 b))))) else (if i < 1123 then (if i < 1120 then (if i < 1119 then decide (13 ≤ count1106 b) else decide (14 ≤ count1106 b)) else (if i < 1121 then decide (15 ≤ count1106 b) else (if i < 1122 then decide (16 ≤ count1106 b) else decide (17 ≤ count1106 b)))) else (if i < 1126 then (if i < 1124 then decide (18 ≤ count1106 b) else (if i < 1125 then decide (19 ≤ count1106 b) else decide (20 ≤ count1106 b))) else (if i < 1127 then decide (21 ≤ count1106 b) else (if i < 1128 then decide (22 ≤ count1106 b) else decide (23 ≤ count1106 b)))))) else (if i < 1140 then (if i < 1134 then (if i < 1131 then (if i < 1130 then decide (24 ≤ count1106 b) else decide (25 ≤ count1106 b)) else (if i < 1132 then decide (26 ≤ count1106 b) else (if i < 1133 then decide (27 ≤ count1106 b) else decide (28 ≤ count1106 b)))) else (if i < 1137 then (if i < 1135 then decide (29 ≤ count1106 b) else (if i < 1136 then decide (30 ≤ count1106 b) else decide (31 ≤ count1106 b))) else (if i < 1138 then decide (32 ≤ count1106 b) else (if i < 1139 then decide (33 ≤ count1106 b) else decide (34 ≤ count1106 b))))) else (if i < 1145 then (if i < 1142 then (if i < 1141 then decide (35 ≤ count1106 b) else decide (36 ≤ count1106 b)) else (if i < 1143 then decide (37 ≤ count1106 b) else (if i < 1144 then decide (38 ≤ count1106 b) else decide (39 ≤ count1106 b)))) else (if i < 1148 then (if i < 1146 then decide (40 ≤ count1106 b) else (if i < 1147 then decide (41 ≤ count1106 b) else decide (42 ≤ count1106 b))) else (if i < 1149 then decide (1 ≤ count1148 b) else (if i < 1150 then decide (2 ≤ count1148 b) else decide (1 ≤ count1150 b))))))) else (if i < 1172 then (if i < 1161 then (if i < 1156 then (if i < 1153 then (if i < 1152 then decide (2 ≤ count1150 b) else decide (3 ≤ count1150 b)) else (if i < 1154 then decide (1 ≤ count1153 b) else (if i < 1155 then decide (2 ≤ count1153 b) else decide (1 ≤ count1155 b)))) else (if i < 1158 then (if i < 1157 then decide (2 ≤ count1155 b) else decide (3 ≤ count1155 b)) else (if i < 1159 then decide (1 ≤ count1158 b) else (if i < 1160 then decide (2 ≤ count1158 b) else decide (3 ≤ count1158 b))))) else (if i < 1166 then (if i < 1163 then (if i < 1162 then decide (4 ≤ count1158 b) else decide (5 ≤ count1158 b)) else (if i < 1164 then decide (6 ≤ count1158 b) else (if i < 1165 then decide (1 ≤ count1164 b) else decide (2 ≤ count1164 b)))) else (if i < 1169 then (if i < 1167 then decide (1 ≤ count1166 b) else (if i < 1168 then decide (2 ≤ count1166 b) else decide (3 ≤ count1166 b))) else (if i < 1170 then decide (1 ≤ count1169 b) else (if i < 1171 then decide (2 ≤ count1169 b) else decide (1 ≤ count1171 b)))))) else (if i < 1183 then (if i < 1177 then (if i < 1174 then (if i < 1173 then decide (2 ≤ count1171 b) else decide (3 ≤ count1171 b)) else (if i < 1175 then decide (1 ≤ count1174 b) else (if i < 1176 then decide (2 ≤ count1174 b) else decide (3 ≤ count1174 b)))) else (if i < 1180 then (if i < 1178 then decide (4 ≤ count1174 b) else (if i < 1179 then decide (5 ≤ count1174 b) else decide (6 ≤ count1174 b))) else (if i < 1181 then decide (1 ≤ count1180 b) else (if i < 1182 then decide (2 ≤ count1180 b) else decide (3 ≤ count1180 b))))) else (if i < 1188 then (if i < 1185 then (if i < 1184 then decide (4 ≤ count1180 b) else decide (5 ≤ count1180 b)) else (if i < 1186 then decide (6 ≤ count1180 b) else (if i < 1187 then decide (7 ≤ count1180 b) else decide (8 ≤ count1180 b)))) else (if i < 1191 then (if i < 1189 then decide (9 ≤ count1180 b) else (if i < 1190 then decide (10 ≤ count1180 b) else decide (11 ≤ count1180 b))) else (if i < 1192 then decide (1 ≤ count1191 b) else (if i < 1193 then decide (2 ≤ count1191 b) else decide (1 ≤ count1193 b))))))))) else (if i < 1279 then (if i < 1236 then (if i < 1215 then (if i < 1204 then (if i < 1199 then (if i < 1196 then (if i < 1195 then decide (2 ≤ count1193 b) else decide (3 ≤ count1193 b)) else (if i < 1197 then decide (1 ≤ count1196 b) else (if i < 1198 then decide (2 ≤ count1196 b) else decide (1 ≤ count1198 b)))) else (if i < 1201 then (if i < 1200 then decide (2 ≤ count1198 b) else decide (3 ≤ count1198 b)) else (if i < 1202 then decide (1 ≤ count1201 b) else (if i < 1203 then decide (2 ≤ count1201 b) else decide (3 ≤ count1201 b))))) else (if i < 1209 then (if i < 1206 then (if i < 1205 then decide (4 ≤ count1201 b) else decide (5 ≤ count1201 b)) else (if i < 1207 then decide (6 ≤ count1201 b) else (if i < 1208 then decide (1 ≤ count1207 b) else decide (2 ≤ count1207 b)))) else (if i < 1212 then (if i < 1210 then decide (1 ≤ count1209 b) else (if i < 1211 then decide (2 ≤ count1209 b) else decide (3 ≤ count1209 b))) else (if i < 1213 then decide (1 ≤ count1212 b) else (if i < 1214 then decide (2 ≤ count1212 b) else decide (1 ≤ count1214 b)))))) else (if i < 1225 then (if i < 1220 then (if i < 1217 then (if i < 1216 then decide (2 ≤ count1214 b) else decide (1 ≤ count1216 b)) else (if i < 1218 then decide (2 ≤ count1216 b) else (if i < 1219 then decide (3 ≤ count1216 b) else decide (4 ≤ count1216 b)))) else (if i < 1222 then (if i < 1221 then decide (1 ≤ count1220 b) else decide (2 ≤ count1220 b)) else (if i < 1223 then decide (3 ≤ count1220 b) else (if i < 1224 then decide (4 ≤ count1220 b) else decide (5 ≤ count1220 b))))) else (if i < 1230 then (if i < 1227 then (if i < 1226 then decide (6 ≤ count1220 b) else decide (7 ≤ count1220 b)) else (if i < 1228 then decide (1 ≤ count1227 b) else (if i < 1229 then decide (2 ≤ count1227 b) else decide (3 ≤ count1227 b)))) else (if i < 1233 then (if i < 1231 then decide (4 ≤ count1227 b) else (if i < 1232 then decide (5 ≤ count1227 b) else decide (6 ≤ count1227 b))) else (if i < 1234 then decide (7 ≤ count1227 b) else (if i < 1235 then decide (8 ≤ count1227 b) else decide (9 ≤ count1227 b))))))) else (if i < 1257 then (if i < 1246 then (if i < 1241 then (if i < 1238 then (if i < 1237 then decide (10 ≤ count1227 b) else decide (11 ≤ count1227 b)) else (if i < 1239 then decide (1 ≤ count1238 b) else (if i < 1240 then decide (2 ≤ count1238 b) else decide (3 ≤ count1238 b)))) else (if i < 1243 then (if i < 1242 then decide (4 ≤ count1238 b) else decide (5 ≤ count1238 b)) else (if i < 1244 then decide (6 ≤ count1238 b) else (if i < 1245 then decide (7 ≤ count1238 b) else decide (8 ≤ count1238 b))))) else (if i < 1251 then (if i < 1248 then (if i < 1247 then decide (9 ≤ count1238 b) else decide (10 ≤ count1238 b)) else (if i < 1249 then decide (11 ≤ count1238 b) else (if i < 1250 then decide (1 ≤ count1249 b) else decide (2 ≤ count1249 b)))) else (if i < 1254 then (if i < 1252 then decide (1 ≤ count1251 b) else (if i < 1253 then decide (2 ≤ count1251 b) else decide (3 ≤ count1251 b))) else (if i < 1255 then decide (1 ≤ count1254 b) else (if i < 1256 then decide (2 ≤ count1254 b) else decide (1 ≤ count1256 b)))))) else (if i < 1268 then (if i < 1262 then (if i < 1259 then (if i < 1258 then decide (2 ≤ count1256 b) else decide (3 ≤ count1256 b)) else (if i < 1260 then decide (1 ≤ count1259 b) else (if i < 1261 then decide (2 ≤ count1259 b) else decide (3 ≤ count1259 b)))) else (if i < 1265 then (if i < 1263 then decide (4 ≤ count1259 b) else (if i < 1264 then decide (5 ≤ count1259 b) else decide (6 ≤ count1259 b))) else (if i < 1266 then decide (1 ≤ count1265 b) else (if i < 1267 then decide (2 ≤ count1265 b) else decide (1 ≤ count1267 b))))) else (if i < 1273 then (if i < 1270 then (if i < 1269 then decide (2 ≤ count1267 b) else decide (3 ≤ count1267 b)) else (if i < 1271 then decide (1 ≤ count1270 b) else (if i < 1272 then decide (2 ≤ count1270 b) else decide (1 ≤ count1272 b)))) else (if i < 1276 then (if i < 1274 then decide (2 ≤ count1272 b) else (if i < 1275 then decide (1 ≤ count1274 b) else decide (2 ≤ count1274 b))) else (if i < 1277 then decide (3 ≤ count1274 b) else (if i < 1278 then decide (4 ≤ count1274 b) else decide (1 ≤ count1278 b)))))))) else (if i < 1322 then (if i < 1300 then (if i < 1289 then (if i < 1284 then (if i < 1281 then (if i < 1280 then decide (2 ≤ count1278 b) else decide (3 ≤ count1278 b)) else (if i < 1282 then decide (4 ≤ count1278 b) else (if i < 1283 then decide (5 ≤ count1278 b) else decide (6 ≤ count1278 b)))) else (if i < 1286 then (if i < 1285 then decide (7 ≤ count1278 b) else decide (1 ≤ count1285 b)) else (if i < 1287 then decide (2 ≤ count1285 b) else (if i < 1288 then decide (3 ≤ count1285 b) else decide (4 ≤ count1285 b))))) else (if i < 1294 then (if i < 1291 then (if i < 1290 then decide (5 ≤ count1285 b) else decide (6 ≤ count1285 b)) else (if i < 1292 then decide (7 ≤ count1285 b) else (if i < 1293 then decide (8 ≤ count1285 b) else decide (9 ≤ count1285 b)))) else (if i < 1297 then (if i < 1295 then decide (10 ≤ count1285 b) else (if i < 1296 then decide (11 ≤ count1285 b) else decide (1 ≤ count1296 b))) else (if i < 1298 then decide (2 ≤ count1296 b) else (if i < 1299 then decide (1 ≤ count1298 b) else decide (2 ≤ count1298 b)))))) else (if i < 1311 then (if i < 1305 then (if i < 1302 then (if i < 1301 then decide (3 ≤ count1298 b) else decide (1 ≤ count1301 b)) else (if i < 1303 then decide (2 ≤ count1301 b) else (if i < 1304 then decide (1 ≤ count1303 b) else decide (2 ≤ count1303 b)))) else (if i < 1308 then (if i < 1306 then decide (3 ≤ count1303 b) else (if i < 1307 then decide (1 ≤ count1306 b) else decide (2 ≤ count1306 b))) else (if i < 1309 then decide (3 ≤ count1306 b) else (if i < 1310 then decide (4 ≤ count1306 b) else decide (5 ≤ count1306 b))))) else (if i < 1316 then (if i < 1313 then (if i < 1312 then decide (6 ≤ count1306 b) else decide (1 ≤ count1312 b)) else (if i < 1314 then decide (2 ≤ count1312 b) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b)))) else (if i < 1319 then (if i < 1317 then decide (3 ≤ count1314 b) else (if i < 1318 then decide (1 ≤ count1317 b) else decide (2 ≤ count1317 b))) else (if i < 1320 then decide (1 ≤ count1319 b) else (if i < 1321 then decide (2 ≤ count1319 b) else decide (1 ≤ count1321 b))))))) else (if i < 1343 then (if i < 1332 then (if i < 1327 then (if i < 1324 then (if i < 1323 then decide (2 ≤ count1321 b) else decide (3 ≤ count1321 b)) else (if i < 1325 then decide (4 ≤ count1321 b) else (if i < 1326 then decide (1 ≤ count1325 b) else decide (2 ≤ count1325 b)))) else (if i < 1329 then (if i < 1328 then decide (3 ≤ count1325 b) else decide (4 ≤ count1325 b)) else (if i < 1330 then decide (5 ≤ count1325 b) else (if i < 1331 then decide (6 ≤ count1325 b) else decide (7 ≤ count1325 b))))) else (if i < 1337 then (if i < 1334 then (if i < 1333 then decide (1 ≤ count1332 b) else decide (2 ≤ count1332 b)) else (if i < 1335 then decide (3 ≤ count1332 b) else (if i < 1336 then decide (4 ≤ count1332 b) else decide (5 ≤ count1332 b)))) else (if i < 1340 then (if i < 1338 then decide (6 ≤ count1332 b) else (if i < 1339 then decide (7 ≤ count1332 b) else decide (8 ≤ count1332 b))) else (if i < 1341 then decide (9 ≤ count1332 b) else (if i < 1342 then decide (10 ≤ count1332 b) else decide (11 ≤ count1332 b)))))) else (if i < 1354 then (if i < 1348 then (if i < 1345 then (if i < 1344 then decide (1 ≤ count1343 b) else decide (2 ≤ count1343 b)) else (if i < 1346 then decide (3 ≤ count1343 b) else (if i < 1347 then decide (4 ≤ count1343 b) else decide (5 ≤ count1343 b)))) else (if i < 1351 then (if i < 1349 then decide (6 ≤ count1343 b) else (if i < 1350 then decide (7 ≤ count1343 b) else decide (8 ≤ count1343 b))) else (if i < 1352 then decide (9 ≤ count1343 b) else (if i < 1353 then decide (10 ≤ count1343 b) else decide (11 ≤ count1343 b))))) else (if i < 1359 then (if i < 1356 then (if i < 1355 then decide (1 ≤ count1354 b) else decide (2 ≤ count1354 b)) else (if i < 1357 then decide (3 ≤ count1354 b) else (if i < 1358 then decide (4 ≤ count1354 b) else decide (5 ≤ count1354 b)))) else (if i < 1362 then (if i < 1360 then decide (6 ≤ count1354 b) else (if i < 1361 then decide (7 ≤ count1354 b) else decide (8 ≤ count1354 b))) else (if i < 1363 then decide (9 ≤ count1354 b) else (if i < 1364 then decide (10 ≤ count1354 b) else decide (11 ≤ count1354 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (4 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (6 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (19 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (22 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (23 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (72 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (104 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (160 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (164 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (166 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (168 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (169 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (170 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (171 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (174 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (179 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (180 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (181 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (182 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (183 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (184 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (185 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (186 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (187 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (189 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (224 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (225 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (229 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (231 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (232 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (233 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (238 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (239 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (240 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (242 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (243 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (244 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (252 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (254 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (255 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (256 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (257 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (261 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (263 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (264 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (265 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (270 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (271 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (272 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (274 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (275 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (276 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (283 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (284 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (286 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (352 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (353 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (359 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (360 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (361 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (366 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (367 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (368 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (370 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (371 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (372 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (380 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (382 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (392 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (408 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (410 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (411 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (416 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (424 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (430 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (432 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (434 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (436 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (443 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (444 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (446 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (447 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (448 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (449 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (456 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (457 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (464 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (466 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (467 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (468 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (475 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (476 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (BallClauseLogic.Endpoint q (4 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (BallClauseLogic.Endpoint q (23 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (72 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (104 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (166 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (170 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (184 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (225 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (231 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (239 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (240 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (242 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (243 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (252 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (254 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (257 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (263 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (270 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (271 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (274 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (275 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (284 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (286 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (353 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (359 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (360 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (361 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (366 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (367 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (370 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (380 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (382 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (408 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (416 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (424 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (434 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (444 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (446 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (449 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (456 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (457 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (466 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (467 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (476 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (1 ≤ count201 (baseVal q)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (1 ≤ count203 (baseVal q)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (1 ≤ count205 (baseVal q)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (1 ≤ count207 (baseVal q)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (1 ≤ count209 (baseVal q)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (1 ≤ count211 (baseVal q)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (1 ≤ count213 (baseVal q)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (2 ≤ count221 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (2 ≤ count245 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value396 (q : Snake 81) : valuation q 396 = decide (2 ≤ count395 (baseVal q)) := rfl
theorem value670 (q : Snake 81) : valuation q 670 = decide (2 ≤ count669 (baseVal q)) := rfl
theorem value671 (q : Snake 81) : valuation q 671 = decide (1 ≤ count671 (baseVal q)) := rfl
theorem value673 (q : Snake 81) : valuation q 673 = decide (3 ≤ count671 (baseVal q)) := rfl
theorem value674 (q : Snake 81) : valuation q 674 = decide (1 ≤ count674 (baseVal q)) := rfl
theorem value675 (q : Snake 81) : valuation q 675 = decide (2 ≤ count674 (baseVal q)) := rfl
theorem value676 (q : Snake 81) : valuation q 676 = decide (1 ≤ count676 (baseVal q)) := rfl
theorem value677 (q : Snake 81) : valuation q 677 = decide (2 ≤ count676 (baseVal q)) := rfl
theorem value678 (q : Snake 81) : valuation q 678 = decide (3 ≤ count676 (baseVal q)) := rfl
theorem value679 (q : Snake 81) : valuation q 679 = decide (1 ≤ count679 (baseVal q)) := rfl
theorem value680 (q : Snake 81) : valuation q 680 = decide (2 ≤ count679 (baseVal q)) := rfl
theorem value681 (q : Snake 81) : valuation q 681 = decide (3 ≤ count679 (baseVal q)) := rfl
theorem value682 (q : Snake 81) : valuation q 682 = decide (4 ≤ count679 (baseVal q)) := rfl
theorem value683 (q : Snake 81) : valuation q 683 = decide (5 ≤ count679 (baseVal q)) := rfl
theorem value685 (q : Snake 81) : valuation q 685 = decide (1 ≤ count685 (baseVal q)) := rfl
theorem value686 (q : Snake 81) : valuation q 686 = decide (2 ≤ count685 (baseVal q)) := rfl
theorem value687 (q : Snake 81) : valuation q 687 = decide (1 ≤ count687 (baseVal q)) := rfl
theorem value688 (q : Snake 81) : valuation q 688 = decide (2 ≤ count687 (baseVal q)) := rfl
theorem value689 (q : Snake 81) : valuation q 689 = decide (3 ≤ count687 (baseVal q)) := rfl
theorem value690 (q : Snake 81) : valuation q 690 = decide (1 ≤ count690 (baseVal q)) := rfl
theorem value691 (q : Snake 81) : valuation q 691 = decide (2 ≤ count690 (baseVal q)) := rfl
theorem value692 (q : Snake 81) : valuation q 692 = decide (1 ≤ count692 (baseVal q)) := rfl
theorem value693 (q : Snake 81) : valuation q 693 = decide (2 ≤ count692 (baseVal q)) := rfl
theorem value695 (q : Snake 81) : valuation q 695 = decide (1 ≤ count695 (baseVal q)) := rfl
theorem value696 (q : Snake 81) : valuation q 696 = decide (2 ≤ count695 (baseVal q)) := rfl
theorem value697 (q : Snake 81) : valuation q 697 = decide (3 ≤ count695 (baseVal q)) := rfl
theorem value702 (q : Snake 81) : valuation q 702 = decide (2 ≤ count701 (baseVal q)) := rfl
theorem value703 (q : Snake 81) : valuation q 703 = decide (3 ≤ count701 (baseVal q)) := rfl
theorem value704 (q : Snake 81) : valuation q 704 = decide (4 ≤ count701 (baseVal q)) := rfl
theorem value705 (q : Snake 81) : valuation q 705 = decide (5 ≤ count701 (baseVal q)) := rfl
theorem value706 (q : Snake 81) : valuation q 706 = decide (6 ≤ count701 (baseVal q)) := rfl
theorem value710 (q : Snake 81) : valuation q 710 = decide (1 ≤ count710 (baseVal q)) := rfl
theorem value712 (q : Snake 81) : valuation q 712 = decide (1 ≤ count712 (baseVal q)) := rfl
theorem value713 (q : Snake 81) : valuation q 713 = decide (2 ≤ count712 (baseVal q)) := rfl
theorem value715 (q : Snake 81) : valuation q 715 = decide (1 ≤ count715 (baseVal q)) := rfl
theorem value716 (q : Snake 81) : valuation q 716 = decide (2 ≤ count715 (baseVal q)) := rfl
theorem value717 (q : Snake 81) : valuation q 717 = decide (1 ≤ count717 (baseVal q)) := rfl
theorem value718 (q : Snake 81) : valuation q 718 = decide (2 ≤ count717 (baseVal q)) := rfl
theorem value720 (q : Snake 81) : valuation q 720 = decide (1 ≤ count720 (baseVal q)) := rfl
theorem value721 (q : Snake 81) : valuation q 721 = decide (2 ≤ count720 (baseVal q)) := rfl
theorem value722 (q : Snake 81) : valuation q 722 = decide (3 ≤ count720 (baseVal q)) := rfl
theorem value726 (q : Snake 81) : valuation q 726 = decide (1 ≤ count726 (baseVal q)) := rfl
theorem value727 (q : Snake 81) : valuation q 727 = decide (2 ≤ count726 (baseVal q)) := rfl
theorem value728 (q : Snake 81) : valuation q 728 = decide (1 ≤ count728 (baseVal q)) := rfl
theorem value729 (q : Snake 81) : valuation q 729 = decide (2 ≤ count728 (baseVal q)) := rfl
theorem value731 (q : Snake 81) : valuation q 731 = decide (1 ≤ count731 (baseVal q)) := rfl
theorem value733 (q : Snake 81) : valuation q 733 = decide (1 ≤ count733 (baseVal q)) := rfl
theorem value734 (q : Snake 81) : valuation q 734 = decide (2 ≤ count733 (baseVal q)) := rfl
theorem value736 (q : Snake 81) : valuation q 736 = decide (1 ≤ count736 (baseVal q)) := rfl
theorem value737 (q : Snake 81) : valuation q 737 = decide (2 ≤ count736 (baseVal q)) := rfl
theorem value738 (q : Snake 81) : valuation q 738 = decide (3 ≤ count736 (baseVal q)) := rfl
theorem value742 (q : Snake 81) : valuation q 742 = decide (1 ≤ count742 (baseVal q)) := rfl
theorem value743 (q : Snake 81) : valuation q 743 = decide (2 ≤ count742 (baseVal q)) := rfl
theorem value744 (q : Snake 81) : valuation q 744 = decide (3 ≤ count742 (baseVal q)) := rfl
theorem value745 (q : Snake 81) : valuation q 745 = decide (4 ≤ count742 (baseVal q)) := rfl
theorem value754 (q : Snake 81) : valuation q 754 = decide (4 ≤ count751 (baseVal q)) := rfl
theorem value755 (q : Snake 81) : valuation q 755 = decide (5 ≤ count751 (baseVal q)) := rfl
theorem value756 (q : Snake 81) : valuation q 756 = decide (6 ≤ count751 (baseVal q)) := rfl
theorem value757 (q : Snake 81) : valuation q 757 = decide (7 ≤ count751 (baseVal q)) := rfl
theorem value758 (q : Snake 81) : valuation q 758 = decide (8 ≤ count751 (baseVal q)) := rfl
theorem value760 (q : Snake 81) : valuation q 760 = decide (1 ≤ count760 (baseVal q)) := rfl
theorem value761 (q : Snake 81) : valuation q 761 = decide (2 ≤ count760 (baseVal q)) := rfl
theorem value762 (q : Snake 81) : valuation q 762 = decide (1 ≤ count762 (baseVal q)) := rfl
theorem value763 (q : Snake 81) : valuation q 763 = decide (2 ≤ count762 (baseVal q)) := rfl
theorem value765 (q : Snake 81) : valuation q 765 = decide (1 ≤ count765 (baseVal q)) := rfl
theorem value767 (q : Snake 81) : valuation q 767 = decide (1 ≤ count767 (baseVal q)) := rfl
theorem value770 (q : Snake 81) : valuation q 770 = decide (1 ≤ count770 (baseVal q)) := rfl
theorem value771 (q : Snake 81) : valuation q 771 = decide (2 ≤ count770 (baseVal q)) := rfl
theorem value778 (q : Snake 81) : valuation q 778 = decide (1 ≤ count778 (baseVal q)) := rfl
theorem value781 (q : Snake 81) : valuation q 781 = decide (1 ≤ count781 (baseVal q)) := rfl
theorem value783 (q : Snake 81) : valuation q 783 = decide (1 ≤ count783 (baseVal q)) := rfl
theorem value786 (q : Snake 81) : valuation q 786 = decide (1 ≤ count786 (baseVal q)) := rfl
theorem value787 (q : Snake 81) : valuation q 787 = decide (2 ≤ count786 (baseVal q)) := rfl
theorem value792 (q : Snake 81) : valuation q 792 = decide (1 ≤ count792 (baseVal q)) := rfl
theorem value793 (q : Snake 81) : valuation q 793 = decide (2 ≤ count792 (baseVal q)) := rfl
theorem value794 (q : Snake 81) : valuation q 794 = decide (3 ≤ count792 (baseVal q)) := rfl
theorem value801 (q : Snake 81) : valuation q 801 = decide (1 ≤ count801 (baseVal q)) := rfl
theorem value802 (q : Snake 81) : valuation q 802 = decide (2 ≤ count801 (baseVal q)) := rfl
theorem value803 (q : Snake 81) : valuation q 803 = decide (1 ≤ count803 (baseVal q)) := rfl
theorem value804 (q : Snake 81) : valuation q 804 = decide (2 ≤ count803 (baseVal q)) := rfl
theorem value805 (q : Snake 81) : valuation q 805 = decide (3 ≤ count803 (baseVal q)) := rfl
theorem value806 (q : Snake 81) : valuation q 806 = decide (1 ≤ count806 (baseVal q)) := rfl
theorem value807 (q : Snake 81) : valuation q 807 = decide (2 ≤ count806 (baseVal q)) := rfl
theorem value808 (q : Snake 81) : valuation q 808 = decide (1 ≤ count808 (baseVal q)) := rfl
theorem value809 (q : Snake 81) : valuation q 809 = decide (2 ≤ count808 (baseVal q)) := rfl
theorem value811 (q : Snake 81) : valuation q 811 = decide (1 ≤ count811 (baseVal q)) := rfl
theorem value812 (q : Snake 81) : valuation q 812 = decide (2 ≤ count811 (baseVal q)) := rfl
theorem value813 (q : Snake 81) : valuation q 813 = decide (3 ≤ count811 (baseVal q)) := rfl
theorem value817 (q : Snake 81) : valuation q 817 = decide (1 ≤ count817 (baseVal q)) := rfl
theorem value819 (q : Snake 81) : valuation q 819 = decide (1 ≤ count819 (baseVal q)) := rfl
theorem value820 (q : Snake 81) : valuation q 820 = decide (2 ≤ count819 (baseVal q)) := rfl
theorem value822 (q : Snake 81) : valuation q 822 = decide (1 ≤ count822 (baseVal q)) := rfl
theorem value824 (q : Snake 81) : valuation q 824 = decide (1 ≤ count824 (baseVal q)) := rfl
theorem value826 (q : Snake 81) : valuation q 826 = decide (1 ≤ count826 (baseVal q)) := rfl
theorem value827 (q : Snake 81) : valuation q 827 = decide (2 ≤ count826 (baseVal q)) := rfl
theorem value830 (q : Snake 81) : valuation q 830 = decide (1 ≤ count830 (baseVal q)) := rfl
theorem value831 (q : Snake 81) : valuation q 831 = decide (2 ≤ count830 (baseVal q)) := rfl
theorem value837 (q : Snake 81) : valuation q 837 = decide (1 ≤ count837 (baseVal q)) := rfl
theorem value838 (q : Snake 81) : valuation q 838 = decide (2 ≤ count837 (baseVal q)) := rfl
theorem value839 (q : Snake 81) : valuation q 839 = decide (3 ≤ count837 (baseVal q)) := rfl
theorem value840 (q : Snake 81) : valuation q 840 = decide (4 ≤ count837 (baseVal q)) := rfl
theorem value846 (q : Snake 81) : valuation q 846 = decide (1 ≤ count846 (baseVal q)) := rfl
theorem value847 (q : Snake 81) : valuation q 847 = decide (2 ≤ count846 (baseVal q)) := rfl
theorem value848 (q : Snake 81) : valuation q 848 = decide (3 ≤ count846 (baseVal q)) := rfl
theorem value849 (q : Snake 81) : valuation q 849 = decide (4 ≤ count846 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (5 ≤ count846 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (9 ≤ count855 (baseVal q)) := rfl
theorem meaningNeg99 (b : Nat → Bool) : literal (valuationOf b) (-99) = decide (1 ≤ countLit b [-99]) := by
  change literal b (-99) = decide (1 ≤ countLit b [-99])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-99) <;> decide
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
theorem meaningNeg90 (b : Nat → Bool) : literal (valuationOf b) (-90) = decide (1 ≤ countLit b [-90]) := by
  change literal b (-90) = decide (1 ≤ countLit b [-90])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-90) <;> decide
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
theorem meaningNeg83 (b : Nat → Bool) : literal (valuationOf b) (-83) = decide (1 ≤ countLit b [-83]) := by
  change literal b (-83) = decide (1 ≤ countLit b [-83])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-83) <;> decide
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
theorem meaningNeg52 (b : Nat → Bool) : literal (valuationOf b) (-52) = decide (1 ≤ countLit b [-52]) := by
  change literal b (-52) = decide (1 ≤ countLit b [-52])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-52) <;> decide
theorem meaningNeg50 (b : Nat → Bool) : literal (valuationOf b) (-50) = decide (1 ≤ countLit b [-50]) := by
  change literal b (-50) = decide (1 ≤ countLit b [-50])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-50) <;> decide
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
theorem meaningNeg9 (b : Nat → Bool) : literal (valuationOf b) (-9) = decide (1 ≤ countLit b [-9]) := by
  change literal b (-9) = decide (1 ≤ countLit b [-9])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-9) <;> decide
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
theorem meaningNeg3 (b : Nat → Bool) : literal (valuationOf b) (-3) = decide (1 ≤ countLit b [-3]) := by
  change literal b (-3) = decide (1 ≤ countLit b [-3])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-3) <;> decide
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning102 (b : Nat → Bool) : literal (valuationOf b) (102) = decide (1 ≤ countLit b [102]) := by
  change literal b (102) = decide (1 ≤ countLit b [102])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (102) <;> decide
theorem meaning104 (b : Nat → Bool) : literal (valuationOf b) (104) = decide (1 ≤ countLit b [104]) := by
  change literal b (104) = decide (1 ≤ countLit b [104])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (104) <;> decide
theorem meaning105 (b : Nat → Bool) : literal (valuationOf b) (105) = decide (1 ≤ countLit b [105]) := by
  change literal b (105) = decide (1 ≤ countLit b [105])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (105) <;> decide
theorem meaning108 (b : Nat → Bool) : literal (valuationOf b) (108) = decide (1 ≤ countLit b [108]) := by
  change literal b (108) = decide (1 ≤ countLit b [108])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (108) <;> decide
theorem meaning124 (b : Nat → Bool) : literal (valuationOf b) (124) = decide (1 ≤ countLit b [124]) := by
  change literal b (124) = decide (1 ≤ countLit b [124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (124) <;> decide
theorem meaning129 (b : Nat → Bool) : literal (valuationOf b) (129) = decide (1 ≤ countLit b [129]) := by
  change literal b (129) = decide (1 ≤ countLit b [129])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (129) <;> decide
theorem meaning134 (b : Nat → Bool) : literal (valuationOf b) (134) = decide (1 ≤ countLit b [134]) := by
  change literal b (134) = decide (1 ≤ countLit b [134])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (134) <;> decide
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
theorem meaning156 (b : Nat → Bool) : literal (valuationOf b) (156) = decide (1 ≤ countLit b [156]) := by
  change literal b (156) = decide (1 ≤ countLit b [156])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (156) <;> decide
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
theorem meaning166 (b : Nat → Bool) : literal (valuationOf b) (166) = decide (1 ≤ countLit b [166]) := by
  change literal b (166) = decide (1 ≤ countLit b [166])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (166) <;> decide
theorem meaning170 (b : Nat → Bool) : literal (valuationOf b) (170) = decide (1 ≤ countLit b [170]) := by
  change literal b (170) = decide (1 ≤ countLit b [170])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (170) <;> decide
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
theorem meaning180 (b : Nat → Bool) : literal (valuationOf b) (180) = decide (1 ≤ countLit b [180]) := by
  change literal b (180) = decide (1 ≤ countLit b [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (180) <;> decide
theorem meaning184 (b : Nat → Bool) : literal (valuationOf b) (184) = decide (1 ≤ countLit b [184]) := by
  change literal b (184) = decide (1 ≤ countLit b [184])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (184) <;> decide
theorem meaning191 (b : Nat → Bool) : literal (valuationOf b) (191) = decide (1 ≤ countLit b [191]) := by
  change literal b (191) = decide (1 ≤ countLit b [191])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (191) <;> decide
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
theorem meaning201 (b : Nat → Bool) : literal (valuationOf b) 201 = decide (1 ≤ count201 b) := rfl
theorem meaning203 (b : Nat → Bool) : literal (valuationOf b) 203 = decide (1 ≤ count203 b) := rfl
theorem meaning205 (b : Nat → Bool) : literal (valuationOf b) 205 = decide (1 ≤ count205 b) := rfl
theorem meaning207 (b : Nat → Bool) : literal (valuationOf b) 207 = decide (1 ≤ count207 b) := rfl
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) 209 = decide (1 ≤ count209 b) := rfl
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) 211 = decide (1 ≤ count211 b) := rfl
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) 213 = decide (1 ≤ count213 b) := rfl
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) 222 = decide (2 ≤ count221 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning246 (b : Nat → Bool) : literal (valuationOf b) 246 = decide (2 ≤ count245 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning396 (b : Nat → Bool) : literal (valuationOf b) 396 = decide (2 ≤ count395 b) := rfl
theorem meaning670 (b : Nat → Bool) : literal (valuationOf b) 670 = decide (2 ≤ count669 b) := rfl
theorem meaning671 (b : Nat → Bool) : literal (valuationOf b) 671 = decide (1 ≤ count671 b) := rfl
theorem meaning673 (b : Nat → Bool) : literal (valuationOf b) 673 = decide (3 ≤ count671 b) := rfl
theorem meaning674 (b : Nat → Bool) : literal (valuationOf b) 674 = decide (1 ≤ count674 b) := rfl
theorem meaning675 (b : Nat → Bool) : literal (valuationOf b) 675 = decide (2 ≤ count674 b) := rfl
theorem meaning676 (b : Nat → Bool) : literal (valuationOf b) 676 = decide (1 ≤ count676 b) := rfl
theorem meaning677 (b : Nat → Bool) : literal (valuationOf b) 677 = decide (2 ≤ count676 b) := rfl
theorem meaning678 (b : Nat → Bool) : literal (valuationOf b) 678 = decide (3 ≤ count676 b) := rfl
theorem meaning679 (b : Nat → Bool) : literal (valuationOf b) 679 = decide (1 ≤ count679 b) := rfl
theorem meaning680 (b : Nat → Bool) : literal (valuationOf b) 680 = decide (2 ≤ count679 b) := rfl
theorem meaning681 (b : Nat → Bool) : literal (valuationOf b) 681 = decide (3 ≤ count679 b) := rfl
theorem meaning682 (b : Nat → Bool) : literal (valuationOf b) 682 = decide (4 ≤ count679 b) := rfl
theorem meaning683 (b : Nat → Bool) : literal (valuationOf b) 683 = decide (5 ≤ count679 b) := rfl
theorem meaning685 (b : Nat → Bool) : literal (valuationOf b) 685 = decide (1 ≤ count685 b) := rfl
theorem meaning686 (b : Nat → Bool) : literal (valuationOf b) 686 = decide (2 ≤ count685 b) := rfl
theorem meaning687 (b : Nat → Bool) : literal (valuationOf b) 687 = decide (1 ≤ count687 b) := rfl
theorem meaning688 (b : Nat → Bool) : literal (valuationOf b) 688 = decide (2 ≤ count687 b) := rfl
theorem meaning689 (b : Nat → Bool) : literal (valuationOf b) 689 = decide (3 ≤ count687 b) := rfl
theorem meaning690 (b : Nat → Bool) : literal (valuationOf b) 690 = decide (1 ≤ count690 b) := rfl
theorem meaning691 (b : Nat → Bool) : literal (valuationOf b) 691 = decide (2 ≤ count690 b) := rfl
theorem meaning692 (b : Nat → Bool) : literal (valuationOf b) 692 = decide (1 ≤ count692 b) := rfl
theorem meaning693 (b : Nat → Bool) : literal (valuationOf b) 693 = decide (2 ≤ count692 b) := rfl
theorem meaning695 (b : Nat → Bool) : literal (valuationOf b) 695 = decide (1 ≤ count695 b) := rfl
theorem meaning696 (b : Nat → Bool) : literal (valuationOf b) 696 = decide (2 ≤ count695 b) := rfl
theorem meaning697 (b : Nat → Bool) : literal (valuationOf b) 697 = decide (3 ≤ count695 b) := rfl
theorem meaning702 (b : Nat → Bool) : literal (valuationOf b) 702 = decide (2 ≤ count701 b) := rfl
theorem meaning703 (b : Nat → Bool) : literal (valuationOf b) 703 = decide (3 ≤ count701 b) := rfl
theorem meaning704 (b : Nat → Bool) : literal (valuationOf b) 704 = decide (4 ≤ count701 b) := rfl
theorem meaning705 (b : Nat → Bool) : literal (valuationOf b) 705 = decide (5 ≤ count701 b) := rfl
theorem meaning706 (b : Nat → Bool) : literal (valuationOf b) 706 = decide (6 ≤ count701 b) := rfl
theorem meaning710 (b : Nat → Bool) : literal (valuationOf b) 710 = decide (1 ≤ count710 b) := rfl
theorem meaning712 (b : Nat → Bool) : literal (valuationOf b) 712 = decide (1 ≤ count712 b) := rfl
theorem meaning713 (b : Nat → Bool) : literal (valuationOf b) 713 = decide (2 ≤ count712 b) := rfl
theorem meaning715 (b : Nat → Bool) : literal (valuationOf b) 715 = decide (1 ≤ count715 b) := rfl
theorem meaning716 (b : Nat → Bool) : literal (valuationOf b) 716 = decide (2 ≤ count715 b) := rfl
theorem meaning717 (b : Nat → Bool) : literal (valuationOf b) 717 = decide (1 ≤ count717 b) := rfl
theorem meaning718 (b : Nat → Bool) : literal (valuationOf b) 718 = decide (2 ≤ count717 b) := rfl
theorem meaning720 (b : Nat → Bool) : literal (valuationOf b) 720 = decide (1 ≤ count720 b) := rfl
theorem meaning721 (b : Nat → Bool) : literal (valuationOf b) 721 = decide (2 ≤ count720 b) := rfl
theorem meaning722 (b : Nat → Bool) : literal (valuationOf b) 722 = decide (3 ≤ count720 b) := rfl
theorem meaning726 (b : Nat → Bool) : literal (valuationOf b) 726 = decide (1 ≤ count726 b) := rfl
theorem meaning727 (b : Nat → Bool) : literal (valuationOf b) 727 = decide (2 ≤ count726 b) := rfl
theorem meaning728 (b : Nat → Bool) : literal (valuationOf b) 728 = decide (1 ≤ count728 b) := rfl
theorem meaning729 (b : Nat → Bool) : literal (valuationOf b) 729 = decide (2 ≤ count728 b) := rfl
theorem meaning731 (b : Nat → Bool) : literal (valuationOf b) 731 = decide (1 ≤ count731 b) := rfl
theorem meaning733 (b : Nat → Bool) : literal (valuationOf b) 733 = decide (1 ≤ count733 b) := rfl
theorem meaning734 (b : Nat → Bool) : literal (valuationOf b) 734 = decide (2 ≤ count733 b) := rfl
theorem meaning736 (b : Nat → Bool) : literal (valuationOf b) 736 = decide (1 ≤ count736 b) := rfl
theorem meaning737 (b : Nat → Bool) : literal (valuationOf b) 737 = decide (2 ≤ count736 b) := rfl
theorem meaning738 (b : Nat → Bool) : literal (valuationOf b) 738 = decide (3 ≤ count736 b) := rfl
theorem meaning742 (b : Nat → Bool) : literal (valuationOf b) 742 = decide (1 ≤ count742 b) := rfl
theorem meaning743 (b : Nat → Bool) : literal (valuationOf b) 743 = decide (2 ≤ count742 b) := rfl
theorem meaning744 (b : Nat → Bool) : literal (valuationOf b) 744 = decide (3 ≤ count742 b) := rfl
theorem meaning745 (b : Nat → Bool) : literal (valuationOf b) 745 = decide (4 ≤ count742 b) := rfl
theorem meaning754 (b : Nat → Bool) : literal (valuationOf b) 754 = decide (4 ≤ count751 b) := rfl
theorem meaning755 (b : Nat → Bool) : literal (valuationOf b) 755 = decide (5 ≤ count751 b) := rfl
theorem meaning756 (b : Nat → Bool) : literal (valuationOf b) 756 = decide (6 ≤ count751 b) := rfl
theorem meaning757 (b : Nat → Bool) : literal (valuationOf b) 757 = decide (7 ≤ count751 b) := rfl
theorem meaning758 (b : Nat → Bool) : literal (valuationOf b) 758 = decide (8 ≤ count751 b) := rfl
theorem meaning760 (b : Nat → Bool) : literal (valuationOf b) 760 = decide (1 ≤ count760 b) := rfl
theorem meaning761 (b : Nat → Bool) : literal (valuationOf b) 761 = decide (2 ≤ count760 b) := rfl
theorem meaning762 (b : Nat → Bool) : literal (valuationOf b) 762 = decide (1 ≤ count762 b) := rfl
theorem meaning763 (b : Nat → Bool) : literal (valuationOf b) 763 = decide (2 ≤ count762 b) := rfl
theorem meaning765 (b : Nat → Bool) : literal (valuationOf b) 765 = decide (1 ≤ count765 b) := rfl
theorem meaning767 (b : Nat → Bool) : literal (valuationOf b) 767 = decide (1 ≤ count767 b) := rfl
theorem meaning770 (b : Nat → Bool) : literal (valuationOf b) 770 = decide (1 ≤ count770 b) := rfl
theorem meaning771 (b : Nat → Bool) : literal (valuationOf b) 771 = decide (2 ≤ count770 b) := rfl
theorem meaning778 (b : Nat → Bool) : literal (valuationOf b) 778 = decide (1 ≤ count778 b) := rfl
theorem meaning781 (b : Nat → Bool) : literal (valuationOf b) 781 = decide (1 ≤ count781 b) := rfl
theorem meaning783 (b : Nat → Bool) : literal (valuationOf b) 783 = decide (1 ≤ count783 b) := rfl
theorem meaning786 (b : Nat → Bool) : literal (valuationOf b) 786 = decide (1 ≤ count786 b) := rfl
theorem meaning787 (b : Nat → Bool) : literal (valuationOf b) 787 = decide (2 ≤ count786 b) := rfl
theorem meaning792 (b : Nat → Bool) : literal (valuationOf b) 792 = decide (1 ≤ count792 b) := rfl
theorem meaning793 (b : Nat → Bool) : literal (valuationOf b) 793 = decide (2 ≤ count792 b) := rfl
theorem meaning794 (b : Nat → Bool) : literal (valuationOf b) 794 = decide (3 ≤ count792 b) := rfl
theorem meaning801 (b : Nat → Bool) : literal (valuationOf b) 801 = decide (1 ≤ count801 b) := rfl
theorem meaning802 (b : Nat → Bool) : literal (valuationOf b) 802 = decide (2 ≤ count801 b) := rfl
theorem meaning803 (b : Nat → Bool) : literal (valuationOf b) 803 = decide (1 ≤ count803 b) := rfl
theorem meaning804 (b : Nat → Bool) : literal (valuationOf b) 804 = decide (2 ≤ count803 b) := rfl
theorem meaning805 (b : Nat → Bool) : literal (valuationOf b) 805 = decide (3 ≤ count803 b) := rfl
theorem meaning806 (b : Nat → Bool) : literal (valuationOf b) 806 = decide (1 ≤ count806 b) := rfl
theorem meaning807 (b : Nat → Bool) : literal (valuationOf b) 807 = decide (2 ≤ count806 b) := rfl
theorem meaning808 (b : Nat → Bool) : literal (valuationOf b) 808 = decide (1 ≤ count808 b) := rfl
theorem meaning809 (b : Nat → Bool) : literal (valuationOf b) 809 = decide (2 ≤ count808 b) := rfl
theorem meaning811 (b : Nat → Bool) : literal (valuationOf b) 811 = decide (1 ≤ count811 b) := rfl
theorem meaning812 (b : Nat → Bool) : literal (valuationOf b) 812 = decide (2 ≤ count811 b) := rfl
theorem meaning813 (b : Nat → Bool) : literal (valuationOf b) 813 = decide (3 ≤ count811 b) := rfl
theorem meaning817 (b : Nat → Bool) : literal (valuationOf b) 817 = decide (1 ≤ count817 b) := rfl
theorem meaning819 (b : Nat → Bool) : literal (valuationOf b) 819 = decide (1 ≤ count819 b) := rfl
theorem meaning820 (b : Nat → Bool) : literal (valuationOf b) 820 = decide (2 ≤ count819 b) := rfl
theorem meaning822 (b : Nat → Bool) : literal (valuationOf b) 822 = decide (1 ≤ count822 b) := rfl
theorem meaning824 (b : Nat → Bool) : literal (valuationOf b) 824 = decide (1 ≤ count824 b) := rfl
theorem meaning826 (b : Nat → Bool) : literal (valuationOf b) 826 = decide (1 ≤ count826 b) := rfl
theorem meaning827 (b : Nat → Bool) : literal (valuationOf b) 827 = decide (2 ≤ count826 b) := rfl
theorem meaning830 (b : Nat → Bool) : literal (valuationOf b) 830 = decide (1 ≤ count830 b) := rfl
theorem meaning831 (b : Nat → Bool) : literal (valuationOf b) 831 = decide (2 ≤ count830 b) := rfl
theorem meaning837 (b : Nat → Bool) : literal (valuationOf b) 837 = decide (1 ≤ count837 b) := rfl
theorem meaning838 (b : Nat → Bool) : literal (valuationOf b) 838 = decide (2 ≤ count837 b) := rfl
theorem meaning839 (b : Nat → Bool) : literal (valuationOf b) 839 = decide (3 ≤ count837 b) := rfl
theorem meaning840 (b : Nat → Bool) : literal (valuationOf b) 840 = decide (4 ≤ count837 b) := rfl
theorem meaning846 (b : Nat → Bool) : literal (valuationOf b) 846 = decide (1 ≤ count846 b) := rfl
theorem meaning847 (b : Nat → Bool) : literal (valuationOf b) 847 = decide (2 ≤ count846 b) := rfl
theorem meaning848 (b : Nat → Bool) : literal (valuationOf b) 848 = decide (3 ≤ count846 b) := rfl
theorem meaning849 (b : Nat → Bool) : literal (valuationOf b) 849 = decide (4 ≤ count846 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (5 ≤ count846 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (9 ≤ count855 b) := rfl
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
end Snake9.Regrowth.E112147
