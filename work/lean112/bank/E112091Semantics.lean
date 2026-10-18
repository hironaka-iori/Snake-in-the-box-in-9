import E112091Data
namespace Snake9.Regrowth.E112091
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (4 : Vertex)))) else (if i < 4 then decide (InPath q (6 : Vertex)) else (if i < 5 then decide (InPath q (8 : Vertex)) else decide (InPath q (9 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (10 : Vertex)) else (if i < 8 then decide (InPath q (11 : Vertex)) else decide (InPath q (14 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (19 : Vertex)) else decide (InPath q (21 : Vertex))) else (if i < 12 then decide (InPath q (22 : Vertex)) else decide (InPath q (23 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (24 : Vertex)) else (if i < 15 then decide (InPath q (25 : Vertex)) else decide (InPath q (26 : Vertex)))) else (if i < 17 then decide (InPath q (27 : Vertex)) else (if i < 18 then decide (InPath q (29 : Vertex)) else decide (InPath q (64 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (65 : Vertex)) else (if i < 21 then decide (InPath q (69 : Vertex)) else decide (InPath q (71 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (72 : Vertex)) else decide (InPath q (73 : Vertex))) else (if i < 25 then decide (InPath q (78 : Vertex)) else decide (InPath q (79 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (80 : Vertex)) else (if i < 28 then decide (InPath q (82 : Vertex)) else decide (InPath q (83 : Vertex)))) else (if i < 30 then decide (InPath q (84 : Vertex)) else (if i < 31 then decide (InPath q (91 : Vertex)) else decide (InPath q (92 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (94 : Vertex)) else (if i < 34 then decide (InPath q (95 : Vertex)) else decide (InPath q (160 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (164 : Vertex)) else decide (InPath q (166 : Vertex))) else (if i < 38 then decide (InPath q (168 : Vertex)) else decide (InPath q (169 : Vertex)))))) else (if i < 46 then (if i < 42 then (if i < 40 then decide (InPath q (170 : Vertex)) else (if i < 41 then decide (InPath q (171 : Vertex)) else decide (InPath q (174 : Vertex)))) else (if i < 44 then (if i < 43 then decide (InPath q (179 : Vertex)) else decide (InPath q (180 : Vertex))) else (if i < 45 then decide (InPath q (181 : Vertex)) else decide (InPath q (182 : Vertex))))) else (if i < 49 then (if i < 47 then decide (InPath q (183 : Vertex)) else (if i < 48 then decide (InPath q (184 : Vertex)) else decide (InPath q (185 : Vertex)))) else (if i < 51 then (if i < 50 then decide (InPath q (186 : Vertex)) else decide (InPath q (187 : Vertex))) else (if i < 52 then decide (InPath q (189 : Vertex)) else decide (InPath q (200 : Vertex)))))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then decide (InPath q (203 : Vertex)) else (if i < 55 then decide (InPath q (216 : Vertex)) else decide (InPath q (218 : Vertex)))) else (if i < 57 then decide (InPath q (219 : Vertex)) else (if i < 58 then decide (InPath q (224 : Vertex)) else decide (InPath q (232 : Vertex))))) else (if i < 62 then (if i < 60 then decide (InPath q (238 : Vertex)) else (if i < 61 then decide (InPath q (240 : Vertex)) else decide (InPath q (242 : Vertex)))) else (if i < 64 then (if i < 63 then decide (InPath q (244 : Vertex)) else decide (InPath q (251 : Vertex))) else (if i < 65 then decide (InPath q (252 : Vertex)) else decide (InPath q (254 : Vertex)))))) else (if i < 72 then (if i < 69 then (if i < 67 then decide (InPath q (255 : Vertex)) else (if i < 68 then decide (InPath q (264 : Vertex)) else decide (InPath q (296 : Vertex)))) else (if i < 70 then decide (InPath q (353 : Vertex)) else (if i < 71 then decide (InPath q (357 : Vertex)) else decide (InPath q (359 : Vertex))))) else (if i < 75 then (if i < 73 then decide (InPath q (360 : Vertex)) else (if i < 74 then decide (InPath q (361 : Vertex)) else decide (InPath q (366 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (367 : Vertex)) else decide (InPath q (416 : Vertex))) else (if i < 78 then decide (InPath q (417 : Vertex)) else decide (InPath q (421 : Vertex))))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then decide (InPath q (423 : Vertex)) else (if i < 81 then decide (InPath q (424 : Vertex)) else decide (InPath q (425 : Vertex)))) else (if i < 83 then decide (InPath q (430 : Vertex)) else (if i < 84 then decide (InPath q (431 : Vertex)) else decide (InPath q (432 : Vertex))))) else (if i < 88 then (if i < 86 then decide (InPath q (434 : Vertex)) else (if i < 87 then decide (InPath q (435 : Vertex)) else decide (InPath q (436 : Vertex)))) else (if i < 90 then (if i < 89 then decide (InPath q (444 : Vertex)) else decide (InPath q (446 : Vertex))) else (if i < 91 then decide (InPath q (447 : Vertex)) else decide (InPath q (448 : Vertex)))))) else (if i < 99 then (if i < 95 then (if i < 93 then decide (InPath q (449 : Vertex)) else (if i < 94 then decide (InPath q (453 : Vertex)) else decide (InPath q (455 : Vertex)))) else (if i < 97 then (if i < 96 then decide (InPath q (456 : Vertex)) else decide (InPath q (457 : Vertex))) else (if i < 98 then decide (InPath q (462 : Vertex)) else decide (InPath q (463 : Vertex))))) else (if i < 102 then (if i < 100 then decide (InPath q (464 : Vertex)) else (if i < 101 then decide (InPath q (466 : Vertex)) else decide (InPath q (467 : Vertex)))) else (if i < 104 then (if i < 103 then decide (InPath q (468 : Vertex)) else decide (InPath q (475 : Vertex))) else (if i < 105 then decide (InPath q (476 : Vertex)) else decide (InPath q (478 : Vertex))))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then decide (InPath q (479 : Vertex)) else (if i < 108 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (4 : Vertex)))) else (if i < 110 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else (if i < 111 then decide (BallClauseLogic.Endpoint q (8 : Vertex)) else decide (BallClauseLogic.Endpoint q (9 : Vertex))))) else (if i < 115 then (if i < 113 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else (if i < 114 then decide (BallClauseLogic.Endpoint q (11 : Vertex)) else decide (BallClauseLogic.Endpoint q (14 : Vertex)))) else (if i < 117 then (if i < 116 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else decide (BallClauseLogic.Endpoint q (21 : Vertex))) else (if i < 118 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (23 : Vertex)))))) else (if i < 125 then (if i < 122 then (if i < 120 then decide (BallClauseLogic.Endpoint q (24 : Vertex)) else (if i < 121 then decide (BallClauseLogic.Endpoint q (25 : Vertex)) else decide (BallClauseLogic.Endpoint q (26 : Vertex)))) else (if i < 123 then decide (BallClauseLogic.Endpoint q (27 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (29 : Vertex)) else decide (BallClauseLogic.Endpoint q (64 : Vertex))))) else (if i < 128 then (if i < 126 then decide (BallClauseLogic.Endpoint q (65 : Vertex)) else (if i < 127 then decide (BallClauseLogic.Endpoint q (69 : Vertex)) else decide (BallClauseLogic.Endpoint q (71 : Vertex)))) else (if i < 130 then (if i < 129 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else decide (BallClauseLogic.Endpoint q (73 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (78 : Vertex)) else decide (BallClauseLogic.Endpoint q (79 : Vertex))))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else (if i < 134 then decide (BallClauseLogic.Endpoint q (82 : Vertex)) else decide (BallClauseLogic.Endpoint q (83 : Vertex)))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (91 : Vertex)) else decide (BallClauseLogic.Endpoint q (92 : Vertex))))) else (if i < 141 then (if i < 139 then decide (BallClauseLogic.Endpoint q (94 : Vertex)) else (if i < 140 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else decide (BallClauseLogic.Endpoint q (160 : Vertex)))) else (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (164 : Vertex)) else decide (BallClauseLogic.Endpoint q (166 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else decide (BallClauseLogic.Endpoint q (169 : Vertex)))))) else (if i < 152 then (if i < 148 then (if i < 146 then decide (BallClauseLogic.Endpoint q (170 : Vertex)) else (if i < 147 then decide (BallClauseLogic.Endpoint q (171 : Vertex)) else decide (BallClauseLogic.Endpoint q (174 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (180 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (181 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex))))) else (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (183 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (184 : Vertex)) else decide (BallClauseLogic.Endpoint q (185 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (187 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (200 : Vertex)))))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (203 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (216 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex)))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (219 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (224 : Vertex)) else decide (BallClauseLogic.Endpoint q (232 : Vertex))))) else (if i < 168 then (if i < 166 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (240 : Vertex)) else decide (BallClauseLogic.Endpoint q (242 : Vertex)))) else (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (251 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (252 : Vertex)) else decide (BallClauseLogic.Endpoint q (254 : Vertex)))))) else (if i < 179 then (if i < 175 then (if i < 173 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (264 : Vertex)) else decide (BallClauseLogic.Endpoint q (296 : Vertex)))) else (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (353 : Vertex)) else decide (BallClauseLogic.Endpoint q (357 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (360 : Vertex))))) else (if i < 182 then (if i < 180 then decide (BallClauseLogic.Endpoint q (361 : Vertex)) else (if i < 181 then decide (BallClauseLogic.Endpoint q (366 : Vertex)) else decide (BallClauseLogic.Endpoint q (367 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (423 : Vertex))))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (424 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else decide (BallClauseLogic.Endpoint q (430 : Vertex)))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (431 : Vertex)) else (if i < 191 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else decide (BallClauseLogic.Endpoint q (434 : Vertex))))) else (if i < 195 then (if i < 193 then decide (BallClauseLogic.Endpoint q (435 : Vertex)) else (if i < 194 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (444 : Vertex)))) else (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (446 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (448 : Vertex)) else decide (BallClauseLogic.Endpoint q (449 : Vertex)))))) else (if i < 206 then (if i < 202 then (if i < 200 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else (if i < 201 then decide (BallClauseLogic.Endpoint q (455 : Vertex)) else decide (BallClauseLogic.Endpoint q (456 : Vertex)))) else (if i < 204 then (if i < 203 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else decide (BallClauseLogic.Endpoint q (462 : Vertex))) else (if i < 205 then decide (BallClauseLogic.Endpoint q (463 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))))) else (if i < 209 then (if i < 207 then decide (BallClauseLogic.Endpoint q (466 : Vertex)) else (if i < 208 then decide (BallClauseLogic.Endpoint q (467 : Vertex)) else decide (BallClauseLogic.Endpoint q (468 : Vertex)))) else (if i < 211 then (if i < 210 then decide (BallClauseLogic.Endpoint q (475 : Vertex)) else decide (BallClauseLogic.Endpoint q (476 : Vertex))) else (if i < 212 then decide (BallClauseLogic.Endpoint q (478 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
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
def count349 (b : Nat → Bool) : Nat := countLit b [179, 181]
def count351 (b : Nat → Bool) : Nat := countLit b [178, 179, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count357 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [178, 179, 181, 182, 183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]
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
def count417 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count419 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count421 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count423 (b : Nat → Bool) : Nat := countLit b [1, 3, 5]
def count426 (b : Nat → Bool) : Nat := countLit b [12, 13]
def count428 (b : Nat → Bool) : Nat := countLit b [6, 12, 13]
def count431 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 12, 13]
def count437 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count439 (b : Nat → Bool) : Nat := countLit b [16, 17, 19]
def count442 (b : Nat → Bool) : Nat := countLit b [21, 22]
def count444 (b : Nat → Bool) : Nat := countLit b [24, 26]
def count446 (b : Nat → Bool) : Nat := countLit b [21, 22, 24, 26]
def count450 (b : Nat → Bool) : Nat := countLit b [16, 17, 19, 21, 22, 24, 26]
def count457 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 12, 13, 16, 17, 19, 21, 22, 24, 26]
def count470 (b : Nat → Bool) : Nat := countLit b [31, 33]
def count472 (b : Nat → Bool) : Nat := countLit b [28, 31, 33]
def count475 (b : Nat → Bool) : Nat := countLit b [36, 38]
def count477 (b : Nat → Bool) : Nat := countLit b [34, 36, 38]
def count480 (b : Nat → Bool) : Nat := countLit b [28, 31, 33, 34, 36, 38]
def count486 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count488 (b : Nat → Bool) : Nat := countLit b [39, 43, 46]
def count491 (b : Nat → Bool) : Nat := countLit b [47, 50]
def count493 (b : Nat → Bool) : Nat := countLit b [51, 54]
def count495 (b : Nat → Bool) : Nat := countLit b [47, 50, 51, 54]
def count499 (b : Nat → Bool) : Nat := countLit b [39, 43, 46, 47, 50, 51, 54]
def count506 (b : Nat → Bool) : Nat := countLit b [28, 31, 33, 34, 36, 38, 39, 43, 46, 47, 50, 51, 54]
def count519 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 12, 13, 16, 17, 19, 21, 22, 24, 26, 28, 31, 33, 34, 36, 38, 39, 43, 46, 47, 50, 51, 54]
def count545 (b : Nat → Bool) : Nat := countLit b [58, 59]
def count547 (b : Nat → Bool) : Nat := countLit b [56, 58, 59]
def count550 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count552 (b : Nat → Bool) : Nat := countLit b [60, 64, 66]
def count555 (b : Nat → Bool) : Nat := countLit b [56, 58, 59, 60, 64, 66]
def count561 (b : Nat → Bool) : Nat := countLit b [69, 71]
def count563 (b : Nat → Bool) : Nat := countLit b [67, 69, 71]
def count566 (b : Nat → Bool) : Nat := countLit b [72, 74]
def count568 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count570 (b : Nat → Bool) : Nat := countLit b [72, 74, 77, 79]
def count574 (b : Nat → Bool) : Nat := countLit b [67, 69, 71, 72, 74, 77, 79]
def count581 (b : Nat → Bool) : Nat := countLit b [56, 58, 59, 60, 64, 66, 67, 69, 71, 72, 74, 77, 79]
def count594 (b : Nat → Bool) : Nat := countLit b [82, 84]
def count596 (b : Nat → Bool) : Nat := countLit b [80, 82, 84]
def count599 (b : Nat → Bool) : Nat := countLit b [86, 88]
def count601 (b : Nat → Bool) : Nat := countLit b [90, 92]
def count603 (b : Nat → Bool) : Nat := countLit b [86, 88, 90, 92]
def count607 (b : Nat → Bool) : Nat := countLit b [80, 82, 84, 86, 88, 90, 92]
def count614 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count616 (b : Nat → Bool) : Nat := countLit b [94, 95, 97]
def count619 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count621 (b : Nat → Bool) : Nat := countLit b [104, 106]
def count623 (b : Nat → Bool) : Nat := countLit b [99, 101, 104, 106]
def count627 (b : Nat → Bool) : Nat := countLit b [94, 95, 97, 99, 101, 104, 106]
def count634 (b : Nat → Bool) : Nat := countLit b [80, 82, 84, 86, 88, 90, 92, 94, 95, 97, 99, 101, 104, 106]
def count648 (b : Nat → Bool) : Nat := countLit b [56, 58, 59, 60, 64, 66, 67, 69, 71, 72, 74, 77, 79, 80, 82, 84, 86, 88, 90, 92, 94, 95, 97, 99, 101, 104, 106]
def count675 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 12, 13, 16, 17, 19, 21, 22, 24, 26, 28, 31, 33, 34, 36, 38, 39, 43, 46, 47, 50, 51, 54, 56, 58, 59, 60, 64, 66, 67, 69, 71, 72, 74, 77, 79, 80, 82, 84, 86, 88, 90, 92, 94, 95, 97, 99, 101, 104, 106]
def count717 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count719 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5]
def count722 (b : Nat → Bool) : Nat := countLit b [-12, -13]
def count724 (b : Nat → Bool) : Nat := countLit b [-6, -12, -13]
def count727 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -12, -13]
def count733 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count735 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19]
def count738 (b : Nat → Bool) : Nat := countLit b [-21, -22]
def count740 (b : Nat → Bool) : Nat := countLit b [-24, -26]
def count742 (b : Nat → Bool) : Nat := countLit b [-21, -22, -24, -26]
def count746 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19, -21, -22, -24, -26]
def count753 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -12, -13, -16, -17, -19, -21, -22, -24, -26]
def count766 (b : Nat → Bool) : Nat := countLit b [-31, -33]
def count768 (b : Nat → Bool) : Nat := countLit b [-28, -31, -33]
def count771 (b : Nat → Bool) : Nat := countLit b [-36, -38]
def count773 (b : Nat → Bool) : Nat := countLit b [-34, -36, -38]
def count776 (b : Nat → Bool) : Nat := countLit b [-28, -31, -33, -34, -36, -38]
def count782 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count784 (b : Nat → Bool) : Nat := countLit b [-39, -43, -46]
def count787 (b : Nat → Bool) : Nat := countLit b [-47, -50]
def count789 (b : Nat → Bool) : Nat := countLit b [-51, -54]
def count791 (b : Nat → Bool) : Nat := countLit b [-47, -50, -51, -54]
def count795 (b : Nat → Bool) : Nat := countLit b [-39, -43, -46, -47, -50, -51, -54]
def count802 (b : Nat → Bool) : Nat := countLit b [-28, -31, -33, -34, -36, -38, -39, -43, -46, -47, -50, -51, -54]
def count815 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -12, -13, -16, -17, -19, -21, -22, -24, -26, -28, -31, -33, -34, -36, -38, -39, -43, -46, -47, -50, -51, -54]
def count828 (b : Nat → Bool) : Nat := countLit b [-58, -59]
def count830 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59]
def count833 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count835 (b : Nat → Bool) : Nat := countLit b [-60, -64, -66]
def count838 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59, -60, -64, -66]
def count844 (b : Nat → Bool) : Nat := countLit b [-69, -71]
def count846 (b : Nat → Bool) : Nat := countLit b [-67, -69, -71]
def count849 (b : Nat → Bool) : Nat := countLit b [-72, -74]
def count851 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count853 (b : Nat → Bool) : Nat := countLit b [-72, -74, -77, -79]
def count857 (b : Nat → Bool) : Nat := countLit b [-67, -69, -71, -72, -74, -77, -79]
def count864 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59, -60, -64, -66, -67, -69, -71, -72, -74, -77, -79]
def count877 (b : Nat → Bool) : Nat := countLit b [-82, -84]
def count879 (b : Nat → Bool) : Nat := countLit b [-80, -82, -84]
def count882 (b : Nat → Bool) : Nat := countLit b [-86, -88]
def count884 (b : Nat → Bool) : Nat := countLit b [-90, -92]
def count886 (b : Nat → Bool) : Nat := countLit b [-86, -88, -90, -92]
def count890 (b : Nat → Bool) : Nat := countLit b [-80, -82, -84, -86, -88, -90, -92]
def count897 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count899 (b : Nat → Bool) : Nat := countLit b [-94, -95, -97]
def count902 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count904 (b : Nat → Bool) : Nat := countLit b [-104, -106]
def count906 (b : Nat → Bool) : Nat := countLit b [-99, -101, -104, -106]
def count910 (b : Nat → Bool) : Nat := countLit b [-94, -95, -97, -99, -101, -104, -106]
def count917 (b : Nat → Bool) : Nat := countLit b [-80, -82, -84, -86, -88, -90, -92, -94, -95, -97, -99, -101, -104, -106]
def count930 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59, -60, -64, -66, -67, -69, -71, -72, -74, -77, -79, -80, -82, -84, -86, -88, -90, -92, -94, -95, -97, -99, -101, -104, -106]
def count943 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -12, -13, -16, -17, -19, -21, -22, -24, -26, -28, -31, -33, -34, -36, -38, -39, -43, -46, -47, -50, -51, -54, -56, -58, -59, -60, -64, -66, -67, -69, -71, -72, -74, -77, -79, -80, -82, -84, -86, -88, -90, -92, -94, -95, -97, -99, -101, -104, -106]
def count956 (b : Nat → Bool) : Nat := countLit b [4, 7]
def count958 (b : Nat → Bool) : Nat := countLit b [2, 4, 7]
def count961 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count963 (b : Nat → Bool) : Nat := countLit b [8, 9, 10]
def count966 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 8, 9, 10]
def count972 (b : Nat → Bool) : Nat := countLit b [14, 15]
def count974 (b : Nat → Bool) : Nat := countLit b [11, 14, 15]
def count977 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count979 (b : Nat → Bool) : Nat := countLit b [23, 25]
def count981 (b : Nat → Bool) : Nat := countLit b [18, 20, 23, 25]
def count985 (b : Nat → Bool) : Nat := countLit b [11, 14, 15, 18, 20, 23, 25]
def count992 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 8, 9, 10, 11, 14, 15, 18, 20, 23, 25]
def count1005 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count1007 (b : Nat → Bool) : Nat := countLit b [27, 29, 30]
def count1010 (b : Nat → Bool) : Nat := countLit b [35, 37]
def count1012 (b : Nat → Bool) : Nat := countLit b [32, 35, 37]
def count1015 (b : Nat → Bool) : Nat := countLit b [27, 29, 30, 32, 35, 37]
def count1021 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count1023 (b : Nat → Bool) : Nat := countLit b [40, 41, 42]
def count1026 (b : Nat → Bool) : Nat := countLit b [44, 45]
def count1028 (b : Nat → Bool) : Nat := countLit b [48, 49]
def count1030 (b : Nat → Bool) : Nat := countLit b [44, 45, 48, 49]
def count1034 (b : Nat → Bool) : Nat := countLit b [40, 41, 42, 44, 45, 48, 49]
def count1041 (b : Nat → Bool) : Nat := countLit b [27, 29, 30, 32, 35, 37, 40, 41, 42, 44, 45, 48, 49]
def count1054 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 8, 9, 10, 11, 14, 15, 18, 20, 23, 25, 27, 29, 30, 32, 35, 37, 40, 41, 42, 44, 45, 48, 49]
def count1080 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count1082 (b : Nat → Bool) : Nat := countLit b [52, 53, 55]
def count1085 (b : Nat → Bool) : Nat := countLit b [61, 62]
def count1087 (b : Nat → Bool) : Nat := countLit b [57, 61, 62]
def count1090 (b : Nat → Bool) : Nat := countLit b [52, 53, 55, 57, 61, 62]
def count1096 (b : Nat → Bool) : Nat := countLit b [65, 68]
def count1098 (b : Nat → Bool) : Nat := countLit b [63, 65, 68]
def count1101 (b : Nat → Bool) : Nat := countLit b [70, 73]
def count1103 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count1105 (b : Nat → Bool) : Nat := countLit b [70, 73, 75, 76]
def count1109 (b : Nat → Bool) : Nat := countLit b [63, 65, 68, 70, 73, 75, 76]
def count1116 (b : Nat → Bool) : Nat := countLit b [52, 53, 55, 57, 61, 62, 63, 65, 68, 70, 73, 75, 76]
def count1129 (b : Nat → Bool) : Nat := countLit b [81, 83]
def count1131 (b : Nat → Bool) : Nat := countLit b [78, 81, 83]
def count1134 (b : Nat → Bool) : Nat := countLit b [85, 87]
def count1136 (b : Nat → Bool) : Nat := countLit b [89, 91]
def count1138 (b : Nat → Bool) : Nat := countLit b [85, 87, 89, 91]
def count1142 (b : Nat → Bool) : Nat := countLit b [78, 81, 83, 85, 87, 89, 91]
def count1149 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count1151 (b : Nat → Bool) : Nat := countLit b [93, 96, 98]
def count1154 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count1156 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count1158 (b : Nat → Bool) : Nat := countLit b [100, 102, 103, 105]
def count1162 (b : Nat → Bool) : Nat := countLit b [93, 96, 98, 100, 102, 103, 105]
def count1169 (b : Nat → Bool) : Nat := countLit b [78, 81, 83, 85, 87, 89, 91, 93, 96, 98, 100, 102, 103, 105]
def count1183 (b : Nat → Bool) : Nat := countLit b [52, 53, 55, 57, 61, 62, 63, 65, 68, 70, 73, 75, 76, 78, 81, 83, 85, 87, 89, 91, 93, 96, 98, 100, 102, 103, 105]
def count1210 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 8, 9, 10, 11, 14, 15, 18, 20, 23, 25, 27, 29, 30, 32, 35, 37, 40, 41, 42, 44, 45, 48, 49, 52, 53, 55, 57, 61, 62, 63, 65, 68, 70, 73, 75, 76, 78, 81, 83, 85, 87, 89, 91, 93, 96, 98, 100, 102, 103, 105]
def count1252 (b : Nat → Bool) : Nat := countLit b [-4, -7]
def count1254 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7]
def count1257 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count1259 (b : Nat → Bool) : Nat := countLit b [-8, -9, -10]
def count1262 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -8, -9, -10]
def count1268 (b : Nat → Bool) : Nat := countLit b [-14, -15]
def count1270 (b : Nat → Bool) : Nat := countLit b [-11, -14, -15]
def count1273 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count1275 (b : Nat → Bool) : Nat := countLit b [-23, -25]
def count1277 (b : Nat → Bool) : Nat := countLit b [-18, -20, -23, -25]
def count1281 (b : Nat → Bool) : Nat := countLit b [-11, -14, -15, -18, -20, -23, -25]
def count1288 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]
def count1301 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count1303 (b : Nat → Bool) : Nat := countLit b [-27, -29, -30]
def count1306 (b : Nat → Bool) : Nat := countLit b [-35, -37]
def count1308 (b : Nat → Bool) : Nat := countLit b [-32, -35, -37]
def count1311 (b : Nat → Bool) : Nat := countLit b [-27, -29, -30, -32, -35, -37]
def count1317 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count1319 (b : Nat → Bool) : Nat := countLit b [-40, -41, -42]
def count1322 (b : Nat → Bool) : Nat := countLit b [-44, -45]
def count1324 (b : Nat → Bool) : Nat := countLit b [-48, -49]
def count1326 (b : Nat → Bool) : Nat := countLit b [-44, -45, -48, -49]
def count1330 (b : Nat → Bool) : Nat := countLit b [-40, -41, -42, -44, -45, -48, -49]
def count1337 (b : Nat → Bool) : Nat := countLit b [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]
def count1350 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]
def count1363 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count1365 (b : Nat → Bool) : Nat := countLit b [-52, -53, -55]
def count1368 (b : Nat → Bool) : Nat := countLit b [-61, -62]
def count1370 (b : Nat → Bool) : Nat := countLit b [-57, -61, -62]
def count1373 (b : Nat → Bool) : Nat := countLit b [-52, -53, -55, -57, -61, -62]
def count1379 (b : Nat → Bool) : Nat := countLit b [-65, -68]
def count1381 (b : Nat → Bool) : Nat := countLit b [-63, -65, -68]
def count1384 (b : Nat → Bool) : Nat := countLit b [-70, -73]
def count1386 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count1388 (b : Nat → Bool) : Nat := countLit b [-70, -73, -75, -76]
def count1392 (b : Nat → Bool) : Nat := countLit b [-63, -65, -68, -70, -73, -75, -76]
def count1399 (b : Nat → Bool) : Nat := countLit b [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]
def count1412 (b : Nat → Bool) : Nat := countLit b [-81, -83]
def count1414 (b : Nat → Bool) : Nat := countLit b [-78, -81, -83]
def count1417 (b : Nat → Bool) : Nat := countLit b [-85, -87]
def count1419 (b : Nat → Bool) : Nat := countLit b [-89, -91]
def count1421 (b : Nat → Bool) : Nat := countLit b [-85, -87, -89, -91]
def count1425 (b : Nat → Bool) : Nat := countLit b [-78, -81, -83, -85, -87, -89, -91]
def count1432 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count1434 (b : Nat → Bool) : Nat := countLit b [-93, -96, -98]
def count1437 (b : Nat → Bool) : Nat := countLit b [-100, -102]
def count1439 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count1441 (b : Nat → Bool) : Nat := countLit b [-100, -102, -103, -105]
def count1445 (b : Nat → Bool) : Nat := countLit b [-93, -96, -98, -100, -102, -103, -105]
def count1452 (b : Nat → Bool) : Nat := countLit b [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]
def count1465 (b : Nat → Bool) : Nat := countLit b [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]
def count1478 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25, -27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49, -52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76, -78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 745 then (if i < 372 then (if i < 186 then (if i < 93 then (if i < 46 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 17 then (if i < 14 then (if i < 12 then b 11 else (if i < 13 then b 12 else b 13)) else (if i < 15 then b 14 else (if i < 16 then b 15 else b 16))) else (if i < 20 then (if i < 18 then b 17 else (if i < 19 then b 18 else b 19)) else (if i < 21 then b 20 else (if i < 22 then b 21 else b 22))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then b 23 else b 24) else (if i < 26 then b 25 else (if i < 27 then b 26 else b 27))) else (if i < 31 then (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)) else (if i < 32 then b 31 else (if i < 33 then b 32 else b 33)))) else (if i < 40 then (if i < 37 then (if i < 35 then b 34 else (if i < 36 then b 35 else b 36)) else (if i < 38 then b 37 else (if i < 39 then b 38 else b 39))) else (if i < 43 then (if i < 41 then b 40 else (if i < 42 then b 41 else b 42)) else (if i < 44 then b 43 else (if i < 45 then b 44 else b 45)))))) else (if i < 69 then (if i < 57 then (if i < 51 then (if i < 48 then (if i < 47 then b 46 else b 47) else (if i < 49 then b 48 else (if i < 50 then b 49 else b 50))) else (if i < 54 then (if i < 52 then b 51 else (if i < 53 then b 52 else b 53)) else (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)))) else (if i < 63 then (if i < 60 then (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)) else (if i < 61 then b 60 else (if i < 62 then b 61 else b 62))) else (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 67 then b 66 else (if i < 68 then b 67 else b 68))))) else (if i < 81 then (if i < 75 then (if i < 72 then (if i < 70 then b 69 else (if i < 71 then b 70 else b 71)) else (if i < 73 then b 72 else (if i < 74 then b 73 else b 74))) else (if i < 78 then (if i < 76 then b 75 else (if i < 77 then b 76 else b 77)) else (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)))) else (if i < 87 then (if i < 84 then (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)) else (if i < 85 then b 84 else (if i < 86 then b 85 else b 86))) else (if i < 90 then (if i < 88 then b 87 else (if i < 89 then b 88 else b 89)) else (if i < 91 then b 90 else (if i < 92 then b 91 else b 92))))))) else (if i < 139 then (if i < 116 then (if i < 104 then (if i < 98 then (if i < 95 then (if i < 94 then b 93 else b 94) else (if i < 96 then b 95 else (if i < 97 then b 96 else b 97))) else (if i < 101 then (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)) else (if i < 102 then b 101 else (if i < 103 then b 102 else b 103)))) else (if i < 110 then (if i < 107 then (if i < 105 then b 104 else (if i < 106 then b 105 else b 106)) else (if i < 108 then b 107 else (if i < 109 then b 108 else b 109))) else (if i < 113 then (if i < 111 then b 110 else (if i < 112 then b 111 else b 112)) else (if i < 114 then b 113 else (if i < 115 then b 114 else b 115))))) else (if i < 127 then (if i < 121 then (if i < 118 then (if i < 117 then b 116 else b 117) else (if i < 119 then b 118 else (if i < 120 then b 119 else b 120))) else (if i < 124 then (if i < 122 then b 121 else (if i < 123 then b 122 else b 123)) else (if i < 125 then b 124 else (if i < 126 then b 125 else b 126)))) else (if i < 133 then (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 131 then b 130 else (if i < 132 then b 131 else b 132))) else (if i < 136 then (if i < 134 then b 133 else (if i < 135 then b 134 else b 135)) else (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)))))) else (if i < 162 then (if i < 150 then (if i < 144 then (if i < 141 then (if i < 140 then b 139 else b 140) else (if i < 142 then b 141 else (if i < 143 then b 142 else b 143))) else (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)))) else (if i < 156 then (if i < 153 then (if i < 151 then b 150 else (if i < 152 then b 151 else b 152)) else (if i < 154 then b 153 else (if i < 155 then b 154 else b 155))) else (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))))) else (if i < 174 then (if i < 168 then (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 166 then b 165 else (if i < 167 then b 166 else b 167))) else (if i < 171 then (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)) else (if i < 172 then b 171 else (if i < 173 then b 172 else b 173)))) else (if i < 180 then (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179))) else (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185)))))))) else (if i < 279 then (if i < 232 then (if i < 209 then (if i < 197 then (if i < 191 then (if i < 188 then (if i < 187 then b 186 else b 187) else (if i < 189 then b 188 else (if i < 190 then b 189 else b 190))) else (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 195 then b 194 else (if i < 196 then b 195 else b 196)))) else (if i < 203 then (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 201 then b 200 else (if i < 202 then b 201 else b 202))) else (if i < 206 then (if i < 204 then b 203 else (if i < 205 then b 204 else b 205)) else (if i < 207 then b 206 else (if i < 208 then b 207 else b 208))))) else (if i < 220 then (if i < 214 then (if i < 211 then (if i < 210 then b 209 else b 210) else (if i < 212 then b 211 else (if i < 213 then b 212 else decide (1 ≤ count213 b)))) else (if i < 217 then (if i < 215 then decide (2 ≤ count213 b) else (if i < 216 then decide (1 ≤ count215 b) else decide (2 ≤ count215 b))) else (if i < 218 then decide (1 ≤ count217 b) else (if i < 219 then decide (2 ≤ count217 b) else decide (1 ≤ count219 b))))) else (if i < 226 then (if i < 223 then (if i < 221 then decide (2 ≤ count219 b) else (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b))) else (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b)))) else (if i < 229 then (if i < 227 then decide (2 ≤ count225 b) else (if i < 228 then decide (1 ≤ count227 b) else decide (2 ≤ count227 b))) else (if i < 230 then decide (1 ≤ count229 b) else (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b))))))) else (if i < 255 then (if i < 243 then (if i < 237 then (if i < 234 then (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b)) else (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b)))) else (if i < 240 then (if i < 238 then decide (1 ≤ count237 b) else (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b))) else (if i < 241 then decide (2 ≤ count239 b) else (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b))))) else (if i < 249 then (if i < 246 then (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b))) else (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b)))) else (if i < 252 then (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))) else (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b)))))) else (if i < 267 then (if i < 261 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)))) else (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))))) else (if i < 273 then (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)))) else (if i < 276 then (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)))))))) else (if i < 325 then (if i < 302 then (if i < 290 then (if i < 284 then (if i < 281 then (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)) else (if i < 282 then decide (1 ≤ count281 b) else (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b)))) else (if i < 287 then (if i < 285 then decide (2 ≤ count283 b) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b))) else (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))))) else (if i < 296 then (if i < 293 then (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))) else (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)))) else (if i < 299 then (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b))) else (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))))) else (if i < 313 then (if i < 307 then (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)))) else (if i < 310 then (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b))) else (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))))) else (if i < 319 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)))) else (if i < 322 then (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))) else (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))))))) else (if i < 348 then (if i < 336 then (if i < 330 then (if i < 327 then (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)) else (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)))) else (if i < 333 then (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b))) else (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))))) else (if i < 342 then (if i < 339 then (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))) else (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)))) else (if i < 345 then (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b))) else (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)))))) else (if i < 360 then (if i < 354 then (if i < 351 then (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b))) else (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))) else (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))))) else (if i < 366 then (if i < 363 then (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b))) else (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))) else (if i < 369 then (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)))))))))) else (if i < 558 then (if i < 465 then (if i < 418 then (if i < 395 then (if i < 383 then (if i < 377 then (if i < 374 then (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)))) else (if i < 380 then (if i < 378 then decide (1 ≤ count377 b) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b))) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b))))) else (if i < 389 then (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 392 then (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))) else (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)))))) else (if i < 406 then (if i < 400 then (if i < 397 then (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)) else (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))) else (if i < 403 then (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))) else (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))))) else (if i < 412 then (if i < 409 then (if i < 407 then decide (2 ≤ count405 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))) else (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b)))) else (if i < 415 then (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))) else (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))))))) else (if i < 441 then (if i < 429 then (if i < 423 then (if i < 420 then (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)) else (if i < 421 then decide (2 ≤ count419 b) else (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b)))) else (if i < 426 then (if i < 424 then decide (1 ≤ count423 b) else (if i < 425 then decide (2 ≤ count423 b) else decide (3 ≤ count423 b))) else (if i < 427 then decide (1 ≤ count426 b) else (if i < 428 then decide (2 ≤ count426 b) else decide (1 ≤ count428 b))))) else (if i < 435 then (if i < 432 then (if i < 430 then decide (2 ≤ count428 b) else (if i < 431 then decide (3 ≤ count428 b) else decide (1 ≤ count431 b))) else (if i < 433 then decide (2 ≤ count431 b) else (if i < 434 then decide (3 ≤ count431 b) else decide (4 ≤ count431 b)))) else (if i < 438 then (if i < 436 then decide (5 ≤ count431 b) else (if i < 437 then decide (6 ≤ count431 b) else decide (1 ≤ count437 b))) else (if i < 439 then decide (2 ≤ count437 b) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b)))))) else (if i < 453 then (if i < 447 then (if i < 444 then (if i < 442 then decide (3 ≤ count439 b) else (if i < 443 then decide (1 ≤ count442 b) else decide (2 ≤ count442 b))) else (if i < 445 then decide (1 ≤ count444 b) else (if i < 446 then decide (2 ≤ count444 b) else decide (1 ≤ count446 b)))) else (if i < 450 then (if i < 448 then decide (2 ≤ count446 b) else (if i < 449 then decide (3 ≤ count446 b) else decide (4 ≤ count446 b))) else (if i < 451 then decide (1 ≤ count450 b) else (if i < 452 then decide (2 ≤ count450 b) else decide (3 ≤ count450 b))))) else (if i < 459 then (if i < 456 then (if i < 454 then decide (4 ≤ count450 b) else (if i < 455 then decide (5 ≤ count450 b) else decide (6 ≤ count450 b))) else (if i < 457 then decide (7 ≤ count450 b) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)))) else (if i < 462 then (if i < 460 then decide (3 ≤ count457 b) else (if i < 461 then decide (4 ≤ count457 b) else decide (5 ≤ count457 b))) else (if i < 463 then decide (6 ≤ count457 b) else (if i < 464 then decide (7 ≤ count457 b) else decide (8 ≤ count457 b)))))))) else (if i < 511 then (if i < 488 then (if i < 476 then (if i < 470 then (if i < 467 then (if i < 466 then decide (9 ≤ count457 b) else decide (10 ≤ count457 b)) else (if i < 468 then decide (11 ≤ count457 b) else (if i < 469 then decide (12 ≤ count457 b) else decide (13 ≤ count457 b)))) else (if i < 473 then (if i < 471 then decide (1 ≤ count470 b) else (if i < 472 then decide (2 ≤ count470 b) else decide (1 ≤ count472 b))) else (if i < 474 then decide (2 ≤ count472 b) else (if i < 475 then decide (3 ≤ count472 b) else decide (1 ≤ count475 b))))) else (if i < 482 then (if i < 479 then (if i < 477 then decide (2 ≤ count475 b) else (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b))) else (if i < 480 then decide (3 ≤ count477 b) else (if i < 481 then decide (1 ≤ count480 b) else decide (2 ≤ count480 b)))) else (if i < 485 then (if i < 483 then decide (3 ≤ count480 b) else (if i < 484 then decide (4 ≤ count480 b) else decide (5 ≤ count480 b))) else (if i < 486 then decide (6 ≤ count480 b) else (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b)))))) else (if i < 499 then (if i < 493 then (if i < 490 then (if i < 489 then decide (1 ≤ count488 b) else decide (2 ≤ count488 b)) else (if i < 491 then decide (3 ≤ count488 b) else (if i < 492 then decide (1 ≤ count491 b) else decide (2 ≤ count491 b)))) else (if i < 496 then (if i < 494 then decide (1 ≤ count493 b) else (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b))) else (if i < 497 then decide (2 ≤ count495 b) else (if i < 498 then decide (3 ≤ count495 b) else decide (4 ≤ count495 b))))) else (if i < 505 then (if i < 502 then (if i < 500 then decide (1 ≤ count499 b) else (if i < 501 then decide (2 ≤ count499 b) else decide (3 ≤ count499 b))) else (if i < 503 then decide (4 ≤ count499 b) else (if i < 504 then decide (5 ≤ count499 b) else decide (6 ≤ count499 b)))) else (if i < 508 then (if i < 506 then decide (7 ≤ count499 b) else (if i < 507 then decide (1 ≤ count506 b) else decide (2 ≤ count506 b))) else (if i < 509 then decide (3 ≤ count506 b) else (if i < 510 then decide (4 ≤ count506 b) else decide (5 ≤ count506 b))))))) else (if i < 534 then (if i < 522 then (if i < 516 then (if i < 513 then (if i < 512 then decide (6 ≤ count506 b) else decide (7 ≤ count506 b)) else (if i < 514 then decide (8 ≤ count506 b) else (if i < 515 then decide (9 ≤ count506 b) else decide (10 ≤ count506 b)))) else (if i < 519 then (if i < 517 then decide (11 ≤ count506 b) else (if i < 518 then decide (12 ≤ count506 b) else decide (13 ≤ count506 b))) else (if i < 520 then decide (1 ≤ count519 b) else (if i < 521 then decide (2 ≤ count519 b) else decide (3 ≤ count519 b))))) else (if i < 528 then (if i < 525 then (if i < 523 then decide (4 ≤ count519 b) else (if i < 524 then decide (5 ≤ count519 b) else decide (6 ≤ count519 b))) else (if i < 526 then decide (7 ≤ count519 b) else (if i < 527 then decide (8 ≤ count519 b) else decide (9 ≤ count519 b)))) else (if i < 531 then (if i < 529 then decide (10 ≤ count519 b) else (if i < 530 then decide (11 ≤ count519 b) else decide (12 ≤ count519 b))) else (if i < 532 then decide (13 ≤ count519 b) else (if i < 533 then decide (14 ≤ count519 b) else decide (15 ≤ count519 b)))))) else (if i < 546 then (if i < 540 then (if i < 537 then (if i < 535 then decide (16 ≤ count519 b) else (if i < 536 then decide (17 ≤ count519 b) else decide (18 ≤ count519 b))) else (if i < 538 then decide (19 ≤ count519 b) else (if i < 539 then decide (20 ≤ count519 b) else decide (21 ≤ count519 b)))) else (if i < 543 then (if i < 541 then decide (22 ≤ count519 b) else (if i < 542 then decide (23 ≤ count519 b) else decide (24 ≤ count519 b))) else (if i < 544 then decide (25 ≤ count519 b) else (if i < 545 then decide (26 ≤ count519 b) else decide (1 ≤ count545 b))))) else (if i < 552 then (if i < 549 then (if i < 547 then decide (2 ≤ count545 b) else (if i < 548 then decide (1 ≤ count547 b) else decide (2 ≤ count547 b))) else (if i < 550 then decide (3 ≤ count547 b) else (if i < 551 then decide (1 ≤ count550 b) else decide (2 ≤ count550 b)))) else (if i < 555 then (if i < 553 then decide (1 ≤ count552 b) else (if i < 554 then decide (2 ≤ count552 b) else decide (3 ≤ count552 b))) else (if i < 556 then decide (1 ≤ count555 b) else (if i < 557 then decide (2 ≤ count555 b) else decide (3 ≤ count555 b))))))))) else (if i < 651 then (if i < 604 then (if i < 581 then (if i < 569 then (if i < 563 then (if i < 560 then (if i < 559 then decide (4 ≤ count555 b) else decide (5 ≤ count555 b)) else (if i < 561 then decide (6 ≤ count555 b) else (if i < 562 then decide (1 ≤ count561 b) else decide (2 ≤ count561 b)))) else (if i < 566 then (if i < 564 then decide (1 ≤ count563 b) else (if i < 565 then decide (2 ≤ count563 b) else decide (3 ≤ count563 b))) else (if i < 567 then decide (1 ≤ count566 b) else (if i < 568 then decide (2 ≤ count566 b) else decide (1 ≤ count568 b))))) else (if i < 575 then (if i < 572 then (if i < 570 then decide (2 ≤ count568 b) else (if i < 571 then decide (1 ≤ count570 b) else decide (2 ≤ count570 b))) else (if i < 573 then decide (3 ≤ count570 b) else (if i < 574 then decide (4 ≤ count570 b) else decide (1 ≤ count574 b)))) else (if i < 578 then (if i < 576 then decide (2 ≤ count574 b) else (if i < 577 then decide (3 ≤ count574 b) else decide (4 ≤ count574 b))) else (if i < 579 then decide (5 ≤ count574 b) else (if i < 580 then decide (6 ≤ count574 b) else decide (7 ≤ count574 b)))))) else (if i < 592 then (if i < 586 then (if i < 583 then (if i < 582 then decide (1 ≤ count581 b) else decide (2 ≤ count581 b)) else (if i < 584 then decide (3 ≤ count581 b) else (if i < 585 then decide (4 ≤ count581 b) else decide (5 ≤ count581 b)))) else (if i < 589 then (if i < 587 then decide (6 ≤ count581 b) else (if i < 588 then decide (7 ≤ count581 b) else decide (8 ≤ count581 b))) else (if i < 590 then decide (9 ≤ count581 b) else (if i < 591 then decide (10 ≤ count581 b) else decide (11 ≤ count581 b))))) else (if i < 598 then (if i < 595 then (if i < 593 then decide (12 ≤ count581 b) else (if i < 594 then decide (13 ≤ count581 b) else decide (1 ≤ count594 b))) else (if i < 596 then decide (2 ≤ count594 b) else (if i < 597 then decide (1 ≤ count596 b) else decide (2 ≤ count596 b)))) else (if i < 601 then (if i < 599 then decide (3 ≤ count596 b) else (if i < 600 then decide (1 ≤ count599 b) else decide (2 ≤ count599 b))) else (if i < 602 then decide (1 ≤ count601 b) else (if i < 603 then decide (2 ≤ count601 b) else decide (1 ≤ count603 b))))))) else (if i < 627 then (if i < 615 then (if i < 609 then (if i < 606 then (if i < 605 then decide (2 ≤ count603 b) else decide (3 ≤ count603 b)) else (if i < 607 then decide (4 ≤ count603 b) else (if i < 608 then decide (1 ≤ count607 b) else decide (2 ≤ count607 b)))) else (if i < 612 then (if i < 610 then decide (3 ≤ count607 b) else (if i < 611 then decide (4 ≤ count607 b) else decide (5 ≤ count607 b))) else (if i < 613 then decide (6 ≤ count607 b) else (if i < 614 then decide (7 ≤ count607 b) else decide (1 ≤ count614 b))))) else (if i < 621 then (if i < 618 then (if i < 616 then decide (2 ≤ count614 b) else (if i < 617 then decide (1 ≤ count616 b) else decide (2 ≤ count616 b))) else (if i < 619 then decide (3 ≤ count616 b) else (if i < 620 then decide (1 ≤ count619 b) else decide (2 ≤ count619 b)))) else (if i < 624 then (if i < 622 then decide (1 ≤ count621 b) else (if i < 623 then decide (2 ≤ count621 b) else decide (1 ≤ count623 b))) else (if i < 625 then decide (2 ≤ count623 b) else (if i < 626 then decide (3 ≤ count623 b) else decide (4 ≤ count623 b)))))) else (if i < 639 then (if i < 633 then (if i < 630 then (if i < 628 then decide (1 ≤ count627 b) else (if i < 629 then decide (2 ≤ count627 b) else decide (3 ≤ count627 b))) else (if i < 631 then decide (4 ≤ count627 b) else (if i < 632 then decide (5 ≤ count627 b) else decide (6 ≤ count627 b)))) else (if i < 636 then (if i < 634 then decide (7 ≤ count627 b) else (if i < 635 then decide (1 ≤ count634 b) else decide (2 ≤ count634 b))) else (if i < 637 then decide (3 ≤ count634 b) else (if i < 638 then decide (4 ≤ count634 b) else decide (5 ≤ count634 b))))) else (if i < 645 then (if i < 642 then (if i < 640 then decide (6 ≤ count634 b) else (if i < 641 then decide (7 ≤ count634 b) else decide (8 ≤ count634 b))) else (if i < 643 then decide (9 ≤ count634 b) else (if i < 644 then decide (10 ≤ count634 b) else decide (11 ≤ count634 b)))) else (if i < 648 then (if i < 646 then decide (12 ≤ count634 b) else (if i < 647 then decide (13 ≤ count634 b) else decide (14 ≤ count634 b))) else (if i < 649 then decide (1 ≤ count648 b) else (if i < 650 then decide (2 ≤ count648 b) else decide (3 ≤ count648 b)))))))) else (if i < 698 then (if i < 674 then (if i < 662 then (if i < 656 then (if i < 653 then (if i < 652 then decide (4 ≤ count648 b) else decide (5 ≤ count648 b)) else (if i < 654 then decide (6 ≤ count648 b) else (if i < 655 then decide (7 ≤ count648 b) else decide (8 ≤ count648 b)))) else (if i < 659 then (if i < 657 then decide (9 ≤ count648 b) else (if i < 658 then decide (10 ≤ count648 b) else decide (11 ≤ count648 b))) else (if i < 660 then decide (12 ≤ count648 b) else (if i < 661 then decide (13 ≤ count648 b) else decide (14 ≤ count648 b))))) else (if i < 668 then (if i < 665 then (if i < 663 then decide (15 ≤ count648 b) else (if i < 664 then decide (16 ≤ count648 b) else decide (17 ≤ count648 b))) else (if i < 666 then decide (18 ≤ count648 b) else (if i < 667 then decide (19 ≤ count648 b) else decide (20 ≤ count648 b)))) else (if i < 671 then (if i < 669 then decide (21 ≤ count648 b) else (if i < 670 then decide (22 ≤ count648 b) else decide (23 ≤ count648 b))) else (if i < 672 then decide (24 ≤ count648 b) else (if i < 673 then decide (25 ≤ count648 b) else decide (26 ≤ count648 b)))))) else (if i < 686 then (if i < 680 then (if i < 677 then (if i < 675 then decide (27 ≤ count648 b) else (if i < 676 then decide (1 ≤ count675 b) else decide (2 ≤ count675 b))) else (if i < 678 then decide (3 ≤ count675 b) else (if i < 679 then decide (4 ≤ count675 b) else decide (5 ≤ count675 b)))) else (if i < 683 then (if i < 681 then decide (6 ≤ count675 b) else (if i < 682 then decide (7 ≤ count675 b) else decide (8 ≤ count675 b))) else (if i < 684 then decide (9 ≤ count675 b) else (if i < 685 then decide (10 ≤ count675 b) else decide (11 ≤ count675 b))))) else (if i < 692 then (if i < 689 then (if i < 687 then decide (12 ≤ count675 b) else (if i < 688 then decide (13 ≤ count675 b) else decide (14 ≤ count675 b))) else (if i < 690 then decide (15 ≤ count675 b) else (if i < 691 then decide (16 ≤ count675 b) else decide (17 ≤ count675 b)))) else (if i < 695 then (if i < 693 then decide (18 ≤ count675 b) else (if i < 694 then decide (19 ≤ count675 b) else decide (20 ≤ count675 b))) else (if i < 696 then decide (21 ≤ count675 b) else (if i < 697 then decide (22 ≤ count675 b) else decide (23 ≤ count675 b))))))) else (if i < 721 then (if i < 709 then (if i < 703 then (if i < 700 then (if i < 699 then decide (24 ≤ count675 b) else decide (25 ≤ count675 b)) else (if i < 701 then decide (26 ≤ count675 b) else (if i < 702 then decide (27 ≤ count675 b) else decide (28 ≤ count675 b)))) else (if i < 706 then (if i < 704 then decide (29 ≤ count675 b) else (if i < 705 then decide (30 ≤ count675 b) else decide (31 ≤ count675 b))) else (if i < 707 then decide (32 ≤ count675 b) else (if i < 708 then decide (33 ≤ count675 b) else decide (34 ≤ count675 b))))) else (if i < 715 then (if i < 712 then (if i < 710 then decide (35 ≤ count675 b) else (if i < 711 then decide (36 ≤ count675 b) else decide (37 ≤ count675 b))) else (if i < 713 then decide (38 ≤ count675 b) else (if i < 714 then decide (39 ≤ count675 b) else decide (40 ≤ count675 b)))) else (if i < 718 then (if i < 716 then decide (41 ≤ count675 b) else (if i < 717 then decide (42 ≤ count675 b) else decide (1 ≤ count717 b))) else (if i < 719 then decide (2 ≤ count717 b) else (if i < 720 then decide (1 ≤ count719 b) else decide (2 ≤ count719 b)))))) else (if i < 733 then (if i < 727 then (if i < 724 then (if i < 722 then decide (3 ≤ count719 b) else (if i < 723 then decide (1 ≤ count722 b) else decide (2 ≤ count722 b))) else (if i < 725 then decide (1 ≤ count724 b) else (if i < 726 then decide (2 ≤ count724 b) else decide (3 ≤ count724 b)))) else (if i < 730 then (if i < 728 then decide (1 ≤ count727 b) else (if i < 729 then decide (2 ≤ count727 b) else decide (3 ≤ count727 b))) else (if i < 731 then decide (4 ≤ count727 b) else (if i < 732 then decide (5 ≤ count727 b) else decide (6 ≤ count727 b))))) else (if i < 739 then (if i < 736 then (if i < 734 then decide (1 ≤ count733 b) else (if i < 735 then decide (2 ≤ count733 b) else decide (1 ≤ count735 b))) else (if i < 737 then decide (2 ≤ count735 b) else (if i < 738 then decide (3 ≤ count735 b) else decide (1 ≤ count738 b)))) else (if i < 742 then (if i < 740 then decide (2 ≤ count738 b) else (if i < 741 then decide (1 ≤ count740 b) else decide (2 ≤ count740 b))) else (if i < 743 then decide (1 ≤ count742 b) else (if i < 744 then decide (2 ≤ count742 b) else decide (3 ≤ count742 b))))))))))) else (if i < 1118 then (if i < 931 then (if i < 838 then (if i < 791 then (if i < 768 then (if i < 756 then (if i < 750 then (if i < 747 then (if i < 746 then decide (4 ≤ count742 b) else decide (1 ≤ count746 b)) else (if i < 748 then decide (2 ≤ count746 b) else (if i < 749 then decide (3 ≤ count746 b) else decide (4 ≤ count746 b)))) else (if i < 753 then (if i < 751 then decide (5 ≤ count746 b) else (if i < 752 then decide (6 ≤ count746 b) else decide (7 ≤ count746 b))) else (if i < 754 then decide (1 ≤ count753 b) else (if i < 755 then decide (2 ≤ count753 b) else decide (3 ≤ count753 b))))) else (if i < 762 then (if i < 759 then (if i < 757 then decide (4 ≤ count753 b) else (if i < 758 then decide (5 ≤ count753 b) else decide (6 ≤ count753 b))) else (if i < 760 then decide (7 ≤ count753 b) else (if i < 761 then decide (8 ≤ count753 b) else decide (9 ≤ count753 b)))) else (if i < 765 then (if i < 763 then decide (10 ≤ count753 b) else (if i < 764 then decide (11 ≤ count753 b) else decide (12 ≤ count753 b))) else (if i < 766 then decide (13 ≤ count753 b) else (if i < 767 then decide (1 ≤ count766 b) else decide (2 ≤ count766 b)))))) else (if i < 779 then (if i < 773 then (if i < 770 then (if i < 769 then decide (1 ≤ count768 b) else decide (2 ≤ count768 b)) else (if i < 771 then decide (3 ≤ count768 b) else (if i < 772 then decide (1 ≤ count771 b) else decide (2 ≤ count771 b)))) else (if i < 776 then (if i < 774 then decide (1 ≤ count773 b) else (if i < 775 then decide (2 ≤ count773 b) else decide (3 ≤ count773 b))) else (if i < 777 then decide (1 ≤ count776 b) else (if i < 778 then decide (2 ≤ count776 b) else decide (3 ≤ count776 b))))) else (if i < 785 then (if i < 782 then (if i < 780 then decide (4 ≤ count776 b) else (if i < 781 then decide (5 ≤ count776 b) else decide (6 ≤ count776 b))) else (if i < 783 then decide (1 ≤ count782 b) else (if i < 784 then decide (2 ≤ count782 b) else decide (1 ≤ count784 b)))) else (if i < 788 then (if i < 786 then decide (2 ≤ count784 b) else (if i < 787 then decide (3 ≤ count784 b) else decide (1 ≤ count787 b))) else (if i < 789 then decide (2 ≤ count787 b) else (if i < 790 then decide (1 ≤ count789 b) else decide (2 ≤ count789 b))))))) else (if i < 814 then (if i < 802 then (if i < 796 then (if i < 793 then (if i < 792 then decide (1 ≤ count791 b) else decide (2 ≤ count791 b)) else (if i < 794 then decide (3 ≤ count791 b) else (if i < 795 then decide (4 ≤ count791 b) else decide (1 ≤ count795 b)))) else (if i < 799 then (if i < 797 then decide (2 ≤ count795 b) else (if i < 798 then decide (3 ≤ count795 b) else decide (4 ≤ count795 b))) else (if i < 800 then decide (5 ≤ count795 b) else (if i < 801 then decide (6 ≤ count795 b) else decide (7 ≤ count795 b))))) else (if i < 808 then (if i < 805 then (if i < 803 then decide (1 ≤ count802 b) else (if i < 804 then decide (2 ≤ count802 b) else decide (3 ≤ count802 b))) else (if i < 806 then decide (4 ≤ count802 b) else (if i < 807 then decide (5 ≤ count802 b) else decide (6 ≤ count802 b)))) else (if i < 811 then (if i < 809 then decide (7 ≤ count802 b) else (if i < 810 then decide (8 ≤ count802 b) else decide (9 ≤ count802 b))) else (if i < 812 then decide (10 ≤ count802 b) else (if i < 813 then decide (11 ≤ count802 b) else decide (12 ≤ count802 b)))))) else (if i < 826 then (if i < 820 then (if i < 817 then (if i < 815 then decide (13 ≤ count802 b) else (if i < 816 then decide (1 ≤ count815 b) else decide (2 ≤ count815 b))) else (if i < 818 then decide (3 ≤ count815 b) else (if i < 819 then decide (4 ≤ count815 b) else decide (5 ≤ count815 b)))) else (if i < 823 then (if i < 821 then decide (6 ≤ count815 b) else (if i < 822 then decide (7 ≤ count815 b) else decide (8 ≤ count815 b))) else (if i < 824 then decide (9 ≤ count815 b) else (if i < 825 then decide (10 ≤ count815 b) else decide (11 ≤ count815 b))))) else (if i < 832 then (if i < 829 then (if i < 827 then decide (12 ≤ count815 b) else (if i < 828 then decide (13 ≤ count815 b) else decide (1 ≤ count828 b))) else (if i < 830 then decide (2 ≤ count828 b) else (if i < 831 then decide (1 ≤ count830 b) else decide (2 ≤ count830 b)))) else (if i < 835 then (if i < 833 then decide (3 ≤ count830 b) else (if i < 834 then decide (1 ≤ count833 b) else decide (2 ≤ count833 b))) else (if i < 836 then decide (1 ≤ count835 b) else (if i < 837 then decide (2 ≤ count835 b) else decide (3 ≤ count835 b)))))))) else (if i < 884 then (if i < 861 then (if i < 849 then (if i < 843 then (if i < 840 then (if i < 839 then decide (1 ≤ count838 b) else decide (2 ≤ count838 b)) else (if i < 841 then decide (3 ≤ count838 b) else (if i < 842 then decide (4 ≤ count838 b) else decide (5 ≤ count838 b)))) else (if i < 846 then (if i < 844 then decide (6 ≤ count838 b) else (if i < 845 then decide (1 ≤ count844 b) else decide (2 ≤ count844 b))) else (if i < 847 then decide (1 ≤ count846 b) else (if i < 848 then decide (2 ≤ count846 b) else decide (3 ≤ count846 b))))) else (if i < 855 then (if i < 852 then (if i < 850 then decide (1 ≤ count849 b) else (if i < 851 then decide (2 ≤ count849 b) else decide (1 ≤ count851 b))) else (if i < 853 then decide (2 ≤ count851 b) else (if i < 854 then decide (1 ≤ count853 b) else decide (2 ≤ count853 b)))) else (if i < 858 then (if i < 856 then decide (3 ≤ count853 b) else (if i < 857 then decide (4 ≤ count853 b) else decide (1 ≤ count857 b))) else (if i < 859 then decide (2 ≤ count857 b) else (if i < 860 then decide (3 ≤ count857 b) else decide (4 ≤ count857 b)))))) else (if i < 872 then (if i < 866 then (if i < 863 then (if i < 862 then decide (5 ≤ count857 b) else decide (6 ≤ count857 b)) else (if i < 864 then decide (7 ≤ count857 b) else (if i < 865 then decide (1 ≤ count864 b) else decide (2 ≤ count864 b)))) else (if i < 869 then (if i < 867 then decide (3 ≤ count864 b) else (if i < 868 then decide (4 ≤ count864 b) else decide (5 ≤ count864 b))) else (if i < 870 then decide (6 ≤ count864 b) else (if i < 871 then decide (7 ≤ count864 b) else decide (8 ≤ count864 b))))) else (if i < 878 then (if i < 875 then (if i < 873 then decide (9 ≤ count864 b) else (if i < 874 then decide (10 ≤ count864 b) else decide (11 ≤ count864 b))) else (if i < 876 then decide (12 ≤ count864 b) else (if i < 877 then decide (13 ≤ count864 b) else decide (1 ≤ count877 b)))) else (if i < 881 then (if i < 879 then decide (2 ≤ count877 b) else (if i < 880 then decide (1 ≤ count879 b) else decide (2 ≤ count879 b))) else (if i < 882 then decide (3 ≤ count879 b) else (if i < 883 then decide (1 ≤ count882 b) else decide (2 ≤ count882 b))))))) else (if i < 907 then (if i < 895 then (if i < 889 then (if i < 886 then (if i < 885 then decide (1 ≤ count884 b) else decide (2 ≤ count884 b)) else (if i < 887 then decide (1 ≤ count886 b) else (if i < 888 then decide (2 ≤ count886 b) else decide (3 ≤ count886 b)))) else (if i < 892 then (if i < 890 then decide (4 ≤ count886 b) else (if i < 891 then decide (1 ≤ count890 b) else decide (2 ≤ count890 b))) else (if i < 893 then decide (3 ≤ count890 b) else (if i < 894 then decide (4 ≤ count890 b) else decide (5 ≤ count890 b))))) else (if i < 901 then (if i < 898 then (if i < 896 then decide (6 ≤ count890 b) else (if i < 897 then decide (7 ≤ count890 b) else decide (1 ≤ count897 b))) else (if i < 899 then decide (2 ≤ count897 b) else (if i < 900 then decide (1 ≤ count899 b) else decide (2 ≤ count899 b)))) else (if i < 904 then (if i < 902 then decide (3 ≤ count899 b) else (if i < 903 then decide (1 ≤ count902 b) else decide (2 ≤ count902 b))) else (if i < 905 then decide (1 ≤ count904 b) else (if i < 906 then decide (2 ≤ count904 b) else decide (1 ≤ count906 b)))))) else (if i < 919 then (if i < 913 then (if i < 910 then (if i < 908 then decide (2 ≤ count906 b) else (if i < 909 then decide (3 ≤ count906 b) else decide (4 ≤ count906 b))) else (if i < 911 then decide (1 ≤ count910 b) else (if i < 912 then decide (2 ≤ count910 b) else decide (3 ≤ count910 b)))) else (if i < 916 then (if i < 914 then decide (4 ≤ count910 b) else (if i < 915 then decide (5 ≤ count910 b) else decide (6 ≤ count910 b))) else (if i < 917 then decide (7 ≤ count910 b) else (if i < 918 then decide (1 ≤ count917 b) else decide (2 ≤ count917 b))))) else (if i < 925 then (if i < 922 then (if i < 920 then decide (3 ≤ count917 b) else (if i < 921 then decide (4 ≤ count917 b) else decide (5 ≤ count917 b))) else (if i < 923 then decide (6 ≤ count917 b) else (if i < 924 then decide (7 ≤ count917 b) else decide (8 ≤ count917 b)))) else (if i < 928 then (if i < 926 then decide (9 ≤ count917 b) else (if i < 927 then decide (10 ≤ count917 b) else decide (11 ≤ count917 b))) else (if i < 929 then decide (12 ≤ count917 b) else (if i < 930 then decide (13 ≤ count917 b) else decide (1 ≤ count930 b))))))))) else (if i < 1024 then (if i < 977 then (if i < 954 then (if i < 942 then (if i < 936 then (if i < 933 then (if i < 932 then decide (2 ≤ count930 b) else decide (3 ≤ count930 b)) else (if i < 934 then decide (4 ≤ count930 b) else (if i < 935 then decide (5 ≤ count930 b) else decide (6 ≤ count930 b)))) else (if i < 939 then (if i < 937 then decide (7 ≤ count930 b) else (if i < 938 then decide (8 ≤ count930 b) else decide (9 ≤ count930 b))) else (if i < 940 then decide (10 ≤ count930 b) else (if i < 941 then decide (11 ≤ count930 b) else decide (12 ≤ count930 b))))) else (if i < 948 then (if i < 945 then (if i < 943 then decide (13 ≤ count930 b) else (if i < 944 then decide (1 ≤ count943 b) else decide (2 ≤ count943 b))) else (if i < 946 then decide (3 ≤ count943 b) else (if i < 947 then decide (4 ≤ count943 b) else decide (5 ≤ count943 b)))) else (if i < 951 then (if i < 949 then decide (6 ≤ count943 b) else (if i < 950 then decide (7 ≤ count943 b) else decide (8 ≤ count943 b))) else (if i < 952 then decide (9 ≤ count943 b) else (if i < 953 then decide (10 ≤ count943 b) else decide (11 ≤ count943 b)))))) else (if i < 965 then (if i < 959 then (if i < 956 then (if i < 955 then decide (12 ≤ count943 b) else decide (13 ≤ count943 b)) else (if i < 957 then decide (1 ≤ count956 b) else (if i < 958 then decide (2 ≤ count956 b) else decide (1 ≤ count958 b)))) else (if i < 962 then (if i < 960 then decide (2 ≤ count958 b) else (if i < 961 then decide (3 ≤ count958 b) else decide (1 ≤ count961 b))) else (if i < 963 then decide (2 ≤ count961 b) else (if i < 964 then decide (1 ≤ count963 b) else decide (2 ≤ count963 b))))) else (if i < 971 then (if i < 968 then (if i < 966 then decide (3 ≤ count963 b) else (if i < 967 then decide (1 ≤ count966 b) else decide (2 ≤ count966 b))) else (if i < 969 then decide (3 ≤ count966 b) else (if i < 970 then decide (4 ≤ count966 b) else decide (5 ≤ count966 b)))) else (if i < 974 then (if i < 972 then decide (6 ≤ count966 b) else (if i < 973 then decide (1 ≤ count972 b) else decide (2 ≤ count972 b))) else (if i < 975 then decide (1 ≤ count974 b) else (if i < 976 then decide (2 ≤ count974 b) else decide (3 ≤ count974 b))))))) else (if i < 1000 then (if i < 988 then (if i < 982 then (if i < 979 then (if i < 978 then decide (1 ≤ count977 b) else decide (2 ≤ count977 b)) else (if i < 980 then decide (1 ≤ count979 b) else (if i < 981 then decide (2 ≤ count979 b) else decide (1 ≤ count981 b)))) else (if i < 985 then (if i < 983 then decide (2 ≤ count981 b) else (if i < 984 then decide (3 ≤ count981 b) else decide (4 ≤ count981 b))) else (if i < 986 then decide (1 ≤ count985 b) else (if i < 987 then decide (2 ≤ count985 b) else decide (3 ≤ count985 b))))) else (if i < 994 then (if i < 991 then (if i < 989 then decide (4 ≤ count985 b) else (if i < 990 then decide (5 ≤ count985 b) else decide (6 ≤ count985 b))) else (if i < 992 then decide (7 ≤ count985 b) else (if i < 993 then decide (1 ≤ count992 b) else decide (2 ≤ count992 b)))) else (if i < 997 then (if i < 995 then decide (3 ≤ count992 b) else (if i < 996 then decide (4 ≤ count992 b) else decide (5 ≤ count992 b))) else (if i < 998 then decide (6 ≤ count992 b) else (if i < 999 then decide (7 ≤ count992 b) else decide (8 ≤ count992 b)))))) else (if i < 1012 then (if i < 1006 then (if i < 1003 then (if i < 1001 then decide (9 ≤ count992 b) else (if i < 1002 then decide (10 ≤ count992 b) else decide (11 ≤ count992 b))) else (if i < 1004 then decide (12 ≤ count992 b) else (if i < 1005 then decide (13 ≤ count992 b) else decide (1 ≤ count1005 b)))) else (if i < 1009 then (if i < 1007 then decide (2 ≤ count1005 b) else (if i < 1008 then decide (1 ≤ count1007 b) else decide (2 ≤ count1007 b))) else (if i < 1010 then decide (3 ≤ count1007 b) else (if i < 1011 then decide (1 ≤ count1010 b) else decide (2 ≤ count1010 b))))) else (if i < 1018 then (if i < 1015 then (if i < 1013 then decide (1 ≤ count1012 b) else (if i < 1014 then decide (2 ≤ count1012 b) else decide (3 ≤ count1012 b))) else (if i < 1016 then decide (1 ≤ count1015 b) else (if i < 1017 then decide (2 ≤ count1015 b) else decide (3 ≤ count1015 b)))) else (if i < 1021 then (if i < 1019 then decide (4 ≤ count1015 b) else (if i < 1020 then decide (5 ≤ count1015 b) else decide (6 ≤ count1015 b))) else (if i < 1022 then decide (1 ≤ count1021 b) else (if i < 1023 then decide (2 ≤ count1021 b) else decide (1 ≤ count1023 b)))))))) else (if i < 1071 then (if i < 1047 then (if i < 1035 then (if i < 1029 then (if i < 1026 then (if i < 1025 then decide (2 ≤ count1023 b) else decide (3 ≤ count1023 b)) else (if i < 1027 then decide (1 ≤ count1026 b) else (if i < 1028 then decide (2 ≤ count1026 b) else decide (1 ≤ count1028 b)))) else (if i < 1032 then (if i < 1030 then decide (2 ≤ count1028 b) else (if i < 1031 then decide (1 ≤ count1030 b) else decide (2 ≤ count1030 b))) else (if i < 1033 then decide (3 ≤ count1030 b) else (if i < 1034 then decide (4 ≤ count1030 b) else decide (1 ≤ count1034 b))))) else (if i < 1041 then (if i < 1038 then (if i < 1036 then decide (2 ≤ count1034 b) else (if i < 1037 then decide (3 ≤ count1034 b) else decide (4 ≤ count1034 b))) else (if i < 1039 then decide (5 ≤ count1034 b) else (if i < 1040 then decide (6 ≤ count1034 b) else decide (7 ≤ count1034 b)))) else (if i < 1044 then (if i < 1042 then decide (1 ≤ count1041 b) else (if i < 1043 then decide (2 ≤ count1041 b) else decide (3 ≤ count1041 b))) else (if i < 1045 then decide (4 ≤ count1041 b) else (if i < 1046 then decide (5 ≤ count1041 b) else decide (6 ≤ count1041 b)))))) else (if i < 1059 then (if i < 1053 then (if i < 1050 then (if i < 1048 then decide (7 ≤ count1041 b) else (if i < 1049 then decide (8 ≤ count1041 b) else decide (9 ≤ count1041 b))) else (if i < 1051 then decide (10 ≤ count1041 b) else (if i < 1052 then decide (11 ≤ count1041 b) else decide (12 ≤ count1041 b)))) else (if i < 1056 then (if i < 1054 then decide (13 ≤ count1041 b) else (if i < 1055 then decide (1 ≤ count1054 b) else decide (2 ≤ count1054 b))) else (if i < 1057 then decide (3 ≤ count1054 b) else (if i < 1058 then decide (4 ≤ count1054 b) else decide (5 ≤ count1054 b))))) else (if i < 1065 then (if i < 1062 then (if i < 1060 then decide (6 ≤ count1054 b) else (if i < 1061 then decide (7 ≤ count1054 b) else decide (8 ≤ count1054 b))) else (if i < 1063 then decide (9 ≤ count1054 b) else (if i < 1064 then decide (10 ≤ count1054 b) else decide (11 ≤ count1054 b)))) else (if i < 1068 then (if i < 1066 then decide (12 ≤ count1054 b) else (if i < 1067 then decide (13 ≤ count1054 b) else decide (14 ≤ count1054 b))) else (if i < 1069 then decide (15 ≤ count1054 b) else (if i < 1070 then decide (16 ≤ count1054 b) else decide (17 ≤ count1054 b))))))) else (if i < 1094 then (if i < 1082 then (if i < 1076 then (if i < 1073 then (if i < 1072 then decide (18 ≤ count1054 b) else decide (19 ≤ count1054 b)) else (if i < 1074 then decide (20 ≤ count1054 b) else (if i < 1075 then decide (21 ≤ count1054 b) else decide (22 ≤ count1054 b)))) else (if i < 1079 then (if i < 1077 then decide (23 ≤ count1054 b) else (if i < 1078 then decide (24 ≤ count1054 b) else decide (25 ≤ count1054 b))) else (if i < 1080 then decide (26 ≤ count1054 b) else (if i < 1081 then decide (1 ≤ count1080 b) else decide (2 ≤ count1080 b))))) else (if i < 1088 then (if i < 1085 then (if i < 1083 then decide (1 ≤ count1082 b) else (if i < 1084 then decide (2 ≤ count1082 b) else decide (3 ≤ count1082 b))) else (if i < 1086 then decide (1 ≤ count1085 b) else (if i < 1087 then decide (2 ≤ count1085 b) else decide (1 ≤ count1087 b)))) else (if i < 1091 then (if i < 1089 then decide (2 ≤ count1087 b) else (if i < 1090 then decide (3 ≤ count1087 b) else decide (1 ≤ count1090 b))) else (if i < 1092 then decide (2 ≤ count1090 b) else (if i < 1093 then decide (3 ≤ count1090 b) else decide (4 ≤ count1090 b)))))) else (if i < 1106 then (if i < 1100 then (if i < 1097 then (if i < 1095 then decide (5 ≤ count1090 b) else (if i < 1096 then decide (6 ≤ count1090 b) else decide (1 ≤ count1096 b))) else (if i < 1098 then decide (2 ≤ count1096 b) else (if i < 1099 then decide (1 ≤ count1098 b) else decide (2 ≤ count1098 b)))) else (if i < 1103 then (if i < 1101 then decide (3 ≤ count1098 b) else (if i < 1102 then decide (1 ≤ count1101 b) else decide (2 ≤ count1101 b))) else (if i < 1104 then decide (1 ≤ count1103 b) else (if i < 1105 then decide (2 ≤ count1103 b) else decide (1 ≤ count1105 b))))) else (if i < 1112 then (if i < 1109 then (if i < 1107 then decide (2 ≤ count1105 b) else (if i < 1108 then decide (3 ≤ count1105 b) else decide (4 ≤ count1105 b))) else (if i < 1110 then decide (1 ≤ count1109 b) else (if i < 1111 then decide (2 ≤ count1109 b) else decide (3 ≤ count1109 b)))) else (if i < 1115 then (if i < 1113 then decide (4 ≤ count1109 b) else (if i < 1114 then decide (5 ≤ count1109 b) else decide (6 ≤ count1109 b))) else (if i < 1116 then decide (7 ≤ count1109 b) else (if i < 1117 then decide (1 ≤ count1116 b) else decide (2 ≤ count1116 b)))))))))) else (if i < 1304 then (if i < 1211 then (if i < 1164 then (if i < 1141 then (if i < 1129 then (if i < 1123 then (if i < 1120 then (if i < 1119 then decide (3 ≤ count1116 b) else decide (4 ≤ count1116 b)) else (if i < 1121 then decide (5 ≤ count1116 b) else (if i < 1122 then decide (6 ≤ count1116 b) else decide (7 ≤ count1116 b)))) else (if i < 1126 then (if i < 1124 then decide (8 ≤ count1116 b) else (if i < 1125 then decide (9 ≤ count1116 b) else decide (10 ≤ count1116 b))) else (if i < 1127 then decide (11 ≤ count1116 b) else (if i < 1128 then decide (12 ≤ count1116 b) else decide (13 ≤ count1116 b))))) else (if i < 1135 then (if i < 1132 then (if i < 1130 then decide (1 ≤ count1129 b) else (if i < 1131 then decide (2 ≤ count1129 b) else decide (1 ≤ count1131 b))) else (if i < 1133 then decide (2 ≤ count1131 b) else (if i < 1134 then decide (3 ≤ count1131 b) else decide (1 ≤ count1134 b)))) else (if i < 1138 then (if i < 1136 then decide (2 ≤ count1134 b) else (if i < 1137 then decide (1 ≤ count1136 b) else decide (2 ≤ count1136 b))) else (if i < 1139 then decide (1 ≤ count1138 b) else (if i < 1140 then decide (2 ≤ count1138 b) else decide (3 ≤ count1138 b)))))) else (if i < 1152 then (if i < 1146 then (if i < 1143 then (if i < 1142 then decide (4 ≤ count1138 b) else decide (1 ≤ count1142 b)) else (if i < 1144 then decide (2 ≤ count1142 b) else (if i < 1145 then decide (3 ≤ count1142 b) else decide (4 ≤ count1142 b)))) else (if i < 1149 then (if i < 1147 then decide (5 ≤ count1142 b) else (if i < 1148 then decide (6 ≤ count1142 b) else decide (7 ≤ count1142 b))) else (if i < 1150 then decide (1 ≤ count1149 b) else (if i < 1151 then decide (2 ≤ count1149 b) else decide (1 ≤ count1151 b))))) else (if i < 1158 then (if i < 1155 then (if i < 1153 then decide (2 ≤ count1151 b) else (if i < 1154 then decide (3 ≤ count1151 b) else decide (1 ≤ count1154 b))) else (if i < 1156 then decide (2 ≤ count1154 b) else (if i < 1157 then decide (1 ≤ count1156 b) else decide (2 ≤ count1156 b)))) else (if i < 1161 then (if i < 1159 then decide (1 ≤ count1158 b) else (if i < 1160 then decide (2 ≤ count1158 b) else decide (3 ≤ count1158 b))) else (if i < 1162 then decide (4 ≤ count1158 b) else (if i < 1163 then decide (1 ≤ count1162 b) else decide (2 ≤ count1162 b))))))) else (if i < 1187 then (if i < 1175 then (if i < 1169 then (if i < 1166 then (if i < 1165 then decide (3 ≤ count1162 b) else decide (4 ≤ count1162 b)) else (if i < 1167 then decide (5 ≤ count1162 b) else (if i < 1168 then decide (6 ≤ count1162 b) else decide (7 ≤ count1162 b)))) else (if i < 1172 then (if i < 1170 then decide (1 ≤ count1169 b) else (if i < 1171 then decide (2 ≤ count1169 b) else decide (3 ≤ count1169 b))) else (if i < 1173 then decide (4 ≤ count1169 b) else (if i < 1174 then decide (5 ≤ count1169 b) else decide (6 ≤ count1169 b))))) else (if i < 1181 then (if i < 1178 then (if i < 1176 then decide (7 ≤ count1169 b) else (if i < 1177 then decide (8 ≤ count1169 b) else decide (9 ≤ count1169 b))) else (if i < 1179 then decide (10 ≤ count1169 b) else (if i < 1180 then decide (11 ≤ count1169 b) else decide (12 ≤ count1169 b)))) else (if i < 1184 then (if i < 1182 then decide (13 ≤ count1169 b) else (if i < 1183 then decide (14 ≤ count1169 b) else decide (1 ≤ count1183 b))) else (if i < 1185 then decide (2 ≤ count1183 b) else (if i < 1186 then decide (3 ≤ count1183 b) else decide (4 ≤ count1183 b)))))) else (if i < 1199 then (if i < 1193 then (if i < 1190 then (if i < 1188 then decide (5 ≤ count1183 b) else (if i < 1189 then decide (6 ≤ count1183 b) else decide (7 ≤ count1183 b))) else (if i < 1191 then decide (8 ≤ count1183 b) else (if i < 1192 then decide (9 ≤ count1183 b) else decide (10 ≤ count1183 b)))) else (if i < 1196 then (if i < 1194 then decide (11 ≤ count1183 b) else (if i < 1195 then decide (12 ≤ count1183 b) else decide (13 ≤ count1183 b))) else (if i < 1197 then decide (14 ≤ count1183 b) else (if i < 1198 then decide (15 ≤ count1183 b) else decide (16 ≤ count1183 b))))) else (if i < 1205 then (if i < 1202 then (if i < 1200 then decide (17 ≤ count1183 b) else (if i < 1201 then decide (18 ≤ count1183 b) else decide (19 ≤ count1183 b))) else (if i < 1203 then decide (20 ≤ count1183 b) else (if i < 1204 then decide (21 ≤ count1183 b) else decide (22 ≤ count1183 b)))) else (if i < 1208 then (if i < 1206 then decide (23 ≤ count1183 b) else (if i < 1207 then decide (24 ≤ count1183 b) else decide (25 ≤ count1183 b))) else (if i < 1209 then decide (26 ≤ count1183 b) else (if i < 1210 then decide (27 ≤ count1183 b) else decide (1 ≤ count1210 b)))))))) else (if i < 1257 then (if i < 1234 then (if i < 1222 then (if i < 1216 then (if i < 1213 then (if i < 1212 then decide (2 ≤ count1210 b) else decide (3 ≤ count1210 b)) else (if i < 1214 then decide (4 ≤ count1210 b) else (if i < 1215 then decide (5 ≤ count1210 b) else decide (6 ≤ count1210 b)))) else (if i < 1219 then (if i < 1217 then decide (7 ≤ count1210 b) else (if i < 1218 then decide (8 ≤ count1210 b) else decide (9 ≤ count1210 b))) else (if i < 1220 then decide (10 ≤ count1210 b) else (if i < 1221 then decide (11 ≤ count1210 b) else decide (12 ≤ count1210 b))))) else (if i < 1228 then (if i < 1225 then (if i < 1223 then decide (13 ≤ count1210 b) else (if i < 1224 then decide (14 ≤ count1210 b) else decide (15 ≤ count1210 b))) else (if i < 1226 then decide (16 ≤ count1210 b) else (if i < 1227 then decide (17 ≤ count1210 b) else decide (18 ≤ count1210 b)))) else (if i < 1231 then (if i < 1229 then decide (19 ≤ count1210 b) else (if i < 1230 then decide (20 ≤ count1210 b) else decide (21 ≤ count1210 b))) else (if i < 1232 then decide (22 ≤ count1210 b) else (if i < 1233 then decide (23 ≤ count1210 b) else decide (24 ≤ count1210 b)))))) else (if i < 1245 then (if i < 1239 then (if i < 1236 then (if i < 1235 then decide (25 ≤ count1210 b) else decide (26 ≤ count1210 b)) else (if i < 1237 then decide (27 ≤ count1210 b) else (if i < 1238 then decide (28 ≤ count1210 b) else decide (29 ≤ count1210 b)))) else (if i < 1242 then (if i < 1240 then decide (30 ≤ count1210 b) else (if i < 1241 then decide (31 ≤ count1210 b) else decide (32 ≤ count1210 b))) else (if i < 1243 then decide (33 ≤ count1210 b) else (if i < 1244 then decide (34 ≤ count1210 b) else decide (35 ≤ count1210 b))))) else (if i < 1251 then (if i < 1248 then (if i < 1246 then decide (36 ≤ count1210 b) else (if i < 1247 then decide (37 ≤ count1210 b) else decide (38 ≤ count1210 b))) else (if i < 1249 then decide (39 ≤ count1210 b) else (if i < 1250 then decide (40 ≤ count1210 b) else decide (41 ≤ count1210 b)))) else (if i < 1254 then (if i < 1252 then decide (42 ≤ count1210 b) else (if i < 1253 then decide (1 ≤ count1252 b) else decide (2 ≤ count1252 b))) else (if i < 1255 then decide (1 ≤ count1254 b) else (if i < 1256 then decide (2 ≤ count1254 b) else decide (3 ≤ count1254 b))))))) else (if i < 1280 then (if i < 1268 then (if i < 1262 then (if i < 1259 then (if i < 1258 then decide (1 ≤ count1257 b) else decide (2 ≤ count1257 b)) else (if i < 1260 then decide (1 ≤ count1259 b) else (if i < 1261 then decide (2 ≤ count1259 b) else decide (3 ≤ count1259 b)))) else (if i < 1265 then (if i < 1263 then decide (1 ≤ count1262 b) else (if i < 1264 then decide (2 ≤ count1262 b) else decide (3 ≤ count1262 b))) else (if i < 1266 then decide (4 ≤ count1262 b) else (if i < 1267 then decide (5 ≤ count1262 b) else decide (6 ≤ count1262 b))))) else (if i < 1274 then (if i < 1271 then (if i < 1269 then decide (1 ≤ count1268 b) else (if i < 1270 then decide (2 ≤ count1268 b) else decide (1 ≤ count1270 b))) else (if i < 1272 then decide (2 ≤ count1270 b) else (if i < 1273 then decide (3 ≤ count1270 b) else decide (1 ≤ count1273 b)))) else (if i < 1277 then (if i < 1275 then decide (2 ≤ count1273 b) else (if i < 1276 then decide (1 ≤ count1275 b) else decide (2 ≤ count1275 b))) else (if i < 1278 then decide (1 ≤ count1277 b) else (if i < 1279 then decide (2 ≤ count1277 b) else decide (3 ≤ count1277 b)))))) else (if i < 1292 then (if i < 1286 then (if i < 1283 then (if i < 1281 then decide (4 ≤ count1277 b) else (if i < 1282 then decide (1 ≤ count1281 b) else decide (2 ≤ count1281 b))) else (if i < 1284 then decide (3 ≤ count1281 b) else (if i < 1285 then decide (4 ≤ count1281 b) else decide (5 ≤ count1281 b)))) else (if i < 1289 then (if i < 1287 then decide (6 ≤ count1281 b) else (if i < 1288 then decide (7 ≤ count1281 b) else decide (1 ≤ count1288 b))) else (if i < 1290 then decide (2 ≤ count1288 b) else (if i < 1291 then decide (3 ≤ count1288 b) else decide (4 ≤ count1288 b))))) else (if i < 1298 then (if i < 1295 then (if i < 1293 then decide (5 ≤ count1288 b) else (if i < 1294 then decide (6 ≤ count1288 b) else decide (7 ≤ count1288 b))) else (if i < 1296 then decide (8 ≤ count1288 b) else (if i < 1297 then decide (9 ≤ count1288 b) else decide (10 ≤ count1288 b)))) else (if i < 1301 then (if i < 1299 then decide (11 ≤ count1288 b) else (if i < 1300 then decide (12 ≤ count1288 b) else decide (13 ≤ count1288 b))) else (if i < 1302 then decide (1 ≤ count1301 b) else (if i < 1303 then decide (2 ≤ count1301 b) else decide (1 ≤ count1303 b))))))))) else (if i < 1397 then (if i < 1350 then (if i < 1327 then (if i < 1315 then (if i < 1309 then (if i < 1306 then (if i < 1305 then decide (2 ≤ count1303 b) else decide (3 ≤ count1303 b)) else (if i < 1307 then decide (1 ≤ count1306 b) else (if i < 1308 then decide (2 ≤ count1306 b) else decide (1 ≤ count1308 b)))) else (if i < 1312 then (if i < 1310 then decide (2 ≤ count1308 b) else (if i < 1311 then decide (3 ≤ count1308 b) else decide (1 ≤ count1311 b))) else (if i < 1313 then decide (2 ≤ count1311 b) else (if i < 1314 then decide (3 ≤ count1311 b) else decide (4 ≤ count1311 b))))) else (if i < 1321 then (if i < 1318 then (if i < 1316 then decide (5 ≤ count1311 b) else (if i < 1317 then decide (6 ≤ count1311 b) else decide (1 ≤ count1317 b))) else (if i < 1319 then decide (2 ≤ count1317 b) else (if i < 1320 then decide (1 ≤ count1319 b) else decide (2 ≤ count1319 b)))) else (if i < 1324 then (if i < 1322 then decide (3 ≤ count1319 b) else (if i < 1323 then decide (1 ≤ count1322 b) else decide (2 ≤ count1322 b))) else (if i < 1325 then decide (1 ≤ count1324 b) else (if i < 1326 then decide (2 ≤ count1324 b) else decide (1 ≤ count1326 b)))))) else (if i < 1338 then (if i < 1332 then (if i < 1329 then (if i < 1328 then decide (2 ≤ count1326 b) else decide (3 ≤ count1326 b)) else (if i < 1330 then decide (4 ≤ count1326 b) else (if i < 1331 then decide (1 ≤ count1330 b) else decide (2 ≤ count1330 b)))) else (if i < 1335 then (if i < 1333 then decide (3 ≤ count1330 b) else (if i < 1334 then decide (4 ≤ count1330 b) else decide (5 ≤ count1330 b))) else (if i < 1336 then decide (6 ≤ count1330 b) else (if i < 1337 then decide (7 ≤ count1330 b) else decide (1 ≤ count1337 b))))) else (if i < 1344 then (if i < 1341 then (if i < 1339 then decide (2 ≤ count1337 b) else (if i < 1340 then decide (3 ≤ count1337 b) else decide (4 ≤ count1337 b))) else (if i < 1342 then decide (5 ≤ count1337 b) else (if i < 1343 then decide (6 ≤ count1337 b) else decide (7 ≤ count1337 b)))) else (if i < 1347 then (if i < 1345 then decide (8 ≤ count1337 b) else (if i < 1346 then decide (9 ≤ count1337 b) else decide (10 ≤ count1337 b))) else (if i < 1348 then decide (11 ≤ count1337 b) else (if i < 1349 then decide (12 ≤ count1337 b) else decide (13 ≤ count1337 b))))))) else (if i < 1373 then (if i < 1361 then (if i < 1355 then (if i < 1352 then (if i < 1351 then decide (1 ≤ count1350 b) else decide (2 ≤ count1350 b)) else (if i < 1353 then decide (3 ≤ count1350 b) else (if i < 1354 then decide (4 ≤ count1350 b) else decide (5 ≤ count1350 b)))) else (if i < 1358 then (if i < 1356 then decide (6 ≤ count1350 b) else (if i < 1357 then decide (7 ≤ count1350 b) else decide (8 ≤ count1350 b))) else (if i < 1359 then decide (9 ≤ count1350 b) else (if i < 1360 then decide (10 ≤ count1350 b) else decide (11 ≤ count1350 b))))) else (if i < 1367 then (if i < 1364 then (if i < 1362 then decide (12 ≤ count1350 b) else (if i < 1363 then decide (13 ≤ count1350 b) else decide (1 ≤ count1363 b))) else (if i < 1365 then decide (2 ≤ count1363 b) else (if i < 1366 then decide (1 ≤ count1365 b) else decide (2 ≤ count1365 b)))) else (if i < 1370 then (if i < 1368 then decide (3 ≤ count1365 b) else (if i < 1369 then decide (1 ≤ count1368 b) else decide (2 ≤ count1368 b))) else (if i < 1371 then decide (1 ≤ count1370 b) else (if i < 1372 then decide (2 ≤ count1370 b) else decide (3 ≤ count1370 b)))))) else (if i < 1385 then (if i < 1379 then (if i < 1376 then (if i < 1374 then decide (1 ≤ count1373 b) else (if i < 1375 then decide (2 ≤ count1373 b) else decide (3 ≤ count1373 b))) else (if i < 1377 then decide (4 ≤ count1373 b) else (if i < 1378 then decide (5 ≤ count1373 b) else decide (6 ≤ count1373 b)))) else (if i < 1382 then (if i < 1380 then decide (1 ≤ count1379 b) else (if i < 1381 then decide (2 ≤ count1379 b) else decide (1 ≤ count1381 b))) else (if i < 1383 then decide (2 ≤ count1381 b) else (if i < 1384 then decide (3 ≤ count1381 b) else decide (1 ≤ count1384 b))))) else (if i < 1391 then (if i < 1388 then (if i < 1386 then decide (2 ≤ count1384 b) else (if i < 1387 then decide (1 ≤ count1386 b) else decide (2 ≤ count1386 b))) else (if i < 1389 then decide (1 ≤ count1388 b) else (if i < 1390 then decide (2 ≤ count1388 b) else decide (3 ≤ count1388 b)))) else (if i < 1394 then (if i < 1392 then decide (4 ≤ count1388 b) else (if i < 1393 then decide (1 ≤ count1392 b) else decide (2 ≤ count1392 b))) else (if i < 1395 then decide (3 ≤ count1392 b) else (if i < 1396 then decide (4 ≤ count1392 b) else decide (5 ≤ count1392 b)))))))) else (if i < 1444 then (if i < 1420 then (if i < 1408 then (if i < 1402 then (if i < 1399 then (if i < 1398 then decide (6 ≤ count1392 b) else decide (7 ≤ count1392 b)) else (if i < 1400 then decide (1 ≤ count1399 b) else (if i < 1401 then decide (2 ≤ count1399 b) else decide (3 ≤ count1399 b)))) else (if i < 1405 then (if i < 1403 then decide (4 ≤ count1399 b) else (if i < 1404 then decide (5 ≤ count1399 b) else decide (6 ≤ count1399 b))) else (if i < 1406 then decide (7 ≤ count1399 b) else (if i < 1407 then decide (8 ≤ count1399 b) else decide (9 ≤ count1399 b))))) else (if i < 1414 then (if i < 1411 then (if i < 1409 then decide (10 ≤ count1399 b) else (if i < 1410 then decide (11 ≤ count1399 b) else decide (12 ≤ count1399 b))) else (if i < 1412 then decide (13 ≤ count1399 b) else (if i < 1413 then decide (1 ≤ count1412 b) else decide (2 ≤ count1412 b)))) else (if i < 1417 then (if i < 1415 then decide (1 ≤ count1414 b) else (if i < 1416 then decide (2 ≤ count1414 b) else decide (3 ≤ count1414 b))) else (if i < 1418 then decide (1 ≤ count1417 b) else (if i < 1419 then decide (2 ≤ count1417 b) else decide (1 ≤ count1419 b)))))) else (if i < 1432 then (if i < 1426 then (if i < 1423 then (if i < 1421 then decide (2 ≤ count1419 b) else (if i < 1422 then decide (1 ≤ count1421 b) else decide (2 ≤ count1421 b))) else (if i < 1424 then decide (3 ≤ count1421 b) else (if i < 1425 then decide (4 ≤ count1421 b) else decide (1 ≤ count1425 b)))) else (if i < 1429 then (if i < 1427 then decide (2 ≤ count1425 b) else (if i < 1428 then decide (3 ≤ count1425 b) else decide (4 ≤ count1425 b))) else (if i < 1430 then decide (5 ≤ count1425 b) else (if i < 1431 then decide (6 ≤ count1425 b) else decide (7 ≤ count1425 b))))) else (if i < 1438 then (if i < 1435 then (if i < 1433 then decide (1 ≤ count1432 b) else (if i < 1434 then decide (2 ≤ count1432 b) else decide (1 ≤ count1434 b))) else (if i < 1436 then decide (2 ≤ count1434 b) else (if i < 1437 then decide (3 ≤ count1434 b) else decide (1 ≤ count1437 b)))) else (if i < 1441 then (if i < 1439 then decide (2 ≤ count1437 b) else (if i < 1440 then decide (1 ≤ count1439 b) else decide (2 ≤ count1439 b))) else (if i < 1442 then decide (1 ≤ count1441 b) else (if i < 1443 then decide (2 ≤ count1441 b) else decide (3 ≤ count1441 b))))))) else (if i < 1467 then (if i < 1455 then (if i < 1449 then (if i < 1446 then (if i < 1445 then decide (4 ≤ count1441 b) else decide (1 ≤ count1445 b)) else (if i < 1447 then decide (2 ≤ count1445 b) else (if i < 1448 then decide (3 ≤ count1445 b) else decide (4 ≤ count1445 b)))) else (if i < 1452 then (if i < 1450 then decide (5 ≤ count1445 b) else (if i < 1451 then decide (6 ≤ count1445 b) else decide (7 ≤ count1445 b))) else (if i < 1453 then decide (1 ≤ count1452 b) else (if i < 1454 then decide (2 ≤ count1452 b) else decide (3 ≤ count1452 b))))) else (if i < 1461 then (if i < 1458 then (if i < 1456 then decide (4 ≤ count1452 b) else (if i < 1457 then decide (5 ≤ count1452 b) else decide (6 ≤ count1452 b))) else (if i < 1459 then decide (7 ≤ count1452 b) else (if i < 1460 then decide (8 ≤ count1452 b) else decide (9 ≤ count1452 b)))) else (if i < 1464 then (if i < 1462 then decide (10 ≤ count1452 b) else (if i < 1463 then decide (11 ≤ count1452 b) else decide (12 ≤ count1452 b))) else (if i < 1465 then decide (13 ≤ count1452 b) else (if i < 1466 then decide (1 ≤ count1465 b) else decide (2 ≤ count1465 b)))))) else (if i < 1479 then (if i < 1473 then (if i < 1470 then (if i < 1468 then decide (3 ≤ count1465 b) else (if i < 1469 then decide (4 ≤ count1465 b) else decide (5 ≤ count1465 b))) else (if i < 1471 then decide (6 ≤ count1465 b) else (if i < 1472 then decide (7 ≤ count1465 b) else decide (8 ≤ count1465 b)))) else (if i < 1476 then (if i < 1474 then decide (9 ≤ count1465 b) else (if i < 1475 then decide (10 ≤ count1465 b) else decide (11 ≤ count1465 b))) else (if i < 1477 then decide (12 ≤ count1465 b) else (if i < 1478 then decide (13 ≤ count1465 b) else decide (1 ≤ count1478 b))))) else (if i < 1485 then (if i < 1482 then (if i < 1480 then decide (2 ≤ count1478 b) else (if i < 1481 then decide (3 ≤ count1478 b) else decide (4 ≤ count1478 b))) else (if i < 1483 then decide (5 ≤ count1478 b) else (if i < 1484 then decide (6 ≤ count1478 b) else decide (7 ≤ count1478 b)))) else (if i < 1488 then (if i < 1486 then decide (8 ≤ count1478 b) else (if i < 1487 then decide (9 ≤ count1478 b) else decide (10 ≤ count1478 b))) else (if i < 1489 then decide (11 ≤ count1478 b) else (if i < 1490 then decide (12 ≤ count1478 b) else decide (13 ≤ count1478 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (4 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (6 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (8 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (9 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (10 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (11 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (14 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (19 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (21 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (22 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (23 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (24 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (25 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (26 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (27 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (29 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (64 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (65 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (69 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (71 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (72 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (73 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (78 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (79 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (80 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (82 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (83 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (84 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (91 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (92 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (94 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (95 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (160 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (164 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (166 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (168 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (169 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (170 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (171 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (174 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (179 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (180 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (181 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (182 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (183 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (184 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (185 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (186 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (187 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (189 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (200 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (203 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (216 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (218 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (219 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (224 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (232 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (238 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (240 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (242 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (244 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (251 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (252 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (254 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (255 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (264 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (296 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (353 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (357 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (359 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (360 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (361 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (366 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (367 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (416 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (417 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (421 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (423 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (424 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (425 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (430 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (431 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (432 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (434 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (435 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (436 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (444 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (446 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (447 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (448 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (449 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (453 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (455 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (456 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (457 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (462 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (463 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (464 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (466 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (467 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (468 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (475 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (476 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (478 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (479 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (4 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (9 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (21 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (23 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (24 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (26 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (27 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (64 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (65 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (71 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (72 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (78 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (80 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (82 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (83 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (91 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (92 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (164 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (166 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (169 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (170 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (174 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (180 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (181 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (183 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (184 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (185 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (187 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (203 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (216 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (219 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (224 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (232 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (240 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (242 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (252 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (254 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (353 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (359 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (360 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (361 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (367 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (416 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (423 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (424 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (431 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (434 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (444 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (446 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (448 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (449 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (455 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (456 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (457 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (463 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (466 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (467 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (468 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (476 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (478 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (479 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (1 ≤ count213 (baseVal q)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (1 ≤ count215 (baseVal q)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (2 ≤ count227 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (2 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (2 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (2 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (2 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (2 ≤ count245 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value260 (q : Snake 81) : valuation q 260 = decide (2 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value262 (q : Snake 81) : valuation q 262 = decide (2 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value286 (q : Snake 81) : valuation q 286 = decide (2 ≤ count285 (baseVal q)) := rfl
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
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value310 (q : Snake 81) : valuation q 310 = decide (2 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
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
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value364 (q : Snake 81) : valuation q 364 = decide (2 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value414 (q : Snake 81) : valuation q 414 = decide (2 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 (baseVal q)) := rfl
theorem value420 (q : Snake 81) : valuation q 420 = decide (2 ≤ count419 (baseVal q)) := rfl
theorem value1252 (q : Snake 81) : valuation q 1252 = decide (1 ≤ count1252 (baseVal q)) := rfl
theorem value1253 (q : Snake 81) : valuation q 1253 = decide (2 ≤ count1252 (baseVal q)) := rfl
theorem value1254 (q : Snake 81) : valuation q 1254 = decide (1 ≤ count1254 (baseVal q)) := rfl
theorem value1255 (q : Snake 81) : valuation q 1255 = decide (2 ≤ count1254 (baseVal q)) := rfl
theorem value1256 (q : Snake 81) : valuation q 1256 = decide (3 ≤ count1254 (baseVal q)) := rfl
theorem value1257 (q : Snake 81) : valuation q 1257 = decide (1 ≤ count1257 (baseVal q)) := rfl
theorem value1259 (q : Snake 81) : valuation q 1259 = decide (1 ≤ count1259 (baseVal q)) := rfl
theorem value1260 (q : Snake 81) : valuation q 1260 = decide (2 ≤ count1259 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (1 ≤ count1262 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (2 ≤ count1262 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (3 ≤ count1262 (baseVal q)) := rfl
theorem value1268 (q : Snake 81) : valuation q 1268 = decide (1 ≤ count1268 (baseVal q)) := rfl
theorem value1269 (q : Snake 81) : valuation q 1269 = decide (2 ≤ count1268 (baseVal q)) := rfl
theorem value1270 (q : Snake 81) : valuation q 1270 = decide (1 ≤ count1270 (baseVal q)) := rfl
theorem value1271 (q : Snake 81) : valuation q 1271 = decide (2 ≤ count1270 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (3 ≤ count1270 (baseVal q)) := rfl
theorem value1273 (q : Snake 81) : valuation q 1273 = decide (1 ≤ count1273 (baseVal q)) := rfl
theorem value1274 (q : Snake 81) : valuation q 1274 = decide (2 ≤ count1273 (baseVal q)) := rfl
theorem value1275 (q : Snake 81) : valuation q 1275 = decide (1 ≤ count1275 (baseVal q)) := rfl
theorem value1277 (q : Snake 81) : valuation q 1277 = decide (1 ≤ count1277 (baseVal q)) := rfl
theorem value1278 (q : Snake 81) : valuation q 1278 = decide (2 ≤ count1277 (baseVal q)) := rfl
theorem value1279 (q : Snake 81) : valuation q 1279 = decide (3 ≤ count1277 (baseVal q)) := rfl
theorem value1281 (q : Snake 81) : valuation q 1281 = decide (1 ≤ count1281 (baseVal q)) := rfl
theorem value1282 (q : Snake 81) : valuation q 1282 = decide (2 ≤ count1281 (baseVal q)) := rfl
theorem value1283 (q : Snake 81) : valuation q 1283 = decide (3 ≤ count1281 (baseVal q)) := rfl
theorem value1284 (q : Snake 81) : valuation q 1284 = decide (4 ≤ count1281 (baseVal q)) := rfl
theorem value1285 (q : Snake 81) : valuation q 1285 = decide (5 ≤ count1281 (baseVal q)) := rfl
theorem value1288 (q : Snake 81) : valuation q 1288 = decide (1 ≤ count1288 (baseVal q)) := rfl
theorem value1289 (q : Snake 81) : valuation q 1289 = decide (2 ≤ count1288 (baseVal q)) := rfl
theorem value1290 (q : Snake 81) : valuation q 1290 = decide (3 ≤ count1288 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (4 ≤ count1288 (baseVal q)) := rfl
theorem value1292 (q : Snake 81) : valuation q 1292 = decide (5 ≤ count1288 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (1 ≤ count1301 (baseVal q)) := rfl
theorem value1302 (q : Snake 81) : valuation q 1302 = decide (2 ≤ count1301 (baseVal q)) := rfl
theorem value1303 (q : Snake 81) : valuation q 1303 = decide (1 ≤ count1303 (baseVal q)) := rfl
theorem value1304 (q : Snake 81) : valuation q 1304 = decide (2 ≤ count1303 (baseVal q)) := rfl
theorem value1305 (q : Snake 81) : valuation q 1305 = decide (3 ≤ count1303 (baseVal q)) := rfl
theorem value1306 (q : Snake 81) : valuation q 1306 = decide (1 ≤ count1306 (baseVal q)) := rfl
theorem value1307 (q : Snake 81) : valuation q 1307 = decide (2 ≤ count1306 (baseVal q)) := rfl
theorem value1308 (q : Snake 81) : valuation q 1308 = decide (1 ≤ count1308 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (2 ≤ count1308 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (1 ≤ count1311 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (2 ≤ count1311 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (3 ≤ count1311 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (4 ≤ count1311 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (1 ≤ count1317 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (2 ≤ count1317 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (1 ≤ count1319 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (2 ≤ count1319 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (1 ≤ count1322 (baseVal q)) := rfl
theorem value1323 (q : Snake 81) : valuation q 1323 = decide (2 ≤ count1322 (baseVal q)) := rfl
theorem value1324 (q : Snake 81) : valuation q 1324 = decide (1 ≤ count1324 (baseVal q)) := rfl
theorem value1325 (q : Snake 81) : valuation q 1325 = decide (2 ≤ count1324 (baseVal q)) := rfl
theorem value1326 (q : Snake 81) : valuation q 1326 = decide (1 ≤ count1326 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (2 ≤ count1326 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (3 ≤ count1326 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (4 ≤ count1326 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (1 ≤ count1330 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (2 ≤ count1330 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (3 ≤ count1330 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (4 ≤ count1330 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (5 ≤ count1330 (baseVal q)) := rfl
theorem value1337 (q : Snake 81) : valuation q 1337 = decide (1 ≤ count1337 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (2 ≤ count1337 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (3 ≤ count1337 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (4 ≤ count1337 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (5 ≤ count1337 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (6 ≤ count1337 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (3 ≤ count1350 (baseVal q)) := rfl
theorem value1353 (q : Snake 81) : valuation q 1353 = decide (4 ≤ count1350 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (5 ≤ count1350 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (6 ≤ count1350 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (7 ≤ count1350 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (8 ≤ count1350 (baseVal q)) := rfl
theorem value1358 (q : Snake 81) : valuation q 1358 = decide (9 ≤ count1350 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (10 ≤ count1350 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (1 ≤ count1363 (baseVal q)) := rfl
theorem value1364 (q : Snake 81) : valuation q 1364 = decide (2 ≤ count1363 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (1 ≤ count1365 (baseVal q)) := rfl
theorem value1366 (q : Snake 81) : valuation q 1366 = decide (2 ≤ count1365 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (3 ≤ count1365 (baseVal q)) := rfl
theorem value1368 (q : Snake 81) : valuation q 1368 = decide (1 ≤ count1368 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (2 ≤ count1368 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (1 ≤ count1370 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (2 ≤ count1370 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (3 ≤ count1370 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (1 ≤ count1373 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (2 ≤ count1373 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (3 ≤ count1373 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (4 ≤ count1373 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (5 ≤ count1373 (baseVal q)) := rfl
theorem value1378 (q : Snake 81) : valuation q 1378 = decide (6 ≤ count1373 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (1 ≤ count1379 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (1 ≤ count1381 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (2 ≤ count1381 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (1 ≤ count1384 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (1 ≤ count1386 (baseVal q)) := rfl
theorem value1388 (q : Snake 81) : valuation q 1388 = decide (1 ≤ count1388 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (2 ≤ count1388 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (1 ≤ count1392 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (2 ≤ count1392 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (3 ≤ count1392 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (1 ≤ count1399 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (2 ≤ count1399 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (3 ≤ count1399 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (4 ≤ count1399 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (5 ≤ count1399 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (6 ≤ count1399 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (7 ≤ count1399 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (8 ≤ count1399 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (1 ≤ count1412 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (1 ≤ count1414 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (2 ≤ count1414 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (1 ≤ count1417 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (2 ≤ count1417 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (1 ≤ count1419 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (2 ≤ count1419 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (1 ≤ count1421 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (2 ≤ count1421 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (3 ≤ count1421 (baseVal q)) := rfl
theorem value1425 (q : Snake 81) : valuation q 1425 = decide (1 ≤ count1425 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (2 ≤ count1425 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (3 ≤ count1425 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (4 ≤ count1425 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (1 ≤ count1432 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (2 ≤ count1432 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (1 ≤ count1434 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (2 ≤ count1434 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (3 ≤ count1434 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (1 ≤ count1437 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (2 ≤ count1437 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (1 ≤ count1439 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (1 ≤ count1441 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (2 ≤ count1441 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (3 ≤ count1441 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (1 ≤ count1445 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (2 ≤ count1445 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (3 ≤ count1445 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (4 ≤ count1445 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (1 ≤ count1452 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (2 ≤ count1452 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (3 ≤ count1452 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (4 ≤ count1452 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (5 ≤ count1452 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (6 ≤ count1452 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (3 ≤ count1465 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (4 ≤ count1465 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (5 ≤ count1465 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (6 ≤ count1465 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (7 ≤ count1465 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (8 ≤ count1465 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (9 ≤ count1465 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (10 ≤ count1465 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (13 ≤ count1478 (baseVal q)) := rfl
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
theorem meaningNeg96 (b : Nat → Bool) : literal (valuationOf b) (-96) = decide (1 ≤ countLit b [-96]) := by
  change literal b (-96) = decide (1 ≤ countLit b [-96])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-96) <;> decide
theorem meaningNeg93 (b : Nat → Bool) : literal (valuationOf b) (-93) = decide (1 ≤ countLit b [-93]) := by
  change literal b (-93) = decide (1 ≤ countLit b [-93])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-93) <;> decide
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
theorem meaningNeg76 (b : Nat → Bool) : literal (valuationOf b) (-76) = decide (1 ≤ countLit b [-76]) := by
  change literal b (-76) = decide (1 ≤ countLit b [-76])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-76) <;> decide
theorem meaningNeg73 (b : Nat → Bool) : literal (valuationOf b) (-73) = decide (1 ≤ countLit b [-73]) := by
  change literal b (-73) = decide (1 ≤ countLit b [-73])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-73) <;> decide
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
theorem meaningNeg23 (b : Nat → Bool) : literal (valuationOf b) (-23) = decide (1 ≤ countLit b [-23]) := by
  change literal b (-23) = decide (1 ≤ countLit b [-23])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-23) <;> decide
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
theorem meaning108 (b : Nat → Bool) : literal (valuationOf b) (108) = decide (1 ≤ countLit b [108]) := by
  change literal b (108) = decide (1 ≤ countLit b [108])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (108) <;> decide
theorem meaning110 (b : Nat → Bool) : literal (valuationOf b) (110) = decide (1 ≤ countLit b [110]) := by
  change literal b (110) = decide (1 ≤ countLit b [110])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (110) <;> decide
theorem meaning113 (b : Nat → Bool) : literal (valuationOf b) (113) = decide (1 ≤ countLit b [113]) := by
  change literal b (113) = decide (1 ≤ countLit b [113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (113) <;> decide
theorem meaning114 (b : Nat → Bool) : literal (valuationOf b) (114) = decide (1 ≤ countLit b [114]) := by
  change literal b (114) = decide (1 ≤ countLit b [114])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (114) <;> decide
theorem meaning115 (b : Nat → Bool) : literal (valuationOf b) (115) = decide (1 ≤ countLit b [115]) := by
  change literal b (115) = decide (1 ≤ countLit b [115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (115) <;> decide
theorem meaning116 (b : Nat → Bool) : literal (valuationOf b) (116) = decide (1 ≤ countLit b [116]) := by
  change literal b (116) = decide (1 ≤ countLit b [116])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (116) <;> decide
theorem meaning117 (b : Nat → Bool) : literal (valuationOf b) (117) = decide (1 ≤ countLit b [117]) := by
  change literal b (117) = decide (1 ≤ countLit b [117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (117) <;> decide
theorem meaning120 (b : Nat → Bool) : literal (valuationOf b) (120) = decide (1 ≤ countLit b [120]) := by
  change literal b (120) = decide (1 ≤ countLit b [120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (120) <;> decide
theorem meaning121 (b : Nat → Bool) : literal (valuationOf b) (121) = decide (1 ≤ countLit b [121]) := by
  change literal b (121) = decide (1 ≤ countLit b [121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (121) <;> decide
theorem meaning124 (b : Nat → Bool) : literal (valuationOf b) (124) = decide (1 ≤ countLit b [124]) := by
  change literal b (124) = decide (1 ≤ countLit b [124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (124) <;> decide
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
theorem meaning135 (b : Nat → Bool) : literal (valuationOf b) (135) = decide (1 ≤ countLit b [135]) := by
  change literal b (135) = decide (1 ≤ countLit b [135])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (135) <;> decide
theorem meaning138 (b : Nat → Bool) : literal (valuationOf b) (138) = decide (1 ≤ countLit b [138]) := by
  change literal b (138) = decide (1 ≤ countLit b [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (138) <;> decide
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
theorem meaning146 (b : Nat → Bool) : literal (valuationOf b) (146) = decide (1 ≤ countLit b [146]) := by
  change literal b (146) = decide (1 ≤ countLit b [146])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (146) <;> decide
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
theorem meaning163 (b : Nat → Bool) : literal (valuationOf b) (163) = decide (1 ≤ countLit b [163]) := by
  change literal b (163) = decide (1 ≤ countLit b [163])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (163) <;> decide
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
theorem meaning179 (b : Nat → Bool) : literal (valuationOf b) (179) = decide (1 ≤ countLit b [179]) := by
  change literal b (179) = decide (1 ≤ countLit b [179])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (179) <;> decide
theorem meaning181 (b : Nat → Bool) : literal (valuationOf b) (181) = decide (1 ≤ countLit b [181]) := by
  change literal b (181) = decide (1 ≤ countLit b [181])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (181) <;> decide
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
theorem meaning187 (b : Nat → Bool) : literal (valuationOf b) (187) = decide (1 ≤ countLit b [187]) := by
  change literal b (187) = decide (1 ≤ countLit b [187])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (187) <;> decide
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
theorem meaning202 (b : Nat → Bool) : literal (valuationOf b) (202) = decide (1 ≤ countLit b [202]) := by
  change literal b (202) = decide (1 ≤ countLit b [202])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (202) <;> decide
theorem meaning204 (b : Nat → Bool) : literal (valuationOf b) (204) = decide (1 ≤ countLit b [204]) := by
  change literal b (204) = decide (1 ≤ countLit b [204])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (204) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning208 (b : Nat → Bool) : literal (valuationOf b) (208) = decide (1 ≤ countLit b [208]) := by
  change literal b (208) = decide (1 ≤ countLit b [208])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (208) <;> decide
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
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) 213 = decide (1 ≤ count213 b) := rfl
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) 215 = decide (1 ≤ count215 b) := rfl
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) 228 = decide (2 ≤ count227 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) 232 = decide (2 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning234 (b : Nat → Bool) : literal (valuationOf b) 234 = decide (2 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning236 (b : Nat → Bool) : literal (valuationOf b) 236 = decide (2 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) 240 = decide (2 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning246 (b : Nat → Bool) : literal (valuationOf b) 246 = decide (2 ≤ count245 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning260 (b : Nat → Bool) : literal (valuationOf b) 260 = decide (2 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning262 (b : Nat → Bool) : literal (valuationOf b) 262 = decide (2 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning286 (b : Nat → Bool) : literal (valuationOf b) 286 = decide (2 ≤ count285 b) := rfl
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
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning310 (b : Nat → Bool) : literal (valuationOf b) 310 = decide (2 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
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
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning364 (b : Nat → Bool) : literal (valuationOf b) 364 = decide (2 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning414 (b : Nat → Bool) : literal (valuationOf b) 414 = decide (2 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning418 (b : Nat → Bool) : literal (valuationOf b) 418 = decide (2 ≤ count417 b) := rfl
theorem meaning420 (b : Nat → Bool) : literal (valuationOf b) 420 = decide (2 ≤ count419 b) := rfl
theorem meaning1252 (b : Nat → Bool) : literal (valuationOf b) 1252 = decide (1 ≤ count1252 b) := rfl
theorem meaning1253 (b : Nat → Bool) : literal (valuationOf b) 1253 = decide (2 ≤ count1252 b) := rfl
theorem meaning1254 (b : Nat → Bool) : literal (valuationOf b) 1254 = decide (1 ≤ count1254 b) := rfl
theorem meaning1255 (b : Nat → Bool) : literal (valuationOf b) 1255 = decide (2 ≤ count1254 b) := rfl
theorem meaning1256 (b : Nat → Bool) : literal (valuationOf b) 1256 = decide (3 ≤ count1254 b) := rfl
theorem meaning1257 (b : Nat → Bool) : literal (valuationOf b) 1257 = decide (1 ≤ count1257 b) := rfl
theorem meaning1259 (b : Nat → Bool) : literal (valuationOf b) 1259 = decide (1 ≤ count1259 b) := rfl
theorem meaning1260 (b : Nat → Bool) : literal (valuationOf b) 1260 = decide (2 ≤ count1259 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (1 ≤ count1262 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (2 ≤ count1262 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (3 ≤ count1262 b) := rfl
theorem meaning1268 (b : Nat → Bool) : literal (valuationOf b) 1268 = decide (1 ≤ count1268 b) := rfl
theorem meaning1269 (b : Nat → Bool) : literal (valuationOf b) 1269 = decide (2 ≤ count1268 b) := rfl
theorem meaning1270 (b : Nat → Bool) : literal (valuationOf b) 1270 = decide (1 ≤ count1270 b) := rfl
theorem meaning1271 (b : Nat → Bool) : literal (valuationOf b) 1271 = decide (2 ≤ count1270 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (3 ≤ count1270 b) := rfl
theorem meaning1273 (b : Nat → Bool) : literal (valuationOf b) 1273 = decide (1 ≤ count1273 b) := rfl
theorem meaning1274 (b : Nat → Bool) : literal (valuationOf b) 1274 = decide (2 ≤ count1273 b) := rfl
theorem meaning1275 (b : Nat → Bool) : literal (valuationOf b) 1275 = decide (1 ≤ count1275 b) := rfl
theorem meaning1277 (b : Nat → Bool) : literal (valuationOf b) 1277 = decide (1 ≤ count1277 b) := rfl
theorem meaning1278 (b : Nat → Bool) : literal (valuationOf b) 1278 = decide (2 ≤ count1277 b) := rfl
theorem meaning1279 (b : Nat → Bool) : literal (valuationOf b) 1279 = decide (3 ≤ count1277 b) := rfl
theorem meaning1281 (b : Nat → Bool) : literal (valuationOf b) 1281 = decide (1 ≤ count1281 b) := rfl
theorem meaning1282 (b : Nat → Bool) : literal (valuationOf b) 1282 = decide (2 ≤ count1281 b) := rfl
theorem meaning1283 (b : Nat → Bool) : literal (valuationOf b) 1283 = decide (3 ≤ count1281 b) := rfl
theorem meaning1284 (b : Nat → Bool) : literal (valuationOf b) 1284 = decide (4 ≤ count1281 b) := rfl
theorem meaning1285 (b : Nat → Bool) : literal (valuationOf b) 1285 = decide (5 ≤ count1281 b) := rfl
theorem meaning1288 (b : Nat → Bool) : literal (valuationOf b) 1288 = decide (1 ≤ count1288 b) := rfl
theorem meaning1289 (b : Nat → Bool) : literal (valuationOf b) 1289 = decide (2 ≤ count1288 b) := rfl
theorem meaning1290 (b : Nat → Bool) : literal (valuationOf b) 1290 = decide (3 ≤ count1288 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (4 ≤ count1288 b) := rfl
theorem meaning1292 (b : Nat → Bool) : literal (valuationOf b) 1292 = decide (5 ≤ count1288 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (1 ≤ count1301 b) := rfl
theorem meaning1302 (b : Nat → Bool) : literal (valuationOf b) 1302 = decide (2 ≤ count1301 b) := rfl
theorem meaning1303 (b : Nat → Bool) : literal (valuationOf b) 1303 = decide (1 ≤ count1303 b) := rfl
theorem meaning1304 (b : Nat → Bool) : literal (valuationOf b) 1304 = decide (2 ≤ count1303 b) := rfl
theorem meaning1305 (b : Nat → Bool) : literal (valuationOf b) 1305 = decide (3 ≤ count1303 b) := rfl
theorem meaning1306 (b : Nat → Bool) : literal (valuationOf b) 1306 = decide (1 ≤ count1306 b) := rfl
theorem meaning1307 (b : Nat → Bool) : literal (valuationOf b) 1307 = decide (2 ≤ count1306 b) := rfl
theorem meaning1308 (b : Nat → Bool) : literal (valuationOf b) 1308 = decide (1 ≤ count1308 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (2 ≤ count1308 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (1 ≤ count1311 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (2 ≤ count1311 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (3 ≤ count1311 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (4 ≤ count1311 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (1 ≤ count1317 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (2 ≤ count1317 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (1 ≤ count1319 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (2 ≤ count1319 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (1 ≤ count1322 b) := rfl
theorem meaning1323 (b : Nat → Bool) : literal (valuationOf b) 1323 = decide (2 ≤ count1322 b) := rfl
theorem meaning1324 (b : Nat → Bool) : literal (valuationOf b) 1324 = decide (1 ≤ count1324 b) := rfl
theorem meaning1325 (b : Nat → Bool) : literal (valuationOf b) 1325 = decide (2 ≤ count1324 b) := rfl
theorem meaning1326 (b : Nat → Bool) : literal (valuationOf b) 1326 = decide (1 ≤ count1326 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (2 ≤ count1326 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (3 ≤ count1326 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (4 ≤ count1326 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (1 ≤ count1330 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (2 ≤ count1330 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (3 ≤ count1330 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (4 ≤ count1330 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (5 ≤ count1330 b) := rfl
theorem meaning1337 (b : Nat → Bool) : literal (valuationOf b) 1337 = decide (1 ≤ count1337 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (2 ≤ count1337 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (3 ≤ count1337 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (4 ≤ count1337 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (5 ≤ count1337 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (6 ≤ count1337 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (3 ≤ count1350 b) := rfl
theorem meaning1353 (b : Nat → Bool) : literal (valuationOf b) 1353 = decide (4 ≤ count1350 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (5 ≤ count1350 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (6 ≤ count1350 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (7 ≤ count1350 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (8 ≤ count1350 b) := rfl
theorem meaning1358 (b : Nat → Bool) : literal (valuationOf b) 1358 = decide (9 ≤ count1350 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (10 ≤ count1350 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (1 ≤ count1363 b) := rfl
theorem meaning1364 (b : Nat → Bool) : literal (valuationOf b) 1364 = decide (2 ≤ count1363 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (1 ≤ count1365 b) := rfl
theorem meaning1366 (b : Nat → Bool) : literal (valuationOf b) 1366 = decide (2 ≤ count1365 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (3 ≤ count1365 b) := rfl
theorem meaning1368 (b : Nat → Bool) : literal (valuationOf b) 1368 = decide (1 ≤ count1368 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (2 ≤ count1368 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (1 ≤ count1370 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (2 ≤ count1370 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (3 ≤ count1370 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (1 ≤ count1373 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (2 ≤ count1373 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (3 ≤ count1373 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (4 ≤ count1373 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (5 ≤ count1373 b) := rfl
theorem meaning1378 (b : Nat → Bool) : literal (valuationOf b) 1378 = decide (6 ≤ count1373 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (1 ≤ count1379 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (1 ≤ count1381 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (2 ≤ count1381 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (1 ≤ count1384 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (1 ≤ count1386 b) := rfl
theorem meaning1388 (b : Nat → Bool) : literal (valuationOf b) 1388 = decide (1 ≤ count1388 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (2 ≤ count1388 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (1 ≤ count1392 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (2 ≤ count1392 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (3 ≤ count1392 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (1 ≤ count1399 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (2 ≤ count1399 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (3 ≤ count1399 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (4 ≤ count1399 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (5 ≤ count1399 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (6 ≤ count1399 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (7 ≤ count1399 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (8 ≤ count1399 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (1 ≤ count1412 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (1 ≤ count1414 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (2 ≤ count1414 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (1 ≤ count1417 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (2 ≤ count1417 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (1 ≤ count1419 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (2 ≤ count1419 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (1 ≤ count1421 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (2 ≤ count1421 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (3 ≤ count1421 b) := rfl
theorem meaning1425 (b : Nat → Bool) : literal (valuationOf b) 1425 = decide (1 ≤ count1425 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (2 ≤ count1425 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (3 ≤ count1425 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (4 ≤ count1425 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (1 ≤ count1432 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (2 ≤ count1432 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (1 ≤ count1434 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (2 ≤ count1434 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (3 ≤ count1434 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (1 ≤ count1437 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (2 ≤ count1437 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (1 ≤ count1439 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (1 ≤ count1441 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (2 ≤ count1441 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (3 ≤ count1441 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (1 ≤ count1445 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (2 ≤ count1445 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (3 ≤ count1445 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (4 ≤ count1445 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (1 ≤ count1452 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (2 ≤ count1452 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (3 ≤ count1452 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (4 ≤ count1452 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (5 ≤ count1452 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (6 ≤ count1452 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (3 ≤ count1465 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (4 ≤ count1465 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (5 ≤ count1465 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (6 ≤ count1465 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (7 ≤ count1465 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (8 ≤ count1465 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (9 ≤ count1465 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (10 ≤ count1465 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (13 ≤ count1478 b) := rfl
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
end Snake9.Regrowth.E112091
