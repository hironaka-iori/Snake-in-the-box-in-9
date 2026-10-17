import E112040Data
namespace Snake9.Regrowth.E112040
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 120 then (if i < 60 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (34 : Vertex)) else decide (InPath q (36 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (37 : Vertex)) else decide (InPath q (38 : Vertex))) else (if i < 6 then decide (InPath q (40 : Vertex)) else decide (InPath q (41 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (42 : Vertex)) else decide (InPath q (43 : Vertex))) else (if i < 10 then decide (InPath q (44 : Vertex)) else decide (InPath q (46 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (48 : Vertex)) else decide (InPath q (49 : Vertex))) else (if i < 14 then decide (InPath q (51 : Vertex)) else decide (InPath q (53 : Vertex)))))) else (if i < 22 then (if i < 18 then (if i < 16 then decide (InPath q (55 : Vertex)) else (if i < 17 then decide (InPath q (56 : Vertex)) else decide (InPath q (57 : Vertex)))) else (if i < 20 then (if i < 19 then decide (InPath q (62 : Vertex)) else decide (InPath q (63 : Vertex))) else (if i < 21 then decide (InPath q (96 : Vertex)) else decide (InPath q (97 : Vertex))))) else (if i < 26 then (if i < 24 then (if i < 23 then decide (InPath q (98 : Vertex)) else decide (InPath q (99 : Vertex))) else (if i < 25 then decide (InPath q (103 : Vertex)) else decide (InPath q (105 : Vertex)))) else (if i < 28 then (if i < 27 then decide (InPath q (107 : Vertex)) else decide (InPath q (108 : Vertex))) else (if i < 29 then decide (InPath q (109 : Vertex)) else decide (InPath q (111 : Vertex))))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then decide (InPath q (112 : Vertex)) else (if i < 32 then decide (InPath q (114 : Vertex)) else decide (InPath q (115 : Vertex)))) else (if i < 35 then (if i < 34 then decide (InPath q (116 : Vertex)) else decide (InPath q (118 : Vertex))) else (if i < 36 then decide (InPath q (119 : Vertex)) else decide (InPath q (120 : Vertex))))) else (if i < 41 then (if i < 39 then (if i < 38 then decide (InPath q (121 : Vertex)) else decide (InPath q (122 : Vertex))) else (if i < 40 then decide (InPath q (124 : Vertex)) else decide (InPath q (125 : Vertex)))) else (if i < 43 then (if i < 42 then decide (InPath q (126 : Vertex)) else decide (InPath q (127 : Vertex))) else (if i < 44 then decide (InPath q (160 : Vertex)) else decide (InPath q (161 : Vertex)))))) else (if i < 52 then (if i < 48 then (if i < 46 then decide (InPath q (163 : Vertex)) else (if i < 47 then decide (InPath q (167 : Vertex)) else decide (InPath q (168 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (173 : Vertex)) else decide (InPath q (175 : Vertex))) else (if i < 51 then decide (InPath q (176 : Vertex)) else decide (InPath q (178 : Vertex))))) else (if i < 56 then (if i < 54 then (if i < 53 then decide (InPath q (179 : Vertex)) else decide (InPath q (180 : Vertex))) else (if i < 55 then decide (InPath q (182 : Vertex)) else decide (InPath q (184 : Vertex)))) else (if i < 58 then (if i < 57 then decide (InPath q (186 : Vertex)) else decide (InPath q (187 : Vertex))) else (if i < 59 then decide (InPath q (188 : Vertex)) else decide (InPath q (189 : Vertex)))))))) else (if i < 90 then (if i < 75 then (if i < 67 then (if i < 63 then (if i < 61 then decide (InPath q (228 : Vertex)) else (if i < 62 then decide (InPath q (229 : Vertex)) else decide (InPath q (230 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (233 : Vertex)) else decide (InPath q (234 : Vertex))) else (if i < 66 then decide (InPath q (235 : Vertex)) else decide (InPath q (238 : Vertex))))) else (if i < 71 then (if i < 69 then (if i < 68 then decide (InPath q (240 : Vertex)) else decide (InPath q (243 : Vertex))) else (if i < 70 then decide (InPath q (245 : Vertex)) else decide (InPath q (247 : Vertex)))) else (if i < 73 then (if i < 72 then decide (InPath q (248 : Vertex)) else decide (InPath q (249 : Vertex))) else (if i < 74 then decide (InPath q (254 : Vertex)) else decide (InPath q (255 : Vertex)))))) else (if i < 82 then (if i < 78 then (if i < 76 then decide (InPath q (288 : Vertex)) else (if i < 77 then decide (InPath q (289 : Vertex)) else decide (InPath q (290 : Vertex)))) else (if i < 80 then (if i < 79 then decide (InPath q (291 : Vertex)) else decide (InPath q (295 : Vertex))) else (if i < 81 then decide (InPath q (296 : Vertex)) else decide (InPath q (300 : Vertex))))) else (if i < 86 then (if i < 84 then (if i < 83 then decide (InPath q (301 : Vertex)) else decide (InPath q (303 : Vertex))) else (if i < 85 then decide (InPath q (306 : Vertex)) else decide (InPath q (307 : Vertex)))) else (if i < 88 then (if i < 87 then decide (InPath q (308 : Vertex)) else decide (InPath q (310 : Vertex))) else (if i < 89 then decide (InPath q (314 : Vertex)) else decide (InPath q (315 : Vertex))))))) else (if i < 105 then (if i < 97 then (if i < 93 then (if i < 91 then decide (InPath q (316 : Vertex)) else (if i < 92 then decide (InPath q (317 : Vertex)) else decide (InPath q (352 : Vertex)))) else (if i < 95 then (if i < 94 then decide (InPath q (356 : Vertex)) else decide (InPath q (357 : Vertex))) else (if i < 96 then decide (InPath q (358 : Vertex)) else decide (InPath q (359 : Vertex))))) else (if i < 101 then (if i < 99 then (if i < 98 then decide (InPath q (360 : Vertex)) else decide (InPath q (361 : Vertex))) else (if i < 100 then decide (InPath q (362 : Vertex)) else decide (InPath q (363 : Vertex)))) else (if i < 103 then (if i < 102 then decide (InPath q (366 : Vertex)) else decide (InPath q (368 : Vertex))) else (if i < 104 then decide (InPath q (371 : Vertex)) else decide (InPath q (373 : Vertex)))))) else (if i < 112 then (if i < 108 then (if i < 106 then decide (InPath q (375 : Vertex)) else (if i < 107 then decide (InPath q (376 : Vertex)) else decide (InPath q (377 : Vertex)))) else (if i < 110 then (if i < 109 then decide (InPath q (378 : Vertex)) else decide (InPath q (379 : Vertex))) else (if i < 111 then decide (InPath q (381 : Vertex)) else decide (InPath q (382 : Vertex))))) else (if i < 116 then (if i < 114 then (if i < 113 then decide (InPath q (424 : Vertex)) else decide (InPath q (425 : Vertex))) else (if i < 115 then decide (InPath q (427 : Vertex)) else decide (InPath q (440 : Vertex)))) else (if i < 118 then (if i < 117 then decide (InPath q (443 : Vertex)) else decide (InPath q (493 : Vertex))) else (if i < 119 then decide (InPath q (495 : Vertex)) else decide (InPath q (507 : Vertex))))))))) else (if i < 180 then (if i < 150 then (if i < 135 then (if i < 127 then (if i < 123 then (if i < 121 then decide (InPath q (511 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (34 : Vertex)) else decide (BallClauseLogic.Endpoint q (36 : Vertex)))) else (if i < 125 then (if i < 124 then decide (BallClauseLogic.Endpoint q (37 : Vertex)) else decide (BallClauseLogic.Endpoint q (38 : Vertex))) else (if i < 126 then decide (BallClauseLogic.Endpoint q (40 : Vertex)) else decide (BallClauseLogic.Endpoint q (41 : Vertex))))) else (if i < 131 then (if i < 129 then (if i < 128 then decide (BallClauseLogic.Endpoint q (42 : Vertex)) else decide (BallClauseLogic.Endpoint q (43 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (44 : Vertex)) else decide (BallClauseLogic.Endpoint q (46 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (48 : Vertex)) else decide (BallClauseLogic.Endpoint q (49 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (51 : Vertex)) else decide (BallClauseLogic.Endpoint q (53 : Vertex)))))) else (if i < 142 then (if i < 138 then (if i < 136 then decide (BallClauseLogic.Endpoint q (55 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (56 : Vertex)) else decide (BallClauseLogic.Endpoint q (57 : Vertex)))) else (if i < 140 then (if i < 139 then decide (BallClauseLogic.Endpoint q (62 : Vertex)) else decide (BallClauseLogic.Endpoint q (63 : Vertex))) else (if i < 141 then decide (BallClauseLogic.Endpoint q (96 : Vertex)) else decide (BallClauseLogic.Endpoint q (97 : Vertex))))) else (if i < 146 then (if i < 144 then (if i < 143 then decide (BallClauseLogic.Endpoint q (98 : Vertex)) else decide (BallClauseLogic.Endpoint q (99 : Vertex))) else (if i < 145 then decide (BallClauseLogic.Endpoint q (103 : Vertex)) else decide (BallClauseLogic.Endpoint q (105 : Vertex)))) else (if i < 148 then (if i < 147 then decide (BallClauseLogic.Endpoint q (107 : Vertex)) else decide (BallClauseLogic.Endpoint q (108 : Vertex))) else (if i < 149 then decide (BallClauseLogic.Endpoint q (109 : Vertex)) else decide (BallClauseLogic.Endpoint q (111 : Vertex))))))) else (if i < 165 then (if i < 157 then (if i < 153 then (if i < 151 then decide (BallClauseLogic.Endpoint q (112 : Vertex)) else (if i < 152 then decide (BallClauseLogic.Endpoint q (114 : Vertex)) else decide (BallClauseLogic.Endpoint q (115 : Vertex)))) else (if i < 155 then (if i < 154 then decide (BallClauseLogic.Endpoint q (116 : Vertex)) else decide (BallClauseLogic.Endpoint q (118 : Vertex))) else (if i < 156 then decide (BallClauseLogic.Endpoint q (119 : Vertex)) else decide (BallClauseLogic.Endpoint q (120 : Vertex))))) else (if i < 161 then (if i < 159 then (if i < 158 then decide (BallClauseLogic.Endpoint q (121 : Vertex)) else decide (BallClauseLogic.Endpoint q (122 : Vertex))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (124 : Vertex)) else decide (BallClauseLogic.Endpoint q (125 : Vertex)))) else (if i < 163 then (if i < 162 then decide (BallClauseLogic.Endpoint q (126 : Vertex)) else decide (BallClauseLogic.Endpoint q (127 : Vertex))) else (if i < 164 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (161 : Vertex)))))) else (if i < 172 then (if i < 168 then (if i < 166 then decide (BallClauseLogic.Endpoint q (163 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (167 : Vertex)) else decide (BallClauseLogic.Endpoint q (168 : Vertex)))) else (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (173 : Vertex)) else decide (BallClauseLogic.Endpoint q (175 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (176 : Vertex)) else decide (BallClauseLogic.Endpoint q (178 : Vertex))))) else (if i < 176 then (if i < 174 then (if i < 173 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (180 : Vertex))) else (if i < 175 then decide (BallClauseLogic.Endpoint q (182 : Vertex)) else decide (BallClauseLogic.Endpoint q (184 : Vertex)))) else (if i < 178 then (if i < 177 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (187 : Vertex))) else (if i < 179 then decide (BallClauseLogic.Endpoint q (188 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex)))))))) else (if i < 210 then (if i < 195 then (if i < 187 then (if i < 183 then (if i < 181 then decide (BallClauseLogic.Endpoint q (228 : Vertex)) else (if i < 182 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (230 : Vertex)))) else (if i < 185 then (if i < 184 then decide (BallClauseLogic.Endpoint q (233 : Vertex)) else decide (BallClauseLogic.Endpoint q (234 : Vertex))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (235 : Vertex)) else decide (BallClauseLogic.Endpoint q (238 : Vertex))))) else (if i < 191 then (if i < 189 then (if i < 188 then decide (BallClauseLogic.Endpoint q (240 : Vertex)) else decide (BallClauseLogic.Endpoint q (243 : Vertex))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else decide (BallClauseLogic.Endpoint q (247 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (248 : Vertex)) else decide (BallClauseLogic.Endpoint q (249 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (254 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex)))))) else (if i < 202 then (if i < 198 then (if i < 196 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (289 : Vertex)) else decide (BallClauseLogic.Endpoint q (290 : Vertex)))) else (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (291 : Vertex)) else decide (BallClauseLogic.Endpoint q (295 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else decide (BallClauseLogic.Endpoint q (300 : Vertex))))) else (if i < 206 then (if i < 204 then (if i < 203 then decide (BallClauseLogic.Endpoint q (301 : Vertex)) else decide (BallClauseLogic.Endpoint q (303 : Vertex))) else (if i < 205 then decide (BallClauseLogic.Endpoint q (306 : Vertex)) else decide (BallClauseLogic.Endpoint q (307 : Vertex)))) else (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (308 : Vertex)) else decide (BallClauseLogic.Endpoint q (310 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (314 : Vertex)) else decide (BallClauseLogic.Endpoint q (315 : Vertex))))))) else (if i < 225 then (if i < 217 then (if i < 213 then (if i < 211 then decide (BallClauseLogic.Endpoint q (316 : Vertex)) else (if i < 212 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (352 : Vertex)))) else (if i < 215 then (if i < 214 then decide (BallClauseLogic.Endpoint q (356 : Vertex)) else decide (BallClauseLogic.Endpoint q (357 : Vertex))) else (if i < 216 then decide (BallClauseLogic.Endpoint q (358 : Vertex)) else decide (BallClauseLogic.Endpoint q (359 : Vertex))))) else (if i < 221 then (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (360 : Vertex)) else decide (BallClauseLogic.Endpoint q (361 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (362 : Vertex)) else decide (BallClauseLogic.Endpoint q (363 : Vertex)))) else (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (366 : Vertex)) else decide (BallClauseLogic.Endpoint q (368 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (371 : Vertex)) else decide (BallClauseLogic.Endpoint q (373 : Vertex)))))) else (if i < 233 then (if i < 229 then (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (375 : Vertex)) else decide (BallClauseLogic.Endpoint q (376 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (377 : Vertex)) else decide (BallClauseLogic.Endpoint q (378 : Vertex)))) else (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (379 : Vertex)) else decide (BallClauseLogic.Endpoint q (381 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (382 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex))))) else (if i < 237 then (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else decide (BallClauseLogic.Endpoint q (443 : Vertex)))) else (if i < 239 then (if i < 238 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else decide (BallClauseLogic.Endpoint q (495 : Vertex))) else (if i < 240 then decide (BallClauseLogic.Endpoint q (507 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count241 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count243 (b : Nat → Bool) : Nat := countLit b [121, 122, 123]
def count245 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count247 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127]
def count253 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [128, 129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count289 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145, 146, 147, 148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
def count295 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [150, 151, 152]
def count301 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156]
def count307 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156]
def count309 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count313 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160]
def count315 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count319 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171]
def count337 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count347 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179]
def count349 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 178, 179]
def count351 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]
def count353 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]
def count355 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]
def count357 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [180, 181, 182]
def count361 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count363 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count365 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186]
def count367 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185, 186]
def count369 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193, 194]
def count383 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]
def count385 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [195, 196, 197]
def count389 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count391 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201]
def count395 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198, 199, 200, 201]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205]
def count403 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205, 206, 207, 208, 209]
def count411 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]
def count413 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]
def count415 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [210, 211, 212]
def count419 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count421 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216]
def count425 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213, 214, 215, 216]
def count427 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count429 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220]
def count433 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220, 221, 222, 223, 224]
def count441 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]
def count443 (b : Nat → Bool) : Nat := countLit b [226, 227]
def count445 (b : Nat → Bool) : Nat := countLit b [225, 226, 227]
def count447 (b : Nat → Bool) : Nat := countLit b [228, 229]
def count449 (b : Nat → Bool) : Nat := countLit b [230, 231]
def count451 (b : Nat → Bool) : Nat := countLit b [228, 229, 230, 231]
def count453 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228, 229, 230, 231]
def count455 (b : Nat → Bool) : Nat := countLit b [232, 233]
def count457 (b : Nat → Bool) : Nat := countLit b [234, 235]
def count459 (b : Nat → Bool) : Nat := countLit b [232, 233, 234, 235]
def count461 (b : Nat → Bool) : Nat := countLit b [236, 238]
def count463 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count465 (b : Nat → Bool) : Nat := countLit b [236, 238, 239, 240]
def count467 (b : Nat → Bool) : Nat := countLit b [232, 233, 234, 235, 236, 238, 239, 240]
def count469 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]
def count471 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]
def count473 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]
def count475 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 238, 239, 240]
def count477 (b : Nat → Bool) : Nat := countLit b [2, 5]
def count479 (b : Nat → Bool) : Nat := countLit b [1, 2, 5]
def count482 (b : Nat → Bool) : Nat := countLit b [8, 10]
def count484 (b : Nat → Bool) : Nat := countLit b [11, 13]
def count486 (b : Nat → Bool) : Nat := countLit b [8, 10, 11, 13]
def count490 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 11, 13]
def count497 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count499 (b : Nat → Bool) : Nat := countLit b [14, 17, 19]
def count502 (b : Nat → Bool) : Nat := countLit b [20, 23]
def count504 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count506 (b : Nat → Bool) : Nat := countLit b [20, 23, 25, 27]
def count510 (b : Nat → Bool) : Nat := countLit b [14, 17, 19, 20, 23, 25, 27]
def count517 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 11, 13, 14, 17, 19, 20, 23, 25, 27]
def count531 (b : Nat → Bool) : Nat := countLit b [31, 33]
def count533 (b : Nat → Bool) : Nat := countLit b [29, 31, 33]
def count536 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count538 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count540 (b : Nat → Bool) : Nat := countLit b [35, 36, 40, 41]
def count544 (b : Nat → Bool) : Nat := countLit b [29, 31, 33, 35, 36, 40, 41]
def count551 (b : Nat → Bool) : Nat := countLit b [43, 45]
def count553 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count555 (b : Nat → Bool) : Nat := countLit b [43, 45, 49, 51]
def count559 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count561 (b : Nat → Bool) : Nat := countLit b [57, 59]
def count563 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 59]
def count567 (b : Nat → Bool) : Nat := countLit b [43, 45, 49, 51, 53, 55, 57, 59]
def count575 (b : Nat → Bool) : Nat := countLit b [29, 31, 33, 35, 36, 40, 41, 43, 45, 49, 51, 53, 55, 57, 59]
def count590 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 11, 13, 14, 17, 19, 20, 23, 25, 27, 29, 31, 33, 35, 36, 40, 41, 43, 45, 49, 51, 53, 55, 57, 59]
def count619 (b : Nat → Bool) : Nat := countLit b [65, 66]
def count621 (b : Nat → Bool) : Nat := countLit b [60, 65, 66]
def count624 (b : Nat → Bool) : Nat := countLit b [67, 68]
def count626 (b : Nat → Bool) : Nat := countLit b [69, 72]
def count628 (b : Nat → Bool) : Nat := countLit b [67, 68, 69, 72]
def count632 (b : Nat → Bool) : Nat := countLit b [60, 65, 66, 67, 68, 69, 72]
def count639 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count641 (b : Nat → Bool) : Nat := countLit b [78, 81]
def count643 (b : Nat → Bool) : Nat := countLit b [74, 75, 78, 81]
def count647 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count649 (b : Nat → Bool) : Nat := countLit b [86, 89]
def count651 (b : Nat → Bool) : Nat := countLit b [83, 84, 86, 89]
def count655 (b : Nat → Bool) : Nat := countLit b [74, 75, 78, 81, 83, 84, 86, 89]
def count663 (b : Nat → Bool) : Nat := countLit b [60, 65, 66, 67, 68, 69, 72, 74, 75, 78, 81, 83, 84, 86, 89]
def count678 (b : Nat → Bool) : Nat := countLit b [93, 96]
def count680 (b : Nat → Bool) : Nat := countLit b [91, 93, 96]
def count683 (b : Nat → Bool) : Nat := countLit b [97, 100]
def count685 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count687 (b : Nat → Bool) : Nat := countLit b [97, 100, 101, 102]
def count691 (b : Nat → Bool) : Nat := countLit b [91, 93, 96, 97, 100, 101, 102]
def count698 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count700 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count702 (b : Nat → Bool) : Nat := countLit b [103, 104, 107, 108]
def count706 (b : Nat → Bool) : Nat := countLit b [112, 114]
def count708 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count710 (b : Nat → Bool) : Nat := countLit b [112, 114, 118, 119]
def count714 (b : Nat → Bool) : Nat := countLit b [103, 104, 107, 108, 112, 114, 118, 119]
def count722 (b : Nat → Bool) : Nat := countLit b [91, 93, 96, 97, 100, 101, 102, 103, 104, 107, 108, 112, 114, 118, 119]
def count737 (b : Nat → Bool) : Nat := countLit b [60, 65, 66, 67, 68, 69, 72, 74, 75, 78, 81, 83, 84, 86, 89, 91, 93, 96, 97, 100, 101, 102, 103, 104, 107, 108, 112, 114, 118, 119]
def count767 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 11, 13, 14, 17, 19, 20, 23, 25, 27, 29, 31, 33, 35, 36, 40, 41, 43, 45, 49, 51, 53, 55, 57, 59, 60, 65, 66, 67, 68, 69, 72, 74, 75, 78, 81, 83, 84, 86, 89, 91, 93, 96, 97, 100, 101, 102, 103, 104, 107, 108, 112, 114, 118, 119]
def count809 (b : Nat → Bool) : Nat := countLit b [-2, -5]
def count811 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5]
def count814 (b : Nat → Bool) : Nat := countLit b [-8, -10]
def count816 (b : Nat → Bool) : Nat := countLit b [-11, -13]
def count818 (b : Nat → Bool) : Nat := countLit b [-8, -10, -11, -13]
def count822 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -11, -13]
def count829 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count831 (b : Nat → Bool) : Nat := countLit b [-14, -17, -19]
def count834 (b : Nat → Bool) : Nat := countLit b [-20, -23]
def count836 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count838 (b : Nat → Bool) : Nat := countLit b [-20, -23, -25, -27]
def count842 (b : Nat → Bool) : Nat := countLit b [-14, -17, -19, -20, -23, -25, -27]
def count849 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27]
def count863 (b : Nat → Bool) : Nat := countLit b [-31, -33]
def count865 (b : Nat → Bool) : Nat := countLit b [-29, -31, -33]
def count868 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count870 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count872 (b : Nat → Bool) : Nat := countLit b [-35, -36, -40, -41]
def count876 (b : Nat → Bool) : Nat := countLit b [-29, -31, -33, -35, -36, -40, -41]
def count883 (b : Nat → Bool) : Nat := countLit b [-43, -45]
def count885 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count887 (b : Nat → Bool) : Nat := countLit b [-43, -45, -49, -51]
def count891 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count893 (b : Nat → Bool) : Nat := countLit b [-57, -59]
def count895 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -59]
def count899 (b : Nat → Bool) : Nat := countLit b [-43, -45, -49, -51, -53, -55, -57, -59]
def count907 (b : Nat → Bool) : Nat := countLit b [-29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59]
def count922 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27, -29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59]
def count941 (b : Nat → Bool) : Nat := countLit b [-65, -66]
def count943 (b : Nat → Bool) : Nat := countLit b [-60, -65, -66]
def count946 (b : Nat → Bool) : Nat := countLit b [-67, -68]
def count948 (b : Nat → Bool) : Nat := countLit b [-69, -72]
def count950 (b : Nat → Bool) : Nat := countLit b [-67, -68, -69, -72]
def count954 (b : Nat → Bool) : Nat := countLit b [-60, -65, -66, -67, -68, -69, -72]
def count961 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count963 (b : Nat → Bool) : Nat := countLit b [-78, -81]
def count965 (b : Nat → Bool) : Nat := countLit b [-74, -75, -78, -81]
def count969 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count971 (b : Nat → Bool) : Nat := countLit b [-86, -89]
def count973 (b : Nat → Bool) : Nat := countLit b [-83, -84, -86, -89]
def count977 (b : Nat → Bool) : Nat := countLit b [-74, -75, -78, -81, -83, -84, -86, -89]
def count985 (b : Nat → Bool) : Nat := countLit b [-60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89]
def count1000 (b : Nat → Bool) : Nat := countLit b [-93, -96]
def count1002 (b : Nat → Bool) : Nat := countLit b [-91, -93, -96]
def count1005 (b : Nat → Bool) : Nat := countLit b [-97, -100]
def count1007 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count1009 (b : Nat → Bool) : Nat := countLit b [-97, -100, -101, -102]
def count1013 (b : Nat → Bool) : Nat := countLit b [-91, -93, -96, -97, -100, -101, -102]
def count1020 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1022 (b : Nat → Bool) : Nat := countLit b [-107, -108]
def count1024 (b : Nat → Bool) : Nat := countLit b [-103, -104, -107, -108]
def count1028 (b : Nat → Bool) : Nat := countLit b [-112, -114]
def count1030 (b : Nat → Bool) : Nat := countLit b [-118, -119]
def count1032 (b : Nat → Bool) : Nat := countLit b [-112, -114, -118, -119]
def count1036 (b : Nat → Bool) : Nat := countLit b [-103, -104, -107, -108, -112, -114, -118, -119]
def count1044 (b : Nat → Bool) : Nat := countLit b [-91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119]
def count1059 (b : Nat → Bool) : Nat := countLit b [-60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89, -91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119]
def count1078 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27, -29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59, -60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89, -91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119]
def count1097 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count1099 (b : Nat → Bool) : Nat := countLit b [3, 4, 6]
def count1102 (b : Nat → Bool) : Nat := countLit b [7, 9]
def count1104 (b : Nat → Bool) : Nat := countLit b [12, 15]
def count1106 (b : Nat → Bool) : Nat := countLit b [7, 9, 12, 15]
def count1110 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 12, 15]
def count1117 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count1119 (b : Nat → Bool) : Nat := countLit b [21, 22]
def count1121 (b : Nat → Bool) : Nat := countLit b [16, 18, 21, 22]
def count1125 (b : Nat → Bool) : Nat := countLit b [24, 26]
def count1127 (b : Nat → Bool) : Nat := countLit b [28, 30]
def count1129 (b : Nat → Bool) : Nat := countLit b [24, 26, 28, 30]
def count1133 (b : Nat → Bool) : Nat := countLit b [16, 18, 21, 22, 24, 26, 28, 30]
def count1141 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 12, 15, 16, 18, 21, 22, 24, 26, 28, 30]
def count1156 (b : Nat → Bool) : Nat := countLit b [34, 37]
def count1158 (b : Nat → Bool) : Nat := countLit b [32, 34, 37]
def count1161 (b : Nat → Bool) : Nat := countLit b [38, 39]
def count1163 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count1165 (b : Nat → Bool) : Nat := countLit b [38, 39, 42, 44]
def count1169 (b : Nat → Bool) : Nat := countLit b [32, 34, 37, 38, 39, 42, 44]
def count1176 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count1178 (b : Nat → Bool) : Nat := countLit b [48, 50]
def count1180 (b : Nat → Bool) : Nat := countLit b [46, 47, 48, 50]
def count1184 (b : Nat → Bool) : Nat := countLit b [52, 54]
def count1186 (b : Nat → Bool) : Nat := countLit b [56, 58]
def count1188 (b : Nat → Bool) : Nat := countLit b [52, 54, 56, 58]
def count1192 (b : Nat → Bool) : Nat := countLit b [46, 47, 48, 50, 52, 54, 56, 58]
def count1200 (b : Nat → Bool) : Nat := countLit b [32, 34, 37, 38, 39, 42, 44, 46, 47, 48, 50, 52, 54, 56, 58]
def count1215 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 12, 15, 16, 18, 21, 22, 24, 26, 28, 30, 32, 34, 37, 38, 39, 42, 44, 46, 47, 48, 50, 52, 54, 56, 58]
def count1245 (b : Nat → Bool) : Nat := countLit b [62, 63]
def count1247 (b : Nat → Bool) : Nat := countLit b [61, 62, 63]
def count1250 (b : Nat → Bool) : Nat := countLit b [64, 70]
def count1252 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count1254 (b : Nat → Bool) : Nat := countLit b [64, 70, 71, 73]
def count1258 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 64, 70, 71, 73]
def count1265 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count1267 (b : Nat → Bool) : Nat := countLit b [79, 80]
def count1269 (b : Nat → Bool) : Nat := countLit b [76, 77, 79, 80]
def count1273 (b : Nat → Bool) : Nat := countLit b [82, 85]
def count1275 (b : Nat → Bool) : Nat := countLit b [87, 88]
def count1277 (b : Nat → Bool) : Nat := countLit b [82, 85, 87, 88]
def count1281 (b : Nat → Bool) : Nat := countLit b [76, 77, 79, 80, 82, 85, 87, 88]
def count1289 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 64, 70, 71, 73, 76, 77, 79, 80, 82, 85, 87, 88]
def count1304 (b : Nat → Bool) : Nat := countLit b [90, 92]
def count1306 (b : Nat → Bool) : Nat := countLit b [94, 95]
def count1308 (b : Nat → Bool) : Nat := countLit b [90, 92, 94, 95]
def count1312 (b : Nat → Bool) : Nat := countLit b [98, 99]
def count1314 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count1316 (b : Nat → Bool) : Nat := countLit b [98, 99, 105, 106]
def count1320 (b : Nat → Bool) : Nat := countLit b [90, 92, 94, 95, 98, 99, 105, 106]
def count1328 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count1330 (b : Nat → Bool) : Nat := countLit b [111, 113]
def count1332 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 113]
def count1336 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count1338 (b : Nat → Bool) : Nat := countLit b [117, 120]
def count1340 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 120]
def count1344 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 113, 115, 116, 117, 120]
def count1352 (b : Nat → Bool) : Nat := countLit b [90, 92, 94, 95, 98, 99, 105, 106, 109, 110, 111, 113, 115, 116, 117, 120]
def count1368 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 64, 70, 71, 73, 76, 77, 79, 80, 82, 85, 87, 88, 90, 92, 94, 95, 98, 99, 105, 106, 109, 110, 111, 113, 115, 116, 117, 120]
def count1399 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 12, 15, 16, 18, 21, 22, 24, 26, 28, 30, 32, 34, 37, 38, 39, 42, 44, 46, 47, 48, 50, 52, 54, 56, 58, 61, 62, 63, 64, 70, 71, 73, 76, 77, 79, 80, 82, 85, 87, 88, 90, 92, 94, 95, 98, 99, 105, 106, 109, 110, 111, 113, 115, 116, 117, 120]
def count1441 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count1443 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6]
def count1446 (b : Nat → Bool) : Nat := countLit b [-7, -9]
def count1448 (b : Nat → Bool) : Nat := countLit b [-12, -15]
def count1450 (b : Nat → Bool) : Nat := countLit b [-7, -9, -12, -15]
def count1454 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -12, -15]
def count1461 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1463 (b : Nat → Bool) : Nat := countLit b [-21, -22]
def count1465 (b : Nat → Bool) : Nat := countLit b [-16, -18, -21, -22]
def count1469 (b : Nat → Bool) : Nat := countLit b [-24, -26]
def count1471 (b : Nat → Bool) : Nat := countLit b [-28, -30]
def count1473 (b : Nat → Bool) : Nat := countLit b [-24, -26, -28, -30]
def count1477 (b : Nat → Bool) : Nat := countLit b [-16, -18, -21, -22, -24, -26, -28, -30]
def count1485 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]
def count1500 (b : Nat → Bool) : Nat := countLit b [-34, -37]
def count1502 (b : Nat → Bool) : Nat := countLit b [-32, -34, -37]
def count1505 (b : Nat → Bool) : Nat := countLit b [-38, -39]
def count1507 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count1509 (b : Nat → Bool) : Nat := countLit b [-38, -39, -42, -44]
def count1513 (b : Nat → Bool) : Nat := countLit b [-32, -34, -37, -38, -39, -42, -44]
def count1520 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count1522 (b : Nat → Bool) : Nat := countLit b [-48, -50]
def count1524 (b : Nat → Bool) : Nat := countLit b [-46, -47, -48, -50]
def count1528 (b : Nat → Bool) : Nat := countLit b [-52, -54]
def count1530 (b : Nat → Bool) : Nat := countLit b [-56, -58]
def count1532 (b : Nat → Bool) : Nat := countLit b [-52, -54, -56, -58]
def count1536 (b : Nat → Bool) : Nat := countLit b [-46, -47, -48, -50, -52, -54, -56, -58]
def count1544 (b : Nat → Bool) : Nat := countLit b [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]
def count1559 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]
def count1580 (b : Nat → Bool) : Nat := countLit b [-62, -63]
def count1582 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63]
def count1585 (b : Nat → Bool) : Nat := countLit b [-64, -70]
def count1587 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count1589 (b : Nat → Bool) : Nat := countLit b [-64, -70, -71, -73]
def count1593 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -64, -70, -71, -73]
def count1600 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count1602 (b : Nat → Bool) : Nat := countLit b [-79, -80]
def count1604 (b : Nat → Bool) : Nat := countLit b [-76, -77, -79, -80]
def count1608 (b : Nat → Bool) : Nat := countLit b [-82, -85]
def count1610 (b : Nat → Bool) : Nat := countLit b [-87, -88]
def count1612 (b : Nat → Bool) : Nat := countLit b [-82, -85, -87, -88]
def count1616 (b : Nat → Bool) : Nat := countLit b [-76, -77, -79, -80, -82, -85, -87, -88]
def count1624 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88]
def count1639 (b : Nat → Bool) : Nat := countLit b [-90, -92]
def count1641 (b : Nat → Bool) : Nat := countLit b [-94, -95]
def count1643 (b : Nat → Bool) : Nat := countLit b [-90, -92, -94, -95]
def count1647 (b : Nat → Bool) : Nat := countLit b [-98, -99]
def count1649 (b : Nat → Bool) : Nat := countLit b [-105, -106]
def count1651 (b : Nat → Bool) : Nat := countLit b [-98, -99, -105, -106]
def count1655 (b : Nat → Bool) : Nat := countLit b [-90, -92, -94, -95, -98, -99, -105, -106]
def count1663 (b : Nat → Bool) : Nat := countLit b [-109, -110]
def count1665 (b : Nat → Bool) : Nat := countLit b [-111, -113]
def count1667 (b : Nat → Bool) : Nat := countLit b [-109, -110, -111, -113]
def count1671 (b : Nat → Bool) : Nat := countLit b [-115, -116]
def count1673 (b : Nat → Bool) : Nat := countLit b [-117, -120]
def count1675 (b : Nat → Bool) : Nat := countLit b [-115, -116, -117, -120]
def count1679 (b : Nat → Bool) : Nat := countLit b [-109, -110, -111, -113, -115, -116, -117, -120]
def count1687 (b : Nat → Bool) : Nat := countLit b [-90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]
def count1703 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]
def count1724 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30, -32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58, -61, -62, -63, -64, -70, -71, -73, -76, -77, -79, -80, -82, -85, -87, -88, -90, -92, -94, -95, -98, -99, -105, -106, -109, -110, -111, -113, -115, -116, -117, -120]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 872 then (if i < 436 then (if i < 218 then (if i < 109 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 20 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 18 then (if i < 17 then b 16 else b 17) else (if i < 19 then b 18 else b 19))) else (if i < 23 then (if i < 21 then b 20 else (if i < 22 then b 21 else b 22)) else (if i < 25 then (if i < 24 then b 23 else b 24) else (if i < 26 then b 25 else b 26))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 31 then b 30 else (if i < 32 then b 31 else b 32))) else (if i < 36 then (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)) else (if i < 38 then (if i < 37 then b 36 else b 37) else (if i < 39 then b 38 else b 39)))) else (if i < 47 then (if i < 43 then (if i < 41 then b 40 else (if i < 42 then b 41 else b 42)) else (if i < 45 then (if i < 44 then b 43 else b 44) else (if i < 46 then b 45 else b 46))) else (if i < 50 then (if i < 48 then b 47 else (if i < 49 then b 48 else b 49)) else (if i < 52 then (if i < 51 then b 50 else b 51) else (if i < 53 then b 52 else b 53)))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)) else (if i < 58 then b 57 else (if i < 59 then b 58 else b 59))) else (if i < 63 then (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)) else (if i < 65 then (if i < 64 then b 63 else b 64) else (if i < 66 then b 65 else b 66)))) else (if i < 74 then (if i < 70 then (if i < 68 then b 67 else (if i < 69 then b 68 else b 69)) else (if i < 72 then (if i < 71 then b 70 else b 71) else (if i < 73 then b 72 else b 73))) else (if i < 77 then (if i < 75 then b 74 else (if i < 76 then b 75 else b 76)) else (if i < 79 then (if i < 78 then b 77 else b 78) else (if i < 80 then b 79 else b 80))))) else (if i < 95 then (if i < 88 then (if i < 84 then (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)) else (if i < 86 then (if i < 85 then b 84 else b 85) else (if i < 87 then b 86 else b 87))) else (if i < 91 then (if i < 89 then b 88 else (if i < 90 then b 89 else b 90)) else (if i < 93 then (if i < 92 then b 91 else b 92) else (if i < 94 then b 93 else b 94)))) else (if i < 102 then (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 100 then (if i < 99 then b 98 else b 99) else (if i < 101 then b 100 else b 101))) else (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 107 then (if i < 106 then b 105 else b 106) else (if i < 108 then b 107 else b 108))))))) else (if i < 163 then (if i < 136 then (if i < 122 then (if i < 115 then (if i < 112 then (if i < 110 then b 109 else (if i < 111 then b 110 else b 111)) else (if i < 113 then b 112 else (if i < 114 then b 113 else b 114))) else (if i < 118 then (if i < 116 then b 115 else (if i < 117 then b 116 else b 117)) else (if i < 120 then (if i < 119 then b 118 else b 119) else (if i < 121 then b 120 else b 121)))) else (if i < 129 then (if i < 125 then (if i < 123 then b 122 else (if i < 124 then b 123 else b 124)) else (if i < 127 then (if i < 126 then b 125 else b 126) else (if i < 128 then b 127 else b 128))) else (if i < 132 then (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)) else (if i < 134 then (if i < 133 then b 132 else b 133) else (if i < 135 then b 134 else b 135))))) else (if i < 149 then (if i < 142 then (if i < 139 then (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)) else (if i < 140 then b 139 else (if i < 141 then b 140 else b 141))) else (if i < 145 then (if i < 143 then b 142 else (if i < 144 then b 143 else b 144)) else (if i < 147 then (if i < 146 then b 145 else b 146) else (if i < 148 then b 147 else b 148)))) else (if i < 156 then (if i < 152 then (if i < 150 then b 149 else (if i < 151 then b 150 else b 151)) else (if i < 154 then (if i < 153 then b 152 else b 153) else (if i < 155 then b 154 else b 155))) else (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 161 then (if i < 160 then b 159 else b 160) else (if i < 162 then b 161 else b 162)))))) else (if i < 190 then (if i < 176 then (if i < 169 then (if i < 166 then (if i < 164 then b 163 else (if i < 165 then b 164 else b 165)) else (if i < 167 then b 166 else (if i < 168 then b 167 else b 168))) else (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 174 then (if i < 173 then b 172 else b 173) else (if i < 175 then b 174 else b 175)))) else (if i < 183 then (if i < 179 then (if i < 177 then b 176 else (if i < 178 then b 177 else b 178)) else (if i < 181 then (if i < 180 then b 179 else b 180) else (if i < 182 then b 181 else b 182))) else (if i < 186 then (if i < 184 then b 183 else (if i < 185 then b 184 else b 185)) else (if i < 188 then (if i < 187 then b 186 else b 187) else (if i < 189 then b 188 else b 189))))) else (if i < 204 then (if i < 197 then (if i < 193 then (if i < 191 then b 190 else (if i < 192 then b 191 else b 192)) else (if i < 195 then (if i < 194 then b 193 else b 194) else (if i < 196 then b 195 else b 196))) else (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 202 then (if i < 201 then b 200 else b 201) else (if i < 203 then b 202 else b 203)))) else (if i < 211 then (if i < 207 then (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)) else (if i < 209 then (if i < 208 then b 207 else b 208) else (if i < 210 then b 209 else b 210))) else (if i < 214 then (if i < 212 then b 211 else (if i < 213 then b 212 else b 213)) else (if i < 216 then (if i < 215 then b 214 else b 215) else (if i < 217 then b 216 else b 217)))))))) else (if i < 327 then (if i < 272 then (if i < 245 then (if i < 231 then (if i < 224 then (if i < 221 then (if i < 219 then b 218 else (if i < 220 then b 219 else b 220)) else (if i < 222 then b 221 else (if i < 223 then b 222 else b 223))) else (if i < 227 then (if i < 225 then b 224 else (if i < 226 then b 225 else b 226)) else (if i < 229 then (if i < 228 then b 227 else b 228) else (if i < 230 then b 229 else b 230)))) else (if i < 238 then (if i < 234 then (if i < 232 then b 231 else (if i < 233 then b 232 else b 233)) else (if i < 236 then (if i < 235 then b 234 else b 235) else (if i < 237 then b 236 else b 237))) else (if i < 241 then (if i < 239 then b 238 else (if i < 240 then b 239 else b 240)) else (if i < 243 then (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b)) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b)))))) else (if i < 258 then (if i < 251 then (if i < 248 then (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b))) else (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b)))) else (if i < 254 then (if i < 252 then decide (1 ≤ count251 b) else (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b))) else (if i < 256 then (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b)) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))))) else (if i < 265 then (if i < 261 then (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 263 then (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b)) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)))) else (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 270 then (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))))))) else (if i < 299 then (if i < 285 then (if i < 278 then (if i < 275 then (if i < 273 then decide (2 ≤ count271 b) else (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b))) else (if i < 276 then decide (1 ≤ count275 b) else (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)))) else (if i < 281 then (if i < 279 then decide (2 ≤ count277 b) else (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b))) else (if i < 283 then (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))))) else (if i < 292 then (if i < 288 then (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))) else (if i < 290 then (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b)))) else (if i < 295 then (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b))) else (if i < 297 then (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b)) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))))) else (if i < 313 then (if i < 306 then (if i < 302 then (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))) else (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)))) else (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 311 then (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))))) else (if i < 320 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))) else (if i < 323 then (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))) else (if i < 325 then (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b)) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)))))))) else (if i < 381 then (if i < 354 then (if i < 340 then (if i < 333 then (if i < 330 then (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b))) else (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)))) else (if i < 336 then (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 338 then (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))))) else (if i < 347 then (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)))) else (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))))) else (if i < 367 then (if i < 360 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b)))) else (if i < 363 then (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b))) else (if i < 365 then (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b)) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))))) else (if i < 374 then (if i < 370 then (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))) else (if i < 372 then (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)))) else (if i < 377 then (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b))) else (if i < 379 then (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))))))) else (if i < 408 then (if i < 394 then (if i < 387 then (if i < 384 then (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b))) else (if i < 385 then decide (2 ≤ count383 b) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)))) else (if i < 390 then (if i < 388 then decide (1 ≤ count387 b) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b))) else (if i < 392 then (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b)) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))))) else (if i < 401 then (if i < 397 then (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))) else (if i < 399 then (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b)) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)))) else (if i < 404 then (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))) else (if i < 406 then (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b)) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b)))))) else (if i < 422 then (if i < 415 then (if i < 411 then (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))) else (if i < 413 then (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b)) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))) else (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 420 then (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))))) else (if i < 429 then (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 427 then (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)))) else (if i < 432 then (if i < 430 then decide (1 ≤ count429 b) else (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b))) else (if i < 434 then (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b)) else (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b)))))))))) else (if i < 654 then (if i < 545 then (if i < 490 then (if i < 463 then (if i < 449 then (if i < 442 then (if i < 439 then (if i < 437 then decide (2 ≤ count435 b) else (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b))) else (if i < 440 then decide (1 ≤ count439 b) else (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)))) else (if i < 445 then (if i < 443 then decide (2 ≤ count441 b) else (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b))) else (if i < 447 then (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b)) else (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b))))) else (if i < 456 then (if i < 452 then (if i < 450 then decide (1 ≤ count449 b) else (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b))) else (if i < 454 then (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b)) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b)))) else (if i < 459 then (if i < 457 then decide (2 ≤ count455 b) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b))) else (if i < 461 then (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b)))))) else (if i < 476 then (if i < 469 then (if i < 466 then (if i < 464 then decide (1 ≤ count463 b) else (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b))) else (if i < 467 then decide (2 ≤ count465 b) else (if i < 468 then decide (1 ≤ count467 b) else decide (2 ≤ count467 b)))) else (if i < 472 then (if i < 470 then decide (1 ≤ count469 b) else (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b))) else (if i < 474 then (if i < 473 then decide (2 ≤ count471 b) else decide (1 ≤ count473 b)) else (if i < 475 then decide (2 ≤ count473 b) else decide (1 ≤ count475 b))))) else (if i < 483 then (if i < 479 then (if i < 477 then decide (2 ≤ count475 b) else (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b))) else (if i < 481 then (if i < 480 then decide (1 ≤ count479 b) else decide (2 ≤ count479 b)) else (if i < 482 then decide (3 ≤ count479 b) else decide (1 ≤ count482 b)))) else (if i < 486 then (if i < 484 then decide (2 ≤ count482 b) else (if i < 485 then decide (1 ≤ count484 b) else decide (2 ≤ count484 b))) else (if i < 488 then (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b)) else (if i < 489 then decide (3 ≤ count486 b) else decide (4 ≤ count486 b))))))) else (if i < 517 then (if i < 503 then (if i < 496 then (if i < 493 then (if i < 491 then decide (1 ≤ count490 b) else (if i < 492 then decide (2 ≤ count490 b) else decide (3 ≤ count490 b))) else (if i < 494 then decide (4 ≤ count490 b) else (if i < 495 then decide (5 ≤ count490 b) else decide (6 ≤ count490 b)))) else (if i < 499 then (if i < 497 then decide (7 ≤ count490 b) else (if i < 498 then decide (1 ≤ count497 b) else decide (2 ≤ count497 b))) else (if i < 501 then (if i < 500 then decide (1 ≤ count499 b) else decide (2 ≤ count499 b)) else (if i < 502 then decide (3 ≤ count499 b) else decide (1 ≤ count502 b))))) else (if i < 510 then (if i < 506 then (if i < 504 then decide (2 ≤ count502 b) else (if i < 505 then decide (1 ≤ count504 b) else decide (2 ≤ count504 b))) else (if i < 508 then (if i < 507 then decide (1 ≤ count506 b) else decide (2 ≤ count506 b)) else (if i < 509 then decide (3 ≤ count506 b) else decide (4 ≤ count506 b)))) else (if i < 513 then (if i < 511 then decide (1 ≤ count510 b) else (if i < 512 then decide (2 ≤ count510 b) else decide (3 ≤ count510 b))) else (if i < 515 then (if i < 514 then decide (4 ≤ count510 b) else decide (5 ≤ count510 b)) else (if i < 516 then decide (6 ≤ count510 b) else decide (7 ≤ count510 b)))))) else (if i < 531 then (if i < 524 then (if i < 520 then (if i < 518 then decide (1 ≤ count517 b) else (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b))) else (if i < 522 then (if i < 521 then decide (4 ≤ count517 b) else decide (5 ≤ count517 b)) else (if i < 523 then decide (6 ≤ count517 b) else decide (7 ≤ count517 b)))) else (if i < 527 then (if i < 525 then decide (8 ≤ count517 b) else (if i < 526 then decide (9 ≤ count517 b) else decide (10 ≤ count517 b))) else (if i < 529 then (if i < 528 then decide (11 ≤ count517 b) else decide (12 ≤ count517 b)) else (if i < 530 then decide (13 ≤ count517 b) else decide (14 ≤ count517 b))))) else (if i < 538 then (if i < 534 then (if i < 532 then decide (1 ≤ count531 b) else (if i < 533 then decide (2 ≤ count531 b) else decide (1 ≤ count533 b))) else (if i < 536 then (if i < 535 then decide (2 ≤ count533 b) else decide (3 ≤ count533 b)) else (if i < 537 then decide (1 ≤ count536 b) else decide (2 ≤ count536 b)))) else (if i < 541 then (if i < 539 then decide (1 ≤ count538 b) else (if i < 540 then decide (2 ≤ count538 b) else decide (1 ≤ count540 b))) else (if i < 543 then (if i < 542 then decide (2 ≤ count540 b) else decide (3 ≤ count540 b)) else (if i < 544 then decide (4 ≤ count540 b) else decide (1 ≤ count544 b)))))))) else (if i < 599 then (if i < 572 then (if i < 558 then (if i < 551 then (if i < 548 then (if i < 546 then decide (2 ≤ count544 b) else (if i < 547 then decide (3 ≤ count544 b) else decide (4 ≤ count544 b))) else (if i < 549 then decide (5 ≤ count544 b) else (if i < 550 then decide (6 ≤ count544 b) else decide (7 ≤ count544 b)))) else (if i < 554 then (if i < 552 then decide (1 ≤ count551 b) else (if i < 553 then decide (2 ≤ count551 b) else decide (1 ≤ count553 b))) else (if i < 556 then (if i < 555 then decide (2 ≤ count553 b) else decide (1 ≤ count555 b)) else (if i < 557 then decide (2 ≤ count555 b) else decide (3 ≤ count555 b))))) else (if i < 565 then (if i < 561 then (if i < 559 then decide (4 ≤ count555 b) else (if i < 560 then decide (1 ≤ count559 b) else decide (2 ≤ count559 b))) else (if i < 563 then (if i < 562 then decide (1 ≤ count561 b) else decide (2 ≤ count561 b)) else (if i < 564 then decide (1 ≤ count563 b) else decide (2 ≤ count563 b)))) else (if i < 568 then (if i < 566 then decide (3 ≤ count563 b) else (if i < 567 then decide (4 ≤ count563 b) else decide (1 ≤ count567 b))) else (if i < 570 then (if i < 569 then decide (2 ≤ count567 b) else decide (3 ≤ count567 b)) else (if i < 571 then decide (4 ≤ count567 b) else decide (5 ≤ count567 b)))))) else (if i < 585 then (if i < 578 then (if i < 575 then (if i < 573 then decide (6 ≤ count567 b) else (if i < 574 then decide (7 ≤ count567 b) else decide (8 ≤ count567 b))) else (if i < 576 then decide (1 ≤ count575 b) else (if i < 577 then decide (2 ≤ count575 b) else decide (3 ≤ count575 b)))) else (if i < 581 then (if i < 579 then decide (4 ≤ count575 b) else (if i < 580 then decide (5 ≤ count575 b) else decide (6 ≤ count575 b))) else (if i < 583 then (if i < 582 then decide (7 ≤ count575 b) else decide (8 ≤ count575 b)) else (if i < 584 then decide (9 ≤ count575 b) else decide (10 ≤ count575 b))))) else (if i < 592 then (if i < 588 then (if i < 586 then decide (11 ≤ count575 b) else (if i < 587 then decide (12 ≤ count575 b) else decide (13 ≤ count575 b))) else (if i < 590 then (if i < 589 then decide (14 ≤ count575 b) else decide (15 ≤ count575 b)) else (if i < 591 then decide (1 ≤ count590 b) else decide (2 ≤ count590 b)))) else (if i < 595 then (if i < 593 then decide (3 ≤ count590 b) else (if i < 594 then decide (4 ≤ count590 b) else decide (5 ≤ count590 b))) else (if i < 597 then (if i < 596 then decide (6 ≤ count590 b) else decide (7 ≤ count590 b)) else (if i < 598 then decide (8 ≤ count590 b) else decide (9 ≤ count590 b))))))) else (if i < 626 then (if i < 612 then (if i < 605 then (if i < 602 then (if i < 600 then decide (10 ≤ count590 b) else (if i < 601 then decide (11 ≤ count590 b) else decide (12 ≤ count590 b))) else (if i < 603 then decide (13 ≤ count590 b) else (if i < 604 then decide (14 ≤ count590 b) else decide (15 ≤ count590 b)))) else (if i < 608 then (if i < 606 then decide (16 ≤ count590 b) else (if i < 607 then decide (17 ≤ count590 b) else decide (18 ≤ count590 b))) else (if i < 610 then (if i < 609 then decide (19 ≤ count590 b) else decide (20 ≤ count590 b)) else (if i < 611 then decide (21 ≤ count590 b) else decide (22 ≤ count590 b))))) else (if i < 619 then (if i < 615 then (if i < 613 then decide (23 ≤ count590 b) else (if i < 614 then decide (24 ≤ count590 b) else decide (25 ≤ count590 b))) else (if i < 617 then (if i < 616 then decide (26 ≤ count590 b) else decide (27 ≤ count590 b)) else (if i < 618 then decide (28 ≤ count590 b) else decide (29 ≤ count590 b)))) else (if i < 622 then (if i < 620 then decide (1 ≤ count619 b) else (if i < 621 then decide (2 ≤ count619 b) else decide (1 ≤ count621 b))) else (if i < 624 then (if i < 623 then decide (2 ≤ count621 b) else decide (3 ≤ count621 b)) else (if i < 625 then decide (1 ≤ count624 b) else decide (2 ≤ count624 b)))))) else (if i < 640 then (if i < 633 then (if i < 629 then (if i < 627 then decide (1 ≤ count626 b) else (if i < 628 then decide (2 ≤ count626 b) else decide (1 ≤ count628 b))) else (if i < 631 then (if i < 630 then decide (2 ≤ count628 b) else decide (3 ≤ count628 b)) else (if i < 632 then decide (4 ≤ count628 b) else decide (1 ≤ count632 b)))) else (if i < 636 then (if i < 634 then decide (2 ≤ count632 b) else (if i < 635 then decide (3 ≤ count632 b) else decide (4 ≤ count632 b))) else (if i < 638 then (if i < 637 then decide (5 ≤ count632 b) else decide (6 ≤ count632 b)) else (if i < 639 then decide (7 ≤ count632 b) else decide (1 ≤ count639 b))))) else (if i < 647 then (if i < 643 then (if i < 641 then decide (2 ≤ count639 b) else (if i < 642 then decide (1 ≤ count641 b) else decide (2 ≤ count641 b))) else (if i < 645 then (if i < 644 then decide (1 ≤ count643 b) else decide (2 ≤ count643 b)) else (if i < 646 then decide (3 ≤ count643 b) else decide (4 ≤ count643 b)))) else (if i < 650 then (if i < 648 then decide (1 ≤ count647 b) else (if i < 649 then decide (2 ≤ count647 b) else decide (1 ≤ count649 b))) else (if i < 652 then (if i < 651 then decide (2 ≤ count649 b) else decide (1 ≤ count651 b)) else (if i < 653 then decide (2 ≤ count651 b) else decide (3 ≤ count651 b))))))))) else (if i < 763 then (if i < 708 then (if i < 681 then (if i < 667 then (if i < 660 then (if i < 657 then (if i < 655 then decide (4 ≤ count651 b) else (if i < 656 then decide (1 ≤ count655 b) else decide (2 ≤ count655 b))) else (if i < 658 then decide (3 ≤ count655 b) else (if i < 659 then decide (4 ≤ count655 b) else decide (5 ≤ count655 b)))) else (if i < 663 then (if i < 661 then decide (6 ≤ count655 b) else (if i < 662 then decide (7 ≤ count655 b) else decide (8 ≤ count655 b))) else (if i < 665 then (if i < 664 then decide (1 ≤ count663 b) else decide (2 ≤ count663 b)) else (if i < 666 then decide (3 ≤ count663 b) else decide (4 ≤ count663 b))))) else (if i < 674 then (if i < 670 then (if i < 668 then decide (5 ≤ count663 b) else (if i < 669 then decide (6 ≤ count663 b) else decide (7 ≤ count663 b))) else (if i < 672 then (if i < 671 then decide (8 ≤ count663 b) else decide (9 ≤ count663 b)) else (if i < 673 then decide (10 ≤ count663 b) else decide (11 ≤ count663 b)))) else (if i < 677 then (if i < 675 then decide (12 ≤ count663 b) else (if i < 676 then decide (13 ≤ count663 b) else decide (14 ≤ count663 b))) else (if i < 679 then (if i < 678 then decide (15 ≤ count663 b) else decide (1 ≤ count678 b)) else (if i < 680 then decide (2 ≤ count678 b) else decide (1 ≤ count680 b)))))) else (if i < 694 then (if i < 687 then (if i < 684 then (if i < 682 then decide (2 ≤ count680 b) else (if i < 683 then decide (3 ≤ count680 b) else decide (1 ≤ count683 b))) else (if i < 685 then decide (2 ≤ count683 b) else (if i < 686 then decide (1 ≤ count685 b) else decide (2 ≤ count685 b)))) else (if i < 690 then (if i < 688 then decide (1 ≤ count687 b) else (if i < 689 then decide (2 ≤ count687 b) else decide (3 ≤ count687 b))) else (if i < 692 then (if i < 691 then decide (4 ≤ count687 b) else decide (1 ≤ count691 b)) else (if i < 693 then decide (2 ≤ count691 b) else decide (3 ≤ count691 b))))) else (if i < 701 then (if i < 697 then (if i < 695 then decide (4 ≤ count691 b) else (if i < 696 then decide (5 ≤ count691 b) else decide (6 ≤ count691 b))) else (if i < 699 then (if i < 698 then decide (7 ≤ count691 b) else decide (1 ≤ count698 b)) else (if i < 700 then decide (2 ≤ count698 b) else decide (1 ≤ count700 b)))) else (if i < 704 then (if i < 702 then decide (2 ≤ count700 b) else (if i < 703 then decide (1 ≤ count702 b) else decide (2 ≤ count702 b))) else (if i < 706 then (if i < 705 then decide (3 ≤ count702 b) else decide (4 ≤ count702 b)) else (if i < 707 then decide (1 ≤ count706 b) else decide (2 ≤ count706 b))))))) else (if i < 735 then (if i < 721 then (if i < 714 then (if i < 711 then (if i < 709 then decide (1 ≤ count708 b) else (if i < 710 then decide (2 ≤ count708 b) else decide (1 ≤ count710 b))) else (if i < 712 then decide (2 ≤ count710 b) else (if i < 713 then decide (3 ≤ count710 b) else decide (4 ≤ count710 b)))) else (if i < 717 then (if i < 715 then decide (1 ≤ count714 b) else (if i < 716 then decide (2 ≤ count714 b) else decide (3 ≤ count714 b))) else (if i < 719 then (if i < 718 then decide (4 ≤ count714 b) else decide (5 ≤ count714 b)) else (if i < 720 then decide (6 ≤ count714 b) else decide (7 ≤ count714 b))))) else (if i < 728 then (if i < 724 then (if i < 722 then decide (8 ≤ count714 b) else (if i < 723 then decide (1 ≤ count722 b) else decide (2 ≤ count722 b))) else (if i < 726 then (if i < 725 then decide (3 ≤ count722 b) else decide (4 ≤ count722 b)) else (if i < 727 then decide (5 ≤ count722 b) else decide (6 ≤ count722 b)))) else (if i < 731 then (if i < 729 then decide (7 ≤ count722 b) else (if i < 730 then decide (8 ≤ count722 b) else decide (9 ≤ count722 b))) else (if i < 733 then (if i < 732 then decide (10 ≤ count722 b) else decide (11 ≤ count722 b)) else (if i < 734 then decide (12 ≤ count722 b) else decide (13 ≤ count722 b)))))) else (if i < 749 then (if i < 742 then (if i < 738 then (if i < 736 then decide (14 ≤ count722 b) else (if i < 737 then decide (15 ≤ count722 b) else decide (1 ≤ count737 b))) else (if i < 740 then (if i < 739 then decide (2 ≤ count737 b) else decide (3 ≤ count737 b)) else (if i < 741 then decide (4 ≤ count737 b) else decide (5 ≤ count737 b)))) else (if i < 745 then (if i < 743 then decide (6 ≤ count737 b) else (if i < 744 then decide (7 ≤ count737 b) else decide (8 ≤ count737 b))) else (if i < 747 then (if i < 746 then decide (9 ≤ count737 b) else decide (10 ≤ count737 b)) else (if i < 748 then decide (11 ≤ count737 b) else decide (12 ≤ count737 b))))) else (if i < 756 then (if i < 752 then (if i < 750 then decide (13 ≤ count737 b) else (if i < 751 then decide (14 ≤ count737 b) else decide (15 ≤ count737 b))) else (if i < 754 then (if i < 753 then decide (16 ≤ count737 b) else decide (17 ≤ count737 b)) else (if i < 755 then decide (18 ≤ count737 b) else decide (19 ≤ count737 b)))) else (if i < 759 then (if i < 757 then decide (20 ≤ count737 b) else (if i < 758 then decide (21 ≤ count737 b) else decide (22 ≤ count737 b))) else (if i < 761 then (if i < 760 then decide (23 ≤ count737 b) else decide (24 ≤ count737 b)) else (if i < 762 then decide (25 ≤ count737 b) else decide (26 ≤ count737 b)))))))) else (if i < 817 then (if i < 790 then (if i < 776 then (if i < 769 then (if i < 766 then (if i < 764 then decide (27 ≤ count737 b) else (if i < 765 then decide (28 ≤ count737 b) else decide (29 ≤ count737 b))) else (if i < 767 then decide (30 ≤ count737 b) else (if i < 768 then decide (1 ≤ count767 b) else decide (2 ≤ count767 b)))) else (if i < 772 then (if i < 770 then decide (3 ≤ count767 b) else (if i < 771 then decide (4 ≤ count767 b) else decide (5 ≤ count767 b))) else (if i < 774 then (if i < 773 then decide (6 ≤ count767 b) else decide (7 ≤ count767 b)) else (if i < 775 then decide (8 ≤ count767 b) else decide (9 ≤ count767 b))))) else (if i < 783 then (if i < 779 then (if i < 777 then decide (10 ≤ count767 b) else (if i < 778 then decide (11 ≤ count767 b) else decide (12 ≤ count767 b))) else (if i < 781 then (if i < 780 then decide (13 ≤ count767 b) else decide (14 ≤ count767 b)) else (if i < 782 then decide (15 ≤ count767 b) else decide (16 ≤ count767 b)))) else (if i < 786 then (if i < 784 then decide (17 ≤ count767 b) else (if i < 785 then decide (18 ≤ count767 b) else decide (19 ≤ count767 b))) else (if i < 788 then (if i < 787 then decide (20 ≤ count767 b) else decide (21 ≤ count767 b)) else (if i < 789 then decide (22 ≤ count767 b) else decide (23 ≤ count767 b)))))) else (if i < 803 then (if i < 796 then (if i < 793 then (if i < 791 then decide (24 ≤ count767 b) else (if i < 792 then decide (25 ≤ count767 b) else decide (26 ≤ count767 b))) else (if i < 794 then decide (27 ≤ count767 b) else (if i < 795 then decide (28 ≤ count767 b) else decide (29 ≤ count767 b)))) else (if i < 799 then (if i < 797 then decide (30 ≤ count767 b) else (if i < 798 then decide (31 ≤ count767 b) else decide (32 ≤ count767 b))) else (if i < 801 then (if i < 800 then decide (33 ≤ count767 b) else decide (34 ≤ count767 b)) else (if i < 802 then decide (35 ≤ count767 b) else decide (36 ≤ count767 b))))) else (if i < 810 then (if i < 806 then (if i < 804 then decide (37 ≤ count767 b) else (if i < 805 then decide (38 ≤ count767 b) else decide (39 ≤ count767 b))) else (if i < 808 then (if i < 807 then decide (40 ≤ count767 b) else decide (41 ≤ count767 b)) else (if i < 809 then decide (42 ≤ count767 b) else decide (1 ≤ count809 b)))) else (if i < 813 then (if i < 811 then decide (2 ≤ count809 b) else (if i < 812 then decide (1 ≤ count811 b) else decide (2 ≤ count811 b))) else (if i < 815 then (if i < 814 then decide (3 ≤ count811 b) else decide (1 ≤ count814 b)) else (if i < 816 then decide (2 ≤ count814 b) else decide (1 ≤ count816 b))))))) else (if i < 844 then (if i < 830 then (if i < 823 then (if i < 820 then (if i < 818 then decide (2 ≤ count816 b) else (if i < 819 then decide (1 ≤ count818 b) else decide (2 ≤ count818 b))) else (if i < 821 then decide (3 ≤ count818 b) else (if i < 822 then decide (4 ≤ count818 b) else decide (1 ≤ count822 b)))) else (if i < 826 then (if i < 824 then decide (2 ≤ count822 b) else (if i < 825 then decide (3 ≤ count822 b) else decide (4 ≤ count822 b))) else (if i < 828 then (if i < 827 then decide (5 ≤ count822 b) else decide (6 ≤ count822 b)) else (if i < 829 then decide (7 ≤ count822 b) else decide (1 ≤ count829 b))))) else (if i < 837 then (if i < 833 then (if i < 831 then decide (2 ≤ count829 b) else (if i < 832 then decide (1 ≤ count831 b) else decide (2 ≤ count831 b))) else (if i < 835 then (if i < 834 then decide (3 ≤ count831 b) else decide (1 ≤ count834 b)) else (if i < 836 then decide (2 ≤ count834 b) else decide (1 ≤ count836 b)))) else (if i < 840 then (if i < 838 then decide (2 ≤ count836 b) else (if i < 839 then decide (1 ≤ count838 b) else decide (2 ≤ count838 b))) else (if i < 842 then (if i < 841 then decide (3 ≤ count838 b) else decide (4 ≤ count838 b)) else (if i < 843 then decide (1 ≤ count842 b) else decide (2 ≤ count842 b)))))) else (if i < 858 then (if i < 851 then (if i < 847 then (if i < 845 then decide (3 ≤ count842 b) else (if i < 846 then decide (4 ≤ count842 b) else decide (5 ≤ count842 b))) else (if i < 849 then (if i < 848 then decide (6 ≤ count842 b) else decide (7 ≤ count842 b)) else (if i < 850 then decide (1 ≤ count849 b) else decide (2 ≤ count849 b)))) else (if i < 854 then (if i < 852 then decide (3 ≤ count849 b) else (if i < 853 then decide (4 ≤ count849 b) else decide (5 ≤ count849 b))) else (if i < 856 then (if i < 855 then decide (6 ≤ count849 b) else decide (7 ≤ count849 b)) else (if i < 857 then decide (8 ≤ count849 b) else decide (9 ≤ count849 b))))) else (if i < 865 then (if i < 861 then (if i < 859 then decide (10 ≤ count849 b) else (if i < 860 then decide (11 ≤ count849 b) else decide (12 ≤ count849 b))) else (if i < 863 then (if i < 862 then decide (13 ≤ count849 b) else decide (14 ≤ count849 b)) else (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b)))) else (if i < 868 then (if i < 866 then decide (1 ≤ count865 b) else (if i < 867 then decide (2 ≤ count865 b) else decide (3 ≤ count865 b))) else (if i < 870 then (if i < 869 then decide (1 ≤ count868 b) else decide (2 ≤ count868 b)) else (if i < 871 then decide (1 ≤ count870 b) else decide (2 ≤ count870 b))))))))))) else (if i < 1308 then (if i < 1090 then (if i < 981 then (if i < 926 then (if i < 899 then (if i < 885 then (if i < 878 then (if i < 875 then (if i < 873 then decide (1 ≤ count872 b) else (if i < 874 then decide (2 ≤ count872 b) else decide (3 ≤ count872 b))) else (if i < 876 then decide (4 ≤ count872 b) else (if i < 877 then decide (1 ≤ count876 b) else decide (2 ≤ count876 b)))) else (if i < 881 then (if i < 879 then decide (3 ≤ count876 b) else (if i < 880 then decide (4 ≤ count876 b) else decide (5 ≤ count876 b))) else (if i < 883 then (if i < 882 then decide (6 ≤ count876 b) else decide (7 ≤ count876 b)) else (if i < 884 then decide (1 ≤ count883 b) else decide (2 ≤ count883 b))))) else (if i < 892 then (if i < 888 then (if i < 886 then decide (1 ≤ count885 b) else (if i < 887 then decide (2 ≤ count885 b) else decide (1 ≤ count887 b))) else (if i < 890 then (if i < 889 then decide (2 ≤ count887 b) else decide (3 ≤ count887 b)) else (if i < 891 then decide (4 ≤ count887 b) else decide (1 ≤ count891 b)))) else (if i < 895 then (if i < 893 then decide (2 ≤ count891 b) else (if i < 894 then decide (1 ≤ count893 b) else decide (2 ≤ count893 b))) else (if i < 897 then (if i < 896 then decide (1 ≤ count895 b) else decide (2 ≤ count895 b)) else (if i < 898 then decide (3 ≤ count895 b) else decide (4 ≤ count895 b)))))) else (if i < 912 then (if i < 905 then (if i < 902 then (if i < 900 then decide (1 ≤ count899 b) else (if i < 901 then decide (2 ≤ count899 b) else decide (3 ≤ count899 b))) else (if i < 903 then decide (4 ≤ count899 b) else (if i < 904 then decide (5 ≤ count899 b) else decide (6 ≤ count899 b)))) else (if i < 908 then (if i < 906 then decide (7 ≤ count899 b) else (if i < 907 then decide (8 ≤ count899 b) else decide (1 ≤ count907 b))) else (if i < 910 then (if i < 909 then decide (2 ≤ count907 b) else decide (3 ≤ count907 b)) else (if i < 911 then decide (4 ≤ count907 b) else decide (5 ≤ count907 b))))) else (if i < 919 then (if i < 915 then (if i < 913 then decide (6 ≤ count907 b) else (if i < 914 then decide (7 ≤ count907 b) else decide (8 ≤ count907 b))) else (if i < 917 then (if i < 916 then decide (9 ≤ count907 b) else decide (10 ≤ count907 b)) else (if i < 918 then decide (11 ≤ count907 b) else decide (12 ≤ count907 b)))) else (if i < 922 then (if i < 920 then decide (13 ≤ count907 b) else (if i < 921 then decide (14 ≤ count907 b) else decide (15 ≤ count907 b))) else (if i < 924 then (if i < 923 then decide (1 ≤ count922 b) else decide (2 ≤ count922 b)) else (if i < 925 then decide (3 ≤ count922 b) else decide (4 ≤ count922 b))))))) else (if i < 953 then (if i < 939 then (if i < 932 then (if i < 929 then (if i < 927 then decide (5 ≤ count922 b) else (if i < 928 then decide (6 ≤ count922 b) else decide (7 ≤ count922 b))) else (if i < 930 then decide (8 ≤ count922 b) else (if i < 931 then decide (9 ≤ count922 b) else decide (10 ≤ count922 b)))) else (if i < 935 then (if i < 933 then decide (11 ≤ count922 b) else (if i < 934 then decide (12 ≤ count922 b) else decide (13 ≤ count922 b))) else (if i < 937 then (if i < 936 then decide (14 ≤ count922 b) else decide (15 ≤ count922 b)) else (if i < 938 then decide (16 ≤ count922 b) else decide (17 ≤ count922 b))))) else (if i < 946 then (if i < 942 then (if i < 940 then decide (18 ≤ count922 b) else (if i < 941 then decide (19 ≤ count922 b) else decide (1 ≤ count941 b))) else (if i < 944 then (if i < 943 then decide (2 ≤ count941 b) else decide (1 ≤ count943 b)) else (if i < 945 then decide (2 ≤ count943 b) else decide (3 ≤ count943 b)))) else (if i < 949 then (if i < 947 then decide (1 ≤ count946 b) else (if i < 948 then decide (2 ≤ count946 b) else decide (1 ≤ count948 b))) else (if i < 951 then (if i < 950 then decide (2 ≤ count948 b) else decide (1 ≤ count950 b)) else (if i < 952 then decide (2 ≤ count950 b) else decide (3 ≤ count950 b)))))) else (if i < 967 then (if i < 960 then (if i < 956 then (if i < 954 then decide (4 ≤ count950 b) else (if i < 955 then decide (1 ≤ count954 b) else decide (2 ≤ count954 b))) else (if i < 958 then (if i < 957 then decide (3 ≤ count954 b) else decide (4 ≤ count954 b)) else (if i < 959 then decide (5 ≤ count954 b) else decide (6 ≤ count954 b)))) else (if i < 963 then (if i < 961 then decide (7 ≤ count954 b) else (if i < 962 then decide (1 ≤ count961 b) else decide (2 ≤ count961 b))) else (if i < 965 then (if i < 964 then decide (1 ≤ count963 b) else decide (2 ≤ count963 b)) else (if i < 966 then decide (1 ≤ count965 b) else decide (2 ≤ count965 b))))) else (if i < 974 then (if i < 970 then (if i < 968 then decide (3 ≤ count965 b) else (if i < 969 then decide (4 ≤ count965 b) else decide (1 ≤ count969 b))) else (if i < 972 then (if i < 971 then decide (2 ≤ count969 b) else decide (1 ≤ count971 b)) else (if i < 973 then decide (2 ≤ count971 b) else decide (1 ≤ count973 b)))) else (if i < 977 then (if i < 975 then decide (2 ≤ count973 b) else (if i < 976 then decide (3 ≤ count973 b) else decide (4 ≤ count973 b))) else (if i < 979 then (if i < 978 then decide (1 ≤ count977 b) else decide (2 ≤ count977 b)) else (if i < 980 then decide (3 ≤ count977 b) else decide (4 ≤ count977 b)))))))) else (if i < 1035 then (if i < 1008 then (if i < 994 then (if i < 987 then (if i < 984 then (if i < 982 then decide (5 ≤ count977 b) else (if i < 983 then decide (6 ≤ count977 b) else decide (7 ≤ count977 b))) else (if i < 985 then decide (8 ≤ count977 b) else (if i < 986 then decide (1 ≤ count985 b) else decide (2 ≤ count985 b)))) else (if i < 990 then (if i < 988 then decide (3 ≤ count985 b) else (if i < 989 then decide (4 ≤ count985 b) else decide (5 ≤ count985 b))) else (if i < 992 then (if i < 991 then decide (6 ≤ count985 b) else decide (7 ≤ count985 b)) else (if i < 993 then decide (8 ≤ count985 b) else decide (9 ≤ count985 b))))) else (if i < 1001 then (if i < 997 then (if i < 995 then decide (10 ≤ count985 b) else (if i < 996 then decide (11 ≤ count985 b) else decide (12 ≤ count985 b))) else (if i < 999 then (if i < 998 then decide (13 ≤ count985 b) else decide (14 ≤ count985 b)) else (if i < 1000 then decide (15 ≤ count985 b) else decide (1 ≤ count1000 b)))) else (if i < 1004 then (if i < 1002 then decide (2 ≤ count1000 b) else (if i < 1003 then decide (1 ≤ count1002 b) else decide (2 ≤ count1002 b))) else (if i < 1006 then (if i < 1005 then decide (3 ≤ count1002 b) else decide (1 ≤ count1005 b)) else (if i < 1007 then decide (2 ≤ count1005 b) else decide (1 ≤ count1007 b)))))) else (if i < 1021 then (if i < 1014 then (if i < 1011 then (if i < 1009 then decide (2 ≤ count1007 b) else (if i < 1010 then decide (1 ≤ count1009 b) else decide (2 ≤ count1009 b))) else (if i < 1012 then decide (3 ≤ count1009 b) else (if i < 1013 then decide (4 ≤ count1009 b) else decide (1 ≤ count1013 b)))) else (if i < 1017 then (if i < 1015 then decide (2 ≤ count1013 b) else (if i < 1016 then decide (3 ≤ count1013 b) else decide (4 ≤ count1013 b))) else (if i < 1019 then (if i < 1018 then decide (5 ≤ count1013 b) else decide (6 ≤ count1013 b)) else (if i < 1020 then decide (7 ≤ count1013 b) else decide (1 ≤ count1020 b))))) else (if i < 1028 then (if i < 1024 then (if i < 1022 then decide (2 ≤ count1020 b) else (if i < 1023 then decide (1 ≤ count1022 b) else decide (2 ≤ count1022 b))) else (if i < 1026 then (if i < 1025 then decide (1 ≤ count1024 b) else decide (2 ≤ count1024 b)) else (if i < 1027 then decide (3 ≤ count1024 b) else decide (4 ≤ count1024 b)))) else (if i < 1031 then (if i < 1029 then decide (1 ≤ count1028 b) else (if i < 1030 then decide (2 ≤ count1028 b) else decide (1 ≤ count1030 b))) else (if i < 1033 then (if i < 1032 then decide (2 ≤ count1030 b) else decide (1 ≤ count1032 b)) else (if i < 1034 then decide (2 ≤ count1032 b) else decide (3 ≤ count1032 b))))))) else (if i < 1062 then (if i < 1048 then (if i < 1041 then (if i < 1038 then (if i < 1036 then decide (4 ≤ count1032 b) else (if i < 1037 then decide (1 ≤ count1036 b) else decide (2 ≤ count1036 b))) else (if i < 1039 then decide (3 ≤ count1036 b) else (if i < 1040 then decide (4 ≤ count1036 b) else decide (5 ≤ count1036 b)))) else (if i < 1044 then (if i < 1042 then decide (6 ≤ count1036 b) else (if i < 1043 then decide (7 ≤ count1036 b) else decide (8 ≤ count1036 b))) else (if i < 1046 then (if i < 1045 then decide (1 ≤ count1044 b) else decide (2 ≤ count1044 b)) else (if i < 1047 then decide (3 ≤ count1044 b) else decide (4 ≤ count1044 b))))) else (if i < 1055 then (if i < 1051 then (if i < 1049 then decide (5 ≤ count1044 b) else (if i < 1050 then decide (6 ≤ count1044 b) else decide (7 ≤ count1044 b))) else (if i < 1053 then (if i < 1052 then decide (8 ≤ count1044 b) else decide (9 ≤ count1044 b)) else (if i < 1054 then decide (10 ≤ count1044 b) else decide (11 ≤ count1044 b)))) else (if i < 1058 then (if i < 1056 then decide (12 ≤ count1044 b) else (if i < 1057 then decide (13 ≤ count1044 b) else decide (14 ≤ count1044 b))) else (if i < 1060 then (if i < 1059 then decide (15 ≤ count1044 b) else decide (1 ≤ count1059 b)) else (if i < 1061 then decide (2 ≤ count1059 b) else decide (3 ≤ count1059 b)))))) else (if i < 1076 then (if i < 1069 then (if i < 1065 then (if i < 1063 then decide (4 ≤ count1059 b) else (if i < 1064 then decide (5 ≤ count1059 b) else decide (6 ≤ count1059 b))) else (if i < 1067 then (if i < 1066 then decide (7 ≤ count1059 b) else decide (8 ≤ count1059 b)) else (if i < 1068 then decide (9 ≤ count1059 b) else decide (10 ≤ count1059 b)))) else (if i < 1072 then (if i < 1070 then decide (11 ≤ count1059 b) else (if i < 1071 then decide (12 ≤ count1059 b) else decide (13 ≤ count1059 b))) else (if i < 1074 then (if i < 1073 then decide (14 ≤ count1059 b) else decide (15 ≤ count1059 b)) else (if i < 1075 then decide (16 ≤ count1059 b) else decide (17 ≤ count1059 b))))) else (if i < 1083 then (if i < 1079 then (if i < 1077 then decide (18 ≤ count1059 b) else (if i < 1078 then decide (19 ≤ count1059 b) else decide (1 ≤ count1078 b))) else (if i < 1081 then (if i < 1080 then decide (2 ≤ count1078 b) else decide (3 ≤ count1078 b)) else (if i < 1082 then decide (4 ≤ count1078 b) else decide (5 ≤ count1078 b)))) else (if i < 1086 then (if i < 1084 then decide (6 ≤ count1078 b) else (if i < 1085 then decide (7 ≤ count1078 b) else decide (8 ≤ count1078 b))) else (if i < 1088 then (if i < 1087 then decide (9 ≤ count1078 b) else decide (10 ≤ count1078 b)) else (if i < 1089 then decide (11 ≤ count1078 b) else decide (12 ≤ count1078 b))))))))) else (if i < 1199 then (if i < 1144 then (if i < 1117 then (if i < 1103 then (if i < 1096 then (if i < 1093 then (if i < 1091 then decide (13 ≤ count1078 b) else (if i < 1092 then decide (14 ≤ count1078 b) else decide (15 ≤ count1078 b))) else (if i < 1094 then decide (16 ≤ count1078 b) else (if i < 1095 then decide (17 ≤ count1078 b) else decide (18 ≤ count1078 b)))) else (if i < 1099 then (if i < 1097 then decide (19 ≤ count1078 b) else (if i < 1098 then decide (1 ≤ count1097 b) else decide (2 ≤ count1097 b))) else (if i < 1101 then (if i < 1100 then decide (1 ≤ count1099 b) else decide (2 ≤ count1099 b)) else (if i < 1102 then decide (3 ≤ count1099 b) else decide (1 ≤ count1102 b))))) else (if i < 1110 then (if i < 1106 then (if i < 1104 then decide (2 ≤ count1102 b) else (if i < 1105 then decide (1 ≤ count1104 b) else decide (2 ≤ count1104 b))) else (if i < 1108 then (if i < 1107 then decide (1 ≤ count1106 b) else decide (2 ≤ count1106 b)) else (if i < 1109 then decide (3 ≤ count1106 b) else decide (4 ≤ count1106 b)))) else (if i < 1113 then (if i < 1111 then decide (1 ≤ count1110 b) else (if i < 1112 then decide (2 ≤ count1110 b) else decide (3 ≤ count1110 b))) else (if i < 1115 then (if i < 1114 then decide (4 ≤ count1110 b) else decide (5 ≤ count1110 b)) else (if i < 1116 then decide (6 ≤ count1110 b) else decide (7 ≤ count1110 b)))))) else (if i < 1130 then (if i < 1123 then (if i < 1120 then (if i < 1118 then decide (1 ≤ count1117 b) else (if i < 1119 then decide (2 ≤ count1117 b) else decide (1 ≤ count1119 b))) else (if i < 1121 then decide (2 ≤ count1119 b) else (if i < 1122 then decide (1 ≤ count1121 b) else decide (2 ≤ count1121 b)))) else (if i < 1126 then (if i < 1124 then decide (3 ≤ count1121 b) else (if i < 1125 then decide (4 ≤ count1121 b) else decide (1 ≤ count1125 b))) else (if i < 1128 then (if i < 1127 then decide (2 ≤ count1125 b) else decide (1 ≤ count1127 b)) else (if i < 1129 then decide (2 ≤ count1127 b) else decide (1 ≤ count1129 b))))) else (if i < 1137 then (if i < 1133 then (if i < 1131 then decide (2 ≤ count1129 b) else (if i < 1132 then decide (3 ≤ count1129 b) else decide (4 ≤ count1129 b))) else (if i < 1135 then (if i < 1134 then decide (1 ≤ count1133 b) else decide (2 ≤ count1133 b)) else (if i < 1136 then decide (3 ≤ count1133 b) else decide (4 ≤ count1133 b)))) else (if i < 1140 then (if i < 1138 then decide (5 ≤ count1133 b) else (if i < 1139 then decide (6 ≤ count1133 b) else decide (7 ≤ count1133 b))) else (if i < 1142 then (if i < 1141 then decide (8 ≤ count1133 b) else decide (1 ≤ count1141 b)) else (if i < 1143 then decide (2 ≤ count1141 b) else decide (3 ≤ count1141 b))))))) else (if i < 1171 then (if i < 1157 then (if i < 1150 then (if i < 1147 then (if i < 1145 then decide (4 ≤ count1141 b) else (if i < 1146 then decide (5 ≤ count1141 b) else decide (6 ≤ count1141 b))) else (if i < 1148 then decide (7 ≤ count1141 b) else (if i < 1149 then decide (8 ≤ count1141 b) else decide (9 ≤ count1141 b)))) else (if i < 1153 then (if i < 1151 then decide (10 ≤ count1141 b) else (if i < 1152 then decide (11 ≤ count1141 b) else decide (12 ≤ count1141 b))) else (if i < 1155 then (if i < 1154 then decide (13 ≤ count1141 b) else decide (14 ≤ count1141 b)) else (if i < 1156 then decide (15 ≤ count1141 b) else decide (1 ≤ count1156 b))))) else (if i < 1164 then (if i < 1160 then (if i < 1158 then decide (2 ≤ count1156 b) else (if i < 1159 then decide (1 ≤ count1158 b) else decide (2 ≤ count1158 b))) else (if i < 1162 then (if i < 1161 then decide (3 ≤ count1158 b) else decide (1 ≤ count1161 b)) else (if i < 1163 then decide (2 ≤ count1161 b) else decide (1 ≤ count1163 b)))) else (if i < 1167 then (if i < 1165 then decide (2 ≤ count1163 b) else (if i < 1166 then decide (1 ≤ count1165 b) else decide (2 ≤ count1165 b))) else (if i < 1169 then (if i < 1168 then decide (3 ≤ count1165 b) else decide (4 ≤ count1165 b)) else (if i < 1170 then decide (1 ≤ count1169 b) else decide (2 ≤ count1169 b)))))) else (if i < 1185 then (if i < 1178 then (if i < 1174 then (if i < 1172 then decide (3 ≤ count1169 b) else (if i < 1173 then decide (4 ≤ count1169 b) else decide (5 ≤ count1169 b))) else (if i < 1176 then (if i < 1175 then decide (6 ≤ count1169 b) else decide (7 ≤ count1169 b)) else (if i < 1177 then decide (1 ≤ count1176 b) else decide (2 ≤ count1176 b)))) else (if i < 1181 then (if i < 1179 then decide (1 ≤ count1178 b) else (if i < 1180 then decide (2 ≤ count1178 b) else decide (1 ≤ count1180 b))) else (if i < 1183 then (if i < 1182 then decide (2 ≤ count1180 b) else decide (3 ≤ count1180 b)) else (if i < 1184 then decide (4 ≤ count1180 b) else decide (1 ≤ count1184 b))))) else (if i < 1192 then (if i < 1188 then (if i < 1186 then decide (2 ≤ count1184 b) else (if i < 1187 then decide (1 ≤ count1186 b) else decide (2 ≤ count1186 b))) else (if i < 1190 then (if i < 1189 then decide (1 ≤ count1188 b) else decide (2 ≤ count1188 b)) else (if i < 1191 then decide (3 ≤ count1188 b) else decide (4 ≤ count1188 b)))) else (if i < 1195 then (if i < 1193 then decide (1 ≤ count1192 b) else (if i < 1194 then decide (2 ≤ count1192 b) else decide (3 ≤ count1192 b))) else (if i < 1197 then (if i < 1196 then decide (4 ≤ count1192 b) else decide (5 ≤ count1192 b)) else (if i < 1198 then decide (6 ≤ count1192 b) else decide (7 ≤ count1192 b)))))))) else (if i < 1253 then (if i < 1226 then (if i < 1212 then (if i < 1205 then (if i < 1202 then (if i < 1200 then decide (8 ≤ count1192 b) else (if i < 1201 then decide (1 ≤ count1200 b) else decide (2 ≤ count1200 b))) else (if i < 1203 then decide (3 ≤ count1200 b) else (if i < 1204 then decide (4 ≤ count1200 b) else decide (5 ≤ count1200 b)))) else (if i < 1208 then (if i < 1206 then decide (6 ≤ count1200 b) else (if i < 1207 then decide (7 ≤ count1200 b) else decide (8 ≤ count1200 b))) else (if i < 1210 then (if i < 1209 then decide (9 ≤ count1200 b) else decide (10 ≤ count1200 b)) else (if i < 1211 then decide (11 ≤ count1200 b) else decide (12 ≤ count1200 b))))) else (if i < 1219 then (if i < 1215 then (if i < 1213 then decide (13 ≤ count1200 b) else (if i < 1214 then decide (14 ≤ count1200 b) else decide (15 ≤ count1200 b))) else (if i < 1217 then (if i < 1216 then decide (1 ≤ count1215 b) else decide (2 ≤ count1215 b)) else (if i < 1218 then decide (3 ≤ count1215 b) else decide (4 ≤ count1215 b)))) else (if i < 1222 then (if i < 1220 then decide (5 ≤ count1215 b) else (if i < 1221 then decide (6 ≤ count1215 b) else decide (7 ≤ count1215 b))) else (if i < 1224 then (if i < 1223 then decide (8 ≤ count1215 b) else decide (9 ≤ count1215 b)) else (if i < 1225 then decide (10 ≤ count1215 b) else decide (11 ≤ count1215 b)))))) else (if i < 1239 then (if i < 1232 then (if i < 1229 then (if i < 1227 then decide (12 ≤ count1215 b) else (if i < 1228 then decide (13 ≤ count1215 b) else decide (14 ≤ count1215 b))) else (if i < 1230 then decide (15 ≤ count1215 b) else (if i < 1231 then decide (16 ≤ count1215 b) else decide (17 ≤ count1215 b)))) else (if i < 1235 then (if i < 1233 then decide (18 ≤ count1215 b) else (if i < 1234 then decide (19 ≤ count1215 b) else decide (20 ≤ count1215 b))) else (if i < 1237 then (if i < 1236 then decide (21 ≤ count1215 b) else decide (22 ≤ count1215 b)) else (if i < 1238 then decide (23 ≤ count1215 b) else decide (24 ≤ count1215 b))))) else (if i < 1246 then (if i < 1242 then (if i < 1240 then decide (25 ≤ count1215 b) else (if i < 1241 then decide (26 ≤ count1215 b) else decide (27 ≤ count1215 b))) else (if i < 1244 then (if i < 1243 then decide (28 ≤ count1215 b) else decide (29 ≤ count1215 b)) else (if i < 1245 then decide (30 ≤ count1215 b) else decide (1 ≤ count1245 b)))) else (if i < 1249 then (if i < 1247 then decide (2 ≤ count1245 b) else (if i < 1248 then decide (1 ≤ count1247 b) else decide (2 ≤ count1247 b))) else (if i < 1251 then (if i < 1250 then decide (3 ≤ count1247 b) else decide (1 ≤ count1250 b)) else (if i < 1252 then decide (2 ≤ count1250 b) else decide (1 ≤ count1252 b))))))) else (if i < 1280 then (if i < 1266 then (if i < 1259 then (if i < 1256 then (if i < 1254 then decide (2 ≤ count1252 b) else (if i < 1255 then decide (1 ≤ count1254 b) else decide (2 ≤ count1254 b))) else (if i < 1257 then decide (3 ≤ count1254 b) else (if i < 1258 then decide (4 ≤ count1254 b) else decide (1 ≤ count1258 b)))) else (if i < 1262 then (if i < 1260 then decide (2 ≤ count1258 b) else (if i < 1261 then decide (3 ≤ count1258 b) else decide (4 ≤ count1258 b))) else (if i < 1264 then (if i < 1263 then decide (5 ≤ count1258 b) else decide (6 ≤ count1258 b)) else (if i < 1265 then decide (7 ≤ count1258 b) else decide (1 ≤ count1265 b))))) else (if i < 1273 then (if i < 1269 then (if i < 1267 then decide (2 ≤ count1265 b) else (if i < 1268 then decide (1 ≤ count1267 b) else decide (2 ≤ count1267 b))) else (if i < 1271 then (if i < 1270 then decide (1 ≤ count1269 b) else decide (2 ≤ count1269 b)) else (if i < 1272 then decide (3 ≤ count1269 b) else decide (4 ≤ count1269 b)))) else (if i < 1276 then (if i < 1274 then decide (1 ≤ count1273 b) else (if i < 1275 then decide (2 ≤ count1273 b) else decide (1 ≤ count1275 b))) else (if i < 1278 then (if i < 1277 then decide (2 ≤ count1275 b) else decide (1 ≤ count1277 b)) else (if i < 1279 then decide (2 ≤ count1277 b) else decide (3 ≤ count1277 b)))))) else (if i < 1294 then (if i < 1287 then (if i < 1283 then (if i < 1281 then decide (4 ≤ count1277 b) else (if i < 1282 then decide (1 ≤ count1281 b) else decide (2 ≤ count1281 b))) else (if i < 1285 then (if i < 1284 then decide (3 ≤ count1281 b) else decide (4 ≤ count1281 b)) else (if i < 1286 then decide (5 ≤ count1281 b) else decide (6 ≤ count1281 b)))) else (if i < 1290 then (if i < 1288 then decide (7 ≤ count1281 b) else (if i < 1289 then decide (8 ≤ count1281 b) else decide (1 ≤ count1289 b))) else (if i < 1292 then (if i < 1291 then decide (2 ≤ count1289 b) else decide (3 ≤ count1289 b)) else (if i < 1293 then decide (4 ≤ count1289 b) else decide (5 ≤ count1289 b))))) else (if i < 1301 then (if i < 1297 then (if i < 1295 then decide (6 ≤ count1289 b) else (if i < 1296 then decide (7 ≤ count1289 b) else decide (8 ≤ count1289 b))) else (if i < 1299 then (if i < 1298 then decide (9 ≤ count1289 b) else decide (10 ≤ count1289 b)) else (if i < 1300 then decide (11 ≤ count1289 b) else decide (12 ≤ count1289 b)))) else (if i < 1304 then (if i < 1302 then decide (13 ≤ count1289 b) else (if i < 1303 then decide (14 ≤ count1289 b) else decide (15 ≤ count1289 b))) else (if i < 1306 then (if i < 1305 then decide (1 ≤ count1304 b) else decide (2 ≤ count1304 b)) else (if i < 1307 then decide (1 ≤ count1306 b) else decide (2 ≤ count1306 b)))))))))) else (if i < 1526 then (if i < 1417 then (if i < 1362 then (if i < 1335 then (if i < 1321 then (if i < 1314 then (if i < 1311 then (if i < 1309 then decide (1 ≤ count1308 b) else (if i < 1310 then decide (2 ≤ count1308 b) else decide (3 ≤ count1308 b))) else (if i < 1312 then decide (4 ≤ count1308 b) else (if i < 1313 then decide (1 ≤ count1312 b) else decide (2 ≤ count1312 b)))) else (if i < 1317 then (if i < 1315 then decide (1 ≤ count1314 b) else (if i < 1316 then decide (2 ≤ count1314 b) else decide (1 ≤ count1316 b))) else (if i < 1319 then (if i < 1318 then decide (2 ≤ count1316 b) else decide (3 ≤ count1316 b)) else (if i < 1320 then decide (4 ≤ count1316 b) else decide (1 ≤ count1320 b))))) else (if i < 1328 then (if i < 1324 then (if i < 1322 then decide (2 ≤ count1320 b) else (if i < 1323 then decide (3 ≤ count1320 b) else decide (4 ≤ count1320 b))) else (if i < 1326 then (if i < 1325 then decide (5 ≤ count1320 b) else decide (6 ≤ count1320 b)) else (if i < 1327 then decide (7 ≤ count1320 b) else decide (8 ≤ count1320 b)))) else (if i < 1331 then (if i < 1329 then decide (1 ≤ count1328 b) else (if i < 1330 then decide (2 ≤ count1328 b) else decide (1 ≤ count1330 b))) else (if i < 1333 then (if i < 1332 then decide (2 ≤ count1330 b) else decide (1 ≤ count1332 b)) else (if i < 1334 then decide (2 ≤ count1332 b) else decide (3 ≤ count1332 b)))))) else (if i < 1348 then (if i < 1341 then (if i < 1338 then (if i < 1336 then decide (4 ≤ count1332 b) else (if i < 1337 then decide (1 ≤ count1336 b) else decide (2 ≤ count1336 b))) else (if i < 1339 then decide (1 ≤ count1338 b) else (if i < 1340 then decide (2 ≤ count1338 b) else decide (1 ≤ count1340 b)))) else (if i < 1344 then (if i < 1342 then decide (2 ≤ count1340 b) else (if i < 1343 then decide (3 ≤ count1340 b) else decide (4 ≤ count1340 b))) else (if i < 1346 then (if i < 1345 then decide (1 ≤ count1344 b) else decide (2 ≤ count1344 b)) else (if i < 1347 then decide (3 ≤ count1344 b) else decide (4 ≤ count1344 b))))) else (if i < 1355 then (if i < 1351 then (if i < 1349 then decide (5 ≤ count1344 b) else (if i < 1350 then decide (6 ≤ count1344 b) else decide (7 ≤ count1344 b))) else (if i < 1353 then (if i < 1352 then decide (8 ≤ count1344 b) else decide (1 ≤ count1352 b)) else (if i < 1354 then decide (2 ≤ count1352 b) else decide (3 ≤ count1352 b)))) else (if i < 1358 then (if i < 1356 then decide (4 ≤ count1352 b) else (if i < 1357 then decide (5 ≤ count1352 b) else decide (6 ≤ count1352 b))) else (if i < 1360 then (if i < 1359 then decide (7 ≤ count1352 b) else decide (8 ≤ count1352 b)) else (if i < 1361 then decide (9 ≤ count1352 b) else decide (10 ≤ count1352 b))))))) else (if i < 1389 then (if i < 1375 then (if i < 1368 then (if i < 1365 then (if i < 1363 then decide (11 ≤ count1352 b) else (if i < 1364 then decide (12 ≤ count1352 b) else decide (13 ≤ count1352 b))) else (if i < 1366 then decide (14 ≤ count1352 b) else (if i < 1367 then decide (15 ≤ count1352 b) else decide (16 ≤ count1352 b)))) else (if i < 1371 then (if i < 1369 then decide (1 ≤ count1368 b) else (if i < 1370 then decide (2 ≤ count1368 b) else decide (3 ≤ count1368 b))) else (if i < 1373 then (if i < 1372 then decide (4 ≤ count1368 b) else decide (5 ≤ count1368 b)) else (if i < 1374 then decide (6 ≤ count1368 b) else decide (7 ≤ count1368 b))))) else (if i < 1382 then (if i < 1378 then (if i < 1376 then decide (8 ≤ count1368 b) else (if i < 1377 then decide (9 ≤ count1368 b) else decide (10 ≤ count1368 b))) else (if i < 1380 then (if i < 1379 then decide (11 ≤ count1368 b) else decide (12 ≤ count1368 b)) else (if i < 1381 then decide (13 ≤ count1368 b) else decide (14 ≤ count1368 b)))) else (if i < 1385 then (if i < 1383 then decide (15 ≤ count1368 b) else (if i < 1384 then decide (16 ≤ count1368 b) else decide (17 ≤ count1368 b))) else (if i < 1387 then (if i < 1386 then decide (18 ≤ count1368 b) else decide (19 ≤ count1368 b)) else (if i < 1388 then decide (20 ≤ count1368 b) else decide (21 ≤ count1368 b)))))) else (if i < 1403 then (if i < 1396 then (if i < 1392 then (if i < 1390 then decide (22 ≤ count1368 b) else (if i < 1391 then decide (23 ≤ count1368 b) else decide (24 ≤ count1368 b))) else (if i < 1394 then (if i < 1393 then decide (25 ≤ count1368 b) else decide (26 ≤ count1368 b)) else (if i < 1395 then decide (27 ≤ count1368 b) else decide (28 ≤ count1368 b)))) else (if i < 1399 then (if i < 1397 then decide (29 ≤ count1368 b) else (if i < 1398 then decide (30 ≤ count1368 b) else decide (31 ≤ count1368 b))) else (if i < 1401 then (if i < 1400 then decide (1 ≤ count1399 b) else decide (2 ≤ count1399 b)) else (if i < 1402 then decide (3 ≤ count1399 b) else decide (4 ≤ count1399 b))))) else (if i < 1410 then (if i < 1406 then (if i < 1404 then decide (5 ≤ count1399 b) else (if i < 1405 then decide (6 ≤ count1399 b) else decide (7 ≤ count1399 b))) else (if i < 1408 then (if i < 1407 then decide (8 ≤ count1399 b) else decide (9 ≤ count1399 b)) else (if i < 1409 then decide (10 ≤ count1399 b) else decide (11 ≤ count1399 b)))) else (if i < 1413 then (if i < 1411 then decide (12 ≤ count1399 b) else (if i < 1412 then decide (13 ≤ count1399 b) else decide (14 ≤ count1399 b))) else (if i < 1415 then (if i < 1414 then decide (15 ≤ count1399 b) else decide (16 ≤ count1399 b)) else (if i < 1416 then decide (17 ≤ count1399 b) else decide (18 ≤ count1399 b)))))))) else (if i < 1471 then (if i < 1444 then (if i < 1430 then (if i < 1423 then (if i < 1420 then (if i < 1418 then decide (19 ≤ count1399 b) else (if i < 1419 then decide (20 ≤ count1399 b) else decide (21 ≤ count1399 b))) else (if i < 1421 then decide (22 ≤ count1399 b) else (if i < 1422 then decide (23 ≤ count1399 b) else decide (24 ≤ count1399 b)))) else (if i < 1426 then (if i < 1424 then decide (25 ≤ count1399 b) else (if i < 1425 then decide (26 ≤ count1399 b) else decide (27 ≤ count1399 b))) else (if i < 1428 then (if i < 1427 then decide (28 ≤ count1399 b) else decide (29 ≤ count1399 b)) else (if i < 1429 then decide (30 ≤ count1399 b) else decide (31 ≤ count1399 b))))) else (if i < 1437 then (if i < 1433 then (if i < 1431 then decide (32 ≤ count1399 b) else (if i < 1432 then decide (33 ≤ count1399 b) else decide (34 ≤ count1399 b))) else (if i < 1435 then (if i < 1434 then decide (35 ≤ count1399 b) else decide (36 ≤ count1399 b)) else (if i < 1436 then decide (37 ≤ count1399 b) else decide (38 ≤ count1399 b)))) else (if i < 1440 then (if i < 1438 then decide (39 ≤ count1399 b) else (if i < 1439 then decide (40 ≤ count1399 b) else decide (41 ≤ count1399 b))) else (if i < 1442 then (if i < 1441 then decide (42 ≤ count1399 b) else decide (1 ≤ count1441 b)) else (if i < 1443 then decide (2 ≤ count1441 b) else decide (1 ≤ count1443 b)))))) else (if i < 1457 then (if i < 1450 then (if i < 1447 then (if i < 1445 then decide (2 ≤ count1443 b) else (if i < 1446 then decide (3 ≤ count1443 b) else decide (1 ≤ count1446 b))) else (if i < 1448 then decide (2 ≤ count1446 b) else (if i < 1449 then decide (1 ≤ count1448 b) else decide (2 ≤ count1448 b)))) else (if i < 1453 then (if i < 1451 then decide (1 ≤ count1450 b) else (if i < 1452 then decide (2 ≤ count1450 b) else decide (3 ≤ count1450 b))) else (if i < 1455 then (if i < 1454 then decide (4 ≤ count1450 b) else decide (1 ≤ count1454 b)) else (if i < 1456 then decide (2 ≤ count1454 b) else decide (3 ≤ count1454 b))))) else (if i < 1464 then (if i < 1460 then (if i < 1458 then decide (4 ≤ count1454 b) else (if i < 1459 then decide (5 ≤ count1454 b) else decide (6 ≤ count1454 b))) else (if i < 1462 then (if i < 1461 then decide (7 ≤ count1454 b) else decide (1 ≤ count1461 b)) else (if i < 1463 then decide (2 ≤ count1461 b) else decide (1 ≤ count1463 b)))) else (if i < 1467 then (if i < 1465 then decide (2 ≤ count1463 b) else (if i < 1466 then decide (1 ≤ count1465 b) else decide (2 ≤ count1465 b))) else (if i < 1469 then (if i < 1468 then decide (3 ≤ count1465 b) else decide (4 ≤ count1465 b)) else (if i < 1470 then decide (1 ≤ count1469 b) else decide (2 ≤ count1469 b))))))) else (if i < 1498 then (if i < 1484 then (if i < 1477 then (if i < 1474 then (if i < 1472 then decide (1 ≤ count1471 b) else (if i < 1473 then decide (2 ≤ count1471 b) else decide (1 ≤ count1473 b))) else (if i < 1475 then decide (2 ≤ count1473 b) else (if i < 1476 then decide (3 ≤ count1473 b) else decide (4 ≤ count1473 b)))) else (if i < 1480 then (if i < 1478 then decide (1 ≤ count1477 b) else (if i < 1479 then decide (2 ≤ count1477 b) else decide (3 ≤ count1477 b))) else (if i < 1482 then (if i < 1481 then decide (4 ≤ count1477 b) else decide (5 ≤ count1477 b)) else (if i < 1483 then decide (6 ≤ count1477 b) else decide (7 ≤ count1477 b))))) else (if i < 1491 then (if i < 1487 then (if i < 1485 then decide (8 ≤ count1477 b) else (if i < 1486 then decide (1 ≤ count1485 b) else decide (2 ≤ count1485 b))) else (if i < 1489 then (if i < 1488 then decide (3 ≤ count1485 b) else decide (4 ≤ count1485 b)) else (if i < 1490 then decide (5 ≤ count1485 b) else decide (6 ≤ count1485 b)))) else (if i < 1494 then (if i < 1492 then decide (7 ≤ count1485 b) else (if i < 1493 then decide (8 ≤ count1485 b) else decide (9 ≤ count1485 b))) else (if i < 1496 then (if i < 1495 then decide (10 ≤ count1485 b) else decide (11 ≤ count1485 b)) else (if i < 1497 then decide (12 ≤ count1485 b) else decide (13 ≤ count1485 b)))))) else (if i < 1512 then (if i < 1505 then (if i < 1501 then (if i < 1499 then decide (14 ≤ count1485 b) else (if i < 1500 then decide (15 ≤ count1485 b) else decide (1 ≤ count1500 b))) else (if i < 1503 then (if i < 1502 then decide (2 ≤ count1500 b) else decide (1 ≤ count1502 b)) else (if i < 1504 then decide (2 ≤ count1502 b) else decide (3 ≤ count1502 b)))) else (if i < 1508 then (if i < 1506 then decide (1 ≤ count1505 b) else (if i < 1507 then decide (2 ≤ count1505 b) else decide (1 ≤ count1507 b))) else (if i < 1510 then (if i < 1509 then decide (2 ≤ count1507 b) else decide (1 ≤ count1509 b)) else (if i < 1511 then decide (2 ≤ count1509 b) else decide (3 ≤ count1509 b))))) else (if i < 1519 then (if i < 1515 then (if i < 1513 then decide (4 ≤ count1509 b) else (if i < 1514 then decide (1 ≤ count1513 b) else decide (2 ≤ count1513 b))) else (if i < 1517 then (if i < 1516 then decide (3 ≤ count1513 b) else decide (4 ≤ count1513 b)) else (if i < 1518 then decide (5 ≤ count1513 b) else decide (6 ≤ count1513 b)))) else (if i < 1522 then (if i < 1520 then decide (7 ≤ count1513 b) else (if i < 1521 then decide (1 ≤ count1520 b) else decide (2 ≤ count1520 b))) else (if i < 1524 then (if i < 1523 then decide (1 ≤ count1522 b) else decide (2 ≤ count1522 b)) else (if i < 1525 then decide (1 ≤ count1524 b) else decide (2 ≤ count1524 b))))))))) else (if i < 1635 then (if i < 1580 then (if i < 1553 then (if i < 1539 then (if i < 1532 then (if i < 1529 then (if i < 1527 then decide (3 ≤ count1524 b) else (if i < 1528 then decide (4 ≤ count1524 b) else decide (1 ≤ count1528 b))) else (if i < 1530 then decide (2 ≤ count1528 b) else (if i < 1531 then decide (1 ≤ count1530 b) else decide (2 ≤ count1530 b)))) else (if i < 1535 then (if i < 1533 then decide (1 ≤ count1532 b) else (if i < 1534 then decide (2 ≤ count1532 b) else decide (3 ≤ count1532 b))) else (if i < 1537 then (if i < 1536 then decide (4 ≤ count1532 b) else decide (1 ≤ count1536 b)) else (if i < 1538 then decide (2 ≤ count1536 b) else decide (3 ≤ count1536 b))))) else (if i < 1546 then (if i < 1542 then (if i < 1540 then decide (4 ≤ count1536 b) else (if i < 1541 then decide (5 ≤ count1536 b) else decide (6 ≤ count1536 b))) else (if i < 1544 then (if i < 1543 then decide (7 ≤ count1536 b) else decide (8 ≤ count1536 b)) else (if i < 1545 then decide (1 ≤ count1544 b) else decide (2 ≤ count1544 b)))) else (if i < 1549 then (if i < 1547 then decide (3 ≤ count1544 b) else (if i < 1548 then decide (4 ≤ count1544 b) else decide (5 ≤ count1544 b))) else (if i < 1551 then (if i < 1550 then decide (6 ≤ count1544 b) else decide (7 ≤ count1544 b)) else (if i < 1552 then decide (8 ≤ count1544 b) else decide (9 ≤ count1544 b)))))) else (if i < 1566 then (if i < 1559 then (if i < 1556 then (if i < 1554 then decide (10 ≤ count1544 b) else (if i < 1555 then decide (11 ≤ count1544 b) else decide (12 ≤ count1544 b))) else (if i < 1557 then decide (13 ≤ count1544 b) else (if i < 1558 then decide (14 ≤ count1544 b) else decide (15 ≤ count1544 b)))) else (if i < 1562 then (if i < 1560 then decide (1 ≤ count1559 b) else (if i < 1561 then decide (2 ≤ count1559 b) else decide (3 ≤ count1559 b))) else (if i < 1564 then (if i < 1563 then decide (4 ≤ count1559 b) else decide (5 ≤ count1559 b)) else (if i < 1565 then decide (6 ≤ count1559 b) else decide (7 ≤ count1559 b))))) else (if i < 1573 then (if i < 1569 then (if i < 1567 then decide (8 ≤ count1559 b) else (if i < 1568 then decide (9 ≤ count1559 b) else decide (10 ≤ count1559 b))) else (if i < 1571 then (if i < 1570 then decide (11 ≤ count1559 b) else decide (12 ≤ count1559 b)) else (if i < 1572 then decide (13 ≤ count1559 b) else decide (14 ≤ count1559 b)))) else (if i < 1576 then (if i < 1574 then decide (15 ≤ count1559 b) else (if i < 1575 then decide (16 ≤ count1559 b) else decide (17 ≤ count1559 b))) else (if i < 1578 then (if i < 1577 then decide (18 ≤ count1559 b) else decide (19 ≤ count1559 b)) else (if i < 1579 then decide (20 ≤ count1559 b) else decide (21 ≤ count1559 b))))))) else (if i < 1607 then (if i < 1593 then (if i < 1586 then (if i < 1583 then (if i < 1581 then decide (1 ≤ count1580 b) else (if i < 1582 then decide (2 ≤ count1580 b) else decide (1 ≤ count1582 b))) else (if i < 1584 then decide (2 ≤ count1582 b) else (if i < 1585 then decide (3 ≤ count1582 b) else decide (1 ≤ count1585 b)))) else (if i < 1589 then (if i < 1587 then decide (2 ≤ count1585 b) else (if i < 1588 then decide (1 ≤ count1587 b) else decide (2 ≤ count1587 b))) else (if i < 1591 then (if i < 1590 then decide (1 ≤ count1589 b) else decide (2 ≤ count1589 b)) else (if i < 1592 then decide (3 ≤ count1589 b) else decide (4 ≤ count1589 b))))) else (if i < 1600 then (if i < 1596 then (if i < 1594 then decide (1 ≤ count1593 b) else (if i < 1595 then decide (2 ≤ count1593 b) else decide (3 ≤ count1593 b))) else (if i < 1598 then (if i < 1597 then decide (4 ≤ count1593 b) else decide (5 ≤ count1593 b)) else (if i < 1599 then decide (6 ≤ count1593 b) else decide (7 ≤ count1593 b)))) else (if i < 1603 then (if i < 1601 then decide (1 ≤ count1600 b) else (if i < 1602 then decide (2 ≤ count1600 b) else decide (1 ≤ count1602 b))) else (if i < 1605 then (if i < 1604 then decide (2 ≤ count1602 b) else decide (1 ≤ count1604 b)) else (if i < 1606 then decide (2 ≤ count1604 b) else decide (3 ≤ count1604 b)))))) else (if i < 1621 then (if i < 1614 then (if i < 1610 then (if i < 1608 then decide (4 ≤ count1604 b) else (if i < 1609 then decide (1 ≤ count1608 b) else decide (2 ≤ count1608 b))) else (if i < 1612 then (if i < 1611 then decide (1 ≤ count1610 b) else decide (2 ≤ count1610 b)) else (if i < 1613 then decide (1 ≤ count1612 b) else decide (2 ≤ count1612 b)))) else (if i < 1617 then (if i < 1615 then decide (3 ≤ count1612 b) else (if i < 1616 then decide (4 ≤ count1612 b) else decide (1 ≤ count1616 b))) else (if i < 1619 then (if i < 1618 then decide (2 ≤ count1616 b) else decide (3 ≤ count1616 b)) else (if i < 1620 then decide (4 ≤ count1616 b) else decide (5 ≤ count1616 b))))) else (if i < 1628 then (if i < 1624 then (if i < 1622 then decide (6 ≤ count1616 b) else (if i < 1623 then decide (7 ≤ count1616 b) else decide (8 ≤ count1616 b))) else (if i < 1626 then (if i < 1625 then decide (1 ≤ count1624 b) else decide (2 ≤ count1624 b)) else (if i < 1627 then decide (3 ≤ count1624 b) else decide (4 ≤ count1624 b)))) else (if i < 1631 then (if i < 1629 then decide (5 ≤ count1624 b) else (if i < 1630 then decide (6 ≤ count1624 b) else decide (7 ≤ count1624 b))) else (if i < 1633 then (if i < 1632 then decide (8 ≤ count1624 b) else decide (9 ≤ count1624 b)) else (if i < 1634 then decide (10 ≤ count1624 b) else decide (11 ≤ count1624 b)))))))) else (if i < 1690 then (if i < 1662 then (if i < 1648 then (if i < 1641 then (if i < 1638 then (if i < 1636 then decide (12 ≤ count1624 b) else (if i < 1637 then decide (13 ≤ count1624 b) else decide (14 ≤ count1624 b))) else (if i < 1639 then decide (15 ≤ count1624 b) else (if i < 1640 then decide (1 ≤ count1639 b) else decide (2 ≤ count1639 b)))) else (if i < 1644 then (if i < 1642 then decide (1 ≤ count1641 b) else (if i < 1643 then decide (2 ≤ count1641 b) else decide (1 ≤ count1643 b))) else (if i < 1646 then (if i < 1645 then decide (2 ≤ count1643 b) else decide (3 ≤ count1643 b)) else (if i < 1647 then decide (4 ≤ count1643 b) else decide (1 ≤ count1647 b))))) else (if i < 1655 then (if i < 1651 then (if i < 1649 then decide (2 ≤ count1647 b) else (if i < 1650 then decide (1 ≤ count1649 b) else decide (2 ≤ count1649 b))) else (if i < 1653 then (if i < 1652 then decide (1 ≤ count1651 b) else decide (2 ≤ count1651 b)) else (if i < 1654 then decide (3 ≤ count1651 b) else decide (4 ≤ count1651 b)))) else (if i < 1658 then (if i < 1656 then decide (1 ≤ count1655 b) else (if i < 1657 then decide (2 ≤ count1655 b) else decide (3 ≤ count1655 b))) else (if i < 1660 then (if i < 1659 then decide (4 ≤ count1655 b) else decide (5 ≤ count1655 b)) else (if i < 1661 then decide (6 ≤ count1655 b) else decide (7 ≤ count1655 b)))))) else (if i < 1676 then (if i < 1669 then (if i < 1665 then (if i < 1663 then decide (8 ≤ count1655 b) else (if i < 1664 then decide (1 ≤ count1663 b) else decide (2 ≤ count1663 b))) else (if i < 1667 then (if i < 1666 then decide (1 ≤ count1665 b) else decide (2 ≤ count1665 b)) else (if i < 1668 then decide (1 ≤ count1667 b) else decide (2 ≤ count1667 b)))) else (if i < 1672 then (if i < 1670 then decide (3 ≤ count1667 b) else (if i < 1671 then decide (4 ≤ count1667 b) else decide (1 ≤ count1671 b))) else (if i < 1674 then (if i < 1673 then decide (2 ≤ count1671 b) else decide (1 ≤ count1673 b)) else (if i < 1675 then decide (2 ≤ count1673 b) else decide (1 ≤ count1675 b))))) else (if i < 1683 then (if i < 1679 then (if i < 1677 then decide (2 ≤ count1675 b) else (if i < 1678 then decide (3 ≤ count1675 b) else decide (4 ≤ count1675 b))) else (if i < 1681 then (if i < 1680 then decide (1 ≤ count1679 b) else decide (2 ≤ count1679 b)) else (if i < 1682 then decide (3 ≤ count1679 b) else decide (4 ≤ count1679 b)))) else (if i < 1686 then (if i < 1684 then decide (5 ≤ count1679 b) else (if i < 1685 then decide (6 ≤ count1679 b) else decide (7 ≤ count1679 b))) else (if i < 1688 then (if i < 1687 then decide (8 ≤ count1679 b) else decide (1 ≤ count1687 b)) else (if i < 1689 then decide (2 ≤ count1687 b) else decide (3 ≤ count1687 b))))))) else (if i < 1717 then (if i < 1703 then (if i < 1696 then (if i < 1693 then (if i < 1691 then decide (4 ≤ count1687 b) else (if i < 1692 then decide (5 ≤ count1687 b) else decide (6 ≤ count1687 b))) else (if i < 1694 then decide (7 ≤ count1687 b) else (if i < 1695 then decide (8 ≤ count1687 b) else decide (9 ≤ count1687 b)))) else (if i < 1699 then (if i < 1697 then decide (10 ≤ count1687 b) else (if i < 1698 then decide (11 ≤ count1687 b) else decide (12 ≤ count1687 b))) else (if i < 1701 then (if i < 1700 then decide (13 ≤ count1687 b) else decide (14 ≤ count1687 b)) else (if i < 1702 then decide (15 ≤ count1687 b) else decide (16 ≤ count1687 b))))) else (if i < 1710 then (if i < 1706 then (if i < 1704 then decide (1 ≤ count1703 b) else (if i < 1705 then decide (2 ≤ count1703 b) else decide (3 ≤ count1703 b))) else (if i < 1708 then (if i < 1707 then decide (4 ≤ count1703 b) else decide (5 ≤ count1703 b)) else (if i < 1709 then decide (6 ≤ count1703 b) else decide (7 ≤ count1703 b)))) else (if i < 1713 then (if i < 1711 then decide (8 ≤ count1703 b) else (if i < 1712 then decide (9 ≤ count1703 b) else decide (10 ≤ count1703 b))) else (if i < 1715 then (if i < 1714 then decide (11 ≤ count1703 b) else decide (12 ≤ count1703 b)) else (if i < 1716 then decide (13 ≤ count1703 b) else decide (14 ≤ count1703 b)))))) else (if i < 1731 then (if i < 1724 then (if i < 1720 then (if i < 1718 then decide (15 ≤ count1703 b) else (if i < 1719 then decide (16 ≤ count1703 b) else decide (17 ≤ count1703 b))) else (if i < 1722 then (if i < 1721 then decide (18 ≤ count1703 b) else decide (19 ≤ count1703 b)) else (if i < 1723 then decide (20 ≤ count1703 b) else decide (21 ≤ count1703 b)))) else (if i < 1727 then (if i < 1725 then decide (1 ≤ count1724 b) else (if i < 1726 then decide (2 ≤ count1724 b) else decide (3 ≤ count1724 b))) else (if i < 1729 then (if i < 1728 then decide (4 ≤ count1724 b) else decide (5 ≤ count1724 b)) else (if i < 1730 then decide (6 ≤ count1724 b) else decide (7 ≤ count1724 b))))) else (if i < 1738 then (if i < 1734 then (if i < 1732 then decide (8 ≤ count1724 b) else (if i < 1733 then decide (9 ≤ count1724 b) else decide (10 ≤ count1724 b))) else (if i < 1736 then (if i < 1735 then decide (11 ≤ count1724 b) else decide (12 ≤ count1724 b)) else (if i < 1737 then decide (13 ≤ count1724 b) else decide (14 ≤ count1724 b)))) else (if i < 1741 then (if i < 1739 then decide (15 ≤ count1724 b) else (if i < 1740 then decide (16 ≤ count1724 b) else decide (17 ≤ count1724 b))) else (if i < 1743 then (if i < 1742 then decide (18 ≤ count1724 b) else decide (19 ≤ count1724 b)) else (if i < 1744 then decide (20 ≤ count1724 b) else decide (21 ≤ count1724 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (34 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (36 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (37 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (38 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (40 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (41 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (42 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (43 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (44 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (46 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (48 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (49 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (51 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (53 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (55 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (56 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (57 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (62 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (63 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (96 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (97 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (98 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (99 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (103 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (105 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (107 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (108 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (109 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (111 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (112 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (114 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (115 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (116 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (118 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (119 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (120 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (121 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (122 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (124 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (125 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (126 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (127 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (160 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (161 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (163 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (167 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (168 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (173 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (175 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (176 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (178 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (179 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (180 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (182 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (184 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (186 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (187 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (188 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (189 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (228 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (229 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (230 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (233 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (234 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (235 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (238 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (240 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (243 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (245 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (247 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (248 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (249 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (254 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (255 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (288 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (289 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (290 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (291 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (295 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (296 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (300 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (301 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (303 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (306 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (307 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (308 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (310 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (314 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (315 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (316 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (317 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (352 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (356 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (357 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (358 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (359 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (360 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (361 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (362 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (363 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (366 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (368 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (371 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (373 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (375 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (376 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (377 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (378 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (379 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (381 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (382 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (424 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (425 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (427 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (440 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (443 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (493 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (495 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (507 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (511 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (36 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (37 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (38 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (40 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (41 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (42 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (43 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (44 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (48 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (49 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (53 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (55 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (56 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (57 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (62 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (63 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (96 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (97 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (98 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (103 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (107 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (108 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (109 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (111 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (121 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (124 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (126 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (127 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (163 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (180 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (187 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (228 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (233 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (235 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (240 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (254 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (289 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (290 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (295 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (301 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (306 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (308 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (310 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (314 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (315 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (316 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (352 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (356 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (358 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (360 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (361 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (362 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (363 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (366 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (371 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (373 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (375 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (377 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (379 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (381 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (382 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (424 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (511 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
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
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value350 (q : Snake 81) : valuation q 350 = decide (2 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value352 (q : Snake 81) : valuation q 352 = decide (2 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value356 (q : Snake 81) : valuation q 356 = decide (2 ≤ count355 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value384 (q : Snake 81) : valuation q 384 = decide (2 ≤ count383 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value414 (q : Snake 81) : valuation q 414 = decide (2 ≤ count413 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value440 (q : Snake 81) : valuation q 440 = decide (2 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value442 (q : Snake 81) : valuation q 442 = decide (2 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value460 (q : Snake 81) : valuation q 460 = decide (2 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value468 (q : Snake 81) : valuation q 468 = decide (2 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value470 (q : Snake 81) : valuation q 470 = decide (2 ≤ count469 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value472 (q : Snake 81) : valuation q 472 = decide (2 ≤ count471 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value474 (q : Snake 81) : valuation q 474 = decide (2 ≤ count473 (baseVal q)) := rfl
theorem value476 (q : Snake 81) : valuation q 476 = decide (2 ≤ count475 (baseVal q)) := rfl
theorem value809 (q : Snake 81) : valuation q 809 = decide (1 ≤ count809 (baseVal q)) := rfl
theorem value811 (q : Snake 81) : valuation q 811 = decide (1 ≤ count811 (baseVal q)) := rfl
theorem value814 (q : Snake 81) : valuation q 814 = decide (1 ≤ count814 (baseVal q)) := rfl
theorem value817 (q : Snake 81) : valuation q 817 = decide (2 ≤ count816 (baseVal q)) := rfl
theorem value820 (q : Snake 81) : valuation q 820 = decide (3 ≤ count818 (baseVal q)) := rfl
theorem value825 (q : Snake 81) : valuation q 825 = decide (4 ≤ count822 (baseVal q)) := rfl
theorem value834 (q : Snake 81) : valuation q 834 = decide (1 ≤ count834 (baseVal q)) := rfl
theorem value836 (q : Snake 81) : valuation q 836 = decide (1 ≤ count836 (baseVal q)) := rfl
theorem value839 (q : Snake 81) : valuation q 839 = decide (2 ≤ count838 (baseVal q)) := rfl
theorem value843 (q : Snake 81) : valuation q 843 = decide (2 ≤ count842 (baseVal q)) := rfl
theorem value854 (q : Snake 81) : valuation q 854 = decide (6 ≤ count849 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (1 ≤ count863 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (1 ≤ count865 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (2 ≤ count868 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (1 ≤ count870 (baseVal q)) := rfl
theorem value874 (q : Snake 81) : valuation q 874 = decide (3 ≤ count872 (baseVal q)) := rfl
theorem value879 (q : Snake 81) : valuation q 879 = decide (4 ≤ count876 (baseVal q)) := rfl
theorem value891 (q : Snake 81) : valuation q 891 = decide (1 ≤ count891 (baseVal q)) := rfl
theorem value893 (q : Snake 81) : valuation q 893 = decide (1 ≤ count893 (baseVal q)) := rfl
theorem value894 (q : Snake 81) : valuation q 894 = decide (2 ≤ count893 (baseVal q)) := rfl
theorem value896 (q : Snake 81) : valuation q 896 = decide (2 ≤ count895 (baseVal q)) := rfl
theorem value900 (q : Snake 81) : valuation q 900 = decide (2 ≤ count899 (baseVal q)) := rfl
theorem value912 (q : Snake 81) : valuation q 912 = decide (6 ≤ count907 (baseVal q)) := rfl
theorem value933 (q : Snake 81) : valuation q 933 = decide (12 ≤ count922 (baseVal q)) := rfl
theorem value947 (q : Snake 81) : valuation q 947 = decide (2 ≤ count946 (baseVal q)) := rfl
theorem value951 (q : Snake 81) : valuation q 951 = decide (2 ≤ count950 (baseVal q)) := rfl
theorem value955 (q : Snake 81) : valuation q 955 = decide (2 ≤ count954 (baseVal q)) := rfl
theorem value963 (q : Snake 81) : valuation q 963 = decide (1 ≤ count963 (baseVal q)) := rfl
theorem value965 (q : Snake 81) : valuation q 965 = decide (1 ≤ count965 (baseVal q)) := rfl
theorem value977 (q : Snake 81) : valuation q 977 = decide (1 ≤ count977 (baseVal q)) := rfl
theorem value987 (q : Snake 81) : valuation q 987 = decide (3 ≤ count985 (baseVal q)) := rfl
theorem value1000 (q : Snake 81) : valuation q 1000 = decide (1 ≤ count1000 (baseVal q)) := rfl
theorem value1002 (q : Snake 81) : valuation q 1002 = decide (1 ≤ count1002 (baseVal q)) := rfl
theorem value1005 (q : Snake 81) : valuation q 1005 = decide (1 ≤ count1005 (baseVal q)) := rfl
theorem value1009 (q : Snake 81) : valuation q 1009 = decide (1 ≤ count1009 (baseVal q)) := rfl
theorem value1014 (q : Snake 81) : valuation q 1014 = decide (2 ≤ count1013 (baseVal q)) := rfl
theorem value1022 (q : Snake 81) : valuation q 1022 = decide (1 ≤ count1022 (baseVal q)) := rfl
theorem value1024 (q : Snake 81) : valuation q 1024 = decide (1 ≤ count1024 (baseVal q)) := rfl
theorem value1030 (q : Snake 81) : valuation q 1030 = decide (1 ≤ count1030 (baseVal q)) := rfl
theorem value1032 (q : Snake 81) : valuation q 1032 = decide (1 ≤ count1032 (baseVal q)) := rfl
theorem value1037 (q : Snake 81) : valuation q 1037 = decide (2 ≤ count1036 (baseVal q)) := rfl
theorem value1047 (q : Snake 81) : valuation q 1047 = decide (4 ≤ count1044 (baseVal q)) := rfl
theorem value1065 (q : Snake 81) : valuation q 1065 = decide (7 ≤ count1059 (baseVal q)) := rfl
theorem value1096 (q : Snake 81) : valuation q 1096 = decide (19 ≤ count1078 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (1 ≤ count1441 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (2 ≤ count1441 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (1 ≤ count1443 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (2 ≤ count1443 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (3 ≤ count1443 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (1 ≤ count1446 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (2 ≤ count1446 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (1 ≤ count1448 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (2 ≤ count1448 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (1 ≤ count1450 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (2 ≤ count1450 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (3 ≤ count1450 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (4 ≤ count1450 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (1 ≤ count1454 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (2 ≤ count1454 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (3 ≤ count1454 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (4 ≤ count1454 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (5 ≤ count1454 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (1 ≤ count1461 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (2 ≤ count1461 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (1 ≤ count1463 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (2 ≤ count1463 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (1 ≤ count1465 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (2 ≤ count1465 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (3 ≤ count1465 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (4 ≤ count1465 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (1 ≤ count1469 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (2 ≤ count1469 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (1 ≤ count1471 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (2 ≤ count1471 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (1 ≤ count1473 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (2 ≤ count1473 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (3 ≤ count1473 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (4 ≤ count1473 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (1 ≤ count1477 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (2 ≤ count1477 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (3 ≤ count1477 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (4 ≤ count1477 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (5 ≤ count1477 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (6 ≤ count1477 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (7 ≤ count1477 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (2 ≤ count1485 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (3 ≤ count1485 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (4 ≤ count1485 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (5 ≤ count1485 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (6 ≤ count1485 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (7 ≤ count1485 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (8 ≤ count1485 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (9 ≤ count1485 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (10 ≤ count1485 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (1 ≤ count1500 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (2 ≤ count1500 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (1 ≤ count1502 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (2 ≤ count1502 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (3 ≤ count1502 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (1 ≤ count1505 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (2 ≤ count1505 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (1 ≤ count1507 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (2 ≤ count1507 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (1 ≤ count1509 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (2 ≤ count1509 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (3 ≤ count1509 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (4 ≤ count1509 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (1 ≤ count1513 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (2 ≤ count1513 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (3 ≤ count1513 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (4 ≤ count1513 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (5 ≤ count1513 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (6 ≤ count1513 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (7 ≤ count1513 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (1 ≤ count1520 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (2 ≤ count1520 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (1 ≤ count1522 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (2 ≤ count1522 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (1 ≤ count1524 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (2 ≤ count1524 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (3 ≤ count1524 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (4 ≤ count1524 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (1 ≤ count1528 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (2 ≤ count1528 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (1 ≤ count1530 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (2 ≤ count1530 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (1 ≤ count1532 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (2 ≤ count1532 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (3 ≤ count1532 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (4 ≤ count1532 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (1 ≤ count1536 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (2 ≤ count1536 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (3 ≤ count1536 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (4 ≤ count1536 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (5 ≤ count1536 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (6 ≤ count1536 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (7 ≤ count1536 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (3 ≤ count1544 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (4 ≤ count1544 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (5 ≤ count1544 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (6 ≤ count1544 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (7 ≤ count1544 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (8 ≤ count1544 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (9 ≤ count1544 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (10 ≤ count1544 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (11 ≤ count1544 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (8 ≤ count1559 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (9 ≤ count1559 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (10 ≤ count1559 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (11 ≤ count1559 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (12 ≤ count1559 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (13 ≤ count1559 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (14 ≤ count1559 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (15 ≤ count1559 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (16 ≤ count1559 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (17 ≤ count1559 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (1 ≤ count1580 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (1 ≤ count1582 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (2 ≤ count1582 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (3 ≤ count1582 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (1 ≤ count1585 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (2 ≤ count1585 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (1 ≤ count1587 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (2 ≤ count1587 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (1 ≤ count1589 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (2 ≤ count1589 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (3 ≤ count1589 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (4 ≤ count1589 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (1 ≤ count1593 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (2 ≤ count1593 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (3 ≤ count1593 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (4 ≤ count1593 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (7 ≤ count1593 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (1 ≤ count1600 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (2 ≤ count1600 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (1 ≤ count1602 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (2 ≤ count1602 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (1 ≤ count1604 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (2 ≤ count1604 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (3 ≤ count1604 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (1 ≤ count1608 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (2 ≤ count1608 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (1 ≤ count1610 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (2 ≤ count1610 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (1 ≤ count1612 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (2 ≤ count1612 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (3 ≤ count1612 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (1 ≤ count1616 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (2 ≤ count1616 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (3 ≤ count1616 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (4 ≤ count1616 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (5 ≤ count1616 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (2 ≤ count1624 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (3 ≤ count1624 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (4 ≤ count1624 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (5 ≤ count1624 (baseVal q)) := rfl
theorem value1629 (q : Snake 81) : valuation q 1629 = decide (6 ≤ count1624 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (7 ≤ count1624 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (9 ≤ count1624 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (1 ≤ count1639 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (2 ≤ count1639 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (1 ≤ count1641 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (2 ≤ count1641 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (1 ≤ count1643 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (2 ≤ count1643 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (3 ≤ count1643 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (4 ≤ count1643 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (1 ≤ count1647 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (2 ≤ count1647 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (1 ≤ count1649 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (2 ≤ count1649 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (1 ≤ count1651 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (2 ≤ count1651 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (3 ≤ count1651 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (4 ≤ count1651 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (1 ≤ count1655 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (2 ≤ count1655 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (3 ≤ count1655 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (4 ≤ count1655 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (5 ≤ count1655 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (6 ≤ count1655 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (1 ≤ count1663 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (2 ≤ count1663 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (1 ≤ count1665 (baseVal q)) := rfl
theorem value1666 (q : Snake 81) : valuation q 1666 = decide (2 ≤ count1665 (baseVal q)) := rfl
theorem value1667 (q : Snake 81) : valuation q 1667 = decide (1 ≤ count1667 (baseVal q)) := rfl
theorem value1668 (q : Snake 81) : valuation q 1668 = decide (2 ≤ count1667 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (3 ≤ count1667 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (4 ≤ count1667 (baseVal q)) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (1 ≤ count1671 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (2 ≤ count1671 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (1 ≤ count1673 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (1 ≤ count1675 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (2 ≤ count1675 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (3 ≤ count1675 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (1 ≤ count1679 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (2 ≤ count1679 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (3 ≤ count1679 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (4 ≤ count1679 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (5 ≤ count1679 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (6 ≤ count1679 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (1 ≤ count1687 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (2 ≤ count1687 (baseVal q)) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (3 ≤ count1687 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (4 ≤ count1687 (baseVal q)) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (5 ≤ count1687 (baseVal q)) := rfl
theorem value1692 (q : Snake 81) : valuation q 1692 = decide (6 ≤ count1687 (baseVal q)) := rfl
theorem value1693 (q : Snake 81) : valuation q 1693 = decide (7 ≤ count1687 (baseVal q)) := rfl
theorem value1694 (q : Snake 81) : valuation q 1694 = decide (8 ≤ count1687 (baseVal q)) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (9 ≤ count1687 (baseVal q)) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (4 ≤ count1703 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (5 ≤ count1703 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (6 ≤ count1703 (baseVal q)) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (7 ≤ count1703 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (8 ≤ count1703 (baseVal q)) := rfl
theorem value1711 (q : Snake 81) : valuation q 1711 = decide (9 ≤ count1703 (baseVal q)) := rfl
theorem value1712 (q : Snake 81) : valuation q 1712 = decide (10 ≤ count1703 (baseVal q)) := rfl
theorem value1713 (q : Snake 81) : valuation q 1713 = decide (11 ≤ count1703 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (12 ≤ count1703 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (13 ≤ count1703 (baseVal q)) := rfl
theorem value1744 (q : Snake 81) : valuation q 1744 = decide (21 ≤ count1724 (baseVal q)) := rfl
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
theorem meaningNeg105 (b : Nat → Bool) : literal (valuationOf b) (-105) = decide (1 ≤ countLit b [-105]) := by
  change literal b (-105) = decide (1 ≤ countLit b [-105])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-105) <;> decide
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
theorem meaningNeg73 (b : Nat → Bool) : literal (valuationOf b) (-73) = decide (1 ≤ countLit b [-73]) := by
  change literal b (-73) = decide (1 ≤ countLit b [-73])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-73) <;> decide
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
theorem meaningNeg15 (b : Nat → Bool) : literal (valuationOf b) (-15) = decide (1 ≤ countLit b [-15]) := by
  change literal b (-15) = decide (1 ≤ countLit b [-15])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-15) <;> decide
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
theorem meaning122 (b : Nat → Bool) : literal (valuationOf b) (122) = decide (1 ≤ countLit b [122]) := by
  change literal b (122) = decide (1 ≤ countLit b [122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (122) <;> decide
theorem meaning125 (b : Nat → Bool) : literal (valuationOf b) (125) = decide (1 ≤ countLit b [125]) := by
  change literal b (125) = decide (1 ≤ countLit b [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (125) <;> decide
theorem meaning128 (b : Nat → Bool) : literal (valuationOf b) (128) = decide (1 ≤ countLit b [128]) := by
  change literal b (128) = decide (1 ≤ countLit b [128])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (128) <;> decide
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
theorem meaning137 (b : Nat → Bool) : literal (valuationOf b) (137) = decide (1 ≤ countLit b [137]) := by
  change literal b (137) = decide (1 ≤ countLit b [137])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (137) <;> decide
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
theorem meaning169 (b : Nat → Bool) : literal (valuationOf b) (169) = decide (1 ≤ countLit b [169]) := by
  change literal b (169) = decide (1 ≤ countLit b [169])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (169) <;> decide
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
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) (213) = decide (1 ≤ countLit b [213]) := by
  change literal b (213) = decide (1 ≤ countLit b [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (213) <;> decide
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
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) (223) = decide (1 ≤ countLit b [223]) := by
  change literal b (223) = decide (1 ≤ countLit b [223])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (223) <;> decide
theorem meaning224 (b : Nat → Bool) : literal (valuationOf b) (224) = decide (1 ≤ countLit b [224]) := by
  change literal b (224) = decide (1 ≤ countLit b [224])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (224) <;> decide
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) (227) = decide (1 ≤ countLit b [227]) := by
  change literal b (227) = decide (1 ≤ countLit b [227])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (227) <;> decide
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
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) (238) = decide (1 ≤ countLit b [238]) := by
  change literal b (238) = decide (1 ≤ countLit b [238])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (238) <;> decide
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
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
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning350 (b : Nat → Bool) : literal (valuationOf b) 350 = decide (2 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning352 (b : Nat → Bool) : literal (valuationOf b) 352 = decide (2 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning356 (b : Nat → Bool) : literal (valuationOf b) 356 = decide (2 ≤ count355 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning384 (b : Nat → Bool) : literal (valuationOf b) 384 = decide (2 ≤ count383 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning414 (b : Nat → Bool) : literal (valuationOf b) 414 = decide (2 ≤ count413 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning440 (b : Nat → Bool) : literal (valuationOf b) 440 = decide (2 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning442 (b : Nat → Bool) : literal (valuationOf b) 442 = decide (2 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning460 (b : Nat → Bool) : literal (valuationOf b) 460 = decide (2 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning468 (b : Nat → Bool) : literal (valuationOf b) 468 = decide (2 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning470 (b : Nat → Bool) : literal (valuationOf b) 470 = decide (2 ≤ count469 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning472 (b : Nat → Bool) : literal (valuationOf b) 472 = decide (2 ≤ count471 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning474 (b : Nat → Bool) : literal (valuationOf b) 474 = decide (2 ≤ count473 b) := rfl
theorem meaning476 (b : Nat → Bool) : literal (valuationOf b) 476 = decide (2 ≤ count475 b) := rfl
theorem meaning809 (b : Nat → Bool) : literal (valuationOf b) 809 = decide (1 ≤ count809 b) := rfl
theorem meaning811 (b : Nat → Bool) : literal (valuationOf b) 811 = decide (1 ≤ count811 b) := rfl
theorem meaning814 (b : Nat → Bool) : literal (valuationOf b) 814 = decide (1 ≤ count814 b) := rfl
theorem meaning817 (b : Nat → Bool) : literal (valuationOf b) 817 = decide (2 ≤ count816 b) := rfl
theorem meaning820 (b : Nat → Bool) : literal (valuationOf b) 820 = decide (3 ≤ count818 b) := rfl
theorem meaning825 (b : Nat → Bool) : literal (valuationOf b) 825 = decide (4 ≤ count822 b) := rfl
theorem meaning834 (b : Nat → Bool) : literal (valuationOf b) 834 = decide (1 ≤ count834 b) := rfl
theorem meaning836 (b : Nat → Bool) : literal (valuationOf b) 836 = decide (1 ≤ count836 b) := rfl
theorem meaning839 (b : Nat → Bool) : literal (valuationOf b) 839 = decide (2 ≤ count838 b) := rfl
theorem meaning843 (b : Nat → Bool) : literal (valuationOf b) 843 = decide (2 ≤ count842 b) := rfl
theorem meaning854 (b : Nat → Bool) : literal (valuationOf b) 854 = decide (6 ≤ count849 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (1 ≤ count863 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (1 ≤ count865 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (2 ≤ count868 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (1 ≤ count870 b) := rfl
theorem meaning874 (b : Nat → Bool) : literal (valuationOf b) 874 = decide (3 ≤ count872 b) := rfl
theorem meaning879 (b : Nat → Bool) : literal (valuationOf b) 879 = decide (4 ≤ count876 b) := rfl
theorem meaning891 (b : Nat → Bool) : literal (valuationOf b) 891 = decide (1 ≤ count891 b) := rfl
theorem meaning893 (b : Nat → Bool) : literal (valuationOf b) 893 = decide (1 ≤ count893 b) := rfl
theorem meaning894 (b : Nat → Bool) : literal (valuationOf b) 894 = decide (2 ≤ count893 b) := rfl
theorem meaning896 (b : Nat → Bool) : literal (valuationOf b) 896 = decide (2 ≤ count895 b) := rfl
theorem meaning900 (b : Nat → Bool) : literal (valuationOf b) 900 = decide (2 ≤ count899 b) := rfl
theorem meaning912 (b : Nat → Bool) : literal (valuationOf b) 912 = decide (6 ≤ count907 b) := rfl
theorem meaning933 (b : Nat → Bool) : literal (valuationOf b) 933 = decide (12 ≤ count922 b) := rfl
theorem meaning947 (b : Nat → Bool) : literal (valuationOf b) 947 = decide (2 ≤ count946 b) := rfl
theorem meaning951 (b : Nat → Bool) : literal (valuationOf b) 951 = decide (2 ≤ count950 b) := rfl
theorem meaning955 (b : Nat → Bool) : literal (valuationOf b) 955 = decide (2 ≤ count954 b) := rfl
theorem meaning963 (b : Nat → Bool) : literal (valuationOf b) 963 = decide (1 ≤ count963 b) := rfl
theorem meaning965 (b : Nat → Bool) : literal (valuationOf b) 965 = decide (1 ≤ count965 b) := rfl
theorem meaning977 (b : Nat → Bool) : literal (valuationOf b) 977 = decide (1 ≤ count977 b) := rfl
theorem meaning987 (b : Nat → Bool) : literal (valuationOf b) 987 = decide (3 ≤ count985 b) := rfl
theorem meaning1000 (b : Nat → Bool) : literal (valuationOf b) 1000 = decide (1 ≤ count1000 b) := rfl
theorem meaning1002 (b : Nat → Bool) : literal (valuationOf b) 1002 = decide (1 ≤ count1002 b) := rfl
theorem meaning1005 (b : Nat → Bool) : literal (valuationOf b) 1005 = decide (1 ≤ count1005 b) := rfl
theorem meaning1009 (b : Nat → Bool) : literal (valuationOf b) 1009 = decide (1 ≤ count1009 b) := rfl
theorem meaning1014 (b : Nat → Bool) : literal (valuationOf b) 1014 = decide (2 ≤ count1013 b) := rfl
theorem meaning1022 (b : Nat → Bool) : literal (valuationOf b) 1022 = decide (1 ≤ count1022 b) := rfl
theorem meaning1024 (b : Nat → Bool) : literal (valuationOf b) 1024 = decide (1 ≤ count1024 b) := rfl
theorem meaning1030 (b : Nat → Bool) : literal (valuationOf b) 1030 = decide (1 ≤ count1030 b) := rfl
theorem meaning1032 (b : Nat → Bool) : literal (valuationOf b) 1032 = decide (1 ≤ count1032 b) := rfl
theorem meaning1037 (b : Nat → Bool) : literal (valuationOf b) 1037 = decide (2 ≤ count1036 b) := rfl
theorem meaning1047 (b : Nat → Bool) : literal (valuationOf b) 1047 = decide (4 ≤ count1044 b) := rfl
theorem meaning1065 (b : Nat → Bool) : literal (valuationOf b) 1065 = decide (7 ≤ count1059 b) := rfl
theorem meaning1096 (b : Nat → Bool) : literal (valuationOf b) 1096 = decide (19 ≤ count1078 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (1 ≤ count1441 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (2 ≤ count1441 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (1 ≤ count1443 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (2 ≤ count1443 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (3 ≤ count1443 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (1 ≤ count1446 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (2 ≤ count1446 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (1 ≤ count1448 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (2 ≤ count1448 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (1 ≤ count1450 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (2 ≤ count1450 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (3 ≤ count1450 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (4 ≤ count1450 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (1 ≤ count1454 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (2 ≤ count1454 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (3 ≤ count1454 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (4 ≤ count1454 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (5 ≤ count1454 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (1 ≤ count1461 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (2 ≤ count1461 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (1 ≤ count1463 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (2 ≤ count1463 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (1 ≤ count1465 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (2 ≤ count1465 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (3 ≤ count1465 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (4 ≤ count1465 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (1 ≤ count1469 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (2 ≤ count1469 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (1 ≤ count1471 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (2 ≤ count1471 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (1 ≤ count1473 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (2 ≤ count1473 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (3 ≤ count1473 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (4 ≤ count1473 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (1 ≤ count1477 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (2 ≤ count1477 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (3 ≤ count1477 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (4 ≤ count1477 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (5 ≤ count1477 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (6 ≤ count1477 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (7 ≤ count1477 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (2 ≤ count1485 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (3 ≤ count1485 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (4 ≤ count1485 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (5 ≤ count1485 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (6 ≤ count1485 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (7 ≤ count1485 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (8 ≤ count1485 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (9 ≤ count1485 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (10 ≤ count1485 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (1 ≤ count1500 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (2 ≤ count1500 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (1 ≤ count1502 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (2 ≤ count1502 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (3 ≤ count1502 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (1 ≤ count1505 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (2 ≤ count1505 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (1 ≤ count1507 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (2 ≤ count1507 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (1 ≤ count1509 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (2 ≤ count1509 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (3 ≤ count1509 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (4 ≤ count1509 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (1 ≤ count1513 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (2 ≤ count1513 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (3 ≤ count1513 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (4 ≤ count1513 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (5 ≤ count1513 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (6 ≤ count1513 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (7 ≤ count1513 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (1 ≤ count1520 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (2 ≤ count1520 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (1 ≤ count1522 b) := rfl
theorem meaning1523 (b : Nat → Bool) : literal (valuationOf b) 1523 = decide (2 ≤ count1522 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (1 ≤ count1524 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (2 ≤ count1524 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (3 ≤ count1524 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (4 ≤ count1524 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (1 ≤ count1528 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (2 ≤ count1528 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (1 ≤ count1530 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (2 ≤ count1530 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (1 ≤ count1532 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (2 ≤ count1532 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (3 ≤ count1532 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (4 ≤ count1532 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (1 ≤ count1536 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (2 ≤ count1536 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (3 ≤ count1536 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (4 ≤ count1536 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (5 ≤ count1536 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (6 ≤ count1536 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (7 ≤ count1536 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (3 ≤ count1544 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (4 ≤ count1544 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (5 ≤ count1544 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (6 ≤ count1544 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (7 ≤ count1544 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (8 ≤ count1544 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (9 ≤ count1544 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (10 ≤ count1544 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (11 ≤ count1544 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (8 ≤ count1559 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (9 ≤ count1559 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (10 ≤ count1559 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (11 ≤ count1559 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (12 ≤ count1559 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (13 ≤ count1559 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (14 ≤ count1559 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (15 ≤ count1559 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (16 ≤ count1559 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (17 ≤ count1559 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (1 ≤ count1580 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (1 ≤ count1582 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (2 ≤ count1582 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (3 ≤ count1582 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (1 ≤ count1585 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (2 ≤ count1585 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (1 ≤ count1587 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (2 ≤ count1587 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (1 ≤ count1589 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (2 ≤ count1589 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (3 ≤ count1589 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (4 ≤ count1589 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (1 ≤ count1593 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (2 ≤ count1593 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (3 ≤ count1593 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (4 ≤ count1593 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (7 ≤ count1593 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (1 ≤ count1600 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (2 ≤ count1600 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (1 ≤ count1602 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (2 ≤ count1602 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (1 ≤ count1604 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (2 ≤ count1604 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (3 ≤ count1604 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (1 ≤ count1608 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (2 ≤ count1608 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (1 ≤ count1610 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (2 ≤ count1610 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (1 ≤ count1612 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (2 ≤ count1612 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (3 ≤ count1612 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (1 ≤ count1616 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (2 ≤ count1616 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (3 ≤ count1616 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (4 ≤ count1616 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (5 ≤ count1616 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (2 ≤ count1624 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (3 ≤ count1624 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (4 ≤ count1624 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (5 ≤ count1624 b) := rfl
theorem meaning1629 (b : Nat → Bool) : literal (valuationOf b) 1629 = decide (6 ≤ count1624 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (7 ≤ count1624 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (9 ≤ count1624 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (1 ≤ count1639 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (2 ≤ count1639 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (1 ≤ count1641 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (2 ≤ count1641 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (1 ≤ count1643 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (2 ≤ count1643 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (3 ≤ count1643 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (4 ≤ count1643 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (1 ≤ count1647 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (2 ≤ count1647 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (1 ≤ count1649 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (2 ≤ count1649 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (1 ≤ count1651 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (2 ≤ count1651 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (3 ≤ count1651 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (4 ≤ count1651 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (1 ≤ count1655 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (2 ≤ count1655 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (3 ≤ count1655 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (4 ≤ count1655 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (5 ≤ count1655 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (6 ≤ count1655 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (1 ≤ count1663 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (2 ≤ count1663 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (1 ≤ count1665 b) := rfl
theorem meaning1666 (b : Nat → Bool) : literal (valuationOf b) 1666 = decide (2 ≤ count1665 b) := rfl
theorem meaning1667 (b : Nat → Bool) : literal (valuationOf b) 1667 = decide (1 ≤ count1667 b) := rfl
theorem meaning1668 (b : Nat → Bool) : literal (valuationOf b) 1668 = decide (2 ≤ count1667 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (3 ≤ count1667 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (4 ≤ count1667 b) := rfl
theorem meaning1671 (b : Nat → Bool) : literal (valuationOf b) 1671 = decide (1 ≤ count1671 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (2 ≤ count1671 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (1 ≤ count1673 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (1 ≤ count1675 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (2 ≤ count1675 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (3 ≤ count1675 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (1 ≤ count1679 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (2 ≤ count1679 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (3 ≤ count1679 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (4 ≤ count1679 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (5 ≤ count1679 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (6 ≤ count1679 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (1 ≤ count1687 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (2 ≤ count1687 b) := rfl
theorem meaning1689 (b : Nat → Bool) : literal (valuationOf b) 1689 = decide (3 ≤ count1687 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (4 ≤ count1687 b) := rfl
theorem meaning1691 (b : Nat → Bool) : literal (valuationOf b) 1691 = decide (5 ≤ count1687 b) := rfl
theorem meaning1692 (b : Nat → Bool) : literal (valuationOf b) 1692 = decide (6 ≤ count1687 b) := rfl
theorem meaning1693 (b : Nat → Bool) : literal (valuationOf b) 1693 = decide (7 ≤ count1687 b) := rfl
theorem meaning1694 (b : Nat → Bool) : literal (valuationOf b) 1694 = decide (8 ≤ count1687 b) := rfl
theorem meaning1695 (b : Nat → Bool) : literal (valuationOf b) 1695 = decide (9 ≤ count1687 b) := rfl
theorem meaning1706 (b : Nat → Bool) : literal (valuationOf b) 1706 = decide (4 ≤ count1703 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (5 ≤ count1703 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (6 ≤ count1703 b) := rfl
theorem meaning1709 (b : Nat → Bool) : literal (valuationOf b) 1709 = decide (7 ≤ count1703 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (8 ≤ count1703 b) := rfl
theorem meaning1711 (b : Nat → Bool) : literal (valuationOf b) 1711 = decide (9 ≤ count1703 b) := rfl
theorem meaning1712 (b : Nat → Bool) : literal (valuationOf b) 1712 = decide (10 ≤ count1703 b) := rfl
theorem meaning1713 (b : Nat → Bool) : literal (valuationOf b) 1713 = decide (11 ≤ count1703 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (12 ≤ count1703 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (13 ≤ count1703 b) := rfl
theorem meaning1744 (b : Nat → Bool) : literal (valuationOf b) 1744 = decide (21 ≤ count1724 b) := rfl
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
end Snake9.Regrowth.E112040
