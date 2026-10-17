import E112121Data
namespace Snake9.Regrowth.E112121
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 126 then (if i < 63 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (6 : Vertex)) else decide (InPath q (17 : Vertex))) else (if i < 6 then decide (InPath q (18 : Vertex)) else decide (InPath q (19 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (22 : Vertex)) else decide (InPath q (32 : Vertex))) else (if i < 10 then decide (InPath q (33 : Vertex)) else decide (InPath q (34 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (36 : Vertex)) else decide (InPath q (37 : Vertex))) else (if i < 14 then decide (InPath q (38 : Vertex)) else decide (InPath q (39 : Vertex)))))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then decide (InPath q (40 : Vertex)) else decide (InPath q (41 : Vertex))) else (if i < 18 then decide (InPath q (42 : Vertex)) else decide (InPath q (44 : Vertex)))) else (if i < 21 then (if i < 20 then decide (InPath q (46 : Vertex)) else decide (InPath q (49 : Vertex))) else (if i < 22 then decide (InPath q (50 : Vertex)) else decide (InPath q (51 : Vertex))))) else (if i < 27 then (if i < 25 then (if i < 24 then decide (InPath q (52 : Vertex)) else decide (InPath q (53 : Vertex))) else (if i < 26 then decide (InPath q (54 : Vertex)) else decide (InPath q (55 : Vertex)))) else (if i < 29 then (if i < 28 then decide (InPath q (57 : Vertex)) else decide (InPath q (58 : Vertex))) else (if i < 30 then decide (InPath q (59 : Vertex)) else decide (InPath q (62 : Vertex))))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then decide (InPath q (63 : Vertex)) else decide (InPath q (66 : Vertex))) else (if i < 34 then decide (InPath q (70 : Vertex)) else decide (InPath q (78 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (102 : Vertex)) else decide (InPath q (105 : Vertex))) else (if i < 38 then decide (InPath q (109 : Vertex)) else decide (InPath q (111 : Vertex))))) else (if i < 43 then (if i < 41 then (if i < 40 then decide (InPath q (118 : Vertex)) else decide (InPath q (122 : Vertex))) else (if i < 42 then decide (InPath q (124 : Vertex)) else decide (InPath q (125 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (126 : Vertex)) else decide (InPath q (160 : Vertex))) else (if i < 46 then decide (InPath q (161 : Vertex)) else decide (InPath q (165 : Vertex)))))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then decide (InPath q (166 : Vertex)) else decide (InPath q (168 : Vertex))) else (if i < 50 then decide (InPath q (171 : Vertex)) else decide (InPath q (173 : Vertex)))) else (if i < 53 then (if i < 52 then decide (InPath q (175 : Vertex)) else decide (InPath q (176 : Vertex))) else (if i < 54 then decide (InPath q (177 : Vertex)) else decide (InPath q (178 : Vertex))))) else (if i < 59 then (if i < 57 then (if i < 56 then decide (InPath q (179 : Vertex)) else decide (InPath q (182 : Vertex))) else (if i < 58 then decide (InPath q (184 : Vertex)) else decide (InPath q (188 : Vertex)))) else (if i < 61 then (if i < 60 then decide (InPath q (189 : Vertex)) else decide (InPath q (190 : Vertex))) else (if i < 62 then decide (InPath q (191 : Vertex)) else decide (InPath q (233 : Vertex)))))))) else (if i < 94 then (if i < 78 then (if i < 70 then (if i < 66 then (if i < 64 then decide (InPath q (245 : Vertex)) else (if i < 65 then decide (InPath q (247 : Vertex)) else decide (InPath q (248 : Vertex)))) else (if i < 68 then (if i < 67 then decide (InPath q (249 : Vertex)) else decide (InPath q (251 : Vertex))) else (if i < 69 then decide (InPath q (255 : Vertex)) else decide (InPath q (288 : Vertex))))) else (if i < 74 then (if i < 72 then (if i < 71 then decide (InPath q (289 : Vertex)) else decide (InPath q (294 : Vertex))) else (if i < 73 then decide (InPath q (295 : Vertex)) else decide (InPath q (296 : Vertex)))) else (if i < 76 then (if i < 75 then decide (InPath q (297 : Vertex)) else decide (InPath q (299 : Vertex))) else (if i < 77 then decide (InPath q (301 : Vertex)) else decide (InPath q (303 : Vertex)))))) else (if i < 86 then (if i < 82 then (if i < 80 then (if i < 79 then decide (InPath q (305 : Vertex)) else decide (InPath q (306 : Vertex))) else (if i < 81 then decide (InPath q (307 : Vertex)) else decide (InPath q (308 : Vertex)))) else (if i < 84 then (if i < 83 then decide (InPath q (310 : Vertex)) else decide (InPath q (314 : Vertex))) else (if i < 85 then decide (InPath q (316 : Vertex)) else decide (InPath q (317 : Vertex))))) else (if i < 90 then (if i < 88 then (if i < 87 then decide (InPath q (318 : Vertex)) else decide (InPath q (416 : Vertex))) else (if i < 89 then decide (InPath q (417 : Vertex)) else decide (InPath q (418 : Vertex)))) else (if i < 92 then (if i < 91 then decide (InPath q (420 : Vertex)) else decide (InPath q (421 : Vertex))) else (if i < 93 then decide (InPath q (422 : Vertex)) else decide (InPath q (423 : Vertex))))))) else (if i < 110 then (if i < 102 then (if i < 98 then (if i < 96 then (if i < 95 then decide (InPath q (424 : Vertex)) else decide (InPath q (426 : Vertex))) else (if i < 97 then decide (InPath q (427 : Vertex)) else decide (InPath q (428 : Vertex)))) else (if i < 100 then (if i < 99 then decide (InPath q (430 : Vertex)) else decide (InPath q (431 : Vertex))) else (if i < 101 then decide (InPath q (433 : Vertex)) else decide (InPath q (435 : Vertex))))) else (if i < 106 then (if i < 104 then (if i < 103 then decide (InPath q (436 : Vertex)) else decide (InPath q (437 : Vertex))) else (if i < 105 then decide (InPath q (439 : Vertex)) else decide (InPath q (440 : Vertex)))) else (if i < 108 then (if i < 107 then decide (InPath q (441 : Vertex)) else decide (InPath q (442 : Vertex))) else (if i < 109 then decide (InPath q (443 : Vertex)) else decide (InPath q (447 : Vertex)))))) else (if i < 118 then (if i < 114 then (if i < 112 then (if i < 111 then decide (InPath q (480 : Vertex)) else decide (InPath q (481 : Vertex))) else (if i < 113 then decide (InPath q (486 : Vertex)) else decide (InPath q (487 : Vertex)))) else (if i < 116 then (if i < 115 then decide (InPath q (488 : Vertex)) else decide (InPath q (489 : Vertex))) else (if i < 117 then decide (InPath q (491 : Vertex)) else decide (InPath q (493 : Vertex))))) else (if i < 122 then (if i < 120 then (if i < 119 then decide (InPath q (495 : Vertex)) else decide (InPath q (497 : Vertex))) else (if i < 121 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex)))) else (if i < 124 then (if i < 123 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 125 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 189 then (if i < 157 then (if i < 141 then (if i < 133 then (if i < 129 then (if i < 127 then decide (InPath q (510 : Vertex)) else (if i < 128 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 131 then (if i < 130 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else decide (BallClauseLogic.Endpoint q (17 : Vertex))) else (if i < 132 then decide (BallClauseLogic.Endpoint q (18 : Vertex)) else decide (BallClauseLogic.Endpoint q (19 : Vertex))))) else (if i < 137 then (if i < 135 then (if i < 134 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (32 : Vertex))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (33 : Vertex)) else decide (BallClauseLogic.Endpoint q (34 : Vertex)))) else (if i < 139 then (if i < 138 then decide (BallClauseLogic.Endpoint q (36 : Vertex)) else decide (BallClauseLogic.Endpoint q (37 : Vertex))) else (if i < 140 then decide (BallClauseLogic.Endpoint q (38 : Vertex)) else decide (BallClauseLogic.Endpoint q (39 : Vertex)))))) else (if i < 149 then (if i < 145 then (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (40 : Vertex)) else decide (BallClauseLogic.Endpoint q (41 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (42 : Vertex)) else decide (BallClauseLogic.Endpoint q (44 : Vertex)))) else (if i < 147 then (if i < 146 then decide (BallClauseLogic.Endpoint q (46 : Vertex)) else decide (BallClauseLogic.Endpoint q (49 : Vertex))) else (if i < 148 then decide (BallClauseLogic.Endpoint q (50 : Vertex)) else decide (BallClauseLogic.Endpoint q (51 : Vertex))))) else (if i < 153 then (if i < 151 then (if i < 150 then decide (BallClauseLogic.Endpoint q (52 : Vertex)) else decide (BallClauseLogic.Endpoint q (53 : Vertex))) else (if i < 152 then decide (BallClauseLogic.Endpoint q (54 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex)))) else (if i < 155 then (if i < 154 then decide (BallClauseLogic.Endpoint q (57 : Vertex)) else decide (BallClauseLogic.Endpoint q (58 : Vertex))) else (if i < 156 then decide (BallClauseLogic.Endpoint q (59 : Vertex)) else decide (BallClauseLogic.Endpoint q (62 : Vertex))))))) else (if i < 173 then (if i < 165 then (if i < 161 then (if i < 159 then (if i < 158 then decide (BallClauseLogic.Endpoint q (63 : Vertex)) else decide (BallClauseLogic.Endpoint q (66 : Vertex))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (70 : Vertex)) else decide (BallClauseLogic.Endpoint q (78 : Vertex)))) else (if i < 163 then (if i < 162 then decide (BallClauseLogic.Endpoint q (102 : Vertex)) else decide (BallClauseLogic.Endpoint q (105 : Vertex))) else (if i < 164 then decide (BallClauseLogic.Endpoint q (109 : Vertex)) else decide (BallClauseLogic.Endpoint q (111 : Vertex))))) else (if i < 169 then (if i < 167 then (if i < 166 then decide (BallClauseLogic.Endpoint q (118 : Vertex)) else decide (BallClauseLogic.Endpoint q (122 : Vertex))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (124 : Vertex)) else decide (BallClauseLogic.Endpoint q (125 : Vertex)))) else (if i < 171 then (if i < 170 then decide (BallClauseLogic.Endpoint q (126 : Vertex)) else decide (BallClauseLogic.Endpoint q (160 : Vertex))) else (if i < 172 then decide (BallClauseLogic.Endpoint q (161 : Vertex)) else decide (BallClauseLogic.Endpoint q (165 : Vertex)))))) else (if i < 181 then (if i < 177 then (if i < 175 then (if i < 174 then decide (BallClauseLogic.Endpoint q (166 : Vertex)) else decide (BallClauseLogic.Endpoint q (168 : Vertex))) else (if i < 176 then decide (BallClauseLogic.Endpoint q (171 : Vertex)) else decide (BallClauseLogic.Endpoint q (173 : Vertex)))) else (if i < 179 then (if i < 178 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else decide (BallClauseLogic.Endpoint q (176 : Vertex))) else (if i < 180 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else decide (BallClauseLogic.Endpoint q (178 : Vertex))))) else (if i < 185 then (if i < 183 then (if i < 182 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex))) else (if i < 184 then decide (BallClauseLogic.Endpoint q (184 : Vertex)) else decide (BallClauseLogic.Endpoint q (188 : Vertex)))) else (if i < 187 then (if i < 186 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (190 : Vertex))) else (if i < 188 then decide (BallClauseLogic.Endpoint q (191 : Vertex)) else decide (BallClauseLogic.Endpoint q (233 : Vertex)))))))) else (if i < 221 then (if i < 205 then (if i < 197 then (if i < 193 then (if i < 191 then (if i < 190 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else decide (BallClauseLogic.Endpoint q (247 : Vertex))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (248 : Vertex)) else decide (BallClauseLogic.Endpoint q (249 : Vertex)))) else (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else decide (BallClauseLogic.Endpoint q (289 : Vertex))))) else (if i < 201 then (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (294 : Vertex)) else decide (BallClauseLogic.Endpoint q (295 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else decide (BallClauseLogic.Endpoint q (297 : Vertex)))) else (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (299 : Vertex)) else decide (BallClauseLogic.Endpoint q (301 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (303 : Vertex)) else decide (BallClauseLogic.Endpoint q (305 : Vertex)))))) else (if i < 213 then (if i < 209 then (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (306 : Vertex)) else decide (BallClauseLogic.Endpoint q (307 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (308 : Vertex)) else decide (BallClauseLogic.Endpoint q (310 : Vertex)))) else (if i < 211 then (if i < 210 then decide (BallClauseLogic.Endpoint q (314 : Vertex)) else decide (BallClauseLogic.Endpoint q (316 : Vertex))) else (if i < 212 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (318 : Vertex))))) else (if i < 217 then (if i < 215 then (if i < 214 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex))) else (if i < 216 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (420 : Vertex)))) else (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex))))))) else (if i < 237 then (if i < 229 then (if i < 225 then (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else decide (BallClauseLogic.Endpoint q (430 : Vertex)))) else (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (431 : Vertex)) else decide (BallClauseLogic.Endpoint q (433 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (435 : Vertex)) else decide (BallClauseLogic.Endpoint q (436 : Vertex))))) else (if i < 233 then (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (437 : Vertex)) else decide (BallClauseLogic.Endpoint q (439 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else decide (BallClauseLogic.Endpoint q (441 : Vertex)))) else (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (442 : Vertex)) else decide (BallClauseLogic.Endpoint q (443 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (447 : Vertex)) else decide (BallClauseLogic.Endpoint q (480 : Vertex)))))) else (if i < 245 then (if i < 241 then (if i < 239 then (if i < 238 then decide (BallClauseLogic.Endpoint q (481 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex))) else (if i < 240 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))) else (if i < 243 then (if i < 242 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else decide (BallClauseLogic.Endpoint q (491 : Vertex))) else (if i < 244 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else decide (BallClauseLogic.Endpoint q (495 : Vertex))))) else (if i < 249 then (if i < 247 then (if i < 246 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex))) else (if i < 248 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 251 then (if i < 250 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 252 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [127, 128, 129]
def count257 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133]
def count263 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132, 133]
def count265 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137, 138, 139, 140, 141]
def count279 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141]
def count281 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count283 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145]
def count287 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145, 146, 147, 148, 149]
def count295 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count299 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153]
def count301 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count305 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]
def count311 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]
def count313 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count315 (b : Nat → Bool) : Nat := countLit b [158, 159, 160]
def count317 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161, 162, 163, 164]
def count325 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168]
def count331 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count335 (b : Nat → Bool) : Nat := countLit b [169, 170, 171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171, 172]
def count339 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]
def count341 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count343 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count345 (b : Nat → Bool) : Nat := countLit b [173, 174, 175, 176]
def count347 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [177, 178, 179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [173, 174, 175, 176, 177, 178, 179, 180]
def count355 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count365 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184, 185, 186, 187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]
def count371 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]
def count373 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [190, 191, 192]
def count379 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count383 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196]
def count387 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200, 201, 202, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count403 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count405 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208]
def count409 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count411 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count413 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count419 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count421 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count425 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count427 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220]
def count429 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216, 217, 218, 219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]
def count433 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]
def count435 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count437 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224]
def count441 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count443 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224, 225, 226, 227, 228]
def count449 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count451 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count459 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232, 233, 234, 235, 236]
def count463 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]
def count465 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count467 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count469 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240]
def count471 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count473 (b : Nat → Bool) : Nat := countLit b [243, 244]
def count475 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244]
def count477 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240, 241, 242, 243, 244]
def count479 (b : Nat → Bool) : Nat := countLit b [245, 246]
def count481 (b : Nat → Bool) : Nat := countLit b [247, 248]
def count483 (b : Nat → Bool) : Nat := countLit b [245, 246, 247, 248]
def count485 (b : Nat → Bool) : Nat := countLit b [249, 250]
def count487 (b : Nat → Bool) : Nat := countLit b [251, 252]
def count489 (b : Nat → Bool) : Nat := countLit b [249, 250, 251, 252]
def count491 (b : Nat → Bool) : Nat := countLit b [245, 246, 247, 248, 249, 250, 251, 252]
def count493 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252]
def count495 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252]
def count497 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252]
def count499 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252]
def count501 (b : Nat → Bool) : Nat := countLit b [1, 3]
def count503 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count505 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5]
def count509 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count511 (b : Nat → Bool) : Nat := countLit b [11, 14]
def count513 (b : Nat → Bool) : Nat := countLit b [9, 10, 11, 14]
def count517 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 11, 14]
def count525 (b : Nat → Bool) : Nat := countLit b [15, 19]
def count527 (b : Nat → Bool) : Nat := countLit b [22, 24]
def count529 (b : Nat → Bool) : Nat := countLit b [15, 19, 22, 24]
def count533 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count535 (b : Nat → Bool) : Nat := countLit b [28, 31]
def count537 (b : Nat → Bool) : Nat := countLit b [25, 27, 28, 31]
def count541 (b : Nat → Bool) : Nat := countLit b [15, 19, 22, 24, 25, 27, 28, 31]
def count549 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 11, 14, 15, 19, 22, 24, 25, 27, 28, 31]
def count565 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count567 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count569 (b : Nat → Bool) : Nat := countLit b [32, 34, 35, 36]
def count573 (b : Nat → Bool) : Nat := countLit b [38, 42]
def count575 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count577 (b : Nat → Bool) : Nat := countLit b [38, 42, 43, 44]
def count581 (b : Nat → Bool) : Nat := countLit b [32, 34, 35, 36, 38, 42, 43, 44]
def count589 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count591 (b : Nat → Bool) : Nat := countLit b [51, 53]
def count593 (b : Nat → Bool) : Nat := countLit b [46, 47, 51, 53]
def count597 (b : Nat → Bool) : Nat := countLit b [54, 57]
def count599 (b : Nat → Bool) : Nat := countLit b [59, 60]
def count601 (b : Nat → Bool) : Nat := countLit b [54, 57, 59, 60]
def count605 (b : Nat → Bool) : Nat := countLit b [46, 47, 51, 53, 54, 57, 59, 60]
def count613 (b : Nat → Bool) : Nat := countLit b [32, 34, 35, 36, 38, 42, 43, 44, 46, 47, 51, 53, 54, 57, 59, 60]
def count629 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 11, 14, 15, 19, 22, 24, 25, 27, 28, 31, 32, 34, 35, 36, 38, 42, 43, 44, 46, 47, 51, 53, 54, 57, 59, 60]
def count661 (b : Nat → Bool) : Nat := countLit b [63, 66]
def count663 (b : Nat → Bool) : Nat := countLit b [68, 69]
def count665 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 69]
def count669 (b : Nat → Bool) : Nat := countLit b [71, 74]
def count671 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count673 (b : Nat → Bool) : Nat := countLit b [71, 74, 77, 78]
def count677 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 69, 71, 74, 77, 78]
def count685 (b : Nat → Bool) : Nat := countLit b [79, 81]
def count687 (b : Nat → Bool) : Nat := countLit b [85, 86]
def count689 (b : Nat → Bool) : Nat := countLit b [79, 81, 85, 86]
def count693 (b : Nat → Bool) : Nat := countLit b [88, 89]
def count695 (b : Nat → Bool) : Nat := countLit b [90, 93]
def count697 (b : Nat → Bool) : Nat := countLit b [88, 89, 90, 93]
def count701 (b : Nat → Bool) : Nat := countLit b [79, 81, 85, 86, 88, 89, 90, 93]
def count709 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 69, 71, 74, 77, 78, 79, 81, 85, 86, 88, 89, 90, 93]
def count725 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count727 (b : Nat → Bool) : Nat := countLit b [98, 101]
def count729 (b : Nat → Bool) : Nat := countLit b [94, 96, 98, 101]
def count733 (b : Nat → Bool) : Nat := countLit b [103, 106]
def count735 (b : Nat → Bool) : Nat := countLit b [107, 109]
def count737 (b : Nat → Bool) : Nat := countLit b [103, 106, 107, 109]
def count741 (b : Nat → Bool) : Nat := countLit b [94, 96, 98, 101, 103, 106, 107, 109]
def count749 (b : Nat → Bool) : Nat := countLit b [110, 112]
def count751 (b : Nat → Bool) : Nat := countLit b [115, 118]
def count753 (b : Nat → Bool) : Nat := countLit b [110, 112, 115, 118]
def count757 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count759 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count761 (b : Nat → Bool) : Nat := countLit b [119, 120, 125, 126]
def count765 (b : Nat → Bool) : Nat := countLit b [110, 112, 115, 118, 119, 120, 125, 126]
def count773 (b : Nat → Bool) : Nat := countLit b [94, 96, 98, 101, 103, 106, 107, 109, 110, 112, 115, 118, 119, 120, 125, 126]
def count789 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 69, 71, 74, 77, 78, 79, 81, 85, 86, 88, 89, 90, 93, 94, 96, 98, 101, 103, 106, 107, 109, 110, 112, 115, 118, 119, 120, 125, 126]
def count821 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 11, 14, 15, 19, 22, 24, 25, 27, 28, 31, 32, 34, 35, 36, 38, 42, 43, 44, 46, 47, 51, 53, 54, 57, 59, 60, 63, 66, 68, 69, 71, 74, 77, 78, 79, 81, 85, 86, 88, 89, 90, 93, 94, 96, 98, 101, 103, 106, 107, 109, 110, 112, 115, 118, 119, 120, 125, 126]
def count863 (b : Nat → Bool) : Nat := countLit b [-1, -3]
def count865 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count867 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5]
def count871 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count873 (b : Nat → Bool) : Nat := countLit b [-11, -14]
def count875 (b : Nat → Bool) : Nat := countLit b [-9, -10, -11, -14]
def count879 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -11, -14]
def count887 (b : Nat → Bool) : Nat := countLit b [-15, -19]
def count889 (b : Nat → Bool) : Nat := countLit b [-22, -24]
def count891 (b : Nat → Bool) : Nat := countLit b [-15, -19, -22, -24]
def count895 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count897 (b : Nat → Bool) : Nat := countLit b [-28, -31]
def count899 (b : Nat → Bool) : Nat := countLit b [-25, -27, -28, -31]
def count903 (b : Nat → Bool) : Nat := countLit b [-15, -19, -22, -24, -25, -27, -28, -31]
def count911 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]
def count927 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count929 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count931 (b : Nat → Bool) : Nat := countLit b [-32, -34, -35, -36]
def count935 (b : Nat → Bool) : Nat := countLit b [-38, -42]
def count937 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count939 (b : Nat → Bool) : Nat := countLit b [-38, -42, -43, -44]
def count943 (b : Nat → Bool) : Nat := countLit b [-32, -34, -35, -36, -38, -42, -43, -44]
def count951 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count953 (b : Nat → Bool) : Nat := countLit b [-51, -53]
def count955 (b : Nat → Bool) : Nat := countLit b [-46, -47, -51, -53]
def count959 (b : Nat → Bool) : Nat := countLit b [-54, -57]
def count961 (b : Nat → Bool) : Nat := countLit b [-59, -60]
def count963 (b : Nat → Bool) : Nat := countLit b [-54, -57, -59, -60]
def count967 (b : Nat → Bool) : Nat := countLit b [-46, -47, -51, -53, -54, -57, -59, -60]
def count975 (b : Nat → Bool) : Nat := countLit b [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]
def count991 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]
def count1015 (b : Nat → Bool) : Nat := countLit b [-63, -66]
def count1017 (b : Nat → Bool) : Nat := countLit b [-68, -69]
def count1019 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -69]
def count1023 (b : Nat → Bool) : Nat := countLit b [-71, -74]
def count1025 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count1027 (b : Nat → Bool) : Nat := countLit b [-71, -74, -77, -78]
def count1031 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -69, -71, -74, -77, -78]
def count1039 (b : Nat → Bool) : Nat := countLit b [-79, -81]
def count1041 (b : Nat → Bool) : Nat := countLit b [-85, -86]
def count1043 (b : Nat → Bool) : Nat := countLit b [-79, -81, -85, -86]
def count1047 (b : Nat → Bool) : Nat := countLit b [-88, -89]
def count1049 (b : Nat → Bool) : Nat := countLit b [-90, -93]
def count1051 (b : Nat → Bool) : Nat := countLit b [-88, -89, -90, -93]
def count1055 (b : Nat → Bool) : Nat := countLit b [-79, -81, -85, -86, -88, -89, -90, -93]
def count1063 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]
def count1079 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1081 (b : Nat → Bool) : Nat := countLit b [-98, -101]
def count1083 (b : Nat → Bool) : Nat := countLit b [-94, -96, -98, -101]
def count1087 (b : Nat → Bool) : Nat := countLit b [-103, -106]
def count1089 (b : Nat → Bool) : Nat := countLit b [-107, -109]
def count1091 (b : Nat → Bool) : Nat := countLit b [-103, -106, -107, -109]
def count1095 (b : Nat → Bool) : Nat := countLit b [-94, -96, -98, -101, -103, -106, -107, -109]
def count1103 (b : Nat → Bool) : Nat := countLit b [-110, -112]
def count1105 (b : Nat → Bool) : Nat := countLit b [-115, -118]
def count1107 (b : Nat → Bool) : Nat := countLit b [-110, -112, -115, -118]
def count1111 (b : Nat → Bool) : Nat := countLit b [-119, -120]
def count1113 (b : Nat → Bool) : Nat := countLit b [-125, -126]
def count1115 (b : Nat → Bool) : Nat := countLit b [-119, -120, -125, -126]
def count1119 (b : Nat → Bool) : Nat := countLit b [-110, -112, -115, -118, -119, -120, -125, -126]
def count1127 (b : Nat → Bool) : Nat := countLit b [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]
def count1143 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]
def count1167 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31, -32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60, -63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93, -94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]
def count1191 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count1193 (b : Nat → Bool) : Nat := countLit b [2, 6, 7]
def count1196 (b : Nat → Bool) : Nat := countLit b [8, 12]
def count1198 (b : Nat → Bool) : Nat := countLit b [13, 16]
def count1200 (b : Nat → Bool) : Nat := countLit b [8, 12, 13, 16]
def count1204 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 12, 13, 16]
def count1211 (b : Nat → Bool) : Nat := countLit b [17, 18]
def count1213 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count1215 (b : Nat → Bool) : Nat := countLit b [17, 18, 20, 21]
def count1219 (b : Nat → Bool) : Nat := countLit b [23, 26]
def count1221 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count1223 (b : Nat → Bool) : Nat := countLit b [23, 26, 29, 30]
def count1227 (b : Nat → Bool) : Nat := countLit b [17, 18, 20, 21, 23, 26, 29, 30]
def count1235 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 12, 13, 16, 17, 18, 20, 21, 23, 26, 29, 30]
def count1250 (b : Nat → Bool) : Nat := countLit b [33, 37]
def count1252 (b : Nat → Bool) : Nat := countLit b [39, 40]
def count1254 (b : Nat → Bool) : Nat := countLit b [33, 37, 39, 40]
def count1258 (b : Nat → Bool) : Nat := countLit b [41, 45]
def count1260 (b : Nat → Bool) : Nat := countLit b [48, 49]
def count1262 (b : Nat → Bool) : Nat := countLit b [41, 45, 48, 49]
def count1266 (b : Nat → Bool) : Nat := countLit b [33, 37, 39, 40, 41, 45, 48, 49]
def count1274 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count1276 (b : Nat → Bool) : Nat := countLit b [55, 56]
def count1278 (b : Nat → Bool) : Nat := countLit b [50, 52, 55, 56]
def count1282 (b : Nat → Bool) : Nat := countLit b [58, 61]
def count1284 (b : Nat → Bool) : Nat := countLit b [62, 64]
def count1286 (b : Nat → Bool) : Nat := countLit b [58, 61, 62, 64]
def count1290 (b : Nat → Bool) : Nat := countLit b [50, 52, 55, 56, 58, 61, 62, 64]
def count1298 (b : Nat → Bool) : Nat := countLit b [33, 37, 39, 40, 41, 45, 48, 49, 50, 52, 55, 56, 58, 61, 62, 64]
def count1314 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 12, 13, 16, 17, 18, 20, 21, 23, 26, 29, 30, 33, 37, 39, 40, 41, 45, 48, 49, 50, 52, 55, 56, 58, 61, 62, 64]
def count1345 (b : Nat → Bool) : Nat := countLit b [67, 70]
def count1347 (b : Nat → Bool) : Nat := countLit b [65, 67, 70]
def count1350 (b : Nat → Bool) : Nat := countLit b [72, 73]
def count1352 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count1354 (b : Nat → Bool) : Nat := countLit b [72, 73, 75, 76]
def count1358 (b : Nat → Bool) : Nat := countLit b [65, 67, 70, 72, 73, 75, 76]
def count1365 (b : Nat → Bool) : Nat := countLit b [80, 82]
def count1367 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count1369 (b : Nat → Bool) : Nat := countLit b [80, 82, 83, 84]
def count1373 (b : Nat → Bool) : Nat := countLit b [87, 91]
def count1375 (b : Nat → Bool) : Nat := countLit b [92, 95]
def count1377 (b : Nat → Bool) : Nat := countLit b [87, 91, 92, 95]
def count1381 (b : Nat → Bool) : Nat := countLit b [80, 82, 83, 84, 87, 91, 92, 95]
def count1389 (b : Nat → Bool) : Nat := countLit b [65, 67, 70, 72, 73, 75, 76, 80, 82, 83, 84, 87, 91, 92, 95]
def count1404 (b : Nat → Bool) : Nat := countLit b [97, 99]
def count1406 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count1408 (b : Nat → Bool) : Nat := countLit b [97, 99, 100, 102]
def count1412 (b : Nat → Bool) : Nat := countLit b [104, 105]
def count1414 (b : Nat → Bool) : Nat := countLit b [108, 111]
def count1416 (b : Nat → Bool) : Nat := countLit b [104, 105, 108, 111]
def count1420 (b : Nat → Bool) : Nat := countLit b [97, 99, 100, 102, 104, 105, 108, 111]
def count1428 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count1430 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count1432 (b : Nat → Bool) : Nat := countLit b [113, 114, 116, 117]
def count1436 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count1438 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count1440 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124]
def count1444 (b : Nat → Bool) : Nat := countLit b [113, 114, 116, 117, 121, 122, 123, 124]
def count1452 (b : Nat → Bool) : Nat := countLit b [97, 99, 100, 102, 104, 105, 108, 111, 113, 114, 116, 117, 121, 122, 123, 124]
def count1468 (b : Nat → Bool) : Nat := countLit b [65, 67, 70, 72, 73, 75, 76, 80, 82, 83, 84, 87, 91, 92, 95, 97, 99, 100, 102, 104, 105, 108, 111, 113, 114, 116, 117, 121, 122, 123, 124]
def count1499 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 12, 13, 16, 17, 18, 20, 21, 23, 26, 29, 30, 33, 37, 39, 40, 41, 45, 48, 49, 50, 52, 55, 56, 58, 61, 62, 64, 65, 67, 70, 72, 73, 75, 76, 80, 82, 83, 84, 87, 91, 92, 95, 97, 99, 100, 102, 104, 105, 108, 111, 113, 114, 116, 117, 121, 122, 123, 124]
def count1541 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count1543 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7]
def count1546 (b : Nat → Bool) : Nat := countLit b [-8, -12]
def count1548 (b : Nat → Bool) : Nat := countLit b [-13, -16]
def count1550 (b : Nat → Bool) : Nat := countLit b [-8, -12, -13, -16]
def count1554 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -12, -13, -16]
def count1561 (b : Nat → Bool) : Nat := countLit b [-17, -18]
def count1563 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count1565 (b : Nat → Bool) : Nat := countLit b [-17, -18, -20, -21]
def count1569 (b : Nat → Bool) : Nat := countLit b [-23, -26]
def count1571 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count1573 (b : Nat → Bool) : Nat := countLit b [-23, -26, -29, -30]
def count1577 (b : Nat → Bool) : Nat := countLit b [-17, -18, -20, -21, -23, -26, -29, -30]
def count1585 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -12, -13, -16, -17, -18, -20, -21, -23, -26, -29, -30]
def count1600 (b : Nat → Bool) : Nat := countLit b [-33, -37]
def count1602 (b : Nat → Bool) : Nat := countLit b [-39, -40]
def count1604 (b : Nat → Bool) : Nat := countLit b [-33, -37, -39, -40]
def count1608 (b : Nat → Bool) : Nat := countLit b [-41, -45]
def count1610 (b : Nat → Bool) : Nat := countLit b [-48, -49]
def count1612 (b : Nat → Bool) : Nat := countLit b [-41, -45, -48, -49]
def count1616 (b : Nat → Bool) : Nat := countLit b [-33, -37, -39, -40, -41, -45, -48, -49]
def count1624 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count1626 (b : Nat → Bool) : Nat := countLit b [-55, -56]
def count1628 (b : Nat → Bool) : Nat := countLit b [-50, -52, -55, -56]
def count1632 (b : Nat → Bool) : Nat := countLit b [-58, -61]
def count1634 (b : Nat → Bool) : Nat := countLit b [-62, -64]
def count1636 (b : Nat → Bool) : Nat := countLit b [-58, -61, -62, -64]
def count1640 (b : Nat → Bool) : Nat := countLit b [-50, -52, -55, -56, -58, -61, -62, -64]
def count1648 (b : Nat → Bool) : Nat := countLit b [-33, -37, -39, -40, -41, -45, -48, -49, -50, -52, -55, -56, -58, -61, -62, -64]
def count1664 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -12, -13, -16, -17, -18, -20, -21, -23, -26, -29, -30, -33, -37, -39, -40, -41, -45, -48, -49, -50, -52, -55, -56, -58, -61, -62, -64]
def count1686 (b : Nat → Bool) : Nat := countLit b [-67, -70]
def count1688 (b : Nat → Bool) : Nat := countLit b [-65, -67, -70]
def count1691 (b : Nat → Bool) : Nat := countLit b [-72, -73]
def count1693 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count1695 (b : Nat → Bool) : Nat := countLit b [-72, -73, -75, -76]
def count1699 (b : Nat → Bool) : Nat := countLit b [-65, -67, -70, -72, -73, -75, -76]
def count1706 (b : Nat → Bool) : Nat := countLit b [-80, -82]
def count1708 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count1710 (b : Nat → Bool) : Nat := countLit b [-80, -82, -83, -84]
def count1714 (b : Nat → Bool) : Nat := countLit b [-87, -91]
def count1716 (b : Nat → Bool) : Nat := countLit b [-92, -95]
def count1718 (b : Nat → Bool) : Nat := countLit b [-87, -91, -92, -95]
def count1722 (b : Nat → Bool) : Nat := countLit b [-80, -82, -83, -84, -87, -91, -92, -95]
def count1730 (b : Nat → Bool) : Nat := countLit b [-65, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -91, -92, -95]
def count1745 (b : Nat → Bool) : Nat := countLit b [-97, -99]
def count1747 (b : Nat → Bool) : Nat := countLit b [-100, -102]
def count1749 (b : Nat → Bool) : Nat := countLit b [-97, -99, -100, -102]
def count1753 (b : Nat → Bool) : Nat := countLit b [-104, -105]
def count1755 (b : Nat → Bool) : Nat := countLit b [-108, -111]
def count1757 (b : Nat → Bool) : Nat := countLit b [-104, -105, -108, -111]
def count1761 (b : Nat → Bool) : Nat := countLit b [-97, -99, -100, -102, -104, -105, -108, -111]
def count1769 (b : Nat → Bool) : Nat := countLit b [-113, -114]
def count1771 (b : Nat → Bool) : Nat := countLit b [-116, -117]
def count1773 (b : Nat → Bool) : Nat := countLit b [-113, -114, -116, -117]
def count1777 (b : Nat → Bool) : Nat := countLit b [-121, -122]
def count1779 (b : Nat → Bool) : Nat := countLit b [-123, -124]
def count1781 (b : Nat → Bool) : Nat := countLit b [-121, -122, -123, -124]
def count1785 (b : Nat → Bool) : Nat := countLit b [-113, -114, -116, -117, -121, -122, -123, -124]
def count1793 (b : Nat → Bool) : Nat := countLit b [-97, -99, -100, -102, -104, -105, -108, -111, -113, -114, -116, -117, -121, -122, -123, -124]
def count1809 (b : Nat → Bool) : Nat := countLit b [-65, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -91, -92, -95, -97, -99, -100, -102, -104, -105, -108, -111, -113, -114, -116, -117, -121, -122, -123, -124]
def count1831 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -12, -13, -16, -17, -18, -20, -21, -23, -26, -29, -30, -33, -37, -39, -40, -41, -45, -48, -49, -50, -52, -55, -56, -58, -61, -62, -64, -65, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -91, -92, -95, -97, -99, -100, -102, -104, -105, -108, -111, -113, -114, -116, -117, -121, -122, -123, -124]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 926 then (if i < 463 then (if i < 231 then (if i < 115 then (if i < 57 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 24 then (if i < 22 then b 21 else (if i < 23 then b 22 else b 23)) else (if i < 26 then (if i < 25 then b 24 else b 25) else (if i < 27 then b 26 else b 27))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)) else (if i < 33 then (if i < 32 then b 31 else b 32) else (if i < 34 then b 33 else b 34))) else (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 40 then (if i < 39 then b 38 else b 39) else (if i < 41 then b 40 else b 41)))) else (if i < 49 then (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else b 48))) else (if i < 53 then (if i < 51 then (if i < 50 then b 49 else b 50) else (if i < 52 then b 51 else b 52)) else (if i < 55 then (if i < 54 then b 53 else b 54) else (if i < 56 then b 55 else b 56)))))) else (if i < 86 then (if i < 71 then (if i < 64 then (if i < 60 then (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)) else (if i < 62 then (if i < 61 then b 60 else b 61) else (if i < 63 then b 62 else b 63))) else (if i < 67 then (if i < 65 then b 64 else (if i < 66 then b 65 else b 66)) else (if i < 69 then (if i < 68 then b 67 else b 68) else (if i < 70 then b 69 else b 70)))) else (if i < 78 then (if i < 74 then (if i < 72 then b 71 else (if i < 73 then b 72 else b 73)) else (if i < 76 then (if i < 75 then b 74 else b 75) else (if i < 77 then b 76 else b 77))) else (if i < 82 then (if i < 80 then (if i < 79 then b 78 else b 79) else (if i < 81 then b 80 else b 81)) else (if i < 84 then (if i < 83 then b 82 else b 83) else (if i < 85 then b 84 else b 85))))) else (if i < 100 then (if i < 93 then (if i < 89 then (if i < 87 then b 86 else (if i < 88 then b 87 else b 88)) else (if i < 91 then (if i < 90 then b 89 else b 90) else (if i < 92 then b 91 else b 92))) else (if i < 96 then (if i < 94 then b 93 else (if i < 95 then b 94 else b 95)) else (if i < 98 then (if i < 97 then b 96 else b 97) else (if i < 99 then b 98 else b 99)))) else (if i < 107 then (if i < 103 then (if i < 101 then b 100 else (if i < 102 then b 101 else b 102)) else (if i < 105 then (if i < 104 then b 103 else b 104) else (if i < 106 then b 105 else b 106))) else (if i < 111 then (if i < 109 then (if i < 108 then b 107 else b 108) else (if i < 110 then b 109 else b 110)) else (if i < 113 then (if i < 112 then b 111 else b 112) else (if i < 114 then b 113 else b 114))))))) else (if i < 173 then (if i < 144 then (if i < 129 then (if i < 122 then (if i < 118 then (if i < 116 then b 115 else (if i < 117 then b 116 else b 117)) else (if i < 120 then (if i < 119 then b 118 else b 119) else (if i < 121 then b 120 else b 121))) else (if i < 125 then (if i < 123 then b 122 else (if i < 124 then b 123 else b 124)) else (if i < 127 then (if i < 126 then b 125 else b 126) else (if i < 128 then b 127 else b 128)))) else (if i < 136 then (if i < 132 then (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)) else (if i < 134 then (if i < 133 then b 132 else b 133) else (if i < 135 then b 134 else b 135))) else (if i < 140 then (if i < 138 then (if i < 137 then b 136 else b 137) else (if i < 139 then b 138 else b 139)) else (if i < 142 then (if i < 141 then b 140 else b 141) else (if i < 143 then b 142 else b 143))))) else (if i < 158 then (if i < 151 then (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 149 then (if i < 148 then b 147 else b 148) else (if i < 150 then b 149 else b 150))) else (if i < 154 then (if i < 152 then b 151 else (if i < 153 then b 152 else b 153)) else (if i < 156 then (if i < 155 then b 154 else b 155) else (if i < 157 then b 156 else b 157)))) else (if i < 165 then (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 163 then (if i < 162 then b 161 else b 162) else (if i < 164 then b 163 else b 164))) else (if i < 169 then (if i < 167 then (if i < 166 then b 165 else b 166) else (if i < 168 then b 167 else b 168)) else (if i < 171 then (if i < 170 then b 169 else b 170) else (if i < 172 then b 171 else b 172)))))) else (if i < 202 then (if i < 187 then (if i < 180 then (if i < 176 then (if i < 174 then b 173 else (if i < 175 then b 174 else b 175)) else (if i < 178 then (if i < 177 then b 176 else b 177) else (if i < 179 then b 178 else b 179))) else (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 185 then (if i < 184 then b 183 else b 184) else (if i < 186 then b 185 else b 186)))) else (if i < 194 then (if i < 190 then (if i < 188 then b 187 else (if i < 189 then b 188 else b 189)) else (if i < 192 then (if i < 191 then b 190 else b 191) else (if i < 193 then b 192 else b 193))) else (if i < 198 then (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else b 197)) else (if i < 200 then (if i < 199 then b 198 else b 199) else (if i < 201 then b 200 else b 201))))) else (if i < 216 then (if i < 209 then (if i < 205 then (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)) else (if i < 207 then (if i < 206 then b 205 else b 206) else (if i < 208 then b 207 else b 208))) else (if i < 212 then (if i < 210 then b 209 else (if i < 211 then b 210 else b 211)) else (if i < 214 then (if i < 213 then b 212 else b 213) else (if i < 215 then b 214 else b 215)))) else (if i < 223 then (if i < 219 then (if i < 217 then b 216 else (if i < 218 then b 217 else b 218)) else (if i < 221 then (if i < 220 then b 219 else b 220) else (if i < 222 then b 221 else b 222))) else (if i < 227 then (if i < 225 then (if i < 224 then b 223 else b 224) else (if i < 226 then b 225 else b 226)) else (if i < 229 then (if i < 228 then b 227 else b 228) else (if i < 230 then b 229 else b 230)))))))) else (if i < 347 then (if i < 289 then (if i < 260 then (if i < 245 then (if i < 238 then (if i < 234 then (if i < 232 then b 231 else (if i < 233 then b 232 else b 233)) else (if i < 236 then (if i < 235 then b 234 else b 235) else (if i < 237 then b 236 else b 237))) else (if i < 241 then (if i < 239 then b 238 else (if i < 240 then b 239 else b 240)) else (if i < 243 then (if i < 242 then b 241 else b 242) else (if i < 244 then b 243 else b 244)))) else (if i < 252 then (if i < 248 then (if i < 246 then b 245 else (if i < 247 then b 246 else b 247)) else (if i < 250 then (if i < 249 then b 248 else b 249) else (if i < 251 then b 250 else b 251))) else (if i < 256 then (if i < 254 then (if i < 253 then b 252 else decide (1 ≤ count253 b)) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b))) else (if i < 258 then (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b)) else (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b)))))) else (if i < 274 then (if i < 267 then (if i < 263 then (if i < 261 then decide (2 ≤ count259 b) else (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b))) else (if i < 265 then (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)))) else (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 272 then (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))))) else (if i < 281 then (if i < 277 then (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))) else (if i < 279 then (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)) else (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)))) else (if i < 285 then (if i < 283 then (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))) else (if i < 287 then (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b))))))) else (if i < 318 then (if i < 303 then (if i < 296 then (if i < 292 then (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b))) else (if i < 294 then (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b)) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)))) else (if i < 299 then (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b))) else (if i < 301 then (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b)) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b))))) else (if i < 310 then (if i < 306 then (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b))) else (if i < 308 then (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b)) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)))) else (if i < 314 then (if i < 312 then (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b))) else (if i < 316 then (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)))))) else (if i < 332 then (if i < 325 then (if i < 321 then (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))) else (if i < 323 then (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b)))) else (if i < 328 then (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b))) else (if i < 330 then (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))))) else (if i < 339 then (if i < 335 then (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 337 then (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)))) else (if i < 343 then (if i < 341 then (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)))))))) else (if i < 405 then (if i < 376 then (if i < 361 then (if i < 354 then (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))) else (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 359 then (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b))))) else (if i < 368 then (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 366 then (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)))) else (if i < 372 then (if i < 370 then (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b)) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b))) else (if i < 374 then (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)))))) else (if i < 390 then (if i < 383 then (if i < 379 then (if i < 377 then decide (2 ≤ count375 b) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b))) else (if i < 381 then (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b)) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))) else (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 388 then (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b))))) else (if i < 397 then (if i < 393 then (if i < 391 then decide (2 ≤ count389 b) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))) else (if i < 395 then (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)))) else (if i < 401 then (if i < 399 then (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b)) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 403 then (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b)) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b))))))) else (if i < 434 then (if i < 419 then (if i < 412 then (if i < 408 then (if i < 406 then decide (1 ≤ count405 b) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b))) else (if i < 410 then (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b)))) else (if i < 415 then (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))) else (if i < 417 then (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b)) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b))))) else (if i < 426 then (if i < 422 then (if i < 420 then decide (1 ≤ count419 b) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))) else (if i < 424 then (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b)) else (if i < 425 then decide (2 ≤ count423 b) else decide (1 ≤ count425 b)))) else (if i < 430 then (if i < 428 then (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b)) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b))) else (if i < 432 then (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b)))))) else (if i < 448 then (if i < 441 then (if i < 437 then (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b))) else (if i < 439 then (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b)) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b)))) else (if i < 444 then (if i < 442 then decide (1 ≤ count441 b) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b))) else (if i < 446 then (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)) else (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b))))) else (if i < 455 then (if i < 451 then (if i < 449 then decide (2 ≤ count447 b) else (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b))) else (if i < 453 then (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b)) else (if i < 454 then decide (1 ≤ count453 b) else decide (2 ≤ count453 b)))) else (if i < 459 then (if i < 457 then (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b)) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b))) else (if i < 461 then (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b)))))))))) else (if i < 694 then (if i < 578 then (if i < 520 then (if i < 491 then (if i < 477 then (if i < 470 then (if i < 466 then (if i < 464 then decide (1 ≤ count463 b) else (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b))) else (if i < 468 then (if i < 467 then decide (2 ≤ count465 b) else decide (1 ≤ count467 b)) else (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b)))) else (if i < 473 then (if i < 471 then decide (2 ≤ count469 b) else (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b))) else (if i < 475 then (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)) else (if i < 476 then decide (1 ≤ count475 b) else decide (2 ≤ count475 b))))) else (if i < 484 then (if i < 480 then (if i < 478 then decide (1 ≤ count477 b) else (if i < 479 then decide (2 ≤ count477 b) else decide (1 ≤ count479 b))) else (if i < 482 then (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b)) else (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b)))) else (if i < 487 then (if i < 485 then decide (2 ≤ count483 b) else (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b))) else (if i < 489 then (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b)) else (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b)))))) else (if i < 505 then (if i < 498 then (if i < 494 then (if i < 492 then decide (1 ≤ count491 b) else (if i < 493 then decide (2 ≤ count491 b) else decide (1 ≤ count493 b))) else (if i < 496 then (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b)) else (if i < 497 then decide (2 ≤ count495 b) else decide (1 ≤ count497 b)))) else (if i < 501 then (if i < 499 then decide (2 ≤ count497 b) else (if i < 500 then decide (1 ≤ count499 b) else decide (2 ≤ count499 b))) else (if i < 503 then (if i < 502 then decide (1 ≤ count501 b) else decide (2 ≤ count501 b)) else (if i < 504 then decide (1 ≤ count503 b) else decide (2 ≤ count503 b))))) else (if i < 512 then (if i < 508 then (if i < 506 then decide (1 ≤ count505 b) else (if i < 507 then decide (2 ≤ count505 b) else decide (3 ≤ count505 b))) else (if i < 510 then (if i < 509 then decide (4 ≤ count505 b) else decide (1 ≤ count509 b)) else (if i < 511 then decide (2 ≤ count509 b) else decide (1 ≤ count511 b)))) else (if i < 516 then (if i < 514 then (if i < 513 then decide (2 ≤ count511 b) else decide (1 ≤ count513 b)) else (if i < 515 then decide (2 ≤ count513 b) else decide (3 ≤ count513 b))) else (if i < 518 then (if i < 517 then decide (4 ≤ count513 b) else decide (1 ≤ count517 b)) else (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b))))))) else (if i < 549 then (if i < 534 then (if i < 527 then (if i < 523 then (if i < 521 then decide (4 ≤ count517 b) else (if i < 522 then decide (5 ≤ count517 b) else decide (6 ≤ count517 b))) else (if i < 525 then (if i < 524 then decide (7 ≤ count517 b) else decide (8 ≤ count517 b)) else (if i < 526 then decide (1 ≤ count525 b) else decide (2 ≤ count525 b)))) else (if i < 530 then (if i < 528 then decide (1 ≤ count527 b) else (if i < 529 then decide (2 ≤ count527 b) else decide (1 ≤ count529 b))) else (if i < 532 then (if i < 531 then decide (2 ≤ count529 b) else decide (3 ≤ count529 b)) else (if i < 533 then decide (4 ≤ count529 b) else decide (1 ≤ count533 b))))) else (if i < 541 then (if i < 537 then (if i < 535 then decide (2 ≤ count533 b) else (if i < 536 then decide (1 ≤ count535 b) else decide (2 ≤ count535 b))) else (if i < 539 then (if i < 538 then decide (1 ≤ count537 b) else decide (2 ≤ count537 b)) else (if i < 540 then decide (3 ≤ count537 b) else decide (4 ≤ count537 b)))) else (if i < 545 then (if i < 543 then (if i < 542 then decide (1 ≤ count541 b) else decide (2 ≤ count541 b)) else (if i < 544 then decide (3 ≤ count541 b) else decide (4 ≤ count541 b))) else (if i < 547 then (if i < 546 then decide (5 ≤ count541 b) else decide (6 ≤ count541 b)) else (if i < 548 then decide (7 ≤ count541 b) else decide (8 ≤ count541 b)))))) else (if i < 563 then (if i < 556 then (if i < 552 then (if i < 550 then decide (1 ≤ count549 b) else (if i < 551 then decide (2 ≤ count549 b) else decide (3 ≤ count549 b))) else (if i < 554 then (if i < 553 then decide (4 ≤ count549 b) else decide (5 ≤ count549 b)) else (if i < 555 then decide (6 ≤ count549 b) else decide (7 ≤ count549 b)))) else (if i < 559 then (if i < 557 then decide (8 ≤ count549 b) else (if i < 558 then decide (9 ≤ count549 b) else decide (10 ≤ count549 b))) else (if i < 561 then (if i < 560 then decide (11 ≤ count549 b) else decide (12 ≤ count549 b)) else (if i < 562 then decide (13 ≤ count549 b) else decide (14 ≤ count549 b))))) else (if i < 570 then (if i < 566 then (if i < 564 then decide (15 ≤ count549 b) else (if i < 565 then decide (16 ≤ count549 b) else decide (1 ≤ count565 b))) else (if i < 568 then (if i < 567 then decide (2 ≤ count565 b) else decide (1 ≤ count567 b)) else (if i < 569 then decide (2 ≤ count567 b) else decide (1 ≤ count569 b)))) else (if i < 574 then (if i < 572 then (if i < 571 then decide (2 ≤ count569 b) else decide (3 ≤ count569 b)) else (if i < 573 then decide (4 ≤ count569 b) else decide (1 ≤ count573 b))) else (if i < 576 then (if i < 575 then decide (2 ≤ count573 b) else decide (1 ≤ count575 b)) else (if i < 577 then decide (2 ≤ count575 b) else decide (1 ≤ count577 b)))))))) else (if i < 636 then (if i < 607 then (if i < 592 then (if i < 585 then (if i < 581 then (if i < 579 then decide (2 ≤ count577 b) else (if i < 580 then decide (3 ≤ count577 b) else decide (4 ≤ count577 b))) else (if i < 583 then (if i < 582 then decide (1 ≤ count581 b) else decide (2 ≤ count581 b)) else (if i < 584 then decide (3 ≤ count581 b) else decide (4 ≤ count581 b)))) else (if i < 588 then (if i < 586 then decide (5 ≤ count581 b) else (if i < 587 then decide (6 ≤ count581 b) else decide (7 ≤ count581 b))) else (if i < 590 then (if i < 589 then decide (8 ≤ count581 b) else decide (1 ≤ count589 b)) else (if i < 591 then decide (2 ≤ count589 b) else decide (1 ≤ count591 b))))) else (if i < 599 then (if i < 595 then (if i < 593 then decide (2 ≤ count591 b) else (if i < 594 then decide (1 ≤ count593 b) else decide (2 ≤ count593 b))) else (if i < 597 then (if i < 596 then decide (3 ≤ count593 b) else decide (4 ≤ count593 b)) else (if i < 598 then decide (1 ≤ count597 b) else decide (2 ≤ count597 b)))) else (if i < 603 then (if i < 601 then (if i < 600 then decide (1 ≤ count599 b) else decide (2 ≤ count599 b)) else (if i < 602 then decide (1 ≤ count601 b) else decide (2 ≤ count601 b))) else (if i < 605 then (if i < 604 then decide (3 ≤ count601 b) else decide (4 ≤ count601 b)) else (if i < 606 then decide (1 ≤ count605 b) else decide (2 ≤ count605 b)))))) else (if i < 621 then (if i < 614 then (if i < 610 then (if i < 608 then decide (3 ≤ count605 b) else (if i < 609 then decide (4 ≤ count605 b) else decide (5 ≤ count605 b))) else (if i < 612 then (if i < 611 then decide (6 ≤ count605 b) else decide (7 ≤ count605 b)) else (if i < 613 then decide (8 ≤ count605 b) else decide (1 ≤ count613 b)))) else (if i < 617 then (if i < 615 then decide (2 ≤ count613 b) else (if i < 616 then decide (3 ≤ count613 b) else decide (4 ≤ count613 b))) else (if i < 619 then (if i < 618 then decide (5 ≤ count613 b) else decide (6 ≤ count613 b)) else (if i < 620 then decide (7 ≤ count613 b) else decide (8 ≤ count613 b))))) else (if i < 628 then (if i < 624 then (if i < 622 then decide (9 ≤ count613 b) else (if i < 623 then decide (10 ≤ count613 b) else decide (11 ≤ count613 b))) else (if i < 626 then (if i < 625 then decide (12 ≤ count613 b) else decide (13 ≤ count613 b)) else (if i < 627 then decide (14 ≤ count613 b) else decide (15 ≤ count613 b)))) else (if i < 632 then (if i < 630 then (if i < 629 then decide (16 ≤ count613 b) else decide (1 ≤ count629 b)) else (if i < 631 then decide (2 ≤ count629 b) else decide (3 ≤ count629 b))) else (if i < 634 then (if i < 633 then decide (4 ≤ count629 b) else decide (5 ≤ count629 b)) else (if i < 635 then decide (6 ≤ count629 b) else decide (7 ≤ count629 b))))))) else (if i < 665 then (if i < 650 then (if i < 643 then (if i < 639 then (if i < 637 then decide (8 ≤ count629 b) else (if i < 638 then decide (9 ≤ count629 b) else decide (10 ≤ count629 b))) else (if i < 641 then (if i < 640 then decide (11 ≤ count629 b) else decide (12 ≤ count629 b)) else (if i < 642 then decide (13 ≤ count629 b) else decide (14 ≤ count629 b)))) else (if i < 646 then (if i < 644 then decide (15 ≤ count629 b) else (if i < 645 then decide (16 ≤ count629 b) else decide (17 ≤ count629 b))) else (if i < 648 then (if i < 647 then decide (18 ≤ count629 b) else decide (19 ≤ count629 b)) else (if i < 649 then decide (20 ≤ count629 b) else decide (21 ≤ count629 b))))) else (if i < 657 then (if i < 653 then (if i < 651 then decide (22 ≤ count629 b) else (if i < 652 then decide (23 ≤ count629 b) else decide (24 ≤ count629 b))) else (if i < 655 then (if i < 654 then decide (25 ≤ count629 b) else decide (26 ≤ count629 b)) else (if i < 656 then decide (27 ≤ count629 b) else decide (28 ≤ count629 b)))) else (if i < 661 then (if i < 659 then (if i < 658 then decide (29 ≤ count629 b) else decide (30 ≤ count629 b)) else (if i < 660 then decide (31 ≤ count629 b) else decide (32 ≤ count629 b))) else (if i < 663 then (if i < 662 then decide (1 ≤ count661 b) else decide (2 ≤ count661 b)) else (if i < 664 then decide (1 ≤ count663 b) else decide (2 ≤ count663 b)))))) else (if i < 679 then (if i < 672 then (if i < 668 then (if i < 666 then decide (1 ≤ count665 b) else (if i < 667 then decide (2 ≤ count665 b) else decide (3 ≤ count665 b))) else (if i < 670 then (if i < 669 then decide (4 ≤ count665 b) else decide (1 ≤ count669 b)) else (if i < 671 then decide (2 ≤ count669 b) else decide (1 ≤ count671 b)))) else (if i < 675 then (if i < 673 then decide (2 ≤ count671 b) else (if i < 674 then decide (1 ≤ count673 b) else decide (2 ≤ count673 b))) else (if i < 677 then (if i < 676 then decide (3 ≤ count673 b) else decide (4 ≤ count673 b)) else (if i < 678 then decide (1 ≤ count677 b) else decide (2 ≤ count677 b))))) else (if i < 686 then (if i < 682 then (if i < 680 then decide (3 ≤ count677 b) else (if i < 681 then decide (4 ≤ count677 b) else decide (5 ≤ count677 b))) else (if i < 684 then (if i < 683 then decide (6 ≤ count677 b) else decide (7 ≤ count677 b)) else (if i < 685 then decide (8 ≤ count677 b) else decide (1 ≤ count685 b)))) else (if i < 690 then (if i < 688 then (if i < 687 then decide (2 ≤ count685 b) else decide (1 ≤ count687 b)) else (if i < 689 then decide (2 ≤ count687 b) else decide (1 ≤ count689 b))) else (if i < 692 then (if i < 691 then decide (2 ≤ count689 b) else decide (3 ≤ count689 b)) else (if i < 693 then decide (4 ≤ count689 b) else decide (1 ≤ count693 b))))))))) else (if i < 810 then (if i < 752 then (if i < 723 then (if i < 708 then (if i < 701 then (if i < 697 then (if i < 695 then decide (2 ≤ count693 b) else (if i < 696 then decide (1 ≤ count695 b) else decide (2 ≤ count695 b))) else (if i < 699 then (if i < 698 then decide (1 ≤ count697 b) else decide (2 ≤ count697 b)) else (if i < 700 then decide (3 ≤ count697 b) else decide (4 ≤ count697 b)))) else (if i < 704 then (if i < 702 then decide (1 ≤ count701 b) else (if i < 703 then decide (2 ≤ count701 b) else decide (3 ≤ count701 b))) else (if i < 706 then (if i < 705 then decide (4 ≤ count701 b) else decide (5 ≤ count701 b)) else (if i < 707 then decide (6 ≤ count701 b) else decide (7 ≤ count701 b))))) else (if i < 715 then (if i < 711 then (if i < 709 then decide (8 ≤ count701 b) else (if i < 710 then decide (1 ≤ count709 b) else decide (2 ≤ count709 b))) else (if i < 713 then (if i < 712 then decide (3 ≤ count709 b) else decide (4 ≤ count709 b)) else (if i < 714 then decide (5 ≤ count709 b) else decide (6 ≤ count709 b)))) else (if i < 719 then (if i < 717 then (if i < 716 then decide (7 ≤ count709 b) else decide (8 ≤ count709 b)) else (if i < 718 then decide (9 ≤ count709 b) else decide (10 ≤ count709 b))) else (if i < 721 then (if i < 720 then decide (11 ≤ count709 b) else decide (12 ≤ count709 b)) else (if i < 722 then decide (13 ≤ count709 b) else decide (14 ≤ count709 b)))))) else (if i < 737 then (if i < 730 then (if i < 726 then (if i < 724 then decide (15 ≤ count709 b) else (if i < 725 then decide (16 ≤ count709 b) else decide (1 ≤ count725 b))) else (if i < 728 then (if i < 727 then decide (2 ≤ count725 b) else decide (1 ≤ count727 b)) else (if i < 729 then decide (2 ≤ count727 b) else decide (1 ≤ count729 b)))) else (if i < 733 then (if i < 731 then decide (2 ≤ count729 b) else (if i < 732 then decide (3 ≤ count729 b) else decide (4 ≤ count729 b))) else (if i < 735 then (if i < 734 then decide (1 ≤ count733 b) else decide (2 ≤ count733 b)) else (if i < 736 then decide (1 ≤ count735 b) else decide (2 ≤ count735 b))))) else (if i < 744 then (if i < 740 then (if i < 738 then decide (1 ≤ count737 b) else (if i < 739 then decide (2 ≤ count737 b) else decide (3 ≤ count737 b))) else (if i < 742 then (if i < 741 then decide (4 ≤ count737 b) else decide (1 ≤ count741 b)) else (if i < 743 then decide (2 ≤ count741 b) else decide (3 ≤ count741 b)))) else (if i < 748 then (if i < 746 then (if i < 745 then decide (4 ≤ count741 b) else decide (5 ≤ count741 b)) else (if i < 747 then decide (6 ≤ count741 b) else decide (7 ≤ count741 b))) else (if i < 750 then (if i < 749 then decide (8 ≤ count741 b) else decide (1 ≤ count749 b)) else (if i < 751 then decide (2 ≤ count749 b) else decide (1 ≤ count751 b))))))) else (if i < 781 then (if i < 766 then (if i < 759 then (if i < 755 then (if i < 753 then decide (2 ≤ count751 b) else (if i < 754 then decide (1 ≤ count753 b) else decide (2 ≤ count753 b))) else (if i < 757 then (if i < 756 then decide (3 ≤ count753 b) else decide (4 ≤ count753 b)) else (if i < 758 then decide (1 ≤ count757 b) else decide (2 ≤ count757 b)))) else (if i < 762 then (if i < 760 then decide (1 ≤ count759 b) else (if i < 761 then decide (2 ≤ count759 b) else decide (1 ≤ count761 b))) else (if i < 764 then (if i < 763 then decide (2 ≤ count761 b) else decide (3 ≤ count761 b)) else (if i < 765 then decide (4 ≤ count761 b) else decide (1 ≤ count765 b))))) else (if i < 773 then (if i < 769 then (if i < 767 then decide (2 ≤ count765 b) else (if i < 768 then decide (3 ≤ count765 b) else decide (4 ≤ count765 b))) else (if i < 771 then (if i < 770 then decide (5 ≤ count765 b) else decide (6 ≤ count765 b)) else (if i < 772 then decide (7 ≤ count765 b) else decide (8 ≤ count765 b)))) else (if i < 777 then (if i < 775 then (if i < 774 then decide (1 ≤ count773 b) else decide (2 ≤ count773 b)) else (if i < 776 then decide (3 ≤ count773 b) else decide (4 ≤ count773 b))) else (if i < 779 then (if i < 778 then decide (5 ≤ count773 b) else decide (6 ≤ count773 b)) else (if i < 780 then decide (7 ≤ count773 b) else decide (8 ≤ count773 b)))))) else (if i < 795 then (if i < 788 then (if i < 784 then (if i < 782 then decide (9 ≤ count773 b) else (if i < 783 then decide (10 ≤ count773 b) else decide (11 ≤ count773 b))) else (if i < 786 then (if i < 785 then decide (12 ≤ count773 b) else decide (13 ≤ count773 b)) else (if i < 787 then decide (14 ≤ count773 b) else decide (15 ≤ count773 b)))) else (if i < 791 then (if i < 789 then decide (16 ≤ count773 b) else (if i < 790 then decide (1 ≤ count789 b) else decide (2 ≤ count789 b))) else (if i < 793 then (if i < 792 then decide (3 ≤ count789 b) else decide (4 ≤ count789 b)) else (if i < 794 then decide (5 ≤ count789 b) else decide (6 ≤ count789 b))))) else (if i < 802 then (if i < 798 then (if i < 796 then decide (7 ≤ count789 b) else (if i < 797 then decide (8 ≤ count789 b) else decide (9 ≤ count789 b))) else (if i < 800 then (if i < 799 then decide (10 ≤ count789 b) else decide (11 ≤ count789 b)) else (if i < 801 then decide (12 ≤ count789 b) else decide (13 ≤ count789 b)))) else (if i < 806 then (if i < 804 then (if i < 803 then decide (14 ≤ count789 b) else decide (15 ≤ count789 b)) else (if i < 805 then decide (16 ≤ count789 b) else decide (17 ≤ count789 b))) else (if i < 808 then (if i < 807 then decide (18 ≤ count789 b) else decide (19 ≤ count789 b)) else (if i < 809 then decide (20 ≤ count789 b) else decide (21 ≤ count789 b)))))))) else (if i < 868 then (if i < 839 then (if i < 824 then (if i < 817 then (if i < 813 then (if i < 811 then decide (22 ≤ count789 b) else (if i < 812 then decide (23 ≤ count789 b) else decide (24 ≤ count789 b))) else (if i < 815 then (if i < 814 then decide (25 ≤ count789 b) else decide (26 ≤ count789 b)) else (if i < 816 then decide (27 ≤ count789 b) else decide (28 ≤ count789 b)))) else (if i < 820 then (if i < 818 then decide (29 ≤ count789 b) else (if i < 819 then decide (30 ≤ count789 b) else decide (31 ≤ count789 b))) else (if i < 822 then (if i < 821 then decide (32 ≤ count789 b) else decide (1 ≤ count821 b)) else (if i < 823 then decide (2 ≤ count821 b) else decide (3 ≤ count821 b))))) else (if i < 831 then (if i < 827 then (if i < 825 then decide (4 ≤ count821 b) else (if i < 826 then decide (5 ≤ count821 b) else decide (6 ≤ count821 b))) else (if i < 829 then (if i < 828 then decide (7 ≤ count821 b) else decide (8 ≤ count821 b)) else (if i < 830 then decide (9 ≤ count821 b) else decide (10 ≤ count821 b)))) else (if i < 835 then (if i < 833 then (if i < 832 then decide (11 ≤ count821 b) else decide (12 ≤ count821 b)) else (if i < 834 then decide (13 ≤ count821 b) else decide (14 ≤ count821 b))) else (if i < 837 then (if i < 836 then decide (15 ≤ count821 b) else decide (16 ≤ count821 b)) else (if i < 838 then decide (17 ≤ count821 b) else decide (18 ≤ count821 b)))))) else (if i < 853 then (if i < 846 then (if i < 842 then (if i < 840 then decide (19 ≤ count821 b) else (if i < 841 then decide (20 ≤ count821 b) else decide (21 ≤ count821 b))) else (if i < 844 then (if i < 843 then decide (22 ≤ count821 b) else decide (23 ≤ count821 b)) else (if i < 845 then decide (24 ≤ count821 b) else decide (25 ≤ count821 b)))) else (if i < 849 then (if i < 847 then decide (26 ≤ count821 b) else (if i < 848 then decide (27 ≤ count821 b) else decide (28 ≤ count821 b))) else (if i < 851 then (if i < 850 then decide (29 ≤ count821 b) else decide (30 ≤ count821 b)) else (if i < 852 then decide (31 ≤ count821 b) else decide (32 ≤ count821 b))))) else (if i < 860 then (if i < 856 then (if i < 854 then decide (33 ≤ count821 b) else (if i < 855 then decide (34 ≤ count821 b) else decide (35 ≤ count821 b))) else (if i < 858 then (if i < 857 then decide (36 ≤ count821 b) else decide (37 ≤ count821 b)) else (if i < 859 then decide (38 ≤ count821 b) else decide (39 ≤ count821 b)))) else (if i < 864 then (if i < 862 then (if i < 861 then decide (40 ≤ count821 b) else decide (41 ≤ count821 b)) else (if i < 863 then decide (42 ≤ count821 b) else decide (1 ≤ count863 b))) else (if i < 866 then (if i < 865 then decide (2 ≤ count863 b) else decide (1 ≤ count865 b)) else (if i < 867 then decide (2 ≤ count865 b) else decide (1 ≤ count867 b))))))) else (if i < 897 then (if i < 882 then (if i < 875 then (if i < 871 then (if i < 869 then decide (2 ≤ count867 b) else (if i < 870 then decide (3 ≤ count867 b) else decide (4 ≤ count867 b))) else (if i < 873 then (if i < 872 then decide (1 ≤ count871 b) else decide (2 ≤ count871 b)) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b)))) else (if i < 878 then (if i < 876 then decide (1 ≤ count875 b) else (if i < 877 then decide (2 ≤ count875 b) else decide (3 ≤ count875 b))) else (if i < 880 then (if i < 879 then decide (4 ≤ count875 b) else decide (1 ≤ count879 b)) else (if i < 881 then decide (2 ≤ count879 b) else decide (3 ≤ count879 b))))) else (if i < 889 then (if i < 885 then (if i < 883 then decide (4 ≤ count879 b) else (if i < 884 then decide (5 ≤ count879 b) else decide (6 ≤ count879 b))) else (if i < 887 then (if i < 886 then decide (7 ≤ count879 b) else decide (8 ≤ count879 b)) else (if i < 888 then decide (1 ≤ count887 b) else decide (2 ≤ count887 b)))) else (if i < 893 then (if i < 891 then (if i < 890 then decide (1 ≤ count889 b) else decide (2 ≤ count889 b)) else (if i < 892 then decide (1 ≤ count891 b) else decide (2 ≤ count891 b))) else (if i < 895 then (if i < 894 then decide (3 ≤ count891 b) else decide (4 ≤ count891 b)) else (if i < 896 then decide (1 ≤ count895 b) else decide (2 ≤ count895 b)))))) else (if i < 911 then (if i < 904 then (if i < 900 then (if i < 898 then decide (1 ≤ count897 b) else (if i < 899 then decide (2 ≤ count897 b) else decide (1 ≤ count899 b))) else (if i < 902 then (if i < 901 then decide (2 ≤ count899 b) else decide (3 ≤ count899 b)) else (if i < 903 then decide (4 ≤ count899 b) else decide (1 ≤ count903 b)))) else (if i < 907 then (if i < 905 then decide (2 ≤ count903 b) else (if i < 906 then decide (3 ≤ count903 b) else decide (4 ≤ count903 b))) else (if i < 909 then (if i < 908 then decide (5 ≤ count903 b) else decide (6 ≤ count903 b)) else (if i < 910 then decide (7 ≤ count903 b) else decide (8 ≤ count903 b))))) else (if i < 918 then (if i < 914 then (if i < 912 then decide (1 ≤ count911 b) else (if i < 913 then decide (2 ≤ count911 b) else decide (3 ≤ count911 b))) else (if i < 916 then (if i < 915 then decide (4 ≤ count911 b) else decide (5 ≤ count911 b)) else (if i < 917 then decide (6 ≤ count911 b) else decide (7 ≤ count911 b)))) else (if i < 922 then (if i < 920 then (if i < 919 then decide (8 ≤ count911 b) else decide (9 ≤ count911 b)) else (if i < 921 then decide (10 ≤ count911 b) else decide (11 ≤ count911 b))) else (if i < 924 then (if i < 923 then decide (12 ≤ count911 b) else decide (13 ≤ count911 b)) else (if i < 925 then decide (14 ≤ count911 b) else decide (15 ≤ count911 b))))))))))) else (if i < 1389 then (if i < 1157 then (if i < 1041 then (if i < 983 then (if i < 954 then (if i < 940 then (if i < 933 then (if i < 929 then (if i < 927 then decide (16 ≤ count911 b) else (if i < 928 then decide (1 ≤ count927 b) else decide (2 ≤ count927 b))) else (if i < 931 then (if i < 930 then decide (1 ≤ count929 b) else decide (2 ≤ count929 b)) else (if i < 932 then decide (1 ≤ count931 b) else decide (2 ≤ count931 b)))) else (if i < 936 then (if i < 934 then decide (3 ≤ count931 b) else (if i < 935 then decide (4 ≤ count931 b) else decide (1 ≤ count935 b))) else (if i < 938 then (if i < 937 then decide (2 ≤ count935 b) else decide (1 ≤ count937 b)) else (if i < 939 then decide (2 ≤ count937 b) else decide (1 ≤ count939 b))))) else (if i < 947 then (if i < 943 then (if i < 941 then decide (2 ≤ count939 b) else (if i < 942 then decide (3 ≤ count939 b) else decide (4 ≤ count939 b))) else (if i < 945 then (if i < 944 then decide (1 ≤ count943 b) else decide (2 ≤ count943 b)) else (if i < 946 then decide (3 ≤ count943 b) else decide (4 ≤ count943 b)))) else (if i < 950 then (if i < 948 then decide (5 ≤ count943 b) else (if i < 949 then decide (6 ≤ count943 b) else decide (7 ≤ count943 b))) else (if i < 952 then (if i < 951 then decide (8 ≤ count943 b) else decide (1 ≤ count951 b)) else (if i < 953 then decide (2 ≤ count951 b) else decide (1 ≤ count953 b)))))) else (if i < 968 then (if i < 961 then (if i < 957 then (if i < 955 then decide (2 ≤ count953 b) else (if i < 956 then decide (1 ≤ count955 b) else decide (2 ≤ count955 b))) else (if i < 959 then (if i < 958 then decide (3 ≤ count955 b) else decide (4 ≤ count955 b)) else (if i < 960 then decide (1 ≤ count959 b) else decide (2 ≤ count959 b)))) else (if i < 964 then (if i < 962 then decide (1 ≤ count961 b) else (if i < 963 then decide (2 ≤ count961 b) else decide (1 ≤ count963 b))) else (if i < 966 then (if i < 965 then decide (2 ≤ count963 b) else decide (3 ≤ count963 b)) else (if i < 967 then decide (4 ≤ count963 b) else decide (1 ≤ count967 b))))) else (if i < 975 then (if i < 971 then (if i < 969 then decide (2 ≤ count967 b) else (if i < 970 then decide (3 ≤ count967 b) else decide (4 ≤ count967 b))) else (if i < 973 then (if i < 972 then decide (5 ≤ count967 b) else decide (6 ≤ count967 b)) else (if i < 974 then decide (7 ≤ count967 b) else decide (8 ≤ count967 b)))) else (if i < 979 then (if i < 977 then (if i < 976 then decide (1 ≤ count975 b) else decide (2 ≤ count975 b)) else (if i < 978 then decide (3 ≤ count975 b) else decide (4 ≤ count975 b))) else (if i < 981 then (if i < 980 then decide (5 ≤ count975 b) else decide (6 ≤ count975 b)) else (if i < 982 then decide (7 ≤ count975 b) else decide (8 ≤ count975 b))))))) else (if i < 1012 then (if i < 997 then (if i < 990 then (if i < 986 then (if i < 984 then decide (9 ≤ count975 b) else (if i < 985 then decide (10 ≤ count975 b) else decide (11 ≤ count975 b))) else (if i < 988 then (if i < 987 then decide (12 ≤ count975 b) else decide (13 ≤ count975 b)) else (if i < 989 then decide (14 ≤ count975 b) else decide (15 ≤ count975 b)))) else (if i < 993 then (if i < 991 then decide (16 ≤ count975 b) else (if i < 992 then decide (1 ≤ count991 b) else decide (2 ≤ count991 b))) else (if i < 995 then (if i < 994 then decide (3 ≤ count991 b) else decide (4 ≤ count991 b)) else (if i < 996 then decide (5 ≤ count991 b) else decide (6 ≤ count991 b))))) else (if i < 1004 then (if i < 1000 then (if i < 998 then decide (7 ≤ count991 b) else (if i < 999 then decide (8 ≤ count991 b) else decide (9 ≤ count991 b))) else (if i < 1002 then (if i < 1001 then decide (10 ≤ count991 b) else decide (11 ≤ count991 b)) else (if i < 1003 then decide (12 ≤ count991 b) else decide (13 ≤ count991 b)))) else (if i < 1008 then (if i < 1006 then (if i < 1005 then decide (14 ≤ count991 b) else decide (15 ≤ count991 b)) else (if i < 1007 then decide (16 ≤ count991 b) else decide (17 ≤ count991 b))) else (if i < 1010 then (if i < 1009 then decide (18 ≤ count991 b) else decide (19 ≤ count991 b)) else (if i < 1011 then decide (20 ≤ count991 b) else decide (21 ≤ count991 b)))))) else (if i < 1026 then (if i < 1019 then (if i < 1015 then (if i < 1013 then decide (22 ≤ count991 b) else (if i < 1014 then decide (23 ≤ count991 b) else decide (24 ≤ count991 b))) else (if i < 1017 then (if i < 1016 then decide (1 ≤ count1015 b) else decide (2 ≤ count1015 b)) else (if i < 1018 then decide (1 ≤ count1017 b) else decide (2 ≤ count1017 b)))) else (if i < 1022 then (if i < 1020 then decide (1 ≤ count1019 b) else (if i < 1021 then decide (2 ≤ count1019 b) else decide (3 ≤ count1019 b))) else (if i < 1024 then (if i < 1023 then decide (4 ≤ count1019 b) else decide (1 ≤ count1023 b)) else (if i < 1025 then decide (2 ≤ count1023 b) else decide (1 ≤ count1025 b))))) else (if i < 1033 then (if i < 1029 then (if i < 1027 then decide (2 ≤ count1025 b) else (if i < 1028 then decide (1 ≤ count1027 b) else decide (2 ≤ count1027 b))) else (if i < 1031 then (if i < 1030 then decide (3 ≤ count1027 b) else decide (4 ≤ count1027 b)) else (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b)))) else (if i < 1037 then (if i < 1035 then (if i < 1034 then decide (3 ≤ count1031 b) else decide (4 ≤ count1031 b)) else (if i < 1036 then decide (5 ≤ count1031 b) else decide (6 ≤ count1031 b))) else (if i < 1039 then (if i < 1038 then decide (7 ≤ count1031 b) else decide (8 ≤ count1031 b)) else (if i < 1040 then decide (1 ≤ count1039 b) else decide (2 ≤ count1039 b)))))))) else (if i < 1099 then (if i < 1070 then (if i < 1055 then (if i < 1048 then (if i < 1044 then (if i < 1042 then decide (1 ≤ count1041 b) else (if i < 1043 then decide (2 ≤ count1041 b) else decide (1 ≤ count1043 b))) else (if i < 1046 then (if i < 1045 then decide (2 ≤ count1043 b) else decide (3 ≤ count1043 b)) else (if i < 1047 then decide (4 ≤ count1043 b) else decide (1 ≤ count1047 b)))) else (if i < 1051 then (if i < 1049 then decide (2 ≤ count1047 b) else (if i < 1050 then decide (1 ≤ count1049 b) else decide (2 ≤ count1049 b))) else (if i < 1053 then (if i < 1052 then decide (1 ≤ count1051 b) else decide (2 ≤ count1051 b)) else (if i < 1054 then decide (3 ≤ count1051 b) else decide (4 ≤ count1051 b))))) else (if i < 1062 then (if i < 1058 then (if i < 1056 then decide (1 ≤ count1055 b) else (if i < 1057 then decide (2 ≤ count1055 b) else decide (3 ≤ count1055 b))) else (if i < 1060 then (if i < 1059 then decide (4 ≤ count1055 b) else decide (5 ≤ count1055 b)) else (if i < 1061 then decide (6 ≤ count1055 b) else decide (7 ≤ count1055 b)))) else (if i < 1066 then (if i < 1064 then (if i < 1063 then decide (8 ≤ count1055 b) else decide (1 ≤ count1063 b)) else (if i < 1065 then decide (2 ≤ count1063 b) else decide (3 ≤ count1063 b))) else (if i < 1068 then (if i < 1067 then decide (4 ≤ count1063 b) else decide (5 ≤ count1063 b)) else (if i < 1069 then decide (6 ≤ count1063 b) else decide (7 ≤ count1063 b)))))) else (if i < 1084 then (if i < 1077 then (if i < 1073 then (if i < 1071 then decide (8 ≤ count1063 b) else (if i < 1072 then decide (9 ≤ count1063 b) else decide (10 ≤ count1063 b))) else (if i < 1075 then (if i < 1074 then decide (11 ≤ count1063 b) else decide (12 ≤ count1063 b)) else (if i < 1076 then decide (13 ≤ count1063 b) else decide (14 ≤ count1063 b)))) else (if i < 1080 then (if i < 1078 then decide (15 ≤ count1063 b) else (if i < 1079 then decide (16 ≤ count1063 b) else decide (1 ≤ count1079 b))) else (if i < 1082 then (if i < 1081 then decide (2 ≤ count1079 b) else decide (1 ≤ count1081 b)) else (if i < 1083 then decide (2 ≤ count1081 b) else decide (1 ≤ count1083 b))))) else (if i < 1091 then (if i < 1087 then (if i < 1085 then decide (2 ≤ count1083 b) else (if i < 1086 then decide (3 ≤ count1083 b) else decide (4 ≤ count1083 b))) else (if i < 1089 then (if i < 1088 then decide (1 ≤ count1087 b) else decide (2 ≤ count1087 b)) else (if i < 1090 then decide (1 ≤ count1089 b) else decide (2 ≤ count1089 b)))) else (if i < 1095 then (if i < 1093 then (if i < 1092 then decide (1 ≤ count1091 b) else decide (2 ≤ count1091 b)) else (if i < 1094 then decide (3 ≤ count1091 b) else decide (4 ≤ count1091 b))) else (if i < 1097 then (if i < 1096 then decide (1 ≤ count1095 b) else decide (2 ≤ count1095 b)) else (if i < 1098 then decide (3 ≤ count1095 b) else decide (4 ≤ count1095 b))))))) else (if i < 1128 then (if i < 1113 then (if i < 1106 then (if i < 1102 then (if i < 1100 then decide (5 ≤ count1095 b) else (if i < 1101 then decide (6 ≤ count1095 b) else decide (7 ≤ count1095 b))) else (if i < 1104 then (if i < 1103 then decide (8 ≤ count1095 b) else decide (1 ≤ count1103 b)) else (if i < 1105 then decide (2 ≤ count1103 b) else decide (1 ≤ count1105 b)))) else (if i < 1109 then (if i < 1107 then decide (2 ≤ count1105 b) else (if i < 1108 then decide (1 ≤ count1107 b) else decide (2 ≤ count1107 b))) else (if i < 1111 then (if i < 1110 then decide (3 ≤ count1107 b) else decide (4 ≤ count1107 b)) else (if i < 1112 then decide (1 ≤ count1111 b) else decide (2 ≤ count1111 b))))) else (if i < 1120 then (if i < 1116 then (if i < 1114 then decide (1 ≤ count1113 b) else (if i < 1115 then decide (2 ≤ count1113 b) else decide (1 ≤ count1115 b))) else (if i < 1118 then (if i < 1117 then decide (2 ≤ count1115 b) else decide (3 ≤ count1115 b)) else (if i < 1119 then decide (4 ≤ count1115 b) else decide (1 ≤ count1119 b)))) else (if i < 1124 then (if i < 1122 then (if i < 1121 then decide (2 ≤ count1119 b) else decide (3 ≤ count1119 b)) else (if i < 1123 then decide (4 ≤ count1119 b) else decide (5 ≤ count1119 b))) else (if i < 1126 then (if i < 1125 then decide (6 ≤ count1119 b) else decide (7 ≤ count1119 b)) else (if i < 1127 then decide (8 ≤ count1119 b) else decide (1 ≤ count1127 b)))))) else (if i < 1142 then (if i < 1135 then (if i < 1131 then (if i < 1129 then decide (2 ≤ count1127 b) else (if i < 1130 then decide (3 ≤ count1127 b) else decide (4 ≤ count1127 b))) else (if i < 1133 then (if i < 1132 then decide (5 ≤ count1127 b) else decide (6 ≤ count1127 b)) else (if i < 1134 then decide (7 ≤ count1127 b) else decide (8 ≤ count1127 b)))) else (if i < 1138 then (if i < 1136 then decide (9 ≤ count1127 b) else (if i < 1137 then decide (10 ≤ count1127 b) else decide (11 ≤ count1127 b))) else (if i < 1140 then (if i < 1139 then decide (12 ≤ count1127 b) else decide (13 ≤ count1127 b)) else (if i < 1141 then decide (14 ≤ count1127 b) else decide (15 ≤ count1127 b))))) else (if i < 1149 then (if i < 1145 then (if i < 1143 then decide (16 ≤ count1127 b) else (if i < 1144 then decide (1 ≤ count1143 b) else decide (2 ≤ count1143 b))) else (if i < 1147 then (if i < 1146 then decide (3 ≤ count1143 b) else decide (4 ≤ count1143 b)) else (if i < 1148 then decide (5 ≤ count1143 b) else decide (6 ≤ count1143 b)))) else (if i < 1153 then (if i < 1151 then (if i < 1150 then decide (7 ≤ count1143 b) else decide (8 ≤ count1143 b)) else (if i < 1152 then decide (9 ≤ count1143 b) else decide (10 ≤ count1143 b))) else (if i < 1155 then (if i < 1154 then decide (11 ≤ count1143 b) else decide (12 ≤ count1143 b)) else (if i < 1156 then decide (13 ≤ count1143 b) else decide (14 ≤ count1143 b))))))))) else (if i < 1273 then (if i < 1215 then (if i < 1186 then (if i < 1171 then (if i < 1164 then (if i < 1160 then (if i < 1158 then decide (15 ≤ count1143 b) else (if i < 1159 then decide (16 ≤ count1143 b) else decide (17 ≤ count1143 b))) else (if i < 1162 then (if i < 1161 then decide (18 ≤ count1143 b) else decide (19 ≤ count1143 b)) else (if i < 1163 then decide (20 ≤ count1143 b) else decide (21 ≤ count1143 b)))) else (if i < 1167 then (if i < 1165 then decide (22 ≤ count1143 b) else (if i < 1166 then decide (23 ≤ count1143 b) else decide (24 ≤ count1143 b))) else (if i < 1169 then (if i < 1168 then decide (1 ≤ count1167 b) else decide (2 ≤ count1167 b)) else (if i < 1170 then decide (3 ≤ count1167 b) else decide (4 ≤ count1167 b))))) else (if i < 1178 then (if i < 1174 then (if i < 1172 then decide (5 ≤ count1167 b) else (if i < 1173 then decide (6 ≤ count1167 b) else decide (7 ≤ count1167 b))) else (if i < 1176 then (if i < 1175 then decide (8 ≤ count1167 b) else decide (9 ≤ count1167 b)) else (if i < 1177 then decide (10 ≤ count1167 b) else decide (11 ≤ count1167 b)))) else (if i < 1182 then (if i < 1180 then (if i < 1179 then decide (12 ≤ count1167 b) else decide (13 ≤ count1167 b)) else (if i < 1181 then decide (14 ≤ count1167 b) else decide (15 ≤ count1167 b))) else (if i < 1184 then (if i < 1183 then decide (16 ≤ count1167 b) else decide (17 ≤ count1167 b)) else (if i < 1185 then decide (18 ≤ count1167 b) else decide (19 ≤ count1167 b)))))) else (if i < 1200 then (if i < 1193 then (if i < 1189 then (if i < 1187 then decide (20 ≤ count1167 b) else (if i < 1188 then decide (21 ≤ count1167 b) else decide (22 ≤ count1167 b))) else (if i < 1191 then (if i < 1190 then decide (23 ≤ count1167 b) else decide (24 ≤ count1167 b)) else (if i < 1192 then decide (1 ≤ count1191 b) else decide (2 ≤ count1191 b)))) else (if i < 1196 then (if i < 1194 then decide (1 ≤ count1193 b) else (if i < 1195 then decide (2 ≤ count1193 b) else decide (3 ≤ count1193 b))) else (if i < 1198 then (if i < 1197 then decide (1 ≤ count1196 b) else decide (2 ≤ count1196 b)) else (if i < 1199 then decide (1 ≤ count1198 b) else decide (2 ≤ count1198 b))))) else (if i < 1207 then (if i < 1203 then (if i < 1201 then decide (1 ≤ count1200 b) else (if i < 1202 then decide (2 ≤ count1200 b) else decide (3 ≤ count1200 b))) else (if i < 1205 then (if i < 1204 then decide (4 ≤ count1200 b) else decide (1 ≤ count1204 b)) else (if i < 1206 then decide (2 ≤ count1204 b) else decide (3 ≤ count1204 b)))) else (if i < 1211 then (if i < 1209 then (if i < 1208 then decide (4 ≤ count1204 b) else decide (5 ≤ count1204 b)) else (if i < 1210 then decide (6 ≤ count1204 b) else decide (7 ≤ count1204 b))) else (if i < 1213 then (if i < 1212 then decide (1 ≤ count1211 b) else decide (2 ≤ count1211 b)) else (if i < 1214 then decide (1 ≤ count1213 b) else decide (2 ≤ count1213 b))))))) else (if i < 1244 then (if i < 1229 then (if i < 1222 then (if i < 1218 then (if i < 1216 then decide (1 ≤ count1215 b) else (if i < 1217 then decide (2 ≤ count1215 b) else decide (3 ≤ count1215 b))) else (if i < 1220 then (if i < 1219 then decide (4 ≤ count1215 b) else decide (1 ≤ count1219 b)) else (if i < 1221 then decide (2 ≤ count1219 b) else decide (1 ≤ count1221 b)))) else (if i < 1225 then (if i < 1223 then decide (2 ≤ count1221 b) else (if i < 1224 then decide (1 ≤ count1223 b) else decide (2 ≤ count1223 b))) else (if i < 1227 then (if i < 1226 then decide (3 ≤ count1223 b) else decide (4 ≤ count1223 b)) else (if i < 1228 then decide (1 ≤ count1227 b) else decide (2 ≤ count1227 b))))) else (if i < 1236 then (if i < 1232 then (if i < 1230 then decide (3 ≤ count1227 b) else (if i < 1231 then decide (4 ≤ count1227 b) else decide (5 ≤ count1227 b))) else (if i < 1234 then (if i < 1233 then decide (6 ≤ count1227 b) else decide (7 ≤ count1227 b)) else (if i < 1235 then decide (8 ≤ count1227 b) else decide (1 ≤ count1235 b)))) else (if i < 1240 then (if i < 1238 then (if i < 1237 then decide (2 ≤ count1235 b) else decide (3 ≤ count1235 b)) else (if i < 1239 then decide (4 ≤ count1235 b) else decide (5 ≤ count1235 b))) else (if i < 1242 then (if i < 1241 then decide (6 ≤ count1235 b) else decide (7 ≤ count1235 b)) else (if i < 1243 then decide (8 ≤ count1235 b) else decide (9 ≤ count1235 b)))))) else (if i < 1258 then (if i < 1251 then (if i < 1247 then (if i < 1245 then decide (10 ≤ count1235 b) else (if i < 1246 then decide (11 ≤ count1235 b) else decide (12 ≤ count1235 b))) else (if i < 1249 then (if i < 1248 then decide (13 ≤ count1235 b) else decide (14 ≤ count1235 b)) else (if i < 1250 then decide (15 ≤ count1235 b) else decide (1 ≤ count1250 b)))) else (if i < 1254 then (if i < 1252 then decide (2 ≤ count1250 b) else (if i < 1253 then decide (1 ≤ count1252 b) else decide (2 ≤ count1252 b))) else (if i < 1256 then (if i < 1255 then decide (1 ≤ count1254 b) else decide (2 ≤ count1254 b)) else (if i < 1257 then decide (3 ≤ count1254 b) else decide (4 ≤ count1254 b))))) else (if i < 1265 then (if i < 1261 then (if i < 1259 then decide (1 ≤ count1258 b) else (if i < 1260 then decide (2 ≤ count1258 b) else decide (1 ≤ count1260 b))) else (if i < 1263 then (if i < 1262 then decide (2 ≤ count1260 b) else decide (1 ≤ count1262 b)) else (if i < 1264 then decide (2 ≤ count1262 b) else decide (3 ≤ count1262 b)))) else (if i < 1269 then (if i < 1267 then (if i < 1266 then decide (4 ≤ count1262 b) else decide (1 ≤ count1266 b)) else (if i < 1268 then decide (2 ≤ count1266 b) else decide (3 ≤ count1266 b))) else (if i < 1271 then (if i < 1270 then decide (4 ≤ count1266 b) else decide (5 ≤ count1266 b)) else (if i < 1272 then decide (6 ≤ count1266 b) else decide (7 ≤ count1266 b)))))))) else (if i < 1331 then (if i < 1302 then (if i < 1287 then (if i < 1280 then (if i < 1276 then (if i < 1274 then decide (8 ≤ count1266 b) else (if i < 1275 then decide (1 ≤ count1274 b) else decide (2 ≤ count1274 b))) else (if i < 1278 then (if i < 1277 then decide (1 ≤ count1276 b) else decide (2 ≤ count1276 b)) else (if i < 1279 then decide (1 ≤ count1278 b) else decide (2 ≤ count1278 b)))) else (if i < 1283 then (if i < 1281 then decide (3 ≤ count1278 b) else (if i < 1282 then decide (4 ≤ count1278 b) else decide (1 ≤ count1282 b))) else (if i < 1285 then (if i < 1284 then decide (2 ≤ count1282 b) else decide (1 ≤ count1284 b)) else (if i < 1286 then decide (2 ≤ count1284 b) else decide (1 ≤ count1286 b))))) else (if i < 1294 then (if i < 1290 then (if i < 1288 then decide (2 ≤ count1286 b) else (if i < 1289 then decide (3 ≤ count1286 b) else decide (4 ≤ count1286 b))) else (if i < 1292 then (if i < 1291 then decide (1 ≤ count1290 b) else decide (2 ≤ count1290 b)) else (if i < 1293 then decide (3 ≤ count1290 b) else decide (4 ≤ count1290 b)))) else (if i < 1298 then (if i < 1296 then (if i < 1295 then decide (5 ≤ count1290 b) else decide (6 ≤ count1290 b)) else (if i < 1297 then decide (7 ≤ count1290 b) else decide (8 ≤ count1290 b))) else (if i < 1300 then (if i < 1299 then decide (1 ≤ count1298 b) else decide (2 ≤ count1298 b)) else (if i < 1301 then decide (3 ≤ count1298 b) else decide (4 ≤ count1298 b)))))) else (if i < 1316 then (if i < 1309 then (if i < 1305 then (if i < 1303 then decide (5 ≤ count1298 b) else (if i < 1304 then decide (6 ≤ count1298 b) else decide (7 ≤ count1298 b))) else (if i < 1307 then (if i < 1306 then decide (8 ≤ count1298 b) else decide (9 ≤ count1298 b)) else (if i < 1308 then decide (10 ≤ count1298 b) else decide (11 ≤ count1298 b)))) else (if i < 1312 then (if i < 1310 then decide (12 ≤ count1298 b) else (if i < 1311 then decide (13 ≤ count1298 b) else decide (14 ≤ count1298 b))) else (if i < 1314 then (if i < 1313 then decide (15 ≤ count1298 b) else decide (16 ≤ count1298 b)) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b))))) else (if i < 1323 then (if i < 1319 then (if i < 1317 then decide (3 ≤ count1314 b) else (if i < 1318 then decide (4 ≤ count1314 b) else decide (5 ≤ count1314 b))) else (if i < 1321 then (if i < 1320 then decide (6 ≤ count1314 b) else decide (7 ≤ count1314 b)) else (if i < 1322 then decide (8 ≤ count1314 b) else decide (9 ≤ count1314 b)))) else (if i < 1327 then (if i < 1325 then (if i < 1324 then decide (10 ≤ count1314 b) else decide (11 ≤ count1314 b)) else (if i < 1326 then decide (12 ≤ count1314 b) else decide (13 ≤ count1314 b))) else (if i < 1329 then (if i < 1328 then decide (14 ≤ count1314 b) else decide (15 ≤ count1314 b)) else (if i < 1330 then decide (16 ≤ count1314 b) else decide (17 ≤ count1314 b))))))) else (if i < 1360 then (if i < 1345 then (if i < 1338 then (if i < 1334 then (if i < 1332 then decide (18 ≤ count1314 b) else (if i < 1333 then decide (19 ≤ count1314 b) else decide (20 ≤ count1314 b))) else (if i < 1336 then (if i < 1335 then decide (21 ≤ count1314 b) else decide (22 ≤ count1314 b)) else (if i < 1337 then decide (23 ≤ count1314 b) else decide (24 ≤ count1314 b)))) else (if i < 1341 then (if i < 1339 then decide (25 ≤ count1314 b) else (if i < 1340 then decide (26 ≤ count1314 b) else decide (27 ≤ count1314 b))) else (if i < 1343 then (if i < 1342 then decide (28 ≤ count1314 b) else decide (29 ≤ count1314 b)) else (if i < 1344 then decide (30 ≤ count1314 b) else decide (31 ≤ count1314 b))))) else (if i < 1352 then (if i < 1348 then (if i < 1346 then decide (1 ≤ count1345 b) else (if i < 1347 then decide (2 ≤ count1345 b) else decide (1 ≤ count1347 b))) else (if i < 1350 then (if i < 1349 then decide (2 ≤ count1347 b) else decide (3 ≤ count1347 b)) else (if i < 1351 then decide (1 ≤ count1350 b) else decide (2 ≤ count1350 b)))) else (if i < 1356 then (if i < 1354 then (if i < 1353 then decide (1 ≤ count1352 b) else decide (2 ≤ count1352 b)) else (if i < 1355 then decide (1 ≤ count1354 b) else decide (2 ≤ count1354 b))) else (if i < 1358 then (if i < 1357 then decide (3 ≤ count1354 b) else decide (4 ≤ count1354 b)) else (if i < 1359 then decide (1 ≤ count1358 b) else decide (2 ≤ count1358 b)))))) else (if i < 1374 then (if i < 1367 then (if i < 1363 then (if i < 1361 then decide (3 ≤ count1358 b) else (if i < 1362 then decide (4 ≤ count1358 b) else decide (5 ≤ count1358 b))) else (if i < 1365 then (if i < 1364 then decide (6 ≤ count1358 b) else decide (7 ≤ count1358 b)) else (if i < 1366 then decide (1 ≤ count1365 b) else decide (2 ≤ count1365 b)))) else (if i < 1370 then (if i < 1368 then decide (1 ≤ count1367 b) else (if i < 1369 then decide (2 ≤ count1367 b) else decide (1 ≤ count1369 b))) else (if i < 1372 then (if i < 1371 then decide (2 ≤ count1369 b) else decide (3 ≤ count1369 b)) else (if i < 1373 then decide (4 ≤ count1369 b) else decide (1 ≤ count1373 b))))) else (if i < 1381 then (if i < 1377 then (if i < 1375 then decide (2 ≤ count1373 b) else (if i < 1376 then decide (1 ≤ count1375 b) else decide (2 ≤ count1375 b))) else (if i < 1379 then (if i < 1378 then decide (1 ≤ count1377 b) else decide (2 ≤ count1377 b)) else (if i < 1380 then decide (3 ≤ count1377 b) else decide (4 ≤ count1377 b)))) else (if i < 1385 then (if i < 1383 then (if i < 1382 then decide (1 ≤ count1381 b) else decide (2 ≤ count1381 b)) else (if i < 1384 then decide (3 ≤ count1381 b) else decide (4 ≤ count1381 b))) else (if i < 1387 then (if i < 1386 then decide (5 ≤ count1381 b) else decide (6 ≤ count1381 b)) else (if i < 1388 then decide (7 ≤ count1381 b) else decide (8 ≤ count1381 b)))))))))) else (if i < 1621 then (if i < 1505 then (if i < 1447 then (if i < 1418 then (if i < 1403 then (if i < 1396 then (if i < 1392 then (if i < 1390 then decide (1 ≤ count1389 b) else (if i < 1391 then decide (2 ≤ count1389 b) else decide (3 ≤ count1389 b))) else (if i < 1394 then (if i < 1393 then decide (4 ≤ count1389 b) else decide (5 ≤ count1389 b)) else (if i < 1395 then decide (6 ≤ count1389 b) else decide (7 ≤ count1389 b)))) else (if i < 1399 then (if i < 1397 then decide (8 ≤ count1389 b) else (if i < 1398 then decide (9 ≤ count1389 b) else decide (10 ≤ count1389 b))) else (if i < 1401 then (if i < 1400 then decide (11 ≤ count1389 b) else decide (12 ≤ count1389 b)) else (if i < 1402 then decide (13 ≤ count1389 b) else decide (14 ≤ count1389 b))))) else (if i < 1410 then (if i < 1406 then (if i < 1404 then decide (15 ≤ count1389 b) else (if i < 1405 then decide (1 ≤ count1404 b) else decide (2 ≤ count1404 b))) else (if i < 1408 then (if i < 1407 then decide (1 ≤ count1406 b) else decide (2 ≤ count1406 b)) else (if i < 1409 then decide (1 ≤ count1408 b) else decide (2 ≤ count1408 b)))) else (if i < 1414 then (if i < 1412 then (if i < 1411 then decide (3 ≤ count1408 b) else decide (4 ≤ count1408 b)) else (if i < 1413 then decide (1 ≤ count1412 b) else decide (2 ≤ count1412 b))) else (if i < 1416 then (if i < 1415 then decide (1 ≤ count1414 b) else decide (2 ≤ count1414 b)) else (if i < 1417 then decide (1 ≤ count1416 b) else decide (2 ≤ count1416 b)))))) else (if i < 1432 then (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (3 ≤ count1416 b) else (if i < 1420 then decide (4 ≤ count1416 b) else decide (1 ≤ count1420 b))) else (if i < 1423 then (if i < 1422 then decide (2 ≤ count1420 b) else decide (3 ≤ count1420 b)) else (if i < 1424 then decide (4 ≤ count1420 b) else decide (5 ≤ count1420 b)))) else (if i < 1428 then (if i < 1426 then decide (6 ≤ count1420 b) else (if i < 1427 then decide (7 ≤ count1420 b) else decide (8 ≤ count1420 b))) else (if i < 1430 then (if i < 1429 then decide (1 ≤ count1428 b) else decide (2 ≤ count1428 b)) else (if i < 1431 then decide (1 ≤ count1430 b) else decide (2 ≤ count1430 b))))) else (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (1 ≤ count1432 b) else (if i < 1434 then decide (2 ≤ count1432 b) else decide (3 ≤ count1432 b))) else (if i < 1437 then (if i < 1436 then decide (4 ≤ count1432 b) else decide (1 ≤ count1436 b)) else (if i < 1438 then decide (2 ≤ count1436 b) else decide (1 ≤ count1438 b)))) else (if i < 1443 then (if i < 1441 then (if i < 1440 then decide (2 ≤ count1438 b) else decide (1 ≤ count1440 b)) else (if i < 1442 then decide (2 ≤ count1440 b) else decide (3 ≤ count1440 b))) else (if i < 1445 then (if i < 1444 then decide (4 ≤ count1440 b) else decide (1 ≤ count1444 b)) else (if i < 1446 then decide (2 ≤ count1444 b) else decide (3 ≤ count1444 b))))))) else (if i < 1476 then (if i < 1461 then (if i < 1454 then (if i < 1450 then (if i < 1448 then decide (4 ≤ count1444 b) else (if i < 1449 then decide (5 ≤ count1444 b) else decide (6 ≤ count1444 b))) else (if i < 1452 then (if i < 1451 then decide (7 ≤ count1444 b) else decide (8 ≤ count1444 b)) else (if i < 1453 then decide (1 ≤ count1452 b) else decide (2 ≤ count1452 b)))) else (if i < 1457 then (if i < 1455 then decide (3 ≤ count1452 b) else (if i < 1456 then decide (4 ≤ count1452 b) else decide (5 ≤ count1452 b))) else (if i < 1459 then (if i < 1458 then decide (6 ≤ count1452 b) else decide (7 ≤ count1452 b)) else (if i < 1460 then decide (8 ≤ count1452 b) else decide (9 ≤ count1452 b))))) else (if i < 1468 then (if i < 1464 then (if i < 1462 then decide (10 ≤ count1452 b) else (if i < 1463 then decide (11 ≤ count1452 b) else decide (12 ≤ count1452 b))) else (if i < 1466 then (if i < 1465 then decide (13 ≤ count1452 b) else decide (14 ≤ count1452 b)) else (if i < 1467 then decide (15 ≤ count1452 b) else decide (16 ≤ count1452 b)))) else (if i < 1472 then (if i < 1470 then (if i < 1469 then decide (1 ≤ count1468 b) else decide (2 ≤ count1468 b)) else (if i < 1471 then decide (3 ≤ count1468 b) else decide (4 ≤ count1468 b))) else (if i < 1474 then (if i < 1473 then decide (5 ≤ count1468 b) else decide (6 ≤ count1468 b)) else (if i < 1475 then decide (7 ≤ count1468 b) else decide (8 ≤ count1468 b)))))) else (if i < 1490 then (if i < 1483 then (if i < 1479 then (if i < 1477 then decide (9 ≤ count1468 b) else (if i < 1478 then decide (10 ≤ count1468 b) else decide (11 ≤ count1468 b))) else (if i < 1481 then (if i < 1480 then decide (12 ≤ count1468 b) else decide (13 ≤ count1468 b)) else (if i < 1482 then decide (14 ≤ count1468 b) else decide (15 ≤ count1468 b)))) else (if i < 1486 then (if i < 1484 then decide (16 ≤ count1468 b) else (if i < 1485 then decide (17 ≤ count1468 b) else decide (18 ≤ count1468 b))) else (if i < 1488 then (if i < 1487 then decide (19 ≤ count1468 b) else decide (20 ≤ count1468 b)) else (if i < 1489 then decide (21 ≤ count1468 b) else decide (22 ≤ count1468 b))))) else (if i < 1497 then (if i < 1493 then (if i < 1491 then decide (23 ≤ count1468 b) else (if i < 1492 then decide (24 ≤ count1468 b) else decide (25 ≤ count1468 b))) else (if i < 1495 then (if i < 1494 then decide (26 ≤ count1468 b) else decide (27 ≤ count1468 b)) else (if i < 1496 then decide (28 ≤ count1468 b) else decide (29 ≤ count1468 b)))) else (if i < 1501 then (if i < 1499 then (if i < 1498 then decide (30 ≤ count1468 b) else decide (31 ≤ count1468 b)) else (if i < 1500 then decide (1 ≤ count1499 b) else decide (2 ≤ count1499 b))) else (if i < 1503 then (if i < 1502 then decide (3 ≤ count1499 b) else decide (4 ≤ count1499 b)) else (if i < 1504 then decide (5 ≤ count1499 b) else decide (6 ≤ count1499 b)))))))) else (if i < 1563 then (if i < 1534 then (if i < 1519 then (if i < 1512 then (if i < 1508 then (if i < 1506 then decide (7 ≤ count1499 b) else (if i < 1507 then decide (8 ≤ count1499 b) else decide (9 ≤ count1499 b))) else (if i < 1510 then (if i < 1509 then decide (10 ≤ count1499 b) else decide (11 ≤ count1499 b)) else (if i < 1511 then decide (12 ≤ count1499 b) else decide (13 ≤ count1499 b)))) else (if i < 1515 then (if i < 1513 then decide (14 ≤ count1499 b) else (if i < 1514 then decide (15 ≤ count1499 b) else decide (16 ≤ count1499 b))) else (if i < 1517 then (if i < 1516 then decide (17 ≤ count1499 b) else decide (18 ≤ count1499 b)) else (if i < 1518 then decide (19 ≤ count1499 b) else decide (20 ≤ count1499 b))))) else (if i < 1526 then (if i < 1522 then (if i < 1520 then decide (21 ≤ count1499 b) else (if i < 1521 then decide (22 ≤ count1499 b) else decide (23 ≤ count1499 b))) else (if i < 1524 then (if i < 1523 then decide (24 ≤ count1499 b) else decide (25 ≤ count1499 b)) else (if i < 1525 then decide (26 ≤ count1499 b) else decide (27 ≤ count1499 b)))) else (if i < 1530 then (if i < 1528 then (if i < 1527 then decide (28 ≤ count1499 b) else decide (29 ≤ count1499 b)) else (if i < 1529 then decide (30 ≤ count1499 b) else decide (31 ≤ count1499 b))) else (if i < 1532 then (if i < 1531 then decide (32 ≤ count1499 b) else decide (33 ≤ count1499 b)) else (if i < 1533 then decide (34 ≤ count1499 b) else decide (35 ≤ count1499 b)))))) else (if i < 1548 then (if i < 1541 then (if i < 1537 then (if i < 1535 then decide (36 ≤ count1499 b) else (if i < 1536 then decide (37 ≤ count1499 b) else decide (38 ≤ count1499 b))) else (if i < 1539 then (if i < 1538 then decide (39 ≤ count1499 b) else decide (40 ≤ count1499 b)) else (if i < 1540 then decide (41 ≤ count1499 b) else decide (42 ≤ count1499 b)))) else (if i < 1544 then (if i < 1542 then decide (1 ≤ count1541 b) else (if i < 1543 then decide (2 ≤ count1541 b) else decide (1 ≤ count1543 b))) else (if i < 1546 then (if i < 1545 then decide (2 ≤ count1543 b) else decide (3 ≤ count1543 b)) else (if i < 1547 then decide (1 ≤ count1546 b) else decide (2 ≤ count1546 b))))) else (if i < 1555 then (if i < 1551 then (if i < 1549 then decide (1 ≤ count1548 b) else (if i < 1550 then decide (2 ≤ count1548 b) else decide (1 ≤ count1550 b))) else (if i < 1553 then (if i < 1552 then decide (2 ≤ count1550 b) else decide (3 ≤ count1550 b)) else (if i < 1554 then decide (4 ≤ count1550 b) else decide (1 ≤ count1554 b)))) else (if i < 1559 then (if i < 1557 then (if i < 1556 then decide (2 ≤ count1554 b) else decide (3 ≤ count1554 b)) else (if i < 1558 then decide (4 ≤ count1554 b) else decide (5 ≤ count1554 b))) else (if i < 1561 then (if i < 1560 then decide (6 ≤ count1554 b) else decide (7 ≤ count1554 b)) else (if i < 1562 then decide (1 ≤ count1561 b) else decide (2 ≤ count1561 b))))))) else (if i < 1592 then (if i < 1577 then (if i < 1570 then (if i < 1566 then (if i < 1564 then decide (1 ≤ count1563 b) else (if i < 1565 then decide (2 ≤ count1563 b) else decide (1 ≤ count1565 b))) else (if i < 1568 then (if i < 1567 then decide (2 ≤ count1565 b) else decide (3 ≤ count1565 b)) else (if i < 1569 then decide (4 ≤ count1565 b) else decide (1 ≤ count1569 b)))) else (if i < 1573 then (if i < 1571 then decide (2 ≤ count1569 b) else (if i < 1572 then decide (1 ≤ count1571 b) else decide (2 ≤ count1571 b))) else (if i < 1575 then (if i < 1574 then decide (1 ≤ count1573 b) else decide (2 ≤ count1573 b)) else (if i < 1576 then decide (3 ≤ count1573 b) else decide (4 ≤ count1573 b))))) else (if i < 1584 then (if i < 1580 then (if i < 1578 then decide (1 ≤ count1577 b) else (if i < 1579 then decide (2 ≤ count1577 b) else decide (3 ≤ count1577 b))) else (if i < 1582 then (if i < 1581 then decide (4 ≤ count1577 b) else decide (5 ≤ count1577 b)) else (if i < 1583 then decide (6 ≤ count1577 b) else decide (7 ≤ count1577 b)))) else (if i < 1588 then (if i < 1586 then (if i < 1585 then decide (8 ≤ count1577 b) else decide (1 ≤ count1585 b)) else (if i < 1587 then decide (2 ≤ count1585 b) else decide (3 ≤ count1585 b))) else (if i < 1590 then (if i < 1589 then decide (4 ≤ count1585 b) else decide (5 ≤ count1585 b)) else (if i < 1591 then decide (6 ≤ count1585 b) else decide (7 ≤ count1585 b)))))) else (if i < 1606 then (if i < 1599 then (if i < 1595 then (if i < 1593 then decide (8 ≤ count1585 b) else (if i < 1594 then decide (9 ≤ count1585 b) else decide (10 ≤ count1585 b))) else (if i < 1597 then (if i < 1596 then decide (11 ≤ count1585 b) else decide (12 ≤ count1585 b)) else (if i < 1598 then decide (13 ≤ count1585 b) else decide (14 ≤ count1585 b)))) else (if i < 1602 then (if i < 1600 then decide (15 ≤ count1585 b) else (if i < 1601 then decide (1 ≤ count1600 b) else decide (2 ≤ count1600 b))) else (if i < 1604 then (if i < 1603 then decide (1 ≤ count1602 b) else decide (2 ≤ count1602 b)) else (if i < 1605 then decide (1 ≤ count1604 b) else decide (2 ≤ count1604 b))))) else (if i < 1613 then (if i < 1609 then (if i < 1607 then decide (3 ≤ count1604 b) else (if i < 1608 then decide (4 ≤ count1604 b) else decide (1 ≤ count1608 b))) else (if i < 1611 then (if i < 1610 then decide (2 ≤ count1608 b) else decide (1 ≤ count1610 b)) else (if i < 1612 then decide (2 ≤ count1610 b) else decide (1 ≤ count1612 b)))) else (if i < 1617 then (if i < 1615 then (if i < 1614 then decide (2 ≤ count1612 b) else decide (3 ≤ count1612 b)) else (if i < 1616 then decide (4 ≤ count1612 b) else decide (1 ≤ count1616 b))) else (if i < 1619 then (if i < 1618 then decide (2 ≤ count1616 b) else decide (3 ≤ count1616 b)) else (if i < 1620 then decide (4 ≤ count1616 b) else decide (5 ≤ count1616 b))))))))) else (if i < 1737 then (if i < 1679 then (if i < 1650 then (if i < 1635 then (if i < 1628 then (if i < 1624 then (if i < 1622 then decide (6 ≤ count1616 b) else (if i < 1623 then decide (7 ≤ count1616 b) else decide (8 ≤ count1616 b))) else (if i < 1626 then (if i < 1625 then decide (1 ≤ count1624 b) else decide (2 ≤ count1624 b)) else (if i < 1627 then decide (1 ≤ count1626 b) else decide (2 ≤ count1626 b)))) else (if i < 1631 then (if i < 1629 then decide (1 ≤ count1628 b) else (if i < 1630 then decide (2 ≤ count1628 b) else decide (3 ≤ count1628 b))) else (if i < 1633 then (if i < 1632 then decide (4 ≤ count1628 b) else decide (1 ≤ count1632 b)) else (if i < 1634 then decide (2 ≤ count1632 b) else decide (1 ≤ count1634 b))))) else (if i < 1642 then (if i < 1638 then (if i < 1636 then decide (2 ≤ count1634 b) else (if i < 1637 then decide (1 ≤ count1636 b) else decide (2 ≤ count1636 b))) else (if i < 1640 then (if i < 1639 then decide (3 ≤ count1636 b) else decide (4 ≤ count1636 b)) else (if i < 1641 then decide (1 ≤ count1640 b) else decide (2 ≤ count1640 b)))) else (if i < 1646 then (if i < 1644 then (if i < 1643 then decide (3 ≤ count1640 b) else decide (4 ≤ count1640 b)) else (if i < 1645 then decide (5 ≤ count1640 b) else decide (6 ≤ count1640 b))) else (if i < 1648 then (if i < 1647 then decide (7 ≤ count1640 b) else decide (8 ≤ count1640 b)) else (if i < 1649 then decide (1 ≤ count1648 b) else decide (2 ≤ count1648 b)))))) else (if i < 1664 then (if i < 1657 then (if i < 1653 then (if i < 1651 then decide (3 ≤ count1648 b) else (if i < 1652 then decide (4 ≤ count1648 b) else decide (5 ≤ count1648 b))) else (if i < 1655 then (if i < 1654 then decide (6 ≤ count1648 b) else decide (7 ≤ count1648 b)) else (if i < 1656 then decide (8 ≤ count1648 b) else decide (9 ≤ count1648 b)))) else (if i < 1660 then (if i < 1658 then decide (10 ≤ count1648 b) else (if i < 1659 then decide (11 ≤ count1648 b) else decide (12 ≤ count1648 b))) else (if i < 1662 then (if i < 1661 then decide (13 ≤ count1648 b) else decide (14 ≤ count1648 b)) else (if i < 1663 then decide (15 ≤ count1648 b) else decide (16 ≤ count1648 b))))) else (if i < 1671 then (if i < 1667 then (if i < 1665 then decide (1 ≤ count1664 b) else (if i < 1666 then decide (2 ≤ count1664 b) else decide (3 ≤ count1664 b))) else (if i < 1669 then (if i < 1668 then decide (4 ≤ count1664 b) else decide (5 ≤ count1664 b)) else (if i < 1670 then decide (6 ≤ count1664 b) else decide (7 ≤ count1664 b)))) else (if i < 1675 then (if i < 1673 then (if i < 1672 then decide (8 ≤ count1664 b) else decide (9 ≤ count1664 b)) else (if i < 1674 then decide (10 ≤ count1664 b) else decide (11 ≤ count1664 b))) else (if i < 1677 then (if i < 1676 then decide (12 ≤ count1664 b) else decide (13 ≤ count1664 b)) else (if i < 1678 then decide (14 ≤ count1664 b) else decide (15 ≤ count1664 b))))))) else (if i < 1708 then (if i < 1693 then (if i < 1686 then (if i < 1682 then (if i < 1680 then decide (16 ≤ count1664 b) else (if i < 1681 then decide (17 ≤ count1664 b) else decide (18 ≤ count1664 b))) else (if i < 1684 then (if i < 1683 then decide (19 ≤ count1664 b) else decide (20 ≤ count1664 b)) else (if i < 1685 then decide (21 ≤ count1664 b) else decide (22 ≤ count1664 b)))) else (if i < 1689 then (if i < 1687 then decide (1 ≤ count1686 b) else (if i < 1688 then decide (2 ≤ count1686 b) else decide (1 ≤ count1688 b))) else (if i < 1691 then (if i < 1690 then decide (2 ≤ count1688 b) else decide (3 ≤ count1688 b)) else (if i < 1692 then decide (1 ≤ count1691 b) else decide (2 ≤ count1691 b))))) else (if i < 1700 then (if i < 1696 then (if i < 1694 then decide (1 ≤ count1693 b) else (if i < 1695 then decide (2 ≤ count1693 b) else decide (1 ≤ count1695 b))) else (if i < 1698 then (if i < 1697 then decide (2 ≤ count1695 b) else decide (3 ≤ count1695 b)) else (if i < 1699 then decide (4 ≤ count1695 b) else decide (1 ≤ count1699 b)))) else (if i < 1704 then (if i < 1702 then (if i < 1701 then decide (2 ≤ count1699 b) else decide (3 ≤ count1699 b)) else (if i < 1703 then decide (4 ≤ count1699 b) else decide (5 ≤ count1699 b))) else (if i < 1706 then (if i < 1705 then decide (6 ≤ count1699 b) else decide (7 ≤ count1699 b)) else (if i < 1707 then decide (1 ≤ count1706 b) else decide (2 ≤ count1706 b)))))) else (if i < 1722 then (if i < 1715 then (if i < 1711 then (if i < 1709 then decide (1 ≤ count1708 b) else (if i < 1710 then decide (2 ≤ count1708 b) else decide (1 ≤ count1710 b))) else (if i < 1713 then (if i < 1712 then decide (2 ≤ count1710 b) else decide (3 ≤ count1710 b)) else (if i < 1714 then decide (4 ≤ count1710 b) else decide (1 ≤ count1714 b)))) else (if i < 1718 then (if i < 1716 then decide (2 ≤ count1714 b) else (if i < 1717 then decide (1 ≤ count1716 b) else decide (2 ≤ count1716 b))) else (if i < 1720 then (if i < 1719 then decide (1 ≤ count1718 b) else decide (2 ≤ count1718 b)) else (if i < 1721 then decide (3 ≤ count1718 b) else decide (4 ≤ count1718 b))))) else (if i < 1729 then (if i < 1725 then (if i < 1723 then decide (1 ≤ count1722 b) else (if i < 1724 then decide (2 ≤ count1722 b) else decide (3 ≤ count1722 b))) else (if i < 1727 then (if i < 1726 then decide (4 ≤ count1722 b) else decide (5 ≤ count1722 b)) else (if i < 1728 then decide (6 ≤ count1722 b) else decide (7 ≤ count1722 b)))) else (if i < 1733 then (if i < 1731 then (if i < 1730 then decide (8 ≤ count1722 b) else decide (1 ≤ count1730 b)) else (if i < 1732 then decide (2 ≤ count1730 b) else decide (3 ≤ count1730 b))) else (if i < 1735 then (if i < 1734 then decide (4 ≤ count1730 b) else decide (5 ≤ count1730 b)) else (if i < 1736 then decide (6 ≤ count1730 b) else decide (7 ≤ count1730 b)))))))) else (if i < 1795 then (if i < 1766 then (if i < 1751 then (if i < 1744 then (if i < 1740 then (if i < 1738 then decide (8 ≤ count1730 b) else (if i < 1739 then decide (9 ≤ count1730 b) else decide (10 ≤ count1730 b))) else (if i < 1742 then (if i < 1741 then decide (11 ≤ count1730 b) else decide (12 ≤ count1730 b)) else (if i < 1743 then decide (13 ≤ count1730 b) else decide (14 ≤ count1730 b)))) else (if i < 1747 then (if i < 1745 then decide (15 ≤ count1730 b) else (if i < 1746 then decide (1 ≤ count1745 b) else decide (2 ≤ count1745 b))) else (if i < 1749 then (if i < 1748 then decide (1 ≤ count1747 b) else decide (2 ≤ count1747 b)) else (if i < 1750 then decide (1 ≤ count1749 b) else decide (2 ≤ count1749 b))))) else (if i < 1758 then (if i < 1754 then (if i < 1752 then decide (3 ≤ count1749 b) else (if i < 1753 then decide (4 ≤ count1749 b) else decide (1 ≤ count1753 b))) else (if i < 1756 then (if i < 1755 then decide (2 ≤ count1753 b) else decide (1 ≤ count1755 b)) else (if i < 1757 then decide (2 ≤ count1755 b) else decide (1 ≤ count1757 b)))) else (if i < 1762 then (if i < 1760 then (if i < 1759 then decide (2 ≤ count1757 b) else decide (3 ≤ count1757 b)) else (if i < 1761 then decide (4 ≤ count1757 b) else decide (1 ≤ count1761 b))) else (if i < 1764 then (if i < 1763 then decide (2 ≤ count1761 b) else decide (3 ≤ count1761 b)) else (if i < 1765 then decide (4 ≤ count1761 b) else decide (5 ≤ count1761 b)))))) else (if i < 1780 then (if i < 1773 then (if i < 1769 then (if i < 1767 then decide (6 ≤ count1761 b) else (if i < 1768 then decide (7 ≤ count1761 b) else decide (8 ≤ count1761 b))) else (if i < 1771 then (if i < 1770 then decide (1 ≤ count1769 b) else decide (2 ≤ count1769 b)) else (if i < 1772 then decide (1 ≤ count1771 b) else decide (2 ≤ count1771 b)))) else (if i < 1776 then (if i < 1774 then decide (1 ≤ count1773 b) else (if i < 1775 then decide (2 ≤ count1773 b) else decide (3 ≤ count1773 b))) else (if i < 1778 then (if i < 1777 then decide (4 ≤ count1773 b) else decide (1 ≤ count1777 b)) else (if i < 1779 then decide (2 ≤ count1777 b) else decide (1 ≤ count1779 b))))) else (if i < 1787 then (if i < 1783 then (if i < 1781 then decide (2 ≤ count1779 b) else (if i < 1782 then decide (1 ≤ count1781 b) else decide (2 ≤ count1781 b))) else (if i < 1785 then (if i < 1784 then decide (3 ≤ count1781 b) else decide (4 ≤ count1781 b)) else (if i < 1786 then decide (1 ≤ count1785 b) else decide (2 ≤ count1785 b)))) else (if i < 1791 then (if i < 1789 then (if i < 1788 then decide (3 ≤ count1785 b) else decide (4 ≤ count1785 b)) else (if i < 1790 then decide (5 ≤ count1785 b) else decide (6 ≤ count1785 b))) else (if i < 1793 then (if i < 1792 then decide (7 ≤ count1785 b) else decide (8 ≤ count1785 b)) else (if i < 1794 then decide (1 ≤ count1793 b) else decide (2 ≤ count1793 b))))))) else (if i < 1824 then (if i < 1809 then (if i < 1802 then (if i < 1798 then (if i < 1796 then decide (3 ≤ count1793 b) else (if i < 1797 then decide (4 ≤ count1793 b) else decide (5 ≤ count1793 b))) else (if i < 1800 then (if i < 1799 then decide (6 ≤ count1793 b) else decide (7 ≤ count1793 b)) else (if i < 1801 then decide (8 ≤ count1793 b) else decide (9 ≤ count1793 b)))) else (if i < 1805 then (if i < 1803 then decide (10 ≤ count1793 b) else (if i < 1804 then decide (11 ≤ count1793 b) else decide (12 ≤ count1793 b))) else (if i < 1807 then (if i < 1806 then decide (13 ≤ count1793 b) else decide (14 ≤ count1793 b)) else (if i < 1808 then decide (15 ≤ count1793 b) else decide (16 ≤ count1793 b))))) else (if i < 1816 then (if i < 1812 then (if i < 1810 then decide (1 ≤ count1809 b) else (if i < 1811 then decide (2 ≤ count1809 b) else decide (3 ≤ count1809 b))) else (if i < 1814 then (if i < 1813 then decide (4 ≤ count1809 b) else decide (5 ≤ count1809 b)) else (if i < 1815 then decide (6 ≤ count1809 b) else decide (7 ≤ count1809 b)))) else (if i < 1820 then (if i < 1818 then (if i < 1817 then decide (8 ≤ count1809 b) else decide (9 ≤ count1809 b)) else (if i < 1819 then decide (10 ≤ count1809 b) else decide (11 ≤ count1809 b))) else (if i < 1822 then (if i < 1821 then decide (12 ≤ count1809 b) else decide (13 ≤ count1809 b)) else (if i < 1823 then decide (14 ≤ count1809 b) else decide (15 ≤ count1809 b)))))) else (if i < 1838 then (if i < 1831 then (if i < 1827 then (if i < 1825 then decide (16 ≤ count1809 b) else (if i < 1826 then decide (17 ≤ count1809 b) else decide (18 ≤ count1809 b))) else (if i < 1829 then (if i < 1828 then decide (19 ≤ count1809 b) else decide (20 ≤ count1809 b)) else (if i < 1830 then decide (21 ≤ count1809 b) else decide (22 ≤ count1809 b)))) else (if i < 1834 then (if i < 1832 then decide (1 ≤ count1831 b) else (if i < 1833 then decide (2 ≤ count1831 b) else decide (3 ≤ count1831 b))) else (if i < 1836 then (if i < 1835 then decide (4 ≤ count1831 b) else decide (5 ≤ count1831 b)) else (if i < 1837 then decide (6 ≤ count1831 b) else decide (7 ≤ count1831 b))))) else (if i < 1845 then (if i < 1841 then (if i < 1839 then decide (8 ≤ count1831 b) else (if i < 1840 then decide (9 ≤ count1831 b) else decide (10 ≤ count1831 b))) else (if i < 1843 then (if i < 1842 then decide (11 ≤ count1831 b) else decide (12 ≤ count1831 b)) else (if i < 1844 then decide (13 ≤ count1831 b) else decide (14 ≤ count1831 b)))) else (if i < 1849 then (if i < 1847 then (if i < 1846 then decide (15 ≤ count1831 b) else decide (16 ≤ count1831 b)) else (if i < 1848 then decide (17 ≤ count1831 b) else decide (18 ≤ count1831 b))) else (if i < 1851 then (if i < 1850 then decide (19 ≤ count1831 b) else decide (20 ≤ count1831 b)) else (if i < 1852 then decide (21 ≤ count1831 b) else decide (22 ≤ count1831 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (6 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (17 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (18 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (19 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (22 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (32 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (33 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (34 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (36 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (37 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (38 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (39 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (40 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (41 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (42 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (44 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (46 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (49 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (50 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (51 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (52 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (53 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (54 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (55 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (57 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (58 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (59 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (62 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (63 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (66 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (70 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (78 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (102 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (105 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (109 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (111 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (118 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (122 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (124 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (125 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (126 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (160 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (161 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (165 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (166 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (168 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (171 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (173 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (175 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (176 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (177 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (178 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (179 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (182 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (184 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (188 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (189 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (190 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (191 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (233 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (245 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (247 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (248 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (249 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (251 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (255 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (288 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (289 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (294 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (295 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (296 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (297 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (299 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (301 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (303 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (305 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (306 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (307 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (308 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (310 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (314 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (316 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (317 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (318 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (416 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (417 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (418 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (420 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (421 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (422 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (423 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (424 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (426 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (427 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (428 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (430 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (431 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (433 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (435 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (436 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (437 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (439 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (440 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (441 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (442 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (443 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (447 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (480 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (481 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (486 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (487 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (488 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (489 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (491 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (493 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (495 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (497 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (498 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (499 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (502 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (506 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (508 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (InPath q (509 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (InPath q (510 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (32 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (33 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (34 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (36 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (37 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (39 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (42 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (44 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (46 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (53 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (55 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (57 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (58 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (59 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (63 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (70 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (78 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (102 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (105 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (109 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (111 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (124 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (126 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (165 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (166 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (176 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (178 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (184 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (190 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (289 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (294 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (295 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (297 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (301 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (303 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (306 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (307 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (317 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (318 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (418 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (420 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (423 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (437 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (441 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (442 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value260 (q : Snake 81) : valuation q 260 = decide (2 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value262 (q : Snake 81) : valuation q 262 = decide (2 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value264 (q : Snake 81) : valuation q 264 = decide (2 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value286 (q : Snake 81) : valuation q 286 = decide (2 ≤ count285 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value310 (q : Snake 81) : valuation q 310 = decide (2 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value330 (q : Snake 81) : valuation q 330 = decide (2 ≤ count329 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value338 (q : Snake 81) : valuation q 338 = decide (2 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value356 (q : Snake 81) : valuation q 356 = decide (2 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value368 (q : Snake 81) : valuation q 368 = decide (2 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value370 (q : Snake 81) : valuation q 370 = decide (2 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value402 (q : Snake 81) : valuation q 402 = decide (2 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value434 (q : Snake 81) : valuation q 434 = decide (2 ≤ count433 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value491 (q : Snake 81) : valuation q 491 = decide (1 ≤ count491 (baseVal q)) := rfl
theorem value493 (q : Snake 81) : valuation q 493 = decide (1 ≤ count493 (baseVal q)) := rfl
theorem value494 (q : Snake 81) : valuation q 494 = decide (2 ≤ count493 (baseVal q)) := rfl
theorem value495 (q : Snake 81) : valuation q 495 = decide (1 ≤ count495 (baseVal q)) := rfl
theorem value496 (q : Snake 81) : valuation q 496 = decide (2 ≤ count495 (baseVal q)) := rfl
theorem value497 (q : Snake 81) : valuation q 497 = decide (1 ≤ count497 (baseVal q)) := rfl
theorem value498 (q : Snake 81) : valuation q 498 = decide (2 ≤ count497 (baseVal q)) := rfl
theorem value500 (q : Snake 81) : valuation q 500 = decide (2 ≤ count499 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (1 ≤ count863 (baseVal q)) := rfl
theorem value864 (q : Snake 81) : valuation q 864 = decide (2 ≤ count863 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (1 ≤ count865 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (2 ≤ count865 (baseVal q)) := rfl
theorem value867 (q : Snake 81) : valuation q 867 = decide (1 ≤ count867 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (2 ≤ count867 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (3 ≤ count867 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (4 ≤ count867 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (1 ≤ count871 (baseVal q)) := rfl
theorem value872 (q : Snake 81) : valuation q 872 = decide (2 ≤ count871 (baseVal q)) := rfl
theorem value873 (q : Snake 81) : valuation q 873 = decide (1 ≤ count873 (baseVal q)) := rfl
theorem value874 (q : Snake 81) : valuation q 874 = decide (2 ≤ count873 (baseVal q)) := rfl
theorem value875 (q : Snake 81) : valuation q 875 = decide (1 ≤ count875 (baseVal q)) := rfl
theorem value876 (q : Snake 81) : valuation q 876 = decide (2 ≤ count875 (baseVal q)) := rfl
theorem value877 (q : Snake 81) : valuation q 877 = decide (3 ≤ count875 (baseVal q)) := rfl
theorem value878 (q : Snake 81) : valuation q 878 = decide (4 ≤ count875 (baseVal q)) := rfl
theorem value879 (q : Snake 81) : valuation q 879 = decide (1 ≤ count879 (baseVal q)) := rfl
theorem value880 (q : Snake 81) : valuation q 880 = decide (2 ≤ count879 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (3 ≤ count879 (baseVal q)) := rfl
theorem value882 (q : Snake 81) : valuation q 882 = decide (4 ≤ count879 (baseVal q)) := rfl
theorem value883 (q : Snake 81) : valuation q 883 = decide (5 ≤ count879 (baseVal q)) := rfl
theorem value884 (q : Snake 81) : valuation q 884 = decide (6 ≤ count879 (baseVal q)) := rfl
theorem value885 (q : Snake 81) : valuation q 885 = decide (7 ≤ count879 (baseVal q)) := rfl
theorem value886 (q : Snake 81) : valuation q 886 = decide (8 ≤ count879 (baseVal q)) := rfl
theorem value887 (q : Snake 81) : valuation q 887 = decide (1 ≤ count887 (baseVal q)) := rfl
theorem value888 (q : Snake 81) : valuation q 888 = decide (2 ≤ count887 (baseVal q)) := rfl
theorem value889 (q : Snake 81) : valuation q 889 = decide (1 ≤ count889 (baseVal q)) := rfl
theorem value890 (q : Snake 81) : valuation q 890 = decide (2 ≤ count889 (baseVal q)) := rfl
theorem value891 (q : Snake 81) : valuation q 891 = decide (1 ≤ count891 (baseVal q)) := rfl
theorem value892 (q : Snake 81) : valuation q 892 = decide (2 ≤ count891 (baseVal q)) := rfl
theorem value893 (q : Snake 81) : valuation q 893 = decide (3 ≤ count891 (baseVal q)) := rfl
theorem value894 (q : Snake 81) : valuation q 894 = decide (4 ≤ count891 (baseVal q)) := rfl
theorem value895 (q : Snake 81) : valuation q 895 = decide (1 ≤ count895 (baseVal q)) := rfl
theorem value896 (q : Snake 81) : valuation q 896 = decide (2 ≤ count895 (baseVal q)) := rfl
theorem value897 (q : Snake 81) : valuation q 897 = decide (1 ≤ count897 (baseVal q)) := rfl
theorem value898 (q : Snake 81) : valuation q 898 = decide (2 ≤ count897 (baseVal q)) := rfl
theorem value899 (q : Snake 81) : valuation q 899 = decide (1 ≤ count899 (baseVal q)) := rfl
theorem value900 (q : Snake 81) : valuation q 900 = decide (2 ≤ count899 (baseVal q)) := rfl
theorem value901 (q : Snake 81) : valuation q 901 = decide (3 ≤ count899 (baseVal q)) := rfl
theorem value902 (q : Snake 81) : valuation q 902 = decide (4 ≤ count899 (baseVal q)) := rfl
theorem value903 (q : Snake 81) : valuation q 903 = decide (1 ≤ count903 (baseVal q)) := rfl
theorem value904 (q : Snake 81) : valuation q 904 = decide (2 ≤ count903 (baseVal q)) := rfl
theorem value905 (q : Snake 81) : valuation q 905 = decide (3 ≤ count903 (baseVal q)) := rfl
theorem value906 (q : Snake 81) : valuation q 906 = decide (4 ≤ count903 (baseVal q)) := rfl
theorem value907 (q : Snake 81) : valuation q 907 = decide (5 ≤ count903 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (6 ≤ count903 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (7 ≤ count903 (baseVal q)) := rfl
theorem value914 (q : Snake 81) : valuation q 914 = decide (4 ≤ count911 (baseVal q)) := rfl
theorem value915 (q : Snake 81) : valuation q 915 = decide (5 ≤ count911 (baseVal q)) := rfl
theorem value916 (q : Snake 81) : valuation q 916 = decide (6 ≤ count911 (baseVal q)) := rfl
theorem value917 (q : Snake 81) : valuation q 917 = decide (7 ≤ count911 (baseVal q)) := rfl
theorem value918 (q : Snake 81) : valuation q 918 = decide (8 ≤ count911 (baseVal q)) := rfl
theorem value919 (q : Snake 81) : valuation q 919 = decide (9 ≤ count911 (baseVal q)) := rfl
theorem value920 (q : Snake 81) : valuation q 920 = decide (10 ≤ count911 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (11 ≤ count911 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (12 ≤ count911 (baseVal q)) := rfl
theorem value923 (q : Snake 81) : valuation q 923 = decide (13 ≤ count911 (baseVal q)) := rfl
theorem value927 (q : Snake 81) : valuation q 927 = decide (1 ≤ count927 (baseVal q)) := rfl
theorem value928 (q : Snake 81) : valuation q 928 = decide (2 ≤ count927 (baseVal q)) := rfl
theorem value929 (q : Snake 81) : valuation q 929 = decide (1 ≤ count929 (baseVal q)) := rfl
theorem value930 (q : Snake 81) : valuation q 930 = decide (2 ≤ count929 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (1 ≤ count931 (baseVal q)) := rfl
theorem value932 (q : Snake 81) : valuation q 932 = decide (2 ≤ count931 (baseVal q)) := rfl
theorem value933 (q : Snake 81) : valuation q 933 = decide (3 ≤ count931 (baseVal q)) := rfl
theorem value934 (q : Snake 81) : valuation q 934 = decide (4 ≤ count931 (baseVal q)) := rfl
theorem value935 (q : Snake 81) : valuation q 935 = decide (1 ≤ count935 (baseVal q)) := rfl
theorem value936 (q : Snake 81) : valuation q 936 = decide (2 ≤ count935 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (1 ≤ count937 (baseVal q)) := rfl
theorem value938 (q : Snake 81) : valuation q 938 = decide (2 ≤ count937 (baseVal q)) := rfl
theorem value939 (q : Snake 81) : valuation q 939 = decide (1 ≤ count939 (baseVal q)) := rfl
theorem value940 (q : Snake 81) : valuation q 940 = decide (2 ≤ count939 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (3 ≤ count939 (baseVal q)) := rfl
theorem value942 (q : Snake 81) : valuation q 942 = decide (4 ≤ count939 (baseVal q)) := rfl
theorem value943 (q : Snake 81) : valuation q 943 = decide (1 ≤ count943 (baseVal q)) := rfl
theorem value944 (q : Snake 81) : valuation q 944 = decide (2 ≤ count943 (baseVal q)) := rfl
theorem value945 (q : Snake 81) : valuation q 945 = decide (3 ≤ count943 (baseVal q)) := rfl
theorem value946 (q : Snake 81) : valuation q 946 = decide (4 ≤ count943 (baseVal q)) := rfl
theorem value947 (q : Snake 81) : valuation q 947 = decide (5 ≤ count943 (baseVal q)) := rfl
theorem value948 (q : Snake 81) : valuation q 948 = decide (6 ≤ count943 (baseVal q)) := rfl
theorem value949 (q : Snake 81) : valuation q 949 = decide (7 ≤ count943 (baseVal q)) := rfl
theorem value951 (q : Snake 81) : valuation q 951 = decide (1 ≤ count951 (baseVal q)) := rfl
theorem value952 (q : Snake 81) : valuation q 952 = decide (2 ≤ count951 (baseVal q)) := rfl
theorem value953 (q : Snake 81) : valuation q 953 = decide (1 ≤ count953 (baseVal q)) := rfl
theorem value954 (q : Snake 81) : valuation q 954 = decide (2 ≤ count953 (baseVal q)) := rfl
theorem value955 (q : Snake 81) : valuation q 955 = decide (1 ≤ count955 (baseVal q)) := rfl
theorem value956 (q : Snake 81) : valuation q 956 = decide (2 ≤ count955 (baseVal q)) := rfl
theorem value957 (q : Snake 81) : valuation q 957 = decide (3 ≤ count955 (baseVal q)) := rfl
theorem value958 (q : Snake 81) : valuation q 958 = decide (4 ≤ count955 (baseVal q)) := rfl
theorem value959 (q : Snake 81) : valuation q 959 = decide (1 ≤ count959 (baseVal q)) := rfl
theorem value960 (q : Snake 81) : valuation q 960 = decide (2 ≤ count959 (baseVal q)) := rfl
theorem value961 (q : Snake 81) : valuation q 961 = decide (1 ≤ count961 (baseVal q)) := rfl
theorem value962 (q : Snake 81) : valuation q 962 = decide (2 ≤ count961 (baseVal q)) := rfl
theorem value963 (q : Snake 81) : valuation q 963 = decide (1 ≤ count963 (baseVal q)) := rfl
theorem value964 (q : Snake 81) : valuation q 964 = decide (2 ≤ count963 (baseVal q)) := rfl
theorem value965 (q : Snake 81) : valuation q 965 = decide (3 ≤ count963 (baseVal q)) := rfl
theorem value967 (q : Snake 81) : valuation q 967 = decide (1 ≤ count967 (baseVal q)) := rfl
theorem value968 (q : Snake 81) : valuation q 968 = decide (2 ≤ count967 (baseVal q)) := rfl
theorem value969 (q : Snake 81) : valuation q 969 = decide (3 ≤ count967 (baseVal q)) := rfl
theorem value970 (q : Snake 81) : valuation q 970 = decide (4 ≤ count967 (baseVal q)) := rfl
theorem value971 (q : Snake 81) : valuation q 971 = decide (5 ≤ count967 (baseVal q)) := rfl
theorem value972 (q : Snake 81) : valuation q 972 = decide (6 ≤ count967 (baseVal q)) := rfl
theorem value977 (q : Snake 81) : valuation q 977 = decide (3 ≤ count975 (baseVal q)) := rfl
theorem value978 (q : Snake 81) : valuation q 978 = decide (4 ≤ count975 (baseVal q)) := rfl
theorem value979 (q : Snake 81) : valuation q 979 = decide (5 ≤ count975 (baseVal q)) := rfl
theorem value980 (q : Snake 81) : valuation q 980 = decide (6 ≤ count975 (baseVal q)) := rfl
theorem value981 (q : Snake 81) : valuation q 981 = decide (7 ≤ count975 (baseVal q)) := rfl
theorem value982 (q : Snake 81) : valuation q 982 = decide (8 ≤ count975 (baseVal q)) := rfl
theorem value983 (q : Snake 81) : valuation q 983 = decide (9 ≤ count975 (baseVal q)) := rfl
theorem value984 (q : Snake 81) : valuation q 984 = decide (10 ≤ count975 (baseVal q)) := rfl
theorem value999 (q : Snake 81) : valuation q 999 = decide (9 ≤ count991 (baseVal q)) := rfl
theorem value1000 (q : Snake 81) : valuation q 1000 = decide (10 ≤ count991 (baseVal q)) := rfl
theorem value1001 (q : Snake 81) : valuation q 1001 = decide (11 ≤ count991 (baseVal q)) := rfl
theorem value1002 (q : Snake 81) : valuation q 1002 = decide (12 ≤ count991 (baseVal q)) := rfl
theorem value1003 (q : Snake 81) : valuation q 1003 = decide (13 ≤ count991 (baseVal q)) := rfl
theorem value1004 (q : Snake 81) : valuation q 1004 = decide (14 ≤ count991 (baseVal q)) := rfl
theorem value1005 (q : Snake 81) : valuation q 1005 = decide (15 ≤ count991 (baseVal q)) := rfl
theorem value1006 (q : Snake 81) : valuation q 1006 = decide (16 ≤ count991 (baseVal q)) := rfl
theorem value1007 (q : Snake 81) : valuation q 1007 = decide (17 ≤ count991 (baseVal q)) := rfl
theorem value1008 (q : Snake 81) : valuation q 1008 = decide (18 ≤ count991 (baseVal q)) := rfl
theorem value1015 (q : Snake 81) : valuation q 1015 = decide (1 ≤ count1015 (baseVal q)) := rfl
theorem value1017 (q : Snake 81) : valuation q 1017 = decide (1 ≤ count1017 (baseVal q)) := rfl
theorem value1018 (q : Snake 81) : valuation q 1018 = decide (2 ≤ count1017 (baseVal q)) := rfl
theorem value1019 (q : Snake 81) : valuation q 1019 = decide (1 ≤ count1019 (baseVal q)) := rfl
theorem value1020 (q : Snake 81) : valuation q 1020 = decide (2 ≤ count1019 (baseVal q)) := rfl
theorem value1021 (q : Snake 81) : valuation q 1021 = decide (3 ≤ count1019 (baseVal q)) := rfl
theorem value1023 (q : Snake 81) : valuation q 1023 = decide (1 ≤ count1023 (baseVal q)) := rfl
theorem value1024 (q : Snake 81) : valuation q 1024 = decide (2 ≤ count1023 (baseVal q)) := rfl
theorem value1025 (q : Snake 81) : valuation q 1025 = decide (1 ≤ count1025 (baseVal q)) := rfl
theorem value1026 (q : Snake 81) : valuation q 1026 = decide (2 ≤ count1025 (baseVal q)) := rfl
theorem value1027 (q : Snake 81) : valuation q 1027 = decide (1 ≤ count1027 (baseVal q)) := rfl
theorem value1028 (q : Snake 81) : valuation q 1028 = decide (2 ≤ count1027 (baseVal q)) := rfl
theorem value1029 (q : Snake 81) : valuation q 1029 = decide (3 ≤ count1027 (baseVal q)) := rfl
theorem value1030 (q : Snake 81) : valuation q 1030 = decide (4 ≤ count1027 (baseVal q)) := rfl
theorem value1031 (q : Snake 81) : valuation q 1031 = decide (1 ≤ count1031 (baseVal q)) := rfl
theorem value1032 (q : Snake 81) : valuation q 1032 = decide (2 ≤ count1031 (baseVal q)) := rfl
theorem value1033 (q : Snake 81) : valuation q 1033 = decide (3 ≤ count1031 (baseVal q)) := rfl
theorem value1034 (q : Snake 81) : valuation q 1034 = decide (4 ≤ count1031 (baseVal q)) := rfl
theorem value1035 (q : Snake 81) : valuation q 1035 = decide (5 ≤ count1031 (baseVal q)) := rfl
theorem value1039 (q : Snake 81) : valuation q 1039 = decide (1 ≤ count1039 (baseVal q)) := rfl
theorem value1040 (q : Snake 81) : valuation q 1040 = decide (2 ≤ count1039 (baseVal q)) := rfl
theorem value1041 (q : Snake 81) : valuation q 1041 = decide (1 ≤ count1041 (baseVal q)) := rfl
theorem value1042 (q : Snake 81) : valuation q 1042 = decide (2 ≤ count1041 (baseVal q)) := rfl
theorem value1043 (q : Snake 81) : valuation q 1043 = decide (1 ≤ count1043 (baseVal q)) := rfl
theorem value1044 (q : Snake 81) : valuation q 1044 = decide (2 ≤ count1043 (baseVal q)) := rfl
theorem value1045 (q : Snake 81) : valuation q 1045 = decide (3 ≤ count1043 (baseVal q)) := rfl
theorem value1047 (q : Snake 81) : valuation q 1047 = decide (1 ≤ count1047 (baseVal q)) := rfl
theorem value1048 (q : Snake 81) : valuation q 1048 = decide (2 ≤ count1047 (baseVal q)) := rfl
theorem value1049 (q : Snake 81) : valuation q 1049 = decide (1 ≤ count1049 (baseVal q)) := rfl
theorem value1050 (q : Snake 81) : valuation q 1050 = decide (2 ≤ count1049 (baseVal q)) := rfl
theorem value1051 (q : Snake 81) : valuation q 1051 = decide (1 ≤ count1051 (baseVal q)) := rfl
theorem value1052 (q : Snake 81) : valuation q 1052 = decide (2 ≤ count1051 (baseVal q)) := rfl
theorem value1053 (q : Snake 81) : valuation q 1053 = decide (3 ≤ count1051 (baseVal q)) := rfl
theorem value1054 (q : Snake 81) : valuation q 1054 = decide (4 ≤ count1051 (baseVal q)) := rfl
theorem value1055 (q : Snake 81) : valuation q 1055 = decide (1 ≤ count1055 (baseVal q)) := rfl
theorem value1056 (q : Snake 81) : valuation q 1056 = decide (2 ≤ count1055 (baseVal q)) := rfl
theorem value1057 (q : Snake 81) : valuation q 1057 = decide (3 ≤ count1055 (baseVal q)) := rfl
theorem value1058 (q : Snake 81) : valuation q 1058 = decide (4 ≤ count1055 (baseVal q)) := rfl
theorem value1059 (q : Snake 81) : valuation q 1059 = decide (5 ≤ count1055 (baseVal q)) := rfl
theorem value1060 (q : Snake 81) : valuation q 1060 = decide (6 ≤ count1055 (baseVal q)) := rfl
theorem value1063 (q : Snake 81) : valuation q 1063 = decide (1 ≤ count1063 (baseVal q)) := rfl
theorem value1064 (q : Snake 81) : valuation q 1064 = decide (2 ≤ count1063 (baseVal q)) := rfl
theorem value1065 (q : Snake 81) : valuation q 1065 = decide (3 ≤ count1063 (baseVal q)) := rfl
theorem value1066 (q : Snake 81) : valuation q 1066 = decide (4 ≤ count1063 (baseVal q)) := rfl
theorem value1067 (q : Snake 81) : valuation q 1067 = decide (5 ≤ count1063 (baseVal q)) := rfl
theorem value1068 (q : Snake 81) : valuation q 1068 = decide (6 ≤ count1063 (baseVal q)) := rfl
theorem value1069 (q : Snake 81) : valuation q 1069 = decide (7 ≤ count1063 (baseVal q)) := rfl
theorem value1070 (q : Snake 81) : valuation q 1070 = decide (8 ≤ count1063 (baseVal q)) := rfl
theorem value1079 (q : Snake 81) : valuation q 1079 = decide (1 ≤ count1079 (baseVal q)) := rfl
theorem value1080 (q : Snake 81) : valuation q 1080 = decide (2 ≤ count1079 (baseVal q)) := rfl
theorem value1081 (q : Snake 81) : valuation q 1081 = decide (1 ≤ count1081 (baseVal q)) := rfl
theorem value1082 (q : Snake 81) : valuation q 1082 = decide (2 ≤ count1081 (baseVal q)) := rfl
theorem value1083 (q : Snake 81) : valuation q 1083 = decide (1 ≤ count1083 (baseVal q)) := rfl
theorem value1084 (q : Snake 81) : valuation q 1084 = decide (2 ≤ count1083 (baseVal q)) := rfl
theorem value1085 (q : Snake 81) : valuation q 1085 = decide (3 ≤ count1083 (baseVal q)) := rfl
theorem value1086 (q : Snake 81) : valuation q 1086 = decide (4 ≤ count1083 (baseVal q)) := rfl
theorem value1087 (q : Snake 81) : valuation q 1087 = decide (1 ≤ count1087 (baseVal q)) := rfl
theorem value1088 (q : Snake 81) : valuation q 1088 = decide (2 ≤ count1087 (baseVal q)) := rfl
theorem value1089 (q : Snake 81) : valuation q 1089 = decide (1 ≤ count1089 (baseVal q)) := rfl
theorem value1090 (q : Snake 81) : valuation q 1090 = decide (2 ≤ count1089 (baseVal q)) := rfl
theorem value1091 (q : Snake 81) : valuation q 1091 = decide (1 ≤ count1091 (baseVal q)) := rfl
theorem value1092 (q : Snake 81) : valuation q 1092 = decide (2 ≤ count1091 (baseVal q)) := rfl
theorem value1093 (q : Snake 81) : valuation q 1093 = decide (3 ≤ count1091 (baseVal q)) := rfl
theorem value1094 (q : Snake 81) : valuation q 1094 = decide (4 ≤ count1091 (baseVal q)) := rfl
theorem value1095 (q : Snake 81) : valuation q 1095 = decide (1 ≤ count1095 (baseVal q)) := rfl
theorem value1096 (q : Snake 81) : valuation q 1096 = decide (2 ≤ count1095 (baseVal q)) := rfl
theorem value1097 (q : Snake 81) : valuation q 1097 = decide (3 ≤ count1095 (baseVal q)) := rfl
theorem value1098 (q : Snake 81) : valuation q 1098 = decide (4 ≤ count1095 (baseVal q)) := rfl
theorem value1099 (q : Snake 81) : valuation q 1099 = decide (5 ≤ count1095 (baseVal q)) := rfl
theorem value1100 (q : Snake 81) : valuation q 1100 = decide (6 ≤ count1095 (baseVal q)) := rfl
theorem value1103 (q : Snake 81) : valuation q 1103 = decide (1 ≤ count1103 (baseVal q)) := rfl
theorem value1104 (q : Snake 81) : valuation q 1104 = decide (2 ≤ count1103 (baseVal q)) := rfl
theorem value1105 (q : Snake 81) : valuation q 1105 = decide (1 ≤ count1105 (baseVal q)) := rfl
theorem value1106 (q : Snake 81) : valuation q 1106 = decide (2 ≤ count1105 (baseVal q)) := rfl
theorem value1107 (q : Snake 81) : valuation q 1107 = decide (1 ≤ count1107 (baseVal q)) := rfl
theorem value1108 (q : Snake 81) : valuation q 1108 = decide (2 ≤ count1107 (baseVal q)) := rfl
theorem value1109 (q : Snake 81) : valuation q 1109 = decide (3 ≤ count1107 (baseVal q)) := rfl
theorem value1111 (q : Snake 81) : valuation q 1111 = decide (1 ≤ count1111 (baseVal q)) := rfl
theorem value1112 (q : Snake 81) : valuation q 1112 = decide (2 ≤ count1111 (baseVal q)) := rfl
theorem value1113 (q : Snake 81) : valuation q 1113 = decide (1 ≤ count1113 (baseVal q)) := rfl
theorem value1114 (q : Snake 81) : valuation q 1114 = decide (2 ≤ count1113 (baseVal q)) := rfl
theorem value1115 (q : Snake 81) : valuation q 1115 = decide (1 ≤ count1115 (baseVal q)) := rfl
theorem value1116 (q : Snake 81) : valuation q 1116 = decide (2 ≤ count1115 (baseVal q)) := rfl
theorem value1117 (q : Snake 81) : valuation q 1117 = decide (3 ≤ count1115 (baseVal q)) := rfl
theorem value1119 (q : Snake 81) : valuation q 1119 = decide (1 ≤ count1119 (baseVal q)) := rfl
theorem value1120 (q : Snake 81) : valuation q 1120 = decide (2 ≤ count1119 (baseVal q)) := rfl
theorem value1121 (q : Snake 81) : valuation q 1121 = decide (3 ≤ count1119 (baseVal q)) := rfl
theorem value1122 (q : Snake 81) : valuation q 1122 = decide (4 ≤ count1119 (baseVal q)) := rfl
theorem value1129 (q : Snake 81) : valuation q 1129 = decide (3 ≤ count1127 (baseVal q)) := rfl
theorem value1130 (q : Snake 81) : valuation q 1130 = decide (4 ≤ count1127 (baseVal q)) := rfl
theorem value1131 (q : Snake 81) : valuation q 1131 = decide (5 ≤ count1127 (baseVal q)) := rfl
theorem value1132 (q : Snake 81) : valuation q 1132 = decide (6 ≤ count1127 (baseVal q)) := rfl
theorem value1133 (q : Snake 81) : valuation q 1133 = decide (7 ≤ count1127 (baseVal q)) := rfl
theorem value1134 (q : Snake 81) : valuation q 1134 = decide (8 ≤ count1127 (baseVal q)) := rfl
theorem value1135 (q : Snake 81) : valuation q 1135 = decide (9 ≤ count1127 (baseVal q)) := rfl
theorem value1148 (q : Snake 81) : valuation q 1148 = decide (6 ≤ count1143 (baseVal q)) := rfl
theorem value1149 (q : Snake 81) : valuation q 1149 = decide (7 ≤ count1143 (baseVal q)) := rfl
theorem value1150 (q : Snake 81) : valuation q 1150 = decide (8 ≤ count1143 (baseVal q)) := rfl
theorem value1151 (q : Snake 81) : valuation q 1151 = decide (9 ≤ count1143 (baseVal q)) := rfl
theorem value1152 (q : Snake 81) : valuation q 1152 = decide (10 ≤ count1143 (baseVal q)) := rfl
theorem value1153 (q : Snake 81) : valuation q 1153 = decide (11 ≤ count1143 (baseVal q)) := rfl
theorem value1154 (q : Snake 81) : valuation q 1154 = decide (12 ≤ count1143 (baseVal q)) := rfl
theorem value1155 (q : Snake 81) : valuation q 1155 = decide (13 ≤ count1143 (baseVal q)) := rfl
theorem value1156 (q : Snake 81) : valuation q 1156 = decide (14 ≤ count1143 (baseVal q)) := rfl
theorem value1157 (q : Snake 81) : valuation q 1157 = decide (15 ≤ count1143 (baseVal q)) := rfl
theorem value1190 (q : Snake 81) : valuation q 1190 = decide (24 ≤ count1167 (baseVal q)) := rfl
theorem meaningNeg126 (b : Nat → Bool) : literal (valuationOf b) (-126) = decide (1 ≤ countLit b [-126]) := by
  change literal b (-126) = decide (1 ≤ countLit b [-126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-126) <;> decide
theorem meaningNeg125 (b : Nat → Bool) : literal (valuationOf b) (-125) = decide (1 ≤ countLit b [-125]) := by
  change literal b (-125) = decide (1 ≤ countLit b [-125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-125) <;> decide
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
theorem meaningNeg118 (b : Nat → Bool) : literal (valuationOf b) (-118) = decide (1 ≤ countLit b [-118]) := by
  change literal b (-118) = decide (1 ≤ countLit b [-118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-118) <;> decide
theorem meaningNeg115 (b : Nat → Bool) : literal (valuationOf b) (-115) = decide (1 ≤ countLit b [-115]) := by
  change literal b (-115) = decide (1 ≤ countLit b [-115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-115) <;> decide
theorem meaningNeg112 (b : Nat → Bool) : literal (valuationOf b) (-112) = decide (1 ≤ countLit b [-112]) := by
  change literal b (-112) = decide (1 ≤ countLit b [-112])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-112) <;> decide
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
theorem meaningNeg103 (b : Nat → Bool) : literal (valuationOf b) (-103) = decide (1 ≤ countLit b [-103]) := by
  change literal b (-103) = decide (1 ≤ countLit b [-103])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-103) <;> decide
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
theorem meaningNeg93 (b : Nat → Bool) : literal (valuationOf b) (-93) = decide (1 ≤ countLit b [-93]) := by
  change literal b (-93) = decide (1 ≤ countLit b [-93])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-93) <;> decide
theorem meaningNeg90 (b : Nat → Bool) : literal (valuationOf b) (-90) = decide (1 ≤ countLit b [-90]) := by
  change literal b (-90) = decide (1 ≤ countLit b [-90])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-90) <;> decide
theorem meaningNeg89 (b : Nat → Bool) : literal (valuationOf b) (-89) = decide (1 ≤ countLit b [-89]) := by
  change literal b (-89) = decide (1 ≤ countLit b [-89])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-89) <;> decide
theorem meaningNeg88 (b : Nat → Bool) : literal (valuationOf b) (-88) = decide (1 ≤ countLit b [-88]) := by
  change literal b (-88) = decide (1 ≤ countLit b [-88])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-88) <;> decide
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
theorem meaningNeg74 (b : Nat → Bool) : literal (valuationOf b) (-74) = decide (1 ≤ countLit b [-74]) := by
  change literal b (-74) = decide (1 ≤ countLit b [-74])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-74) <;> decide
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
theorem meaningNeg57 (b : Nat → Bool) : literal (valuationOf b) (-57) = decide (1 ≤ countLit b [-57]) := by
  change literal b (-57) = decide (1 ≤ countLit b [-57])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-57) <;> decide
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
theorem meaningNeg43 (b : Nat → Bool) : literal (valuationOf b) (-43) = decide (1 ≤ countLit b [-43]) := by
  change literal b (-43) = decide (1 ≤ countLit b [-43])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-43) <;> decide
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
theorem meaningNeg38 (b : Nat → Bool) : literal (valuationOf b) (-38) = decide (1 ≤ countLit b [-38]) := by
  change literal b (-38) = decide (1 ≤ countLit b [-38])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-38) <;> decide
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
theorem meaningNeg28 (b : Nat → Bool) : literal (valuationOf b) (-28) = decide (1 ≤ countLit b [-28]) := by
  change literal b (-28) = decide (1 ≤ countLit b [-28])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-28) <;> decide
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
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning128 (b : Nat → Bool) : literal (valuationOf b) (128) = decide (1 ≤ countLit b [128]) := by
  change literal b (128) = decide (1 ≤ countLit b [128])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (128) <;> decide
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
theorem meaning138 (b : Nat → Bool) : literal (valuationOf b) (138) = decide (1 ≤ countLit b [138]) := by
  change literal b (138) = decide (1 ≤ countLit b [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (138) <;> decide
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
theorem meaning159 (b : Nat → Bool) : literal (valuationOf b) (159) = decide (1 ≤ countLit b [159]) := by
  change literal b (159) = decide (1 ≤ countLit b [159])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (159) <;> decide
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
theorem meaning167 (b : Nat → Bool) : literal (valuationOf b) (167) = decide (1 ≤ countLit b [167]) := by
  change literal b (167) = decide (1 ≤ countLit b [167])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (167) <;> decide
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
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
theorem meaning199 (b : Nat → Bool) : literal (valuationOf b) (199) = decide (1 ≤ countLit b [199]) := by
  change literal b (199) = decide (1 ≤ countLit b [199])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (199) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) (217) = decide (1 ≤ countLit b [217]) := by
  change literal b (217) = decide (1 ≤ countLit b [217])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (217) <;> decide
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) (223) = decide (1 ≤ countLit b [223]) := by
  change literal b (223) = decide (1 ≤ countLit b [223])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (223) <;> decide
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) (230) = decide (1 ≤ countLit b [230]) := by
  change literal b (230) = decide (1 ≤ countLit b [230])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (230) <;> decide
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) (240) = decide (1 ≤ countLit b [240]) := by
  change literal b (240) = decide (1 ≤ countLit b [240])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (240) <;> decide
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) (247) = decide (1 ≤ countLit b [247]) := by
  change literal b (247) = decide (1 ≤ countLit b [247])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (247) <;> decide
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning260 (b : Nat → Bool) : literal (valuationOf b) 260 = decide (2 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning262 (b : Nat → Bool) : literal (valuationOf b) 262 = decide (2 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning264 (b : Nat → Bool) : literal (valuationOf b) 264 = decide (2 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning286 (b : Nat → Bool) : literal (valuationOf b) 286 = decide (2 ≤ count285 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning310 (b : Nat → Bool) : literal (valuationOf b) 310 = decide (2 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning330 (b : Nat → Bool) : literal (valuationOf b) 330 = decide (2 ≤ count329 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning338 (b : Nat → Bool) : literal (valuationOf b) 338 = decide (2 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning340 (b : Nat → Bool) : literal (valuationOf b) 340 = decide (2 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning356 (b : Nat → Bool) : literal (valuationOf b) 356 = decide (2 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning368 (b : Nat → Bool) : literal (valuationOf b) 368 = decide (2 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning370 (b : Nat → Bool) : literal (valuationOf b) 370 = decide (2 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning402 (b : Nat → Bool) : literal (valuationOf b) 402 = decide (2 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning434 (b : Nat → Bool) : literal (valuationOf b) 434 = decide (2 ≤ count433 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning491 (b : Nat → Bool) : literal (valuationOf b) 491 = decide (1 ≤ count491 b) := rfl
theorem meaning493 (b : Nat → Bool) : literal (valuationOf b) 493 = decide (1 ≤ count493 b) := rfl
theorem meaning494 (b : Nat → Bool) : literal (valuationOf b) 494 = decide (2 ≤ count493 b) := rfl
theorem meaning495 (b : Nat → Bool) : literal (valuationOf b) 495 = decide (1 ≤ count495 b) := rfl
theorem meaning496 (b : Nat → Bool) : literal (valuationOf b) 496 = decide (2 ≤ count495 b) := rfl
theorem meaning497 (b : Nat → Bool) : literal (valuationOf b) 497 = decide (1 ≤ count497 b) := rfl
theorem meaning498 (b : Nat → Bool) : literal (valuationOf b) 498 = decide (2 ≤ count497 b) := rfl
theorem meaning500 (b : Nat → Bool) : literal (valuationOf b) 500 = decide (2 ≤ count499 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (1 ≤ count863 b) := rfl
theorem meaning864 (b : Nat → Bool) : literal (valuationOf b) 864 = decide (2 ≤ count863 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (1 ≤ count865 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (2 ≤ count865 b) := rfl
theorem meaning867 (b : Nat → Bool) : literal (valuationOf b) 867 = decide (1 ≤ count867 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (2 ≤ count867 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (3 ≤ count867 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (4 ≤ count867 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (1 ≤ count871 b) := rfl
theorem meaning872 (b : Nat → Bool) : literal (valuationOf b) 872 = decide (2 ≤ count871 b) := rfl
theorem meaning873 (b : Nat → Bool) : literal (valuationOf b) 873 = decide (1 ≤ count873 b) := rfl
theorem meaning874 (b : Nat → Bool) : literal (valuationOf b) 874 = decide (2 ≤ count873 b) := rfl
theorem meaning875 (b : Nat → Bool) : literal (valuationOf b) 875 = decide (1 ≤ count875 b) := rfl
theorem meaning876 (b : Nat → Bool) : literal (valuationOf b) 876 = decide (2 ≤ count875 b) := rfl
theorem meaning877 (b : Nat → Bool) : literal (valuationOf b) 877 = decide (3 ≤ count875 b) := rfl
theorem meaning878 (b : Nat → Bool) : literal (valuationOf b) 878 = decide (4 ≤ count875 b) := rfl
theorem meaning879 (b : Nat → Bool) : literal (valuationOf b) 879 = decide (1 ≤ count879 b) := rfl
theorem meaning880 (b : Nat → Bool) : literal (valuationOf b) 880 = decide (2 ≤ count879 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (3 ≤ count879 b) := rfl
theorem meaning882 (b : Nat → Bool) : literal (valuationOf b) 882 = decide (4 ≤ count879 b) := rfl
theorem meaning883 (b : Nat → Bool) : literal (valuationOf b) 883 = decide (5 ≤ count879 b) := rfl
theorem meaning884 (b : Nat → Bool) : literal (valuationOf b) 884 = decide (6 ≤ count879 b) := rfl
theorem meaning885 (b : Nat → Bool) : literal (valuationOf b) 885 = decide (7 ≤ count879 b) := rfl
theorem meaning886 (b : Nat → Bool) : literal (valuationOf b) 886 = decide (8 ≤ count879 b) := rfl
theorem meaning887 (b : Nat → Bool) : literal (valuationOf b) 887 = decide (1 ≤ count887 b) := rfl
theorem meaning888 (b : Nat → Bool) : literal (valuationOf b) 888 = decide (2 ≤ count887 b) := rfl
theorem meaning889 (b : Nat → Bool) : literal (valuationOf b) 889 = decide (1 ≤ count889 b) := rfl
theorem meaning890 (b : Nat → Bool) : literal (valuationOf b) 890 = decide (2 ≤ count889 b) := rfl
theorem meaning891 (b : Nat → Bool) : literal (valuationOf b) 891 = decide (1 ≤ count891 b) := rfl
theorem meaning892 (b : Nat → Bool) : literal (valuationOf b) 892 = decide (2 ≤ count891 b) := rfl
theorem meaning893 (b : Nat → Bool) : literal (valuationOf b) 893 = decide (3 ≤ count891 b) := rfl
theorem meaning894 (b : Nat → Bool) : literal (valuationOf b) 894 = decide (4 ≤ count891 b) := rfl
theorem meaning895 (b : Nat → Bool) : literal (valuationOf b) 895 = decide (1 ≤ count895 b) := rfl
theorem meaning896 (b : Nat → Bool) : literal (valuationOf b) 896 = decide (2 ≤ count895 b) := rfl
theorem meaning897 (b : Nat → Bool) : literal (valuationOf b) 897 = decide (1 ≤ count897 b) := rfl
theorem meaning898 (b : Nat → Bool) : literal (valuationOf b) 898 = decide (2 ≤ count897 b) := rfl
theorem meaning899 (b : Nat → Bool) : literal (valuationOf b) 899 = decide (1 ≤ count899 b) := rfl
theorem meaning900 (b : Nat → Bool) : literal (valuationOf b) 900 = decide (2 ≤ count899 b) := rfl
theorem meaning901 (b : Nat → Bool) : literal (valuationOf b) 901 = decide (3 ≤ count899 b) := rfl
theorem meaning902 (b : Nat → Bool) : literal (valuationOf b) 902 = decide (4 ≤ count899 b) := rfl
theorem meaning903 (b : Nat → Bool) : literal (valuationOf b) 903 = decide (1 ≤ count903 b) := rfl
theorem meaning904 (b : Nat → Bool) : literal (valuationOf b) 904 = decide (2 ≤ count903 b) := rfl
theorem meaning905 (b : Nat → Bool) : literal (valuationOf b) 905 = decide (3 ≤ count903 b) := rfl
theorem meaning906 (b : Nat → Bool) : literal (valuationOf b) 906 = decide (4 ≤ count903 b) := rfl
theorem meaning907 (b : Nat → Bool) : literal (valuationOf b) 907 = decide (5 ≤ count903 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (6 ≤ count903 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (7 ≤ count903 b) := rfl
theorem meaning914 (b : Nat → Bool) : literal (valuationOf b) 914 = decide (4 ≤ count911 b) := rfl
theorem meaning915 (b : Nat → Bool) : literal (valuationOf b) 915 = decide (5 ≤ count911 b) := rfl
theorem meaning916 (b : Nat → Bool) : literal (valuationOf b) 916 = decide (6 ≤ count911 b) := rfl
theorem meaning917 (b : Nat → Bool) : literal (valuationOf b) 917 = decide (7 ≤ count911 b) := rfl
theorem meaning918 (b : Nat → Bool) : literal (valuationOf b) 918 = decide (8 ≤ count911 b) := rfl
theorem meaning919 (b : Nat → Bool) : literal (valuationOf b) 919 = decide (9 ≤ count911 b) := rfl
theorem meaning920 (b : Nat → Bool) : literal (valuationOf b) 920 = decide (10 ≤ count911 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (11 ≤ count911 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (12 ≤ count911 b) := rfl
theorem meaning923 (b : Nat → Bool) : literal (valuationOf b) 923 = decide (13 ≤ count911 b) := rfl
theorem meaning927 (b : Nat → Bool) : literal (valuationOf b) 927 = decide (1 ≤ count927 b) := rfl
theorem meaning928 (b : Nat → Bool) : literal (valuationOf b) 928 = decide (2 ≤ count927 b) := rfl
theorem meaning929 (b : Nat → Bool) : literal (valuationOf b) 929 = decide (1 ≤ count929 b) := rfl
theorem meaning930 (b : Nat → Bool) : literal (valuationOf b) 930 = decide (2 ≤ count929 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (1 ≤ count931 b) := rfl
theorem meaning932 (b : Nat → Bool) : literal (valuationOf b) 932 = decide (2 ≤ count931 b) := rfl
theorem meaning933 (b : Nat → Bool) : literal (valuationOf b) 933 = decide (3 ≤ count931 b) := rfl
theorem meaning934 (b : Nat → Bool) : literal (valuationOf b) 934 = decide (4 ≤ count931 b) := rfl
theorem meaning935 (b : Nat → Bool) : literal (valuationOf b) 935 = decide (1 ≤ count935 b) := rfl
theorem meaning936 (b : Nat → Bool) : literal (valuationOf b) 936 = decide (2 ≤ count935 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (1 ≤ count937 b) := rfl
theorem meaning938 (b : Nat → Bool) : literal (valuationOf b) 938 = decide (2 ≤ count937 b) := rfl
theorem meaning939 (b : Nat → Bool) : literal (valuationOf b) 939 = decide (1 ≤ count939 b) := rfl
theorem meaning940 (b : Nat → Bool) : literal (valuationOf b) 940 = decide (2 ≤ count939 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (3 ≤ count939 b) := rfl
theorem meaning942 (b : Nat → Bool) : literal (valuationOf b) 942 = decide (4 ≤ count939 b) := rfl
theorem meaning943 (b : Nat → Bool) : literal (valuationOf b) 943 = decide (1 ≤ count943 b) := rfl
theorem meaning944 (b : Nat → Bool) : literal (valuationOf b) 944 = decide (2 ≤ count943 b) := rfl
theorem meaning945 (b : Nat → Bool) : literal (valuationOf b) 945 = decide (3 ≤ count943 b) := rfl
theorem meaning946 (b : Nat → Bool) : literal (valuationOf b) 946 = decide (4 ≤ count943 b) := rfl
theorem meaning947 (b : Nat → Bool) : literal (valuationOf b) 947 = decide (5 ≤ count943 b) := rfl
theorem meaning948 (b : Nat → Bool) : literal (valuationOf b) 948 = decide (6 ≤ count943 b) := rfl
theorem meaning949 (b : Nat → Bool) : literal (valuationOf b) 949 = decide (7 ≤ count943 b) := rfl
theorem meaning951 (b : Nat → Bool) : literal (valuationOf b) 951 = decide (1 ≤ count951 b) := rfl
theorem meaning952 (b : Nat → Bool) : literal (valuationOf b) 952 = decide (2 ≤ count951 b) := rfl
theorem meaning953 (b : Nat → Bool) : literal (valuationOf b) 953 = decide (1 ≤ count953 b) := rfl
theorem meaning954 (b : Nat → Bool) : literal (valuationOf b) 954 = decide (2 ≤ count953 b) := rfl
theorem meaning955 (b : Nat → Bool) : literal (valuationOf b) 955 = decide (1 ≤ count955 b) := rfl
theorem meaning956 (b : Nat → Bool) : literal (valuationOf b) 956 = decide (2 ≤ count955 b) := rfl
theorem meaning957 (b : Nat → Bool) : literal (valuationOf b) 957 = decide (3 ≤ count955 b) := rfl
theorem meaning958 (b : Nat → Bool) : literal (valuationOf b) 958 = decide (4 ≤ count955 b) := rfl
theorem meaning959 (b : Nat → Bool) : literal (valuationOf b) 959 = decide (1 ≤ count959 b) := rfl
theorem meaning960 (b : Nat → Bool) : literal (valuationOf b) 960 = decide (2 ≤ count959 b) := rfl
theorem meaning961 (b : Nat → Bool) : literal (valuationOf b) 961 = decide (1 ≤ count961 b) := rfl
theorem meaning962 (b : Nat → Bool) : literal (valuationOf b) 962 = decide (2 ≤ count961 b) := rfl
theorem meaning963 (b : Nat → Bool) : literal (valuationOf b) 963 = decide (1 ≤ count963 b) := rfl
theorem meaning964 (b : Nat → Bool) : literal (valuationOf b) 964 = decide (2 ≤ count963 b) := rfl
theorem meaning965 (b : Nat → Bool) : literal (valuationOf b) 965 = decide (3 ≤ count963 b) := rfl
theorem meaning967 (b : Nat → Bool) : literal (valuationOf b) 967 = decide (1 ≤ count967 b) := rfl
theorem meaning968 (b : Nat → Bool) : literal (valuationOf b) 968 = decide (2 ≤ count967 b) := rfl
theorem meaning969 (b : Nat → Bool) : literal (valuationOf b) 969 = decide (3 ≤ count967 b) := rfl
theorem meaning970 (b : Nat → Bool) : literal (valuationOf b) 970 = decide (4 ≤ count967 b) := rfl
theorem meaning971 (b : Nat → Bool) : literal (valuationOf b) 971 = decide (5 ≤ count967 b) := rfl
theorem meaning972 (b : Nat → Bool) : literal (valuationOf b) 972 = decide (6 ≤ count967 b) := rfl
theorem meaning977 (b : Nat → Bool) : literal (valuationOf b) 977 = decide (3 ≤ count975 b) := rfl
theorem meaning978 (b : Nat → Bool) : literal (valuationOf b) 978 = decide (4 ≤ count975 b) := rfl
theorem meaning979 (b : Nat → Bool) : literal (valuationOf b) 979 = decide (5 ≤ count975 b) := rfl
theorem meaning980 (b : Nat → Bool) : literal (valuationOf b) 980 = decide (6 ≤ count975 b) := rfl
theorem meaning981 (b : Nat → Bool) : literal (valuationOf b) 981 = decide (7 ≤ count975 b) := rfl
theorem meaning982 (b : Nat → Bool) : literal (valuationOf b) 982 = decide (8 ≤ count975 b) := rfl
theorem meaning983 (b : Nat → Bool) : literal (valuationOf b) 983 = decide (9 ≤ count975 b) := rfl
theorem meaning984 (b : Nat → Bool) : literal (valuationOf b) 984 = decide (10 ≤ count975 b) := rfl
theorem meaning999 (b : Nat → Bool) : literal (valuationOf b) 999 = decide (9 ≤ count991 b) := rfl
theorem meaning1000 (b : Nat → Bool) : literal (valuationOf b) 1000 = decide (10 ≤ count991 b) := rfl
theorem meaning1001 (b : Nat → Bool) : literal (valuationOf b) 1001 = decide (11 ≤ count991 b) := rfl
theorem meaning1002 (b : Nat → Bool) : literal (valuationOf b) 1002 = decide (12 ≤ count991 b) := rfl
theorem meaning1003 (b : Nat → Bool) : literal (valuationOf b) 1003 = decide (13 ≤ count991 b) := rfl
theorem meaning1004 (b : Nat → Bool) : literal (valuationOf b) 1004 = decide (14 ≤ count991 b) := rfl
theorem meaning1005 (b : Nat → Bool) : literal (valuationOf b) 1005 = decide (15 ≤ count991 b) := rfl
theorem meaning1006 (b : Nat → Bool) : literal (valuationOf b) 1006 = decide (16 ≤ count991 b) := rfl
theorem meaning1007 (b : Nat → Bool) : literal (valuationOf b) 1007 = decide (17 ≤ count991 b) := rfl
theorem meaning1008 (b : Nat → Bool) : literal (valuationOf b) 1008 = decide (18 ≤ count991 b) := rfl
theorem meaning1015 (b : Nat → Bool) : literal (valuationOf b) 1015 = decide (1 ≤ count1015 b) := rfl
theorem meaning1017 (b : Nat → Bool) : literal (valuationOf b) 1017 = decide (1 ≤ count1017 b) := rfl
theorem meaning1018 (b : Nat → Bool) : literal (valuationOf b) 1018 = decide (2 ≤ count1017 b) := rfl
theorem meaning1019 (b : Nat → Bool) : literal (valuationOf b) 1019 = decide (1 ≤ count1019 b) := rfl
theorem meaning1020 (b : Nat → Bool) : literal (valuationOf b) 1020 = decide (2 ≤ count1019 b) := rfl
theorem meaning1021 (b : Nat → Bool) : literal (valuationOf b) 1021 = decide (3 ≤ count1019 b) := rfl
theorem meaning1023 (b : Nat → Bool) : literal (valuationOf b) 1023 = decide (1 ≤ count1023 b) := rfl
theorem meaning1024 (b : Nat → Bool) : literal (valuationOf b) 1024 = decide (2 ≤ count1023 b) := rfl
theorem meaning1025 (b : Nat → Bool) : literal (valuationOf b) 1025 = decide (1 ≤ count1025 b) := rfl
theorem meaning1026 (b : Nat → Bool) : literal (valuationOf b) 1026 = decide (2 ≤ count1025 b) := rfl
theorem meaning1027 (b : Nat → Bool) : literal (valuationOf b) 1027 = decide (1 ≤ count1027 b) := rfl
theorem meaning1028 (b : Nat → Bool) : literal (valuationOf b) 1028 = decide (2 ≤ count1027 b) := rfl
theorem meaning1029 (b : Nat → Bool) : literal (valuationOf b) 1029 = decide (3 ≤ count1027 b) := rfl
theorem meaning1030 (b : Nat → Bool) : literal (valuationOf b) 1030 = decide (4 ≤ count1027 b) := rfl
theorem meaning1031 (b : Nat → Bool) : literal (valuationOf b) 1031 = decide (1 ≤ count1031 b) := rfl
theorem meaning1032 (b : Nat → Bool) : literal (valuationOf b) 1032 = decide (2 ≤ count1031 b) := rfl
theorem meaning1033 (b : Nat → Bool) : literal (valuationOf b) 1033 = decide (3 ≤ count1031 b) := rfl
theorem meaning1034 (b : Nat → Bool) : literal (valuationOf b) 1034 = decide (4 ≤ count1031 b) := rfl
theorem meaning1035 (b : Nat → Bool) : literal (valuationOf b) 1035 = decide (5 ≤ count1031 b) := rfl
theorem meaning1039 (b : Nat → Bool) : literal (valuationOf b) 1039 = decide (1 ≤ count1039 b) := rfl
theorem meaning1040 (b : Nat → Bool) : literal (valuationOf b) 1040 = decide (2 ≤ count1039 b) := rfl
theorem meaning1041 (b : Nat → Bool) : literal (valuationOf b) 1041 = decide (1 ≤ count1041 b) := rfl
theorem meaning1042 (b : Nat → Bool) : literal (valuationOf b) 1042 = decide (2 ≤ count1041 b) := rfl
theorem meaning1043 (b : Nat → Bool) : literal (valuationOf b) 1043 = decide (1 ≤ count1043 b) := rfl
theorem meaning1044 (b : Nat → Bool) : literal (valuationOf b) 1044 = decide (2 ≤ count1043 b) := rfl
theorem meaning1045 (b : Nat → Bool) : literal (valuationOf b) 1045 = decide (3 ≤ count1043 b) := rfl
theorem meaning1047 (b : Nat → Bool) : literal (valuationOf b) 1047 = decide (1 ≤ count1047 b) := rfl
theorem meaning1048 (b : Nat → Bool) : literal (valuationOf b) 1048 = decide (2 ≤ count1047 b) := rfl
theorem meaning1049 (b : Nat → Bool) : literal (valuationOf b) 1049 = decide (1 ≤ count1049 b) := rfl
theorem meaning1050 (b : Nat → Bool) : literal (valuationOf b) 1050 = decide (2 ≤ count1049 b) := rfl
theorem meaning1051 (b : Nat → Bool) : literal (valuationOf b) 1051 = decide (1 ≤ count1051 b) := rfl
theorem meaning1052 (b : Nat → Bool) : literal (valuationOf b) 1052 = decide (2 ≤ count1051 b) := rfl
theorem meaning1053 (b : Nat → Bool) : literal (valuationOf b) 1053 = decide (3 ≤ count1051 b) := rfl
theorem meaning1054 (b : Nat → Bool) : literal (valuationOf b) 1054 = decide (4 ≤ count1051 b) := rfl
theorem meaning1055 (b : Nat → Bool) : literal (valuationOf b) 1055 = decide (1 ≤ count1055 b) := rfl
theorem meaning1056 (b : Nat → Bool) : literal (valuationOf b) 1056 = decide (2 ≤ count1055 b) := rfl
theorem meaning1057 (b : Nat → Bool) : literal (valuationOf b) 1057 = decide (3 ≤ count1055 b) := rfl
theorem meaning1058 (b : Nat → Bool) : literal (valuationOf b) 1058 = decide (4 ≤ count1055 b) := rfl
theorem meaning1059 (b : Nat → Bool) : literal (valuationOf b) 1059 = decide (5 ≤ count1055 b) := rfl
theorem meaning1060 (b : Nat → Bool) : literal (valuationOf b) 1060 = decide (6 ≤ count1055 b) := rfl
theorem meaning1063 (b : Nat → Bool) : literal (valuationOf b) 1063 = decide (1 ≤ count1063 b) := rfl
theorem meaning1064 (b : Nat → Bool) : literal (valuationOf b) 1064 = decide (2 ≤ count1063 b) := rfl
theorem meaning1065 (b : Nat → Bool) : literal (valuationOf b) 1065 = decide (3 ≤ count1063 b) := rfl
theorem meaning1066 (b : Nat → Bool) : literal (valuationOf b) 1066 = decide (4 ≤ count1063 b) := rfl
theorem meaning1067 (b : Nat → Bool) : literal (valuationOf b) 1067 = decide (5 ≤ count1063 b) := rfl
theorem meaning1068 (b : Nat → Bool) : literal (valuationOf b) 1068 = decide (6 ≤ count1063 b) := rfl
theorem meaning1069 (b : Nat → Bool) : literal (valuationOf b) 1069 = decide (7 ≤ count1063 b) := rfl
theorem meaning1070 (b : Nat → Bool) : literal (valuationOf b) 1070 = decide (8 ≤ count1063 b) := rfl
theorem meaning1079 (b : Nat → Bool) : literal (valuationOf b) 1079 = decide (1 ≤ count1079 b) := rfl
theorem meaning1080 (b : Nat → Bool) : literal (valuationOf b) 1080 = decide (2 ≤ count1079 b) := rfl
theorem meaning1081 (b : Nat → Bool) : literal (valuationOf b) 1081 = decide (1 ≤ count1081 b) := rfl
theorem meaning1082 (b : Nat → Bool) : literal (valuationOf b) 1082 = decide (2 ≤ count1081 b) := rfl
theorem meaning1083 (b : Nat → Bool) : literal (valuationOf b) 1083 = decide (1 ≤ count1083 b) := rfl
theorem meaning1084 (b : Nat → Bool) : literal (valuationOf b) 1084 = decide (2 ≤ count1083 b) := rfl
theorem meaning1085 (b : Nat → Bool) : literal (valuationOf b) 1085 = decide (3 ≤ count1083 b) := rfl
theorem meaning1086 (b : Nat → Bool) : literal (valuationOf b) 1086 = decide (4 ≤ count1083 b) := rfl
theorem meaning1087 (b : Nat → Bool) : literal (valuationOf b) 1087 = decide (1 ≤ count1087 b) := rfl
theorem meaning1088 (b : Nat → Bool) : literal (valuationOf b) 1088 = decide (2 ≤ count1087 b) := rfl
theorem meaning1089 (b : Nat → Bool) : literal (valuationOf b) 1089 = decide (1 ≤ count1089 b) := rfl
theorem meaning1090 (b : Nat → Bool) : literal (valuationOf b) 1090 = decide (2 ≤ count1089 b) := rfl
theorem meaning1091 (b : Nat → Bool) : literal (valuationOf b) 1091 = decide (1 ≤ count1091 b) := rfl
theorem meaning1092 (b : Nat → Bool) : literal (valuationOf b) 1092 = decide (2 ≤ count1091 b) := rfl
theorem meaning1093 (b : Nat → Bool) : literal (valuationOf b) 1093 = decide (3 ≤ count1091 b) := rfl
theorem meaning1094 (b : Nat → Bool) : literal (valuationOf b) 1094 = decide (4 ≤ count1091 b) := rfl
theorem meaning1095 (b : Nat → Bool) : literal (valuationOf b) 1095 = decide (1 ≤ count1095 b) := rfl
theorem meaning1096 (b : Nat → Bool) : literal (valuationOf b) 1096 = decide (2 ≤ count1095 b) := rfl
theorem meaning1097 (b : Nat → Bool) : literal (valuationOf b) 1097 = decide (3 ≤ count1095 b) := rfl
theorem meaning1098 (b : Nat → Bool) : literal (valuationOf b) 1098 = decide (4 ≤ count1095 b) := rfl
theorem meaning1099 (b : Nat → Bool) : literal (valuationOf b) 1099 = decide (5 ≤ count1095 b) := rfl
theorem meaning1100 (b : Nat → Bool) : literal (valuationOf b) 1100 = decide (6 ≤ count1095 b) := rfl
theorem meaning1103 (b : Nat → Bool) : literal (valuationOf b) 1103 = decide (1 ≤ count1103 b) := rfl
theorem meaning1104 (b : Nat → Bool) : literal (valuationOf b) 1104 = decide (2 ≤ count1103 b) := rfl
theorem meaning1105 (b : Nat → Bool) : literal (valuationOf b) 1105 = decide (1 ≤ count1105 b) := rfl
theorem meaning1106 (b : Nat → Bool) : literal (valuationOf b) 1106 = decide (2 ≤ count1105 b) := rfl
theorem meaning1107 (b : Nat → Bool) : literal (valuationOf b) 1107 = decide (1 ≤ count1107 b) := rfl
theorem meaning1108 (b : Nat → Bool) : literal (valuationOf b) 1108 = decide (2 ≤ count1107 b) := rfl
theorem meaning1109 (b : Nat → Bool) : literal (valuationOf b) 1109 = decide (3 ≤ count1107 b) := rfl
theorem meaning1111 (b : Nat → Bool) : literal (valuationOf b) 1111 = decide (1 ≤ count1111 b) := rfl
theorem meaning1112 (b : Nat → Bool) : literal (valuationOf b) 1112 = decide (2 ≤ count1111 b) := rfl
theorem meaning1113 (b : Nat → Bool) : literal (valuationOf b) 1113 = decide (1 ≤ count1113 b) := rfl
theorem meaning1114 (b : Nat → Bool) : literal (valuationOf b) 1114 = decide (2 ≤ count1113 b) := rfl
theorem meaning1115 (b : Nat → Bool) : literal (valuationOf b) 1115 = decide (1 ≤ count1115 b) := rfl
theorem meaning1116 (b : Nat → Bool) : literal (valuationOf b) 1116 = decide (2 ≤ count1115 b) := rfl
theorem meaning1117 (b : Nat → Bool) : literal (valuationOf b) 1117 = decide (3 ≤ count1115 b) := rfl
theorem meaning1119 (b : Nat → Bool) : literal (valuationOf b) 1119 = decide (1 ≤ count1119 b) := rfl
theorem meaning1120 (b : Nat → Bool) : literal (valuationOf b) 1120 = decide (2 ≤ count1119 b) := rfl
theorem meaning1121 (b : Nat → Bool) : literal (valuationOf b) 1121 = decide (3 ≤ count1119 b) := rfl
theorem meaning1122 (b : Nat → Bool) : literal (valuationOf b) 1122 = decide (4 ≤ count1119 b) := rfl
theorem meaning1129 (b : Nat → Bool) : literal (valuationOf b) 1129 = decide (3 ≤ count1127 b) := rfl
theorem meaning1130 (b : Nat → Bool) : literal (valuationOf b) 1130 = decide (4 ≤ count1127 b) := rfl
theorem meaning1131 (b : Nat → Bool) : literal (valuationOf b) 1131 = decide (5 ≤ count1127 b) := rfl
theorem meaning1132 (b : Nat → Bool) : literal (valuationOf b) 1132 = decide (6 ≤ count1127 b) := rfl
theorem meaning1133 (b : Nat → Bool) : literal (valuationOf b) 1133 = decide (7 ≤ count1127 b) := rfl
theorem meaning1134 (b : Nat → Bool) : literal (valuationOf b) 1134 = decide (8 ≤ count1127 b) := rfl
theorem meaning1135 (b : Nat → Bool) : literal (valuationOf b) 1135 = decide (9 ≤ count1127 b) := rfl
theorem meaning1148 (b : Nat → Bool) : literal (valuationOf b) 1148 = decide (6 ≤ count1143 b) := rfl
theorem meaning1149 (b : Nat → Bool) : literal (valuationOf b) 1149 = decide (7 ≤ count1143 b) := rfl
theorem meaning1150 (b : Nat → Bool) : literal (valuationOf b) 1150 = decide (8 ≤ count1143 b) := rfl
theorem meaning1151 (b : Nat → Bool) : literal (valuationOf b) 1151 = decide (9 ≤ count1143 b) := rfl
theorem meaning1152 (b : Nat → Bool) : literal (valuationOf b) 1152 = decide (10 ≤ count1143 b) := rfl
theorem meaning1153 (b : Nat → Bool) : literal (valuationOf b) 1153 = decide (11 ≤ count1143 b) := rfl
theorem meaning1154 (b : Nat → Bool) : literal (valuationOf b) 1154 = decide (12 ≤ count1143 b) := rfl
theorem meaning1155 (b : Nat → Bool) : literal (valuationOf b) 1155 = decide (13 ≤ count1143 b) := rfl
theorem meaning1156 (b : Nat → Bool) : literal (valuationOf b) 1156 = decide (14 ≤ count1143 b) := rfl
theorem meaning1157 (b : Nat → Bool) : literal (valuationOf b) 1157 = decide (15 ≤ count1143 b) := rfl
theorem meaning1190 (b : Nat → Bool) : literal (valuationOf b) 1190 = decide (24 ≤ count1167 b) := rfl
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
end Snake9.Regrowth.E112121
