import E112026Data
namespace Snake9.Regrowth.E112026
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 121 then (if i < 60 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (35 : Vertex)) else decide (InPath q (36 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (37 : Vertex)) else decide (InPath q (39 : Vertex))) else (if i < 6 then decide (InPath q (44 : Vertex)) else decide (InPath q (52 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (53 : Vertex)) else decide (InPath q (55 : Vertex))) else (if i < 10 then decide (InPath q (99 : Vertex)) else decide (InPath q (100 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (103 : Vertex)) else decide (InPath q (160 : Vertex))) else (if i < 14 then decide (InPath q (161 : Vertex)) else decide (InPath q (162 : Vertex)))))) else (if i < 22 then (if i < 18 then (if i < 16 then decide (InPath q (163 : Vertex)) else (if i < 17 then decide (InPath q (165 : Vertex)) else decide (InPath q (166 : Vertex)))) else (if i < 20 then (if i < 19 then decide (InPath q (168 : Vertex)) else decide (InPath q (171 : Vertex))) else (if i < 21 then decide (InPath q (173 : Vertex)) else decide (InPath q (175 : Vertex))))) else (if i < 26 then (if i < 24 then (if i < 23 then decide (InPath q (176 : Vertex)) else decide (InPath q (177 : Vertex))) else (if i < 25 then decide (InPath q (178 : Vertex)) else decide (InPath q (179 : Vertex)))) else (if i < 28 then (if i < 27 then decide (InPath q (182 : Vertex)) else decide (InPath q (184 : Vertex))) else (if i < 29 then decide (InPath q (188 : Vertex)) else decide (InPath q (189 : Vertex))))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then decide (InPath q (190 : Vertex)) else (if i < 32 then decide (InPath q (191 : Vertex)) else decide (InPath q (226 : Vertex)))) else (if i < 35 then (if i < 34 then decide (InPath q (227 : Vertex)) else decide (InPath q (228 : Vertex))) else (if i < 36 then decide (InPath q (229 : Vertex)) else decide (InPath q (230 : Vertex))))) else (if i < 41 then (if i < 39 then (if i < 38 then decide (InPath q (234 : Vertex)) else decide (InPath q (235 : Vertex))) else (if i < 40 then decide (InPath q (236 : Vertex)) else decide (InPath q (238 : Vertex)))) else (if i < 43 then (if i < 42 then decide (InPath q (244 : Vertex)) else decide (InPath q (245 : Vertex))) else (if i < 44 then decide (InPath q (247 : Vertex)) else decide (InPath q (248 : Vertex)))))) else (if i < 52 then (if i < 48 then (if i < 46 then decide (InPath q (249 : Vertex)) else (if i < 47 then decide (InPath q (250 : Vertex)) else decide (InPath q (251 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (255 : Vertex)) else decide (InPath q (288 : Vertex))) else (if i < 51 then decide (InPath q (289 : Vertex)) else decide (InPath q (294 : Vertex))))) else (if i < 56 then (if i < 54 then (if i < 53 then decide (InPath q (295 : Vertex)) else decide (InPath q (296 : Vertex))) else (if i < 55 then decide (InPath q (299 : Vertex)) else decide (InPath q (301 : Vertex)))) else (if i < 58 then (if i < 57 then decide (InPath q (303 : Vertex)) else decide (InPath q (304 : Vertex))) else (if i < 59 then decide (InPath q (305 : Vertex)) else decide (InPath q (306 : Vertex)))))))) else (if i < 90 then (if i < 75 then (if i < 67 then (if i < 63 then (if i < 61 then decide (InPath q (307 : Vertex)) else (if i < 62 then decide (InPath q (308 : Vertex)) else decide (InPath q (310 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (316 : Vertex)) else decide (InPath q (317 : Vertex))) else (if i < 66 then decide (InPath q (318 : Vertex)) else decide (InPath q (354 : Vertex))))) else (if i < 71 then (if i < 69 then (if i < 68 then decide (InPath q (355 : Vertex)) else decide (InPath q (356 : Vertex))) else (if i < 70 then decide (InPath q (357 : Vertex)) else decide (InPath q (362 : Vertex)))) else (if i < 73 then (if i < 72 then decide (InPath q (363 : Vertex)) else decide (InPath q (364 : Vertex))) else (if i < 74 then decide (InPath q (366 : Vertex)) else decide (InPath q (372 : Vertex)))))) else (if i < 82 then (if i < 78 then (if i < 76 then decide (InPath q (373 : Vertex)) else (if i < 77 then decide (InPath q (375 : Vertex)) else decide (InPath q (376 : Vertex)))) else (if i < 80 then (if i < 79 then decide (InPath q (377 : Vertex)) else decide (InPath q (379 : Vertex))) else (if i < 81 then decide (InPath q (383 : Vertex)) else decide (InPath q (416 : Vertex))))) else (if i < 86 then (if i < 84 then (if i < 83 then decide (InPath q (417 : Vertex)) else decide (InPath q (418 : Vertex))) else (if i < 85 then decide (InPath q (420 : Vertex)) else decide (InPath q (421 : Vertex)))) else (if i < 88 then (if i < 87 then decide (InPath q (422 : Vertex)) else decide (InPath q (423 : Vertex))) else (if i < 89 then decide (InPath q (424 : Vertex)) else decide (InPath q (426 : Vertex))))))) else (if i < 105 then (if i < 97 then (if i < 93 then (if i < 91 then decide (InPath q (427 : Vertex)) else (if i < 92 then decide (InPath q (428 : Vertex)) else decide (InPath q (430 : Vertex)))) else (if i < 95 then (if i < 94 then decide (InPath q (431 : Vertex)) else decide (InPath q (433 : Vertex))) else (if i < 96 then decide (InPath q (435 : Vertex)) else decide (InPath q (436 : Vertex))))) else (if i < 101 then (if i < 99 then (if i < 98 then decide (InPath q (437 : Vertex)) else decide (InPath q (439 : Vertex))) else (if i < 100 then decide (InPath q (440 : Vertex)) else decide (InPath q (441 : Vertex)))) else (if i < 103 then (if i < 102 then decide (InPath q (442 : Vertex)) else decide (InPath q (443 : Vertex))) else (if i < 104 then decide (InPath q (447 : Vertex)) else decide (InPath q (480 : Vertex)))))) else (if i < 113 then (if i < 109 then (if i < 107 then (if i < 106 then decide (InPath q (481 : Vertex)) else decide (InPath q (486 : Vertex))) else (if i < 108 then decide (InPath q (487 : Vertex)) else decide (InPath q (488 : Vertex)))) else (if i < 111 then (if i < 110 then decide (InPath q (489 : Vertex)) else decide (InPath q (491 : Vertex))) else (if i < 112 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))))) else (if i < 117 then (if i < 115 then (if i < 114 then decide (InPath q (497 : Vertex)) else decide (InPath q (498 : Vertex))) else (if i < 116 then decide (InPath q (499 : Vertex)) else decide (InPath q (500 : Vertex)))) else (if i < 119 then (if i < 118 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 120 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 182 then (if i < 151 then (if i < 136 then (if i < 128 then (if i < 124 then (if i < 122 then decide (InPath q (510 : Vertex)) else (if i < 123 then decide (BallClauseLogic.Endpoint q (35 : Vertex)) else decide (BallClauseLogic.Endpoint q (36 : Vertex)))) else (if i < 126 then (if i < 125 then decide (BallClauseLogic.Endpoint q (37 : Vertex)) else decide (BallClauseLogic.Endpoint q (39 : Vertex))) else (if i < 127 then decide (BallClauseLogic.Endpoint q (44 : Vertex)) else decide (BallClauseLogic.Endpoint q (52 : Vertex))))) else (if i < 132 then (if i < 130 then (if i < 129 then decide (BallClauseLogic.Endpoint q (53 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (99 : Vertex)) else decide (BallClauseLogic.Endpoint q (100 : Vertex)))) else (if i < 134 then (if i < 133 then decide (BallClauseLogic.Endpoint q (103 : Vertex)) else decide (BallClauseLogic.Endpoint q (160 : Vertex))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (161 : Vertex)) else decide (BallClauseLogic.Endpoint q (162 : Vertex)))))) else (if i < 143 then (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (163 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (165 : Vertex)) else decide (BallClauseLogic.Endpoint q (166 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else decide (BallClauseLogic.Endpoint q (171 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (173 : Vertex)) else decide (BallClauseLogic.Endpoint q (175 : Vertex))))) else (if i < 147 then (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (176 : Vertex)) else decide (BallClauseLogic.Endpoint q (177 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (178 : Vertex)) else decide (BallClauseLogic.Endpoint q (179 : Vertex)))) else (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (182 : Vertex)) else decide (BallClauseLogic.Endpoint q (184 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (188 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex))))))) else (if i < 166 then (if i < 158 then (if i < 154 then (if i < 152 then decide (BallClauseLogic.Endpoint q (190 : Vertex)) else (if i < 153 then decide (BallClauseLogic.Endpoint q (191 : Vertex)) else decide (BallClauseLogic.Endpoint q (226 : Vertex)))) else (if i < 156 then (if i < 155 then decide (BallClauseLogic.Endpoint q (227 : Vertex)) else decide (BallClauseLogic.Endpoint q (228 : Vertex))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (230 : Vertex))))) else (if i < 162 then (if i < 160 then (if i < 159 then decide (BallClauseLogic.Endpoint q (234 : Vertex)) else decide (BallClauseLogic.Endpoint q (235 : Vertex))) else (if i < 161 then decide (BallClauseLogic.Endpoint q (236 : Vertex)) else decide (BallClauseLogic.Endpoint q (238 : Vertex)))) else (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (245 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (247 : Vertex)) else decide (BallClauseLogic.Endpoint q (248 : Vertex)))))) else (if i < 174 then (if i < 170 then (if i < 168 then (if i < 167 then decide (BallClauseLogic.Endpoint q (249 : Vertex)) else decide (BallClauseLogic.Endpoint q (250 : Vertex))) else (if i < 169 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex)))) else (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else decide (BallClauseLogic.Endpoint q (289 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (294 : Vertex)) else decide (BallClauseLogic.Endpoint q (295 : Vertex))))) else (if i < 178 then (if i < 176 then (if i < 175 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else decide (BallClauseLogic.Endpoint q (299 : Vertex))) else (if i < 177 then decide (BallClauseLogic.Endpoint q (301 : Vertex)) else decide (BallClauseLogic.Endpoint q (303 : Vertex)))) else (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (304 : Vertex)) else decide (BallClauseLogic.Endpoint q (305 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (306 : Vertex)) else decide (BallClauseLogic.Endpoint q (307 : Vertex)))))))) else (if i < 212 then (if i < 197 then (if i < 189 then (if i < 185 then (if i < 183 then decide (BallClauseLogic.Endpoint q (308 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (310 : Vertex)) else decide (BallClauseLogic.Endpoint q (316 : Vertex)))) else (if i < 187 then (if i < 186 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (318 : Vertex))) else (if i < 188 then decide (BallClauseLogic.Endpoint q (354 : Vertex)) else decide (BallClauseLogic.Endpoint q (355 : Vertex))))) else (if i < 193 then (if i < 191 then (if i < 190 then decide (BallClauseLogic.Endpoint q (356 : Vertex)) else decide (BallClauseLogic.Endpoint q (357 : Vertex))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (362 : Vertex)) else decide (BallClauseLogic.Endpoint q (363 : Vertex)))) else (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (364 : Vertex)) else decide (BallClauseLogic.Endpoint q (366 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (372 : Vertex)) else decide (BallClauseLogic.Endpoint q (373 : Vertex)))))) else (if i < 204 then (if i < 200 then (if i < 198 then decide (BallClauseLogic.Endpoint q (375 : Vertex)) else (if i < 199 then decide (BallClauseLogic.Endpoint q (376 : Vertex)) else decide (BallClauseLogic.Endpoint q (377 : Vertex)))) else (if i < 202 then (if i < 201 then decide (BallClauseLogic.Endpoint q (379 : Vertex)) else decide (BallClauseLogic.Endpoint q (383 : Vertex))) else (if i < 203 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex))))) else (if i < 208 then (if i < 206 then (if i < 205 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (420 : Vertex))) else (if i < 207 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex)))) else (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))))))) else (if i < 227 then (if i < 219 then (if i < 215 then (if i < 213 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else (if i < 214 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (431 : Vertex)))) else (if i < 217 then (if i < 216 then decide (BallClauseLogic.Endpoint q (433 : Vertex)) else decide (BallClauseLogic.Endpoint q (435 : Vertex))) else (if i < 218 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (437 : Vertex))))) else (if i < 223 then (if i < 221 then (if i < 220 then decide (BallClauseLogic.Endpoint q (439 : Vertex)) else decide (BallClauseLogic.Endpoint q (440 : Vertex))) else (if i < 222 then decide (BallClauseLogic.Endpoint q (441 : Vertex)) else decide (BallClauseLogic.Endpoint q (442 : Vertex)))) else (if i < 225 then (if i < 224 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))) else (if i < 226 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))))) else (if i < 235 then (if i < 231 then (if i < 229 then (if i < 228 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else decide (BallClauseLogic.Endpoint q (487 : Vertex))) else (if i < 230 then decide (BallClauseLogic.Endpoint q (488 : Vertex)) else decide (BallClauseLogic.Endpoint q (489 : Vertex)))) else (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (491 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 239 then (if i < 237 then (if i < 236 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else decide (BallClauseLogic.Endpoint q (499 : Vertex))) else (if i < 238 then decide (BallClauseLogic.Endpoint q (500 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 241 then (if i < 240 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 242 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count243 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [122, 123, 124]
def count247 (b : Nat → Bool) : Nat := countLit b [125, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [125, 127, 128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 127, 128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count259 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count265 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137]
def count267 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135, 136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count287 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count291 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count293 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count301 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count317 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count323 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count335 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count337 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count349 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count369 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189]
def count371 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189]
def count373 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count377 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193]
def count379 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count383 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count409 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count411 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212]
def count413 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count419 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count421 (b : Nat → Bool) : Nat := countLit b [213, 214, 215]
def count423 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [218, 219]
def count427 (b : Nat → Bool) : Nat := countLit b [216, 217, 218, 219]
def count429 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216, 217, 218, 219]
def count431 (b : Nat → Bool) : Nat := countLit b [220, 221]
def count433 (b : Nat → Bool) : Nat := countLit b [222, 223]
def count435 (b : Nat → Bool) : Nat := countLit b [220, 221, 222, 223]
def count437 (b : Nat → Bool) : Nat := countLit b [224, 225]
def count439 (b : Nat → Bool) : Nat := countLit b [226, 227]
def count441 (b : Nat → Bool) : Nat := countLit b [224, 225, 226, 227]
def count443 (b : Nat → Bool) : Nat := countLit b [220, 221, 222, 223, 224, 225, 226, 227]
def count445 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]
def count447 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [228, 229, 230]
def count451 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count455 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [228, 229, 230, 231, 232, 233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count463 (b : Nat → Bool) : Nat := countLit b [235, 236, 237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count467 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count469 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242]
def count471 (b : Nat → Bool) : Nat := countLit b [235, 236, 237, 238, 239, 240, 241, 242]
def count473 (b : Nat → Bool) : Nat := countLit b [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]
def count475 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]
def count477 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]
def count479 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]
def count481 (b : Nat → Bool) : Nat := countLit b [4, 7]
def count483 (b : Nat → Bool) : Nat := countLit b [2, 4, 7]
def count486 (b : Nat → Bool) : Nat := countLit b [9, 12]
def count488 (b : Nat → Bool) : Nat := countLit b [15, 16]
def count490 (b : Nat → Bool) : Nat := countLit b [9, 12, 15, 16]
def count494 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 9, 12, 15, 16]
def count501 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count503 (b : Nat → Bool) : Nat := countLit b [17, 21, 23]
def count506 (b : Nat → Bool) : Nat := countLit b [24, 27]
def count508 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count510 (b : Nat → Bool) : Nat := countLit b [24, 27, 29, 30]
def count514 (b : Nat → Bool) : Nat := countLit b [17, 21, 23, 24, 27, 29, 30]
def count521 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 9, 12, 15, 16, 17, 21, 23, 24, 27, 29, 30]
def count535 (b : Nat → Bool) : Nat := countLit b [34, 38]
def count537 (b : Nat → Bool) : Nat := countLit b [32, 34, 38]
def count540 (b : Nat → Bool) : Nat := countLit b [40, 42]
def count542 (b : Nat → Bool) : Nat := countLit b [45, 46]
def count544 (b : Nat → Bool) : Nat := countLit b [40, 42, 45, 46]
def count548 (b : Nat → Bool) : Nat := countLit b [32, 34, 38, 40, 42, 45, 46]
def count555 (b : Nat → Bool) : Nat := countLit b [48, 49]
def count557 (b : Nat → Bool) : Nat := countLit b [51, 56]
def count559 (b : Nat → Bool) : Nat := countLit b [48, 49, 51, 56]
def count563 (b : Nat → Bool) : Nat := countLit b [58, 59]
def count565 (b : Nat → Bool) : Nat := countLit b [61, 64]
def count567 (b : Nat → Bool) : Nat := countLit b [58, 59, 61, 64]
def count571 (b : Nat → Bool) : Nat := countLit b [48, 49, 51, 56, 58, 59, 61, 64]
def count579 (b : Nat → Bool) : Nat := countLit b [32, 34, 38, 40, 42, 45, 46, 48, 49, 51, 56, 58, 59, 61, 64]
def count594 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 9, 12, 15, 16, 17, 21, 23, 24, 27, 29, 30, 32, 34, 38, 40, 42, 45, 46, 48, 49, 51, 56, 58, 59, 61, 64]
def count623 (b : Nat → Bool) : Nat := countLit b [66, 68]
def count625 (b : Nat → Bool) : Nat := countLit b [65, 66, 68]
def count628 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count630 (b : Nat → Bool) : Nat := countLit b [75, 78]
def count632 (b : Nat → Bool) : Nat := countLit b [71, 73, 75, 78]
def count636 (b : Nat → Bool) : Nat := countLit b [65, 66, 68, 71, 73, 75, 78]
def count643 (b : Nat → Bool) : Nat := countLit b [82, 83]
def count645 (b : Nat → Bool) : Nat := countLit b [80, 82, 83]
def count648 (b : Nat → Bool) : Nat := countLit b [84, 87]
def count650 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count652 (b : Nat → Bool) : Nat := countLit b [84, 87, 88, 90]
def count656 (b : Nat → Bool) : Nat := countLit b [80, 82, 83, 84, 87, 88, 90]
def count663 (b : Nat → Bool) : Nat := countLit b [65, 66, 68, 71, 73, 75, 78, 80, 82, 83, 84, 87, 88, 90]
def count677 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count679 (b : Nat → Bool) : Nat := countLit b [92, 95, 97]
def count682 (b : Nat → Bool) : Nat := countLit b [100, 101]
def count684 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count686 (b : Nat → Bool) : Nat := countLit b [100, 101, 103, 104]
def count690 (b : Nat → Bool) : Nat := countLit b [92, 95, 97, 100, 101, 103, 104]
def count697 (b : Nat → Bool) : Nat := countLit b [106, 109]
def count699 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count701 (b : Nat → Bool) : Nat := countLit b [106, 109, 112, 113]
def count705 (b : Nat → Bool) : Nat := countLit b [114, 116]
def count707 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count709 (b : Nat → Bool) : Nat := countLit b [114, 116, 120, 121]
def count713 (b : Nat → Bool) : Nat := countLit b [106, 109, 112, 113, 114, 116, 120, 121]
def count721 (b : Nat → Bool) : Nat := countLit b [92, 95, 97, 100, 101, 103, 104, 106, 109, 112, 113, 114, 116, 120, 121]
def count736 (b : Nat → Bool) : Nat := countLit b [65, 66, 68, 71, 73, 75, 78, 80, 82, 83, 84, 87, 88, 90, 92, 95, 97, 100, 101, 103, 104, 106, 109, 112, 113, 114, 116, 120, 121]
def count765 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 9, 12, 15, 16, 17, 21, 23, 24, 27, 29, 30, 32, 34, 38, 40, 42, 45, 46, 48, 49, 51, 56, 58, 59, 61, 64, 65, 66, 68, 71, 73, 75, 78, 80, 82, 83, 84, 87, 88, 90, 92, 95, 97, 100, 101, 103, 104, 106, 109, 112, 113, 114, 116, 120, 121]
def count807 (b : Nat → Bool) : Nat := countLit b [-4, -7]
def count809 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7]
def count812 (b : Nat → Bool) : Nat := countLit b [-9, -12]
def count814 (b : Nat → Bool) : Nat := countLit b [-15, -16]
def count816 (b : Nat → Bool) : Nat := countLit b [-9, -12, -15, -16]
def count820 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -9, -12, -15, -16]
def count827 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count829 (b : Nat → Bool) : Nat := countLit b [-17, -21, -23]
def count832 (b : Nat → Bool) : Nat := countLit b [-24, -27]
def count834 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count836 (b : Nat → Bool) : Nat := countLit b [-24, -27, -29, -30]
def count840 (b : Nat → Bool) : Nat := countLit b [-17, -21, -23, -24, -27, -29, -30]
def count847 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -9, -12, -15, -16, -17, -21, -23, -24, -27, -29, -30]
def count861 (b : Nat → Bool) : Nat := countLit b [-34, -38]
def count863 (b : Nat → Bool) : Nat := countLit b [-32, -34, -38]
def count866 (b : Nat → Bool) : Nat := countLit b [-40, -42]
def count868 (b : Nat → Bool) : Nat := countLit b [-45, -46]
def count870 (b : Nat → Bool) : Nat := countLit b [-40, -42, -45, -46]
def count874 (b : Nat → Bool) : Nat := countLit b [-32, -34, -38, -40, -42, -45, -46]
def count881 (b : Nat → Bool) : Nat := countLit b [-48, -49]
def count883 (b : Nat → Bool) : Nat := countLit b [-51, -56]
def count885 (b : Nat → Bool) : Nat := countLit b [-48, -49, -51, -56]
def count889 (b : Nat → Bool) : Nat := countLit b [-58, -59]
def count891 (b : Nat → Bool) : Nat := countLit b [-61, -64]
def count893 (b : Nat → Bool) : Nat := countLit b [-58, -59, -61, -64]
def count897 (b : Nat → Bool) : Nat := countLit b [-48, -49, -51, -56, -58, -59, -61, -64]
def count905 (b : Nat → Bool) : Nat := countLit b [-32, -34, -38, -40, -42, -45, -46, -48, -49, -51, -56, -58, -59, -61, -64]
def count920 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -9, -12, -15, -16, -17, -21, -23, -24, -27, -29, -30, -32, -34, -38, -40, -42, -45, -46, -48, -49, -51, -56, -58, -59, -61, -64]
def count938 (b : Nat → Bool) : Nat := countLit b [-66, -68]
def count940 (b : Nat → Bool) : Nat := countLit b [-65, -66, -68]
def count943 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count945 (b : Nat → Bool) : Nat := countLit b [-75, -78]
def count947 (b : Nat → Bool) : Nat := countLit b [-71, -73, -75, -78]
def count951 (b : Nat → Bool) : Nat := countLit b [-65, -66, -68, -71, -73, -75, -78]
def count958 (b : Nat → Bool) : Nat := countLit b [-82, -83]
def count960 (b : Nat → Bool) : Nat := countLit b [-80, -82, -83]
def count963 (b : Nat → Bool) : Nat := countLit b [-84, -87]
def count965 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count967 (b : Nat → Bool) : Nat := countLit b [-84, -87, -88, -90]
def count971 (b : Nat → Bool) : Nat := countLit b [-80, -82, -83, -84, -87, -88, -90]
def count978 (b : Nat → Bool) : Nat := countLit b [-65, -66, -68, -71, -73, -75, -78, -80, -82, -83, -84, -87, -88, -90]
def count992 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count994 (b : Nat → Bool) : Nat := countLit b [-92, -95, -97]
def count997 (b : Nat → Bool) : Nat := countLit b [-100, -101]
def count999 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1001 (b : Nat → Bool) : Nat := countLit b [-100, -101, -103, -104]
def count1005 (b : Nat → Bool) : Nat := countLit b [-92, -95, -97, -100, -101, -103, -104]
def count1012 (b : Nat → Bool) : Nat := countLit b [-106, -109]
def count1014 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1016 (b : Nat → Bool) : Nat := countLit b [-106, -109, -112, -113]
def count1020 (b : Nat → Bool) : Nat := countLit b [-114, -116]
def count1022 (b : Nat → Bool) : Nat := countLit b [-120, -121]
def count1024 (b : Nat → Bool) : Nat := countLit b [-114, -116, -120, -121]
def count1028 (b : Nat → Bool) : Nat := countLit b [-106, -109, -112, -113, -114, -116, -120, -121]
def count1036 (b : Nat → Bool) : Nat := countLit b [-92, -95, -97, -100, -101, -103, -104, -106, -109, -112, -113, -114, -116, -120, -121]
def count1051 (b : Nat → Bool) : Nat := countLit b [-65, -66, -68, -71, -73, -75, -78, -80, -82, -83, -84, -87, -88, -90, -92, -95, -97, -100, -101, -103, -104, -106, -109, -112, -113, -114, -116, -120, -121]
def count1069 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -9, -12, -15, -16, -17, -21, -23, -24, -27, -29, -30, -32, -34, -38, -40, -42, -45, -46, -48, -49, -51, -56, -58, -59, -61, -64, -65, -66, -68, -71, -73, -75, -78, -80, -82, -83, -84, -87, -88, -90, -92, -95, -97, -100, -101, -103, -104, -106, -109, -112, -113, -114, -116, -120, -121]
def count1087 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count1089 (b : Nat → Bool) : Nat := countLit b [1, 3, 5]
def count1092 (b : Nat → Bool) : Nat := countLit b [6, 8]
def count1094 (b : Nat → Bool) : Nat := countLit b [10, 11]
def count1096 (b : Nat → Bool) : Nat := countLit b [6, 8, 10, 11]
def count1100 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 8, 10, 11]
def count1107 (b : Nat → Bool) : Nat := countLit b [13, 14]
def count1109 (b : Nat → Bool) : Nat := countLit b [18, 19]
def count1111 (b : Nat → Bool) : Nat := countLit b [13, 14, 18, 19]
def count1115 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count1117 (b : Nat → Bool) : Nat := countLit b [25, 26]
def count1119 (b : Nat → Bool) : Nat := countLit b [20, 22, 25, 26]
def count1123 (b : Nat → Bool) : Nat := countLit b [13, 14, 18, 19, 20, 22, 25, 26]
def count1131 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 8, 10, 11, 13, 14, 18, 19, 20, 22, 25, 26]
def count1146 (b : Nat → Bool) : Nat := countLit b [28, 31]
def count1148 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count1150 (b : Nat → Bool) : Nat := countLit b [28, 31, 33, 35]
def count1154 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count1156 (b : Nat → Bool) : Nat := countLit b [39, 41]
def count1158 (b : Nat → Bool) : Nat := countLit b [36, 37, 39, 41]
def count1162 (b : Nat → Bool) : Nat := countLit b [28, 31, 33, 35, 36, 37, 39, 41]
def count1170 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count1172 (b : Nat → Bool) : Nat := countLit b [47, 50]
def count1174 (b : Nat → Bool) : Nat := countLit b [43, 44, 47, 50]
def count1178 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count1180 (b : Nat → Bool) : Nat := countLit b [54, 55]
def count1182 (b : Nat → Bool) : Nat := countLit b [52, 53, 54, 55]
def count1186 (b : Nat → Bool) : Nat := countLit b [43, 44, 47, 50, 52, 53, 54, 55]
def count1194 (b : Nat → Bool) : Nat := countLit b [28, 31, 33, 35, 36, 37, 39, 41, 43, 44, 47, 50, 52, 53, 54, 55]
def count1210 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 8, 10, 11, 13, 14, 18, 19, 20, 22, 25, 26, 28, 31, 33, 35, 36, 37, 39, 41, 43, 44, 47, 50, 52, 53, 54, 55]
def count1241 (b : Nat → Bool) : Nat := countLit b [57, 60]
def count1243 (b : Nat → Bool) : Nat := countLit b [62, 63]
def count1245 (b : Nat → Bool) : Nat := countLit b [57, 60, 62, 63]
def count1249 (b : Nat → Bool) : Nat := countLit b [67, 69]
def count1251 (b : Nat → Bool) : Nat := countLit b [70, 72]
def count1253 (b : Nat → Bool) : Nat := countLit b [67, 69, 70, 72]
def count1257 (b : Nat → Bool) : Nat := countLit b [57, 60, 62, 63, 67, 69, 70, 72]
def count1265 (b : Nat → Bool) : Nat := countLit b [74, 76]
def count1267 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count1269 (b : Nat → Bool) : Nat := countLit b [74, 76, 77, 79]
def count1273 (b : Nat → Bool) : Nat := countLit b [81, 85]
def count1275 (b : Nat → Bool) : Nat := countLit b [86, 89]
def count1277 (b : Nat → Bool) : Nat := countLit b [81, 85, 86, 89]
def count1281 (b : Nat → Bool) : Nat := countLit b [74, 76, 77, 79, 81, 85, 86, 89]
def count1289 (b : Nat → Bool) : Nat := countLit b [57, 60, 62, 63, 67, 69, 70, 72, 74, 76, 77, 79, 81, 85, 86, 89]
def count1305 (b : Nat → Bool) : Nat := countLit b [91, 93]
def count1307 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count1309 (b : Nat → Bool) : Nat := countLit b [91, 93, 94, 96]
def count1313 (b : Nat → Bool) : Nat := countLit b [98, 99]
def count1315 (b : Nat → Bool) : Nat := countLit b [102, 105]
def count1317 (b : Nat → Bool) : Nat := countLit b [98, 99, 102, 105]
def count1321 (b : Nat → Bool) : Nat := countLit b [91, 93, 94, 96, 98, 99, 102, 105]
def count1329 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count1331 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count1333 (b : Nat → Bool) : Nat := countLit b [107, 108, 110, 111]
def count1337 (b : Nat → Bool) : Nat := countLit b [115, 117]
def count1339 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count1341 (b : Nat → Bool) : Nat := countLit b [115, 117, 118, 119]
def count1345 (b : Nat → Bool) : Nat := countLit b [107, 108, 110, 111, 115, 117, 118, 119]
def count1353 (b : Nat → Bool) : Nat := countLit b [91, 93, 94, 96, 98, 99, 102, 105, 107, 108, 110, 111, 115, 117, 118, 119]
def count1369 (b : Nat → Bool) : Nat := countLit b [57, 60, 62, 63, 67, 69, 70, 72, 74, 76, 77, 79, 81, 85, 86, 89, 91, 93, 94, 96, 98, 99, 102, 105, 107, 108, 110, 111, 115, 117, 118, 119]
def count1401 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 8, 10, 11, 13, 14, 18, 19, 20, 22, 25, 26, 28, 31, 33, 35, 36, 37, 39, 41, 43, 44, 47, 50, 52, 53, 54, 55, 57, 60, 62, 63, 67, 69, 70, 72, 74, 76, 77, 79, 81, 85, 86, 89, 91, 93, 94, 96, 98, 99, 102, 105, 107, 108, 110, 111, 115, 117, 118, 119]
def count1443 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count1445 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5]
def count1448 (b : Nat → Bool) : Nat := countLit b [-6, -8]
def count1450 (b : Nat → Bool) : Nat := countLit b [-10, -11]
def count1452 (b : Nat → Bool) : Nat := countLit b [-6, -8, -10, -11]
def count1456 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -8, -10, -11]
def count1463 (b : Nat → Bool) : Nat := countLit b [-13, -14]
def count1465 (b : Nat → Bool) : Nat := countLit b [-18, -19]
def count1467 (b : Nat → Bool) : Nat := countLit b [-13, -14, -18, -19]
def count1471 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count1473 (b : Nat → Bool) : Nat := countLit b [-25, -26]
def count1475 (b : Nat → Bool) : Nat := countLit b [-20, -22, -25, -26]
def count1479 (b : Nat → Bool) : Nat := countLit b [-13, -14, -18, -19, -20, -22, -25, -26]
def count1487 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]
def count1502 (b : Nat → Bool) : Nat := countLit b [-28, -31]
def count1504 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count1506 (b : Nat → Bool) : Nat := countLit b [-28, -31, -33, -35]
def count1510 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count1512 (b : Nat → Bool) : Nat := countLit b [-39, -41]
def count1514 (b : Nat → Bool) : Nat := countLit b [-36, -37, -39, -41]
def count1518 (b : Nat → Bool) : Nat := countLit b [-28, -31, -33, -35, -36, -37, -39, -41]
def count1526 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count1528 (b : Nat → Bool) : Nat := countLit b [-47, -50]
def count1530 (b : Nat → Bool) : Nat := countLit b [-43, -44, -47, -50]
def count1534 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count1536 (b : Nat → Bool) : Nat := countLit b [-54, -55]
def count1538 (b : Nat → Bool) : Nat := countLit b [-52, -53, -54, -55]
def count1542 (b : Nat → Bool) : Nat := countLit b [-43, -44, -47, -50, -52, -53, -54, -55]
def count1550 (b : Nat → Bool) : Nat := countLit b [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]
def count1566 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]
def count1589 (b : Nat → Bool) : Nat := countLit b [-57, -60]
def count1591 (b : Nat → Bool) : Nat := countLit b [-62, -63]
def count1593 (b : Nat → Bool) : Nat := countLit b [-57, -60, -62, -63]
def count1597 (b : Nat → Bool) : Nat := countLit b [-67, -69]
def count1599 (b : Nat → Bool) : Nat := countLit b [-70, -72]
def count1601 (b : Nat → Bool) : Nat := countLit b [-67, -69, -70, -72]
def count1605 (b : Nat → Bool) : Nat := countLit b [-57, -60, -62, -63, -67, -69, -70, -72]
def count1613 (b : Nat → Bool) : Nat := countLit b [-74, -76]
def count1615 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count1617 (b : Nat → Bool) : Nat := countLit b [-74, -76, -77, -79]
def count1621 (b : Nat → Bool) : Nat := countLit b [-81, -85]
def count1623 (b : Nat → Bool) : Nat := countLit b [-86, -89]
def count1625 (b : Nat → Bool) : Nat := countLit b [-81, -85, -86, -89]
def count1629 (b : Nat → Bool) : Nat := countLit b [-74, -76, -77, -79, -81, -85, -86, -89]
def count1637 (b : Nat → Bool) : Nat := countLit b [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]
def count1653 (b : Nat → Bool) : Nat := countLit b [-91, -93]
def count1655 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1657 (b : Nat → Bool) : Nat := countLit b [-91, -93, -94, -96]
def count1661 (b : Nat → Bool) : Nat := countLit b [-98, -99]
def count1663 (b : Nat → Bool) : Nat := countLit b [-102, -105]
def count1665 (b : Nat → Bool) : Nat := countLit b [-98, -99, -102, -105]
def count1669 (b : Nat → Bool) : Nat := countLit b [-91, -93, -94, -96, -98, -99, -102, -105]
def count1677 (b : Nat → Bool) : Nat := countLit b [-107, -108]
def count1679 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count1681 (b : Nat → Bool) : Nat := countLit b [-107, -108, -110, -111]
def count1685 (b : Nat → Bool) : Nat := countLit b [-115, -117]
def count1687 (b : Nat → Bool) : Nat := countLit b [-118, -119]
def count1689 (b : Nat → Bool) : Nat := countLit b [-115, -117, -118, -119]
def count1693 (b : Nat → Bool) : Nat := countLit b [-107, -108, -110, -111, -115, -117, -118, -119]
def count1701 (b : Nat → Bool) : Nat := countLit b [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]
def count1717 (b : Nat → Bool) : Nat := countLit b [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]
def count1740 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55, -57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 881 then (if i < 440 then (if i < 220 then (if i < 110 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 20 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 18 then (if i < 17 then b 16 else b 17) else (if i < 19 then b 18 else b 19))) else (if i < 23 then (if i < 21 then b 20 else (if i < 22 then b 21 else b 22)) else (if i < 25 then (if i < 24 then b 23 else b 24) else (if i < 26 then b 25 else b 26))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 32 then (if i < 31 then b 30 else b 31) else (if i < 33 then b 32 else b 33))) else (if i < 37 then (if i < 35 then b 34 else (if i < 36 then b 35 else b 36)) else (if i < 39 then (if i < 38 then b 37 else b 38) else (if i < 40 then b 39 else b 40)))) else (if i < 48 then (if i < 44 then (if i < 42 then b 41 else (if i < 43 then b 42 else b 43)) else (if i < 46 then (if i < 45 then b 44 else b 45) else (if i < 47 then b 46 else b 47))) else (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 53 then (if i < 52 then b 51 else b 52) else (if i < 54 then b 53 else b 54)))))) else (if i < 82 then (if i < 68 then (if i < 61 then (if i < 58 then (if i < 56 then b 55 else (if i < 57 then b 56 else b 57)) else (if i < 59 then b 58 else (if i < 60 then b 59 else b 60))) else (if i < 64 then (if i < 62 then b 61 else (if i < 63 then b 62 else b 63)) else (if i < 66 then (if i < 65 then b 64 else b 65) else (if i < 67 then b 66 else b 67)))) else (if i < 75 then (if i < 71 then (if i < 69 then b 68 else (if i < 70 then b 69 else b 70)) else (if i < 73 then (if i < 72 then b 71 else b 72) else (if i < 74 then b 73 else b 74))) else (if i < 78 then (if i < 76 then b 75 else (if i < 77 then b 76 else b 77)) else (if i < 80 then (if i < 79 then b 78 else b 79) else (if i < 81 then b 80 else b 81))))) else (if i < 96 then (if i < 89 then (if i < 85 then (if i < 83 then b 82 else (if i < 84 then b 83 else b 84)) else (if i < 87 then (if i < 86 then b 85 else b 86) else (if i < 88 then b 87 else b 88))) else (if i < 92 then (if i < 90 then b 89 else (if i < 91 then b 90 else b 91)) else (if i < 94 then (if i < 93 then b 92 else b 93) else (if i < 95 then b 94 else b 95)))) else (if i < 103 then (if i < 99 then (if i < 97 then b 96 else (if i < 98 then b 97 else b 98)) else (if i < 101 then (if i < 100 then b 99 else b 100) else (if i < 102 then b 101 else b 102))) else (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 108 then (if i < 107 then b 106 else b 107) else (if i < 109 then b 108 else b 109))))))) else (if i < 165 then (if i < 137 then (if i < 123 then (if i < 116 then (if i < 113 then (if i < 111 then b 110 else (if i < 112 then b 111 else b 112)) else (if i < 114 then b 113 else (if i < 115 then b 114 else b 115))) else (if i < 119 then (if i < 117 then b 116 else (if i < 118 then b 117 else b 118)) else (if i < 121 then (if i < 120 then b 119 else b 120) else (if i < 122 then b 121 else b 122)))) else (if i < 130 then (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 128 then (if i < 127 then b 126 else b 127) else (if i < 129 then b 128 else b 129))) else (if i < 133 then (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)) else (if i < 135 then (if i < 134 then b 133 else b 134) else (if i < 136 then b 135 else b 136))))) else (if i < 151 then (if i < 144 then (if i < 140 then (if i < 138 then b 137 else (if i < 139 then b 138 else b 139)) else (if i < 142 then (if i < 141 then b 140 else b 141) else (if i < 143 then b 142 else b 143))) else (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 149 then (if i < 148 then b 147 else b 148) else (if i < 150 then b 149 else b 150)))) else (if i < 158 then (if i < 154 then (if i < 152 then b 151 else (if i < 153 then b 152 else b 153)) else (if i < 156 then (if i < 155 then b 154 else b 155) else (if i < 157 then b 156 else b 157))) else (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 163 then (if i < 162 then b 161 else b 162) else (if i < 164 then b 163 else b 164)))))) else (if i < 192 then (if i < 178 then (if i < 171 then (if i < 168 then (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)) else (if i < 169 then b 168 else (if i < 170 then b 169 else b 170))) else (if i < 174 then (if i < 172 then b 171 else (if i < 173 then b 172 else b 173)) else (if i < 176 then (if i < 175 then b 174 else b 175) else (if i < 177 then b 176 else b 177)))) else (if i < 185 then (if i < 181 then (if i < 179 then b 178 else (if i < 180 then b 179 else b 180)) else (if i < 183 then (if i < 182 then b 181 else b 182) else (if i < 184 then b 183 else b 184))) else (if i < 188 then (if i < 186 then b 185 else (if i < 187 then b 186 else b 187)) else (if i < 190 then (if i < 189 then b 188 else b 189) else (if i < 191 then b 190 else b 191))))) else (if i < 206 then (if i < 199 then (if i < 195 then (if i < 193 then b 192 else (if i < 194 then b 193 else b 194)) else (if i < 197 then (if i < 196 then b 195 else b 196) else (if i < 198 then b 197 else b 198))) else (if i < 202 then (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)) else (if i < 204 then (if i < 203 then b 202 else b 203) else (if i < 205 then b 204 else b 205)))) else (if i < 213 then (if i < 209 then (if i < 207 then b 206 else (if i < 208 then b 207 else b 208)) else (if i < 211 then (if i < 210 then b 209 else b 210) else (if i < 212 then b 211 else b 212))) else (if i < 216 then (if i < 214 then b 213 else (if i < 215 then b 214 else b 215)) else (if i < 218 then (if i < 217 then b 216 else b 217) else (if i < 219 then b 218 else b 219)))))))) else (if i < 330 then (if i < 275 then (if i < 247 then (if i < 233 then (if i < 226 then (if i < 223 then (if i < 221 then b 220 else (if i < 222 then b 221 else b 222)) else (if i < 224 then b 223 else (if i < 225 then b 224 else b 225))) else (if i < 229 then (if i < 227 then b 226 else (if i < 228 then b 227 else b 228)) else (if i < 231 then (if i < 230 then b 229 else b 230) else (if i < 232 then b 231 else b 232)))) else (if i < 240 then (if i < 236 then (if i < 234 then b 233 else (if i < 235 then b 234 else b 235)) else (if i < 238 then (if i < 237 then b 236 else b 237) else (if i < 239 then b 238 else b 239))) else (if i < 243 then (if i < 241 then b 240 else (if i < 242 then b 241 else b 242)) else (if i < 245 then (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b)) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b)))))) else (if i < 261 then (if i < 254 then (if i < 250 then (if i < 248 then decide (1 ≤ count247 b) else (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b))) else (if i < 252 then (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)) else (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)))) else (if i < 257 then (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b))) else (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))))) else (if i < 268 then (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 266 then (if i < 265 then decide (2 ≤ count263 b) else decide (1 ≤ count265 b)) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)))) else (if i < 271 then (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b))) else (if i < 273 then (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)) else (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b))))))) else (if i < 302 then (if i < 288 then (if i < 281 then (if i < 278 then (if i < 276 then decide (1 ≤ count275 b) else (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b))) else (if i < 279 then decide (2 ≤ count277 b) else (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)))) else (if i < 284 then (if i < 282 then decide (1 ≤ count281 b) else (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b))) else (if i < 286 then (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))))) else (if i < 295 then (if i < 291 then (if i < 289 then decide (2 ≤ count287 b) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))) else (if i < 293 then (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)))) else (if i < 298 then (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))) else (if i < 300 then (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b)) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))))) else (if i < 316 then (if i < 309 then (if i < 305 then (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))) else (if i < 307 then (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)))) else (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 314 then (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))))) else (if i < 323 then (if i < 319 then (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b))) else (if i < 321 then (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b)) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)))) else (if i < 326 then (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))) else (if i < 328 then (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b)) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)))))))) else (if i < 385 then (if i < 357 then (if i < 343 then (if i < 336 then (if i < 333 then (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b))) else (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b)))) else (if i < 339 then (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))) else (if i < 341 then (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))))) else (if i < 350 then (if i < 346 then (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)))) else (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 355 then (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)))))) else (if i < 371 then (if i < 364 then (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 362 then (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)))) else (if i < 367 then (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))) else (if i < 369 then (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b)) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))))) else (if i < 378 then (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 376 then (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b)))) else (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 383 then (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))))))) else (if i < 412 then (if i < 398 then (if i < 391 then (if i < 388 then (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b))) else (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)))) else (if i < 394 then (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 396 then (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b)) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))))) else (if i < 405 then (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 403 then (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b)) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b)))) else (if i < 408 then (if i < 406 then decide (1 ≤ count405 b) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b))) else (if i < 410 then (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b)))))) else (if i < 426 then (if i < 419 then (if i < 415 then (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))) else (if i < 417 then (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b)) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b)))) else (if i < 422 then (if i < 420 then decide (1 ≤ count419 b) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))) else (if i < 424 then (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b)) else (if i < 425 then decide (2 ≤ count423 b) else decide (1 ≤ count425 b))))) else (if i < 433 then (if i < 429 then (if i < 427 then decide (2 ≤ count425 b) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b))) else (if i < 431 then (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b)) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)))) else (if i < 436 then (if i < 434 then decide (1 ≤ count433 b) else (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b))) else (if i < 438 then (if i < 437 then decide (2 ≤ count435 b) else decide (1 ≤ count437 b)) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b)))))))))) else (if i < 660 then (if i < 550 then (if i < 495 then (if i < 467 then (if i < 453 then (if i < 446 then (if i < 443 then (if i < 441 then decide (2 ≤ count439 b) else (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b))) else (if i < 444 then decide (1 ≤ count443 b) else (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)))) else (if i < 449 then (if i < 447 then decide (2 ≤ count445 b) else (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b))) else (if i < 451 then (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b))))) else (if i < 460 then (if i < 456 then (if i < 454 then decide (1 ≤ count453 b) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b))) else (if i < 458 then (if i < 457 then decide (2 ≤ count455 b) else decide (1 ≤ count457 b)) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b)))) else (if i < 463 then (if i < 461 then decide (2 ≤ count459 b) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b))) else (if i < 465 then (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b)) else (if i < 466 then decide (1 ≤ count465 b) else decide (2 ≤ count465 b)))))) else (if i < 481 then (if i < 474 then (if i < 470 then (if i < 468 then decide (1 ≤ count467 b) else (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b))) else (if i < 472 then (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b)) else (if i < 473 then decide (2 ≤ count471 b) else decide (1 ≤ count473 b)))) else (if i < 477 then (if i < 475 then decide (2 ≤ count473 b) else (if i < 476 then decide (1 ≤ count475 b) else decide (2 ≤ count475 b))) else (if i < 479 then (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b)) else (if i < 480 then decide (1 ≤ count479 b) else decide (2 ≤ count479 b))))) else (if i < 488 then (if i < 484 then (if i < 482 then decide (1 ≤ count481 b) else (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b))) else (if i < 486 then (if i < 485 then decide (2 ≤ count483 b) else decide (3 ≤ count483 b)) else (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b)))) else (if i < 491 then (if i < 489 then decide (1 ≤ count488 b) else (if i < 490 then decide (2 ≤ count488 b) else decide (1 ≤ count490 b))) else (if i < 493 then (if i < 492 then decide (2 ≤ count490 b) else decide (3 ≤ count490 b)) else (if i < 494 then decide (4 ≤ count490 b) else decide (1 ≤ count494 b))))))) else (if i < 522 then (if i < 508 then (if i < 501 then (if i < 498 then (if i < 496 then decide (2 ≤ count494 b) else (if i < 497 then decide (3 ≤ count494 b) else decide (4 ≤ count494 b))) else (if i < 499 then decide (5 ≤ count494 b) else (if i < 500 then decide (6 ≤ count494 b) else decide (7 ≤ count494 b)))) else (if i < 504 then (if i < 502 then decide (1 ≤ count501 b) else (if i < 503 then decide (2 ≤ count501 b) else decide (1 ≤ count503 b))) else (if i < 506 then (if i < 505 then decide (2 ≤ count503 b) else decide (3 ≤ count503 b)) else (if i < 507 then decide (1 ≤ count506 b) else decide (2 ≤ count506 b))))) else (if i < 515 then (if i < 511 then (if i < 509 then decide (1 ≤ count508 b) else (if i < 510 then decide (2 ≤ count508 b) else decide (1 ≤ count510 b))) else (if i < 513 then (if i < 512 then decide (2 ≤ count510 b) else decide (3 ≤ count510 b)) else (if i < 514 then decide (4 ≤ count510 b) else decide (1 ≤ count514 b)))) else (if i < 518 then (if i < 516 then decide (2 ≤ count514 b) else (if i < 517 then decide (3 ≤ count514 b) else decide (4 ≤ count514 b))) else (if i < 520 then (if i < 519 then decide (5 ≤ count514 b) else decide (6 ≤ count514 b)) else (if i < 521 then decide (7 ≤ count514 b) else decide (1 ≤ count521 b)))))) else (if i < 536 then (if i < 529 then (if i < 525 then (if i < 523 then decide (2 ≤ count521 b) else (if i < 524 then decide (3 ≤ count521 b) else decide (4 ≤ count521 b))) else (if i < 527 then (if i < 526 then decide (5 ≤ count521 b) else decide (6 ≤ count521 b)) else (if i < 528 then decide (7 ≤ count521 b) else decide (8 ≤ count521 b)))) else (if i < 532 then (if i < 530 then decide (9 ≤ count521 b) else (if i < 531 then decide (10 ≤ count521 b) else decide (11 ≤ count521 b))) else (if i < 534 then (if i < 533 then decide (12 ≤ count521 b) else decide (13 ≤ count521 b)) else (if i < 535 then decide (14 ≤ count521 b) else decide (1 ≤ count535 b))))) else (if i < 543 then (if i < 539 then (if i < 537 then decide (2 ≤ count535 b) else (if i < 538 then decide (1 ≤ count537 b) else decide (2 ≤ count537 b))) else (if i < 541 then (if i < 540 then decide (3 ≤ count537 b) else decide (1 ≤ count540 b)) else (if i < 542 then decide (2 ≤ count540 b) else decide (1 ≤ count542 b)))) else (if i < 546 then (if i < 544 then decide (2 ≤ count542 b) else (if i < 545 then decide (1 ≤ count544 b) else decide (2 ≤ count544 b))) else (if i < 548 then (if i < 547 then decide (3 ≤ count544 b) else decide (4 ≤ count544 b)) else (if i < 549 then decide (1 ≤ count548 b) else decide (2 ≤ count548 b)))))))) else (if i < 605 then (if i < 577 then (if i < 563 then (if i < 556 then (if i < 553 then (if i < 551 then decide (3 ≤ count548 b) else (if i < 552 then decide (4 ≤ count548 b) else decide (5 ≤ count548 b))) else (if i < 554 then decide (6 ≤ count548 b) else (if i < 555 then decide (7 ≤ count548 b) else decide (1 ≤ count555 b)))) else (if i < 559 then (if i < 557 then decide (2 ≤ count555 b) else (if i < 558 then decide (1 ≤ count557 b) else decide (2 ≤ count557 b))) else (if i < 561 then (if i < 560 then decide (1 ≤ count559 b) else decide (2 ≤ count559 b)) else (if i < 562 then decide (3 ≤ count559 b) else decide (4 ≤ count559 b))))) else (if i < 570 then (if i < 566 then (if i < 564 then decide (1 ≤ count563 b) else (if i < 565 then decide (2 ≤ count563 b) else decide (1 ≤ count565 b))) else (if i < 568 then (if i < 567 then decide (2 ≤ count565 b) else decide (1 ≤ count567 b)) else (if i < 569 then decide (2 ≤ count567 b) else decide (3 ≤ count567 b)))) else (if i < 573 then (if i < 571 then decide (4 ≤ count567 b) else (if i < 572 then decide (1 ≤ count571 b) else decide (2 ≤ count571 b))) else (if i < 575 then (if i < 574 then decide (3 ≤ count571 b) else decide (4 ≤ count571 b)) else (if i < 576 then decide (5 ≤ count571 b) else decide (6 ≤ count571 b)))))) else (if i < 591 then (if i < 584 then (if i < 580 then (if i < 578 then decide (7 ≤ count571 b) else (if i < 579 then decide (8 ≤ count571 b) else decide (1 ≤ count579 b))) else (if i < 582 then (if i < 581 then decide (2 ≤ count579 b) else decide (3 ≤ count579 b)) else (if i < 583 then decide (4 ≤ count579 b) else decide (5 ≤ count579 b)))) else (if i < 587 then (if i < 585 then decide (6 ≤ count579 b) else (if i < 586 then decide (7 ≤ count579 b) else decide (8 ≤ count579 b))) else (if i < 589 then (if i < 588 then decide (9 ≤ count579 b) else decide (10 ≤ count579 b)) else (if i < 590 then decide (11 ≤ count579 b) else decide (12 ≤ count579 b))))) else (if i < 598 then (if i < 594 then (if i < 592 then decide (13 ≤ count579 b) else (if i < 593 then decide (14 ≤ count579 b) else decide (15 ≤ count579 b))) else (if i < 596 then (if i < 595 then decide (1 ≤ count594 b) else decide (2 ≤ count594 b)) else (if i < 597 then decide (3 ≤ count594 b) else decide (4 ≤ count594 b)))) else (if i < 601 then (if i < 599 then decide (5 ≤ count594 b) else (if i < 600 then decide (6 ≤ count594 b) else decide (7 ≤ count594 b))) else (if i < 603 then (if i < 602 then decide (8 ≤ count594 b) else decide (9 ≤ count594 b)) else (if i < 604 then decide (10 ≤ count594 b) else decide (11 ≤ count594 b))))))) else (if i < 632 then (if i < 618 then (if i < 611 then (if i < 608 then (if i < 606 then decide (12 ≤ count594 b) else (if i < 607 then decide (13 ≤ count594 b) else decide (14 ≤ count594 b))) else (if i < 609 then decide (15 ≤ count594 b) else (if i < 610 then decide (16 ≤ count594 b) else decide (17 ≤ count594 b)))) else (if i < 614 then (if i < 612 then decide (18 ≤ count594 b) else (if i < 613 then decide (19 ≤ count594 b) else decide (20 ≤ count594 b))) else (if i < 616 then (if i < 615 then decide (21 ≤ count594 b) else decide (22 ≤ count594 b)) else (if i < 617 then decide (23 ≤ count594 b) else decide (24 ≤ count594 b))))) else (if i < 625 then (if i < 621 then (if i < 619 then decide (25 ≤ count594 b) else (if i < 620 then decide (26 ≤ count594 b) else decide (27 ≤ count594 b))) else (if i < 623 then (if i < 622 then decide (28 ≤ count594 b) else decide (29 ≤ count594 b)) else (if i < 624 then decide (1 ≤ count623 b) else decide (2 ≤ count623 b)))) else (if i < 628 then (if i < 626 then decide (1 ≤ count625 b) else (if i < 627 then decide (2 ≤ count625 b) else decide (3 ≤ count625 b))) else (if i < 630 then (if i < 629 then decide (1 ≤ count628 b) else decide (2 ≤ count628 b)) else (if i < 631 then decide (1 ≤ count630 b) else decide (2 ≤ count630 b)))))) else (if i < 646 then (if i < 639 then (if i < 635 then (if i < 633 then decide (1 ≤ count632 b) else (if i < 634 then decide (2 ≤ count632 b) else decide (3 ≤ count632 b))) else (if i < 637 then (if i < 636 then decide (4 ≤ count632 b) else decide (1 ≤ count636 b)) else (if i < 638 then decide (2 ≤ count636 b) else decide (3 ≤ count636 b)))) else (if i < 642 then (if i < 640 then decide (4 ≤ count636 b) else (if i < 641 then decide (5 ≤ count636 b) else decide (6 ≤ count636 b))) else (if i < 644 then (if i < 643 then decide (7 ≤ count636 b) else decide (1 ≤ count643 b)) else (if i < 645 then decide (2 ≤ count643 b) else decide (1 ≤ count645 b))))) else (if i < 653 then (if i < 649 then (if i < 647 then decide (2 ≤ count645 b) else (if i < 648 then decide (3 ≤ count645 b) else decide (1 ≤ count648 b))) else (if i < 651 then (if i < 650 then decide (2 ≤ count648 b) else decide (1 ≤ count650 b)) else (if i < 652 then decide (2 ≤ count650 b) else decide (1 ≤ count652 b)))) else (if i < 656 then (if i < 654 then decide (2 ≤ count652 b) else (if i < 655 then decide (3 ≤ count652 b) else decide (4 ≤ count652 b))) else (if i < 658 then (if i < 657 then decide (1 ≤ count656 b) else decide (2 ≤ count656 b)) else (if i < 659 then decide (3 ≤ count656 b) else decide (4 ≤ count656 b))))))))) else (if i < 770 then (if i < 715 then (if i < 687 then (if i < 673 then (if i < 666 then (if i < 663 then (if i < 661 then decide (5 ≤ count656 b) else (if i < 662 then decide (6 ≤ count656 b) else decide (7 ≤ count656 b))) else (if i < 664 then decide (1 ≤ count663 b) else (if i < 665 then decide (2 ≤ count663 b) else decide (3 ≤ count663 b)))) else (if i < 669 then (if i < 667 then decide (4 ≤ count663 b) else (if i < 668 then decide (5 ≤ count663 b) else decide (6 ≤ count663 b))) else (if i < 671 then (if i < 670 then decide (7 ≤ count663 b) else decide (8 ≤ count663 b)) else (if i < 672 then decide (9 ≤ count663 b) else decide (10 ≤ count663 b))))) else (if i < 680 then (if i < 676 then (if i < 674 then decide (11 ≤ count663 b) else (if i < 675 then decide (12 ≤ count663 b) else decide (13 ≤ count663 b))) else (if i < 678 then (if i < 677 then decide (14 ≤ count663 b) else decide (1 ≤ count677 b)) else (if i < 679 then decide (2 ≤ count677 b) else decide (1 ≤ count679 b)))) else (if i < 683 then (if i < 681 then decide (2 ≤ count679 b) else (if i < 682 then decide (3 ≤ count679 b) else decide (1 ≤ count682 b))) else (if i < 685 then (if i < 684 then decide (2 ≤ count682 b) else decide (1 ≤ count684 b)) else (if i < 686 then decide (2 ≤ count684 b) else decide (1 ≤ count686 b)))))) else (if i < 701 then (if i < 694 then (if i < 690 then (if i < 688 then decide (2 ≤ count686 b) else (if i < 689 then decide (3 ≤ count686 b) else decide (4 ≤ count686 b))) else (if i < 692 then (if i < 691 then decide (1 ≤ count690 b) else decide (2 ≤ count690 b)) else (if i < 693 then decide (3 ≤ count690 b) else decide (4 ≤ count690 b)))) else (if i < 697 then (if i < 695 then decide (5 ≤ count690 b) else (if i < 696 then decide (6 ≤ count690 b) else decide (7 ≤ count690 b))) else (if i < 699 then (if i < 698 then decide (1 ≤ count697 b) else decide (2 ≤ count697 b)) else (if i < 700 then decide (1 ≤ count699 b) else decide (2 ≤ count699 b))))) else (if i < 708 then (if i < 704 then (if i < 702 then decide (1 ≤ count701 b) else (if i < 703 then decide (2 ≤ count701 b) else decide (3 ≤ count701 b))) else (if i < 706 then (if i < 705 then decide (4 ≤ count701 b) else decide (1 ≤ count705 b)) else (if i < 707 then decide (2 ≤ count705 b) else decide (1 ≤ count707 b)))) else (if i < 711 then (if i < 709 then decide (2 ≤ count707 b) else (if i < 710 then decide (1 ≤ count709 b) else decide (2 ≤ count709 b))) else (if i < 713 then (if i < 712 then decide (3 ≤ count709 b) else decide (4 ≤ count709 b)) else (if i < 714 then decide (1 ≤ count713 b) else decide (2 ≤ count713 b))))))) else (if i < 742 then (if i < 728 then (if i < 721 then (if i < 718 then (if i < 716 then decide (3 ≤ count713 b) else (if i < 717 then decide (4 ≤ count713 b) else decide (5 ≤ count713 b))) else (if i < 719 then decide (6 ≤ count713 b) else (if i < 720 then decide (7 ≤ count713 b) else decide (8 ≤ count713 b)))) else (if i < 724 then (if i < 722 then decide (1 ≤ count721 b) else (if i < 723 then decide (2 ≤ count721 b) else decide (3 ≤ count721 b))) else (if i < 726 then (if i < 725 then decide (4 ≤ count721 b) else decide (5 ≤ count721 b)) else (if i < 727 then decide (6 ≤ count721 b) else decide (7 ≤ count721 b))))) else (if i < 735 then (if i < 731 then (if i < 729 then decide (8 ≤ count721 b) else (if i < 730 then decide (9 ≤ count721 b) else decide (10 ≤ count721 b))) else (if i < 733 then (if i < 732 then decide (11 ≤ count721 b) else decide (12 ≤ count721 b)) else (if i < 734 then decide (13 ≤ count721 b) else decide (14 ≤ count721 b)))) else (if i < 738 then (if i < 736 then decide (15 ≤ count721 b) else (if i < 737 then decide (1 ≤ count736 b) else decide (2 ≤ count736 b))) else (if i < 740 then (if i < 739 then decide (3 ≤ count736 b) else decide (4 ≤ count736 b)) else (if i < 741 then decide (5 ≤ count736 b) else decide (6 ≤ count736 b)))))) else (if i < 756 then (if i < 749 then (if i < 745 then (if i < 743 then decide (7 ≤ count736 b) else (if i < 744 then decide (8 ≤ count736 b) else decide (9 ≤ count736 b))) else (if i < 747 then (if i < 746 then decide (10 ≤ count736 b) else decide (11 ≤ count736 b)) else (if i < 748 then decide (12 ≤ count736 b) else decide (13 ≤ count736 b)))) else (if i < 752 then (if i < 750 then decide (14 ≤ count736 b) else (if i < 751 then decide (15 ≤ count736 b) else decide (16 ≤ count736 b))) else (if i < 754 then (if i < 753 then decide (17 ≤ count736 b) else decide (18 ≤ count736 b)) else (if i < 755 then decide (19 ≤ count736 b) else decide (20 ≤ count736 b))))) else (if i < 763 then (if i < 759 then (if i < 757 then decide (21 ≤ count736 b) else (if i < 758 then decide (22 ≤ count736 b) else decide (23 ≤ count736 b))) else (if i < 761 then (if i < 760 then decide (24 ≤ count736 b) else decide (25 ≤ count736 b)) else (if i < 762 then decide (26 ≤ count736 b) else decide (27 ≤ count736 b)))) else (if i < 766 then (if i < 764 then decide (28 ≤ count736 b) else (if i < 765 then decide (29 ≤ count736 b) else decide (1 ≤ count765 b))) else (if i < 768 then (if i < 767 then decide (2 ≤ count765 b) else decide (3 ≤ count765 b)) else (if i < 769 then decide (4 ≤ count765 b) else decide (5 ≤ count765 b)))))))) else (if i < 825 then (if i < 797 then (if i < 783 then (if i < 776 then (if i < 773 then (if i < 771 then decide (6 ≤ count765 b) else (if i < 772 then decide (7 ≤ count765 b) else decide (8 ≤ count765 b))) else (if i < 774 then decide (9 ≤ count765 b) else (if i < 775 then decide (10 ≤ count765 b) else decide (11 ≤ count765 b)))) else (if i < 779 then (if i < 777 then decide (12 ≤ count765 b) else (if i < 778 then decide (13 ≤ count765 b) else decide (14 ≤ count765 b))) else (if i < 781 then (if i < 780 then decide (15 ≤ count765 b) else decide (16 ≤ count765 b)) else (if i < 782 then decide (17 ≤ count765 b) else decide (18 ≤ count765 b))))) else (if i < 790 then (if i < 786 then (if i < 784 then decide (19 ≤ count765 b) else (if i < 785 then decide (20 ≤ count765 b) else decide (21 ≤ count765 b))) else (if i < 788 then (if i < 787 then decide (22 ≤ count765 b) else decide (23 ≤ count765 b)) else (if i < 789 then decide (24 ≤ count765 b) else decide (25 ≤ count765 b)))) else (if i < 793 then (if i < 791 then decide (26 ≤ count765 b) else (if i < 792 then decide (27 ≤ count765 b) else decide (28 ≤ count765 b))) else (if i < 795 then (if i < 794 then decide (29 ≤ count765 b) else decide (30 ≤ count765 b)) else (if i < 796 then decide (31 ≤ count765 b) else decide (32 ≤ count765 b)))))) else (if i < 811 then (if i < 804 then (if i < 800 then (if i < 798 then decide (33 ≤ count765 b) else (if i < 799 then decide (34 ≤ count765 b) else decide (35 ≤ count765 b))) else (if i < 802 then (if i < 801 then decide (36 ≤ count765 b) else decide (37 ≤ count765 b)) else (if i < 803 then decide (38 ≤ count765 b) else decide (39 ≤ count765 b)))) else (if i < 807 then (if i < 805 then decide (40 ≤ count765 b) else (if i < 806 then decide (41 ≤ count765 b) else decide (42 ≤ count765 b))) else (if i < 809 then (if i < 808 then decide (1 ≤ count807 b) else decide (2 ≤ count807 b)) else (if i < 810 then decide (1 ≤ count809 b) else decide (2 ≤ count809 b))))) else (if i < 818 then (if i < 814 then (if i < 812 then decide (3 ≤ count809 b) else (if i < 813 then decide (1 ≤ count812 b) else decide (2 ≤ count812 b))) else (if i < 816 then (if i < 815 then decide (1 ≤ count814 b) else decide (2 ≤ count814 b)) else (if i < 817 then decide (1 ≤ count816 b) else decide (2 ≤ count816 b)))) else (if i < 821 then (if i < 819 then decide (3 ≤ count816 b) else (if i < 820 then decide (4 ≤ count816 b) else decide (1 ≤ count820 b))) else (if i < 823 then (if i < 822 then decide (2 ≤ count820 b) else decide (3 ≤ count820 b)) else (if i < 824 then decide (4 ≤ count820 b) else decide (5 ≤ count820 b))))))) else (if i < 853 then (if i < 839 then (if i < 832 then (if i < 828 then (if i < 826 then decide (6 ≤ count820 b) else (if i < 827 then decide (7 ≤ count820 b) else decide (1 ≤ count827 b))) else (if i < 830 then (if i < 829 then decide (2 ≤ count827 b) else decide (1 ≤ count829 b)) else (if i < 831 then decide (2 ≤ count829 b) else decide (3 ≤ count829 b)))) else (if i < 835 then (if i < 833 then decide (1 ≤ count832 b) else (if i < 834 then decide (2 ≤ count832 b) else decide (1 ≤ count834 b))) else (if i < 837 then (if i < 836 then decide (2 ≤ count834 b) else decide (1 ≤ count836 b)) else (if i < 838 then decide (2 ≤ count836 b) else decide (3 ≤ count836 b))))) else (if i < 846 then (if i < 842 then (if i < 840 then decide (4 ≤ count836 b) else (if i < 841 then decide (1 ≤ count840 b) else decide (2 ≤ count840 b))) else (if i < 844 then (if i < 843 then decide (3 ≤ count840 b) else decide (4 ≤ count840 b)) else (if i < 845 then decide (5 ≤ count840 b) else decide (6 ≤ count840 b)))) else (if i < 849 then (if i < 847 then decide (7 ≤ count840 b) else (if i < 848 then decide (1 ≤ count847 b) else decide (2 ≤ count847 b))) else (if i < 851 then (if i < 850 then decide (3 ≤ count847 b) else decide (4 ≤ count847 b)) else (if i < 852 then decide (5 ≤ count847 b) else decide (6 ≤ count847 b)))))) else (if i < 867 then (if i < 860 then (if i < 856 then (if i < 854 then decide (7 ≤ count847 b) else (if i < 855 then decide (8 ≤ count847 b) else decide (9 ≤ count847 b))) else (if i < 858 then (if i < 857 then decide (10 ≤ count847 b) else decide (11 ≤ count847 b)) else (if i < 859 then decide (12 ≤ count847 b) else decide (13 ≤ count847 b)))) else (if i < 863 then (if i < 861 then decide (14 ≤ count847 b) else (if i < 862 then decide (1 ≤ count861 b) else decide (2 ≤ count861 b))) else (if i < 865 then (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b)) else (if i < 866 then decide (3 ≤ count863 b) else decide (1 ≤ count866 b))))) else (if i < 874 then (if i < 870 then (if i < 868 then decide (2 ≤ count866 b) else (if i < 869 then decide (1 ≤ count868 b) else decide (2 ≤ count868 b))) else (if i < 872 then (if i < 871 then decide (1 ≤ count870 b) else decide (2 ≤ count870 b)) else (if i < 873 then decide (3 ≤ count870 b) else decide (4 ≤ count870 b)))) else (if i < 877 then (if i < 875 then decide (1 ≤ count874 b) else (if i < 876 then decide (2 ≤ count874 b) else decide (3 ≤ count874 b))) else (if i < 879 then (if i < 878 then decide (4 ≤ count874 b) else decide (5 ≤ count874 b)) else (if i < 880 then decide (6 ≤ count874 b) else decide (7 ≤ count874 b))))))))))) else (if i < 1322 then (if i < 1101 then (if i < 991 then (if i < 936 then (if i < 908 then (if i < 894 then (if i < 887 then (if i < 884 then (if i < 882 then decide (1 ≤ count881 b) else (if i < 883 then decide (2 ≤ count881 b) else decide (1 ≤ count883 b))) else (if i < 885 then decide (2 ≤ count883 b) else (if i < 886 then decide (1 ≤ count885 b) else decide (2 ≤ count885 b)))) else (if i < 890 then (if i < 888 then decide (3 ≤ count885 b) else (if i < 889 then decide (4 ≤ count885 b) else decide (1 ≤ count889 b))) else (if i < 892 then (if i < 891 then decide (2 ≤ count889 b) else decide (1 ≤ count891 b)) else (if i < 893 then decide (2 ≤ count891 b) else decide (1 ≤ count893 b))))) else (if i < 901 then (if i < 897 then (if i < 895 then decide (2 ≤ count893 b) else (if i < 896 then decide (3 ≤ count893 b) else decide (4 ≤ count893 b))) else (if i < 899 then (if i < 898 then decide (1 ≤ count897 b) else decide (2 ≤ count897 b)) else (if i < 900 then decide (3 ≤ count897 b) else decide (4 ≤ count897 b)))) else (if i < 904 then (if i < 902 then decide (5 ≤ count897 b) else (if i < 903 then decide (6 ≤ count897 b) else decide (7 ≤ count897 b))) else (if i < 906 then (if i < 905 then decide (8 ≤ count897 b) else decide (1 ≤ count905 b)) else (if i < 907 then decide (2 ≤ count905 b) else decide (3 ≤ count905 b)))))) else (if i < 922 then (if i < 915 then (if i < 911 then (if i < 909 then decide (4 ≤ count905 b) else (if i < 910 then decide (5 ≤ count905 b) else decide (6 ≤ count905 b))) else (if i < 913 then (if i < 912 then decide (7 ≤ count905 b) else decide (8 ≤ count905 b)) else (if i < 914 then decide (9 ≤ count905 b) else decide (10 ≤ count905 b)))) else (if i < 918 then (if i < 916 then decide (11 ≤ count905 b) else (if i < 917 then decide (12 ≤ count905 b) else decide (13 ≤ count905 b))) else (if i < 920 then (if i < 919 then decide (14 ≤ count905 b) else decide (15 ≤ count905 b)) else (if i < 921 then decide (1 ≤ count920 b) else decide (2 ≤ count920 b))))) else (if i < 929 then (if i < 925 then (if i < 923 then decide (3 ≤ count920 b) else (if i < 924 then decide (4 ≤ count920 b) else decide (5 ≤ count920 b))) else (if i < 927 then (if i < 926 then decide (6 ≤ count920 b) else decide (7 ≤ count920 b)) else (if i < 928 then decide (8 ≤ count920 b) else decide (9 ≤ count920 b)))) else (if i < 932 then (if i < 930 then decide (10 ≤ count920 b) else (if i < 931 then decide (11 ≤ count920 b) else decide (12 ≤ count920 b))) else (if i < 934 then (if i < 933 then decide (13 ≤ count920 b) else decide (14 ≤ count920 b)) else (if i < 935 then decide (15 ≤ count920 b) else decide (16 ≤ count920 b))))))) else (if i < 963 then (if i < 949 then (if i < 942 then (if i < 939 then (if i < 937 then decide (17 ≤ count920 b) else (if i < 938 then decide (18 ≤ count920 b) else decide (1 ≤ count938 b))) else (if i < 940 then decide (2 ≤ count938 b) else (if i < 941 then decide (1 ≤ count940 b) else decide (2 ≤ count940 b)))) else (if i < 945 then (if i < 943 then decide (3 ≤ count940 b) else (if i < 944 then decide (1 ≤ count943 b) else decide (2 ≤ count943 b))) else (if i < 947 then (if i < 946 then decide (1 ≤ count945 b) else decide (2 ≤ count945 b)) else (if i < 948 then decide (1 ≤ count947 b) else decide (2 ≤ count947 b))))) else (if i < 956 then (if i < 952 then (if i < 950 then decide (3 ≤ count947 b) else (if i < 951 then decide (4 ≤ count947 b) else decide (1 ≤ count951 b))) else (if i < 954 then (if i < 953 then decide (2 ≤ count951 b) else decide (3 ≤ count951 b)) else (if i < 955 then decide (4 ≤ count951 b) else decide (5 ≤ count951 b)))) else (if i < 959 then (if i < 957 then decide (6 ≤ count951 b) else (if i < 958 then decide (7 ≤ count951 b) else decide (1 ≤ count958 b))) else (if i < 961 then (if i < 960 then decide (2 ≤ count958 b) else decide (1 ≤ count960 b)) else (if i < 962 then decide (2 ≤ count960 b) else decide (3 ≤ count960 b)))))) else (if i < 977 then (if i < 970 then (if i < 966 then (if i < 964 then decide (1 ≤ count963 b) else (if i < 965 then decide (2 ≤ count963 b) else decide (1 ≤ count965 b))) else (if i < 968 then (if i < 967 then decide (2 ≤ count965 b) else decide (1 ≤ count967 b)) else (if i < 969 then decide (2 ≤ count967 b) else decide (3 ≤ count967 b)))) else (if i < 973 then (if i < 971 then decide (4 ≤ count967 b) else (if i < 972 then decide (1 ≤ count971 b) else decide (2 ≤ count971 b))) else (if i < 975 then (if i < 974 then decide (3 ≤ count971 b) else decide (4 ≤ count971 b)) else (if i < 976 then decide (5 ≤ count971 b) else decide (6 ≤ count971 b))))) else (if i < 984 then (if i < 980 then (if i < 978 then decide (7 ≤ count971 b) else (if i < 979 then decide (1 ≤ count978 b) else decide (2 ≤ count978 b))) else (if i < 982 then (if i < 981 then decide (3 ≤ count978 b) else decide (4 ≤ count978 b)) else (if i < 983 then decide (5 ≤ count978 b) else decide (6 ≤ count978 b)))) else (if i < 987 then (if i < 985 then decide (7 ≤ count978 b) else (if i < 986 then decide (8 ≤ count978 b) else decide (9 ≤ count978 b))) else (if i < 989 then (if i < 988 then decide (10 ≤ count978 b) else decide (11 ≤ count978 b)) else (if i < 990 then decide (12 ≤ count978 b) else decide (13 ≤ count978 b)))))))) else (if i < 1046 then (if i < 1018 then (if i < 1004 then (if i < 997 then (if i < 994 then (if i < 992 then decide (14 ≤ count978 b) else (if i < 993 then decide (1 ≤ count992 b) else decide (2 ≤ count992 b))) else (if i < 995 then decide (1 ≤ count994 b) else (if i < 996 then decide (2 ≤ count994 b) else decide (3 ≤ count994 b)))) else (if i < 1000 then (if i < 998 then decide (1 ≤ count997 b) else (if i < 999 then decide (2 ≤ count997 b) else decide (1 ≤ count999 b))) else (if i < 1002 then (if i < 1001 then decide (2 ≤ count999 b) else decide (1 ≤ count1001 b)) else (if i < 1003 then decide (2 ≤ count1001 b) else decide (3 ≤ count1001 b))))) else (if i < 1011 then (if i < 1007 then (if i < 1005 then decide (4 ≤ count1001 b) else (if i < 1006 then decide (1 ≤ count1005 b) else decide (2 ≤ count1005 b))) else (if i < 1009 then (if i < 1008 then decide (3 ≤ count1005 b) else decide (4 ≤ count1005 b)) else (if i < 1010 then decide (5 ≤ count1005 b) else decide (6 ≤ count1005 b)))) else (if i < 1014 then (if i < 1012 then decide (7 ≤ count1005 b) else (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b))) else (if i < 1016 then (if i < 1015 then decide (1 ≤ count1014 b) else decide (2 ≤ count1014 b)) else (if i < 1017 then decide (1 ≤ count1016 b) else decide (2 ≤ count1016 b)))))) else (if i < 1032 then (if i < 1025 then (if i < 1021 then (if i < 1019 then decide (3 ≤ count1016 b) else (if i < 1020 then decide (4 ≤ count1016 b) else decide (1 ≤ count1020 b))) else (if i < 1023 then (if i < 1022 then decide (2 ≤ count1020 b) else decide (1 ≤ count1022 b)) else (if i < 1024 then decide (2 ≤ count1022 b) else decide (1 ≤ count1024 b)))) else (if i < 1028 then (if i < 1026 then decide (2 ≤ count1024 b) else (if i < 1027 then decide (3 ≤ count1024 b) else decide (4 ≤ count1024 b))) else (if i < 1030 then (if i < 1029 then decide (1 ≤ count1028 b) else decide (2 ≤ count1028 b)) else (if i < 1031 then decide (3 ≤ count1028 b) else decide (4 ≤ count1028 b))))) else (if i < 1039 then (if i < 1035 then (if i < 1033 then decide (5 ≤ count1028 b) else (if i < 1034 then decide (6 ≤ count1028 b) else decide (7 ≤ count1028 b))) else (if i < 1037 then (if i < 1036 then decide (8 ≤ count1028 b) else decide (1 ≤ count1036 b)) else (if i < 1038 then decide (2 ≤ count1036 b) else decide (3 ≤ count1036 b)))) else (if i < 1042 then (if i < 1040 then decide (4 ≤ count1036 b) else (if i < 1041 then decide (5 ≤ count1036 b) else decide (6 ≤ count1036 b))) else (if i < 1044 then (if i < 1043 then decide (7 ≤ count1036 b) else decide (8 ≤ count1036 b)) else (if i < 1045 then decide (9 ≤ count1036 b) else decide (10 ≤ count1036 b))))))) else (if i < 1073 then (if i < 1059 then (if i < 1052 then (if i < 1049 then (if i < 1047 then decide (11 ≤ count1036 b) else (if i < 1048 then decide (12 ≤ count1036 b) else decide (13 ≤ count1036 b))) else (if i < 1050 then decide (14 ≤ count1036 b) else (if i < 1051 then decide (15 ≤ count1036 b) else decide (1 ≤ count1051 b)))) else (if i < 1055 then (if i < 1053 then decide (2 ≤ count1051 b) else (if i < 1054 then decide (3 ≤ count1051 b) else decide (4 ≤ count1051 b))) else (if i < 1057 then (if i < 1056 then decide (5 ≤ count1051 b) else decide (6 ≤ count1051 b)) else (if i < 1058 then decide (7 ≤ count1051 b) else decide (8 ≤ count1051 b))))) else (if i < 1066 then (if i < 1062 then (if i < 1060 then decide (9 ≤ count1051 b) else (if i < 1061 then decide (10 ≤ count1051 b) else decide (11 ≤ count1051 b))) else (if i < 1064 then (if i < 1063 then decide (12 ≤ count1051 b) else decide (13 ≤ count1051 b)) else (if i < 1065 then decide (14 ≤ count1051 b) else decide (15 ≤ count1051 b)))) else (if i < 1069 then (if i < 1067 then decide (16 ≤ count1051 b) else (if i < 1068 then decide (17 ≤ count1051 b) else decide (18 ≤ count1051 b))) else (if i < 1071 then (if i < 1070 then decide (1 ≤ count1069 b) else decide (2 ≤ count1069 b)) else (if i < 1072 then decide (3 ≤ count1069 b) else decide (4 ≤ count1069 b)))))) else (if i < 1087 then (if i < 1080 then (if i < 1076 then (if i < 1074 then decide (5 ≤ count1069 b) else (if i < 1075 then decide (6 ≤ count1069 b) else decide (7 ≤ count1069 b))) else (if i < 1078 then (if i < 1077 then decide (8 ≤ count1069 b) else decide (9 ≤ count1069 b)) else (if i < 1079 then decide (10 ≤ count1069 b) else decide (11 ≤ count1069 b)))) else (if i < 1083 then (if i < 1081 then decide (12 ≤ count1069 b) else (if i < 1082 then decide (13 ≤ count1069 b) else decide (14 ≤ count1069 b))) else (if i < 1085 then (if i < 1084 then decide (15 ≤ count1069 b) else decide (16 ≤ count1069 b)) else (if i < 1086 then decide (17 ≤ count1069 b) else decide (18 ≤ count1069 b))))) else (if i < 1094 then (if i < 1090 then (if i < 1088 then decide (1 ≤ count1087 b) else (if i < 1089 then decide (2 ≤ count1087 b) else decide (1 ≤ count1089 b))) else (if i < 1092 then (if i < 1091 then decide (2 ≤ count1089 b) else decide (3 ≤ count1089 b)) else (if i < 1093 then decide (1 ≤ count1092 b) else decide (2 ≤ count1092 b)))) else (if i < 1097 then (if i < 1095 then decide (1 ≤ count1094 b) else (if i < 1096 then decide (2 ≤ count1094 b) else decide (1 ≤ count1096 b))) else (if i < 1099 then (if i < 1098 then decide (2 ≤ count1096 b) else decide (3 ≤ count1096 b)) else (if i < 1100 then decide (4 ≤ count1096 b) else decide (1 ≤ count1100 b))))))))) else (if i < 1211 then (if i < 1156 then (if i < 1128 then (if i < 1114 then (if i < 1107 then (if i < 1104 then (if i < 1102 then decide (2 ≤ count1100 b) else (if i < 1103 then decide (3 ≤ count1100 b) else decide (4 ≤ count1100 b))) else (if i < 1105 then decide (5 ≤ count1100 b) else (if i < 1106 then decide (6 ≤ count1100 b) else decide (7 ≤ count1100 b)))) else (if i < 1110 then (if i < 1108 then decide (1 ≤ count1107 b) else (if i < 1109 then decide (2 ≤ count1107 b) else decide (1 ≤ count1109 b))) else (if i < 1112 then (if i < 1111 then decide (2 ≤ count1109 b) else decide (1 ≤ count1111 b)) else (if i < 1113 then decide (2 ≤ count1111 b) else decide (3 ≤ count1111 b))))) else (if i < 1121 then (if i < 1117 then (if i < 1115 then decide (4 ≤ count1111 b) else (if i < 1116 then decide (1 ≤ count1115 b) else decide (2 ≤ count1115 b))) else (if i < 1119 then (if i < 1118 then decide (1 ≤ count1117 b) else decide (2 ≤ count1117 b)) else (if i < 1120 then decide (1 ≤ count1119 b) else decide (2 ≤ count1119 b)))) else (if i < 1124 then (if i < 1122 then decide (3 ≤ count1119 b) else (if i < 1123 then decide (4 ≤ count1119 b) else decide (1 ≤ count1123 b))) else (if i < 1126 then (if i < 1125 then decide (2 ≤ count1123 b) else decide (3 ≤ count1123 b)) else (if i < 1127 then decide (4 ≤ count1123 b) else decide (5 ≤ count1123 b)))))) else (if i < 1142 then (if i < 1135 then (if i < 1131 then (if i < 1129 then decide (6 ≤ count1123 b) else (if i < 1130 then decide (7 ≤ count1123 b) else decide (8 ≤ count1123 b))) else (if i < 1133 then (if i < 1132 then decide (1 ≤ count1131 b) else decide (2 ≤ count1131 b)) else (if i < 1134 then decide (3 ≤ count1131 b) else decide (4 ≤ count1131 b)))) else (if i < 1138 then (if i < 1136 then decide (5 ≤ count1131 b) else (if i < 1137 then decide (6 ≤ count1131 b) else decide (7 ≤ count1131 b))) else (if i < 1140 then (if i < 1139 then decide (8 ≤ count1131 b) else decide (9 ≤ count1131 b)) else (if i < 1141 then decide (10 ≤ count1131 b) else decide (11 ≤ count1131 b))))) else (if i < 1149 then (if i < 1145 then (if i < 1143 then decide (12 ≤ count1131 b) else (if i < 1144 then decide (13 ≤ count1131 b) else decide (14 ≤ count1131 b))) else (if i < 1147 then (if i < 1146 then decide (15 ≤ count1131 b) else decide (1 ≤ count1146 b)) else (if i < 1148 then decide (2 ≤ count1146 b) else decide (1 ≤ count1148 b)))) else (if i < 1152 then (if i < 1150 then decide (2 ≤ count1148 b) else (if i < 1151 then decide (1 ≤ count1150 b) else decide (2 ≤ count1150 b))) else (if i < 1154 then (if i < 1153 then decide (3 ≤ count1150 b) else decide (4 ≤ count1150 b)) else (if i < 1155 then decide (1 ≤ count1154 b) else decide (2 ≤ count1154 b))))))) else (if i < 1183 then (if i < 1169 then (if i < 1162 then (if i < 1159 then (if i < 1157 then decide (1 ≤ count1156 b) else (if i < 1158 then decide (2 ≤ count1156 b) else decide (1 ≤ count1158 b))) else (if i < 1160 then decide (2 ≤ count1158 b) else (if i < 1161 then decide (3 ≤ count1158 b) else decide (4 ≤ count1158 b)))) else (if i < 1165 then (if i < 1163 then decide (1 ≤ count1162 b) else (if i < 1164 then decide (2 ≤ count1162 b) else decide (3 ≤ count1162 b))) else (if i < 1167 then (if i < 1166 then decide (4 ≤ count1162 b) else decide (5 ≤ count1162 b)) else (if i < 1168 then decide (6 ≤ count1162 b) else decide (7 ≤ count1162 b))))) else (if i < 1176 then (if i < 1172 then (if i < 1170 then decide (8 ≤ count1162 b) else (if i < 1171 then decide (1 ≤ count1170 b) else decide (2 ≤ count1170 b))) else (if i < 1174 then (if i < 1173 then decide (1 ≤ count1172 b) else decide (2 ≤ count1172 b)) else (if i < 1175 then decide (1 ≤ count1174 b) else decide (2 ≤ count1174 b)))) else (if i < 1179 then (if i < 1177 then decide (3 ≤ count1174 b) else (if i < 1178 then decide (4 ≤ count1174 b) else decide (1 ≤ count1178 b))) else (if i < 1181 then (if i < 1180 then decide (2 ≤ count1178 b) else decide (1 ≤ count1180 b)) else (if i < 1182 then decide (2 ≤ count1180 b) else decide (1 ≤ count1182 b)))))) else (if i < 1197 then (if i < 1190 then (if i < 1186 then (if i < 1184 then decide (2 ≤ count1182 b) else (if i < 1185 then decide (3 ≤ count1182 b) else decide (4 ≤ count1182 b))) else (if i < 1188 then (if i < 1187 then decide (1 ≤ count1186 b) else decide (2 ≤ count1186 b)) else (if i < 1189 then decide (3 ≤ count1186 b) else decide (4 ≤ count1186 b)))) else (if i < 1193 then (if i < 1191 then decide (5 ≤ count1186 b) else (if i < 1192 then decide (6 ≤ count1186 b) else decide (7 ≤ count1186 b))) else (if i < 1195 then (if i < 1194 then decide (8 ≤ count1186 b) else decide (1 ≤ count1194 b)) else (if i < 1196 then decide (2 ≤ count1194 b) else decide (3 ≤ count1194 b))))) else (if i < 1204 then (if i < 1200 then (if i < 1198 then decide (4 ≤ count1194 b) else (if i < 1199 then decide (5 ≤ count1194 b) else decide (6 ≤ count1194 b))) else (if i < 1202 then (if i < 1201 then decide (7 ≤ count1194 b) else decide (8 ≤ count1194 b)) else (if i < 1203 then decide (9 ≤ count1194 b) else decide (10 ≤ count1194 b)))) else (if i < 1207 then (if i < 1205 then decide (11 ≤ count1194 b) else (if i < 1206 then decide (12 ≤ count1194 b) else decide (13 ≤ count1194 b))) else (if i < 1209 then (if i < 1208 then decide (14 ≤ count1194 b) else decide (15 ≤ count1194 b)) else (if i < 1210 then decide (16 ≤ count1194 b) else decide (1 ≤ count1210 b)))))))) else (if i < 1266 then (if i < 1238 then (if i < 1224 then (if i < 1217 then (if i < 1214 then (if i < 1212 then decide (2 ≤ count1210 b) else (if i < 1213 then decide (3 ≤ count1210 b) else decide (4 ≤ count1210 b))) else (if i < 1215 then decide (5 ≤ count1210 b) else (if i < 1216 then decide (6 ≤ count1210 b) else decide (7 ≤ count1210 b)))) else (if i < 1220 then (if i < 1218 then decide (8 ≤ count1210 b) else (if i < 1219 then decide (9 ≤ count1210 b) else decide (10 ≤ count1210 b))) else (if i < 1222 then (if i < 1221 then decide (11 ≤ count1210 b) else decide (12 ≤ count1210 b)) else (if i < 1223 then decide (13 ≤ count1210 b) else decide (14 ≤ count1210 b))))) else (if i < 1231 then (if i < 1227 then (if i < 1225 then decide (15 ≤ count1210 b) else (if i < 1226 then decide (16 ≤ count1210 b) else decide (17 ≤ count1210 b))) else (if i < 1229 then (if i < 1228 then decide (18 ≤ count1210 b) else decide (19 ≤ count1210 b)) else (if i < 1230 then decide (20 ≤ count1210 b) else decide (21 ≤ count1210 b)))) else (if i < 1234 then (if i < 1232 then decide (22 ≤ count1210 b) else (if i < 1233 then decide (23 ≤ count1210 b) else decide (24 ≤ count1210 b))) else (if i < 1236 then (if i < 1235 then decide (25 ≤ count1210 b) else decide (26 ≤ count1210 b)) else (if i < 1237 then decide (27 ≤ count1210 b) else decide (28 ≤ count1210 b)))))) else (if i < 1252 then (if i < 1245 then (if i < 1241 then (if i < 1239 then decide (29 ≤ count1210 b) else (if i < 1240 then decide (30 ≤ count1210 b) else decide (31 ≤ count1210 b))) else (if i < 1243 then (if i < 1242 then decide (1 ≤ count1241 b) else decide (2 ≤ count1241 b)) else (if i < 1244 then decide (1 ≤ count1243 b) else decide (2 ≤ count1243 b)))) else (if i < 1248 then (if i < 1246 then decide (1 ≤ count1245 b) else (if i < 1247 then decide (2 ≤ count1245 b) else decide (3 ≤ count1245 b))) else (if i < 1250 then (if i < 1249 then decide (4 ≤ count1245 b) else decide (1 ≤ count1249 b)) else (if i < 1251 then decide (2 ≤ count1249 b) else decide (1 ≤ count1251 b))))) else (if i < 1259 then (if i < 1255 then (if i < 1253 then decide (2 ≤ count1251 b) else (if i < 1254 then decide (1 ≤ count1253 b) else decide (2 ≤ count1253 b))) else (if i < 1257 then (if i < 1256 then decide (3 ≤ count1253 b) else decide (4 ≤ count1253 b)) else (if i < 1258 then decide (1 ≤ count1257 b) else decide (2 ≤ count1257 b)))) else (if i < 1262 then (if i < 1260 then decide (3 ≤ count1257 b) else (if i < 1261 then decide (4 ≤ count1257 b) else decide (5 ≤ count1257 b))) else (if i < 1264 then (if i < 1263 then decide (6 ≤ count1257 b) else decide (7 ≤ count1257 b)) else (if i < 1265 then decide (8 ≤ count1257 b) else decide (1 ≤ count1265 b))))))) else (if i < 1294 then (if i < 1280 then (if i < 1273 then (if i < 1269 then (if i < 1267 then decide (2 ≤ count1265 b) else (if i < 1268 then decide (1 ≤ count1267 b) else decide (2 ≤ count1267 b))) else (if i < 1271 then (if i < 1270 then decide (1 ≤ count1269 b) else decide (2 ≤ count1269 b)) else (if i < 1272 then decide (3 ≤ count1269 b) else decide (4 ≤ count1269 b)))) else (if i < 1276 then (if i < 1274 then decide (1 ≤ count1273 b) else (if i < 1275 then decide (2 ≤ count1273 b) else decide (1 ≤ count1275 b))) else (if i < 1278 then (if i < 1277 then decide (2 ≤ count1275 b) else decide (1 ≤ count1277 b)) else (if i < 1279 then decide (2 ≤ count1277 b) else decide (3 ≤ count1277 b))))) else (if i < 1287 then (if i < 1283 then (if i < 1281 then decide (4 ≤ count1277 b) else (if i < 1282 then decide (1 ≤ count1281 b) else decide (2 ≤ count1281 b))) else (if i < 1285 then (if i < 1284 then decide (3 ≤ count1281 b) else decide (4 ≤ count1281 b)) else (if i < 1286 then decide (5 ≤ count1281 b) else decide (6 ≤ count1281 b)))) else (if i < 1290 then (if i < 1288 then decide (7 ≤ count1281 b) else (if i < 1289 then decide (8 ≤ count1281 b) else decide (1 ≤ count1289 b))) else (if i < 1292 then (if i < 1291 then decide (2 ≤ count1289 b) else decide (3 ≤ count1289 b)) else (if i < 1293 then decide (4 ≤ count1289 b) else decide (5 ≤ count1289 b)))))) else (if i < 1308 then (if i < 1301 then (if i < 1297 then (if i < 1295 then decide (6 ≤ count1289 b) else (if i < 1296 then decide (7 ≤ count1289 b) else decide (8 ≤ count1289 b))) else (if i < 1299 then (if i < 1298 then decide (9 ≤ count1289 b) else decide (10 ≤ count1289 b)) else (if i < 1300 then decide (11 ≤ count1289 b) else decide (12 ≤ count1289 b)))) else (if i < 1304 then (if i < 1302 then decide (13 ≤ count1289 b) else (if i < 1303 then decide (14 ≤ count1289 b) else decide (15 ≤ count1289 b))) else (if i < 1306 then (if i < 1305 then decide (16 ≤ count1289 b) else decide (1 ≤ count1305 b)) else (if i < 1307 then decide (2 ≤ count1305 b) else decide (1 ≤ count1307 b))))) else (if i < 1315 then (if i < 1311 then (if i < 1309 then decide (2 ≤ count1307 b) else (if i < 1310 then decide (1 ≤ count1309 b) else decide (2 ≤ count1309 b))) else (if i < 1313 then (if i < 1312 then decide (3 ≤ count1309 b) else decide (4 ≤ count1309 b)) else (if i < 1314 then decide (1 ≤ count1313 b) else decide (2 ≤ count1313 b)))) else (if i < 1318 then (if i < 1316 then decide (1 ≤ count1315 b) else (if i < 1317 then decide (2 ≤ count1315 b) else decide (1 ≤ count1317 b))) else (if i < 1320 then (if i < 1319 then decide (2 ≤ count1317 b) else decide (3 ≤ count1317 b)) else (if i < 1321 then decide (4 ≤ count1317 b) else decide (1 ≤ count1321 b)))))))))) else (if i < 1542 then (if i < 1432 then (if i < 1377 then (if i < 1349 then (if i < 1335 then (if i < 1328 then (if i < 1325 then (if i < 1323 then decide (2 ≤ count1321 b) else (if i < 1324 then decide (3 ≤ count1321 b) else decide (4 ≤ count1321 b))) else (if i < 1326 then decide (5 ≤ count1321 b) else (if i < 1327 then decide (6 ≤ count1321 b) else decide (7 ≤ count1321 b)))) else (if i < 1331 then (if i < 1329 then decide (8 ≤ count1321 b) else (if i < 1330 then decide (1 ≤ count1329 b) else decide (2 ≤ count1329 b))) else (if i < 1333 then (if i < 1332 then decide (1 ≤ count1331 b) else decide (2 ≤ count1331 b)) else (if i < 1334 then decide (1 ≤ count1333 b) else decide (2 ≤ count1333 b))))) else (if i < 1342 then (if i < 1338 then (if i < 1336 then decide (3 ≤ count1333 b) else (if i < 1337 then decide (4 ≤ count1333 b) else decide (1 ≤ count1337 b))) else (if i < 1340 then (if i < 1339 then decide (2 ≤ count1337 b) else decide (1 ≤ count1339 b)) else (if i < 1341 then decide (2 ≤ count1339 b) else decide (1 ≤ count1341 b)))) else (if i < 1345 then (if i < 1343 then decide (2 ≤ count1341 b) else (if i < 1344 then decide (3 ≤ count1341 b) else decide (4 ≤ count1341 b))) else (if i < 1347 then (if i < 1346 then decide (1 ≤ count1345 b) else decide (2 ≤ count1345 b)) else (if i < 1348 then decide (3 ≤ count1345 b) else decide (4 ≤ count1345 b)))))) else (if i < 1363 then (if i < 1356 then (if i < 1352 then (if i < 1350 then decide (5 ≤ count1345 b) else (if i < 1351 then decide (6 ≤ count1345 b) else decide (7 ≤ count1345 b))) else (if i < 1354 then (if i < 1353 then decide (8 ≤ count1345 b) else decide (1 ≤ count1353 b)) else (if i < 1355 then decide (2 ≤ count1353 b) else decide (3 ≤ count1353 b)))) else (if i < 1359 then (if i < 1357 then decide (4 ≤ count1353 b) else (if i < 1358 then decide (5 ≤ count1353 b) else decide (6 ≤ count1353 b))) else (if i < 1361 then (if i < 1360 then decide (7 ≤ count1353 b) else decide (8 ≤ count1353 b)) else (if i < 1362 then decide (9 ≤ count1353 b) else decide (10 ≤ count1353 b))))) else (if i < 1370 then (if i < 1366 then (if i < 1364 then decide (11 ≤ count1353 b) else (if i < 1365 then decide (12 ≤ count1353 b) else decide (13 ≤ count1353 b))) else (if i < 1368 then (if i < 1367 then decide (14 ≤ count1353 b) else decide (15 ≤ count1353 b)) else (if i < 1369 then decide (16 ≤ count1353 b) else decide (1 ≤ count1369 b)))) else (if i < 1373 then (if i < 1371 then decide (2 ≤ count1369 b) else (if i < 1372 then decide (3 ≤ count1369 b) else decide (4 ≤ count1369 b))) else (if i < 1375 then (if i < 1374 then decide (5 ≤ count1369 b) else decide (6 ≤ count1369 b)) else (if i < 1376 then decide (7 ≤ count1369 b) else decide (8 ≤ count1369 b))))))) else (if i < 1404 then (if i < 1390 then (if i < 1383 then (if i < 1380 then (if i < 1378 then decide (9 ≤ count1369 b) else (if i < 1379 then decide (10 ≤ count1369 b) else decide (11 ≤ count1369 b))) else (if i < 1381 then decide (12 ≤ count1369 b) else (if i < 1382 then decide (13 ≤ count1369 b) else decide (14 ≤ count1369 b)))) else (if i < 1386 then (if i < 1384 then decide (15 ≤ count1369 b) else (if i < 1385 then decide (16 ≤ count1369 b) else decide (17 ≤ count1369 b))) else (if i < 1388 then (if i < 1387 then decide (18 ≤ count1369 b) else decide (19 ≤ count1369 b)) else (if i < 1389 then decide (20 ≤ count1369 b) else decide (21 ≤ count1369 b))))) else (if i < 1397 then (if i < 1393 then (if i < 1391 then decide (22 ≤ count1369 b) else (if i < 1392 then decide (23 ≤ count1369 b) else decide (24 ≤ count1369 b))) else (if i < 1395 then (if i < 1394 then decide (25 ≤ count1369 b) else decide (26 ≤ count1369 b)) else (if i < 1396 then decide (27 ≤ count1369 b) else decide (28 ≤ count1369 b)))) else (if i < 1400 then (if i < 1398 then decide (29 ≤ count1369 b) else (if i < 1399 then decide (30 ≤ count1369 b) else decide (31 ≤ count1369 b))) else (if i < 1402 then (if i < 1401 then decide (32 ≤ count1369 b) else decide (1 ≤ count1401 b)) else (if i < 1403 then decide (2 ≤ count1401 b) else decide (3 ≤ count1401 b)))))) else (if i < 1418 then (if i < 1411 then (if i < 1407 then (if i < 1405 then decide (4 ≤ count1401 b) else (if i < 1406 then decide (5 ≤ count1401 b) else decide (6 ≤ count1401 b))) else (if i < 1409 then (if i < 1408 then decide (7 ≤ count1401 b) else decide (8 ≤ count1401 b)) else (if i < 1410 then decide (9 ≤ count1401 b) else decide (10 ≤ count1401 b)))) else (if i < 1414 then (if i < 1412 then decide (11 ≤ count1401 b) else (if i < 1413 then decide (12 ≤ count1401 b) else decide (13 ≤ count1401 b))) else (if i < 1416 then (if i < 1415 then decide (14 ≤ count1401 b) else decide (15 ≤ count1401 b)) else (if i < 1417 then decide (16 ≤ count1401 b) else decide (17 ≤ count1401 b))))) else (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (18 ≤ count1401 b) else (if i < 1420 then decide (19 ≤ count1401 b) else decide (20 ≤ count1401 b))) else (if i < 1423 then (if i < 1422 then decide (21 ≤ count1401 b) else decide (22 ≤ count1401 b)) else (if i < 1424 then decide (23 ≤ count1401 b) else decide (24 ≤ count1401 b)))) else (if i < 1428 then (if i < 1426 then decide (25 ≤ count1401 b) else (if i < 1427 then decide (26 ≤ count1401 b) else decide (27 ≤ count1401 b))) else (if i < 1430 then (if i < 1429 then decide (28 ≤ count1401 b) else decide (29 ≤ count1401 b)) else (if i < 1431 then decide (30 ≤ count1401 b) else decide (31 ≤ count1401 b)))))))) else (if i < 1487 then (if i < 1459 then (if i < 1445 then (if i < 1438 then (if i < 1435 then (if i < 1433 then decide (32 ≤ count1401 b) else (if i < 1434 then decide (33 ≤ count1401 b) else decide (34 ≤ count1401 b))) else (if i < 1436 then decide (35 ≤ count1401 b) else (if i < 1437 then decide (36 ≤ count1401 b) else decide (37 ≤ count1401 b)))) else (if i < 1441 then (if i < 1439 then decide (38 ≤ count1401 b) else (if i < 1440 then decide (39 ≤ count1401 b) else decide (40 ≤ count1401 b))) else (if i < 1443 then (if i < 1442 then decide (41 ≤ count1401 b) else decide (42 ≤ count1401 b)) else (if i < 1444 then decide (1 ≤ count1443 b) else decide (2 ≤ count1443 b))))) else (if i < 1452 then (if i < 1448 then (if i < 1446 then decide (1 ≤ count1445 b) else (if i < 1447 then decide (2 ≤ count1445 b) else decide (3 ≤ count1445 b))) else (if i < 1450 then (if i < 1449 then decide (1 ≤ count1448 b) else decide (2 ≤ count1448 b)) else (if i < 1451 then decide (1 ≤ count1450 b) else decide (2 ≤ count1450 b)))) else (if i < 1455 then (if i < 1453 then decide (1 ≤ count1452 b) else (if i < 1454 then decide (2 ≤ count1452 b) else decide (3 ≤ count1452 b))) else (if i < 1457 then (if i < 1456 then decide (4 ≤ count1452 b) else decide (1 ≤ count1456 b)) else (if i < 1458 then decide (2 ≤ count1456 b) else decide (3 ≤ count1456 b)))))) else (if i < 1473 then (if i < 1466 then (if i < 1462 then (if i < 1460 then decide (4 ≤ count1456 b) else (if i < 1461 then decide (5 ≤ count1456 b) else decide (6 ≤ count1456 b))) else (if i < 1464 then (if i < 1463 then decide (7 ≤ count1456 b) else decide (1 ≤ count1463 b)) else (if i < 1465 then decide (2 ≤ count1463 b) else decide (1 ≤ count1465 b)))) else (if i < 1469 then (if i < 1467 then decide (2 ≤ count1465 b) else (if i < 1468 then decide (1 ≤ count1467 b) else decide (2 ≤ count1467 b))) else (if i < 1471 then (if i < 1470 then decide (3 ≤ count1467 b) else decide (4 ≤ count1467 b)) else (if i < 1472 then decide (1 ≤ count1471 b) else decide (2 ≤ count1471 b))))) else (if i < 1480 then (if i < 1476 then (if i < 1474 then decide (1 ≤ count1473 b) else (if i < 1475 then decide (2 ≤ count1473 b) else decide (1 ≤ count1475 b))) else (if i < 1478 then (if i < 1477 then decide (2 ≤ count1475 b) else decide (3 ≤ count1475 b)) else (if i < 1479 then decide (4 ≤ count1475 b) else decide (1 ≤ count1479 b)))) else (if i < 1483 then (if i < 1481 then decide (2 ≤ count1479 b) else (if i < 1482 then decide (3 ≤ count1479 b) else decide (4 ≤ count1479 b))) else (if i < 1485 then (if i < 1484 then decide (5 ≤ count1479 b) else decide (6 ≤ count1479 b)) else (if i < 1486 then decide (7 ≤ count1479 b) else decide (8 ≤ count1479 b))))))) else (if i < 1514 then (if i < 1500 then (if i < 1493 then (if i < 1490 then (if i < 1488 then decide (1 ≤ count1487 b) else (if i < 1489 then decide (2 ≤ count1487 b) else decide (3 ≤ count1487 b))) else (if i < 1491 then decide (4 ≤ count1487 b) else (if i < 1492 then decide (5 ≤ count1487 b) else decide (6 ≤ count1487 b)))) else (if i < 1496 then (if i < 1494 then decide (7 ≤ count1487 b) else (if i < 1495 then decide (8 ≤ count1487 b) else decide (9 ≤ count1487 b))) else (if i < 1498 then (if i < 1497 then decide (10 ≤ count1487 b) else decide (11 ≤ count1487 b)) else (if i < 1499 then decide (12 ≤ count1487 b) else decide (13 ≤ count1487 b))))) else (if i < 1507 then (if i < 1503 then (if i < 1501 then decide (14 ≤ count1487 b) else (if i < 1502 then decide (15 ≤ count1487 b) else decide (1 ≤ count1502 b))) else (if i < 1505 then (if i < 1504 then decide (2 ≤ count1502 b) else decide (1 ≤ count1504 b)) else (if i < 1506 then decide (2 ≤ count1504 b) else decide (1 ≤ count1506 b)))) else (if i < 1510 then (if i < 1508 then decide (2 ≤ count1506 b) else (if i < 1509 then decide (3 ≤ count1506 b) else decide (4 ≤ count1506 b))) else (if i < 1512 then (if i < 1511 then decide (1 ≤ count1510 b) else decide (2 ≤ count1510 b)) else (if i < 1513 then decide (1 ≤ count1512 b) else decide (2 ≤ count1512 b)))))) else (if i < 1528 then (if i < 1521 then (if i < 1517 then (if i < 1515 then decide (1 ≤ count1514 b) else (if i < 1516 then decide (2 ≤ count1514 b) else decide (3 ≤ count1514 b))) else (if i < 1519 then (if i < 1518 then decide (4 ≤ count1514 b) else decide (1 ≤ count1518 b)) else (if i < 1520 then decide (2 ≤ count1518 b) else decide (3 ≤ count1518 b)))) else (if i < 1524 then (if i < 1522 then decide (4 ≤ count1518 b) else (if i < 1523 then decide (5 ≤ count1518 b) else decide (6 ≤ count1518 b))) else (if i < 1526 then (if i < 1525 then decide (7 ≤ count1518 b) else decide (8 ≤ count1518 b)) else (if i < 1527 then decide (1 ≤ count1526 b) else decide (2 ≤ count1526 b))))) else (if i < 1535 then (if i < 1531 then (if i < 1529 then decide (1 ≤ count1528 b) else (if i < 1530 then decide (2 ≤ count1528 b) else decide (1 ≤ count1530 b))) else (if i < 1533 then (if i < 1532 then decide (2 ≤ count1530 b) else decide (3 ≤ count1530 b)) else (if i < 1534 then decide (4 ≤ count1530 b) else decide (1 ≤ count1534 b)))) else (if i < 1538 then (if i < 1536 then decide (2 ≤ count1534 b) else (if i < 1537 then decide (1 ≤ count1536 b) else decide (2 ≤ count1536 b))) else (if i < 1540 then (if i < 1539 then decide (1 ≤ count1538 b) else decide (2 ≤ count1538 b)) else (if i < 1541 then decide (3 ≤ count1538 b) else decide (4 ≤ count1538 b))))))))) else (if i < 1652 then (if i < 1597 then (if i < 1569 then (if i < 1555 then (if i < 1548 then (if i < 1545 then (if i < 1543 then decide (1 ≤ count1542 b) else (if i < 1544 then decide (2 ≤ count1542 b) else decide (3 ≤ count1542 b))) else (if i < 1546 then decide (4 ≤ count1542 b) else (if i < 1547 then decide (5 ≤ count1542 b) else decide (6 ≤ count1542 b)))) else (if i < 1551 then (if i < 1549 then decide (7 ≤ count1542 b) else (if i < 1550 then decide (8 ≤ count1542 b) else decide (1 ≤ count1550 b))) else (if i < 1553 then (if i < 1552 then decide (2 ≤ count1550 b) else decide (3 ≤ count1550 b)) else (if i < 1554 then decide (4 ≤ count1550 b) else decide (5 ≤ count1550 b))))) else (if i < 1562 then (if i < 1558 then (if i < 1556 then decide (6 ≤ count1550 b) else (if i < 1557 then decide (7 ≤ count1550 b) else decide (8 ≤ count1550 b))) else (if i < 1560 then (if i < 1559 then decide (9 ≤ count1550 b) else decide (10 ≤ count1550 b)) else (if i < 1561 then decide (11 ≤ count1550 b) else decide (12 ≤ count1550 b)))) else (if i < 1565 then (if i < 1563 then decide (13 ≤ count1550 b) else (if i < 1564 then decide (14 ≤ count1550 b) else decide (15 ≤ count1550 b))) else (if i < 1567 then (if i < 1566 then decide (16 ≤ count1550 b) else decide (1 ≤ count1566 b)) else (if i < 1568 then decide (2 ≤ count1566 b) else decide (3 ≤ count1566 b)))))) else (if i < 1583 then (if i < 1576 then (if i < 1572 then (if i < 1570 then decide (4 ≤ count1566 b) else (if i < 1571 then decide (5 ≤ count1566 b) else decide (6 ≤ count1566 b))) else (if i < 1574 then (if i < 1573 then decide (7 ≤ count1566 b) else decide (8 ≤ count1566 b)) else (if i < 1575 then decide (9 ≤ count1566 b) else decide (10 ≤ count1566 b)))) else (if i < 1579 then (if i < 1577 then decide (11 ≤ count1566 b) else (if i < 1578 then decide (12 ≤ count1566 b) else decide (13 ≤ count1566 b))) else (if i < 1581 then (if i < 1580 then decide (14 ≤ count1566 b) else decide (15 ≤ count1566 b)) else (if i < 1582 then decide (16 ≤ count1566 b) else decide (17 ≤ count1566 b))))) else (if i < 1590 then (if i < 1586 then (if i < 1584 then decide (18 ≤ count1566 b) else (if i < 1585 then decide (19 ≤ count1566 b) else decide (20 ≤ count1566 b))) else (if i < 1588 then (if i < 1587 then decide (21 ≤ count1566 b) else decide (22 ≤ count1566 b)) else (if i < 1589 then decide (23 ≤ count1566 b) else decide (1 ≤ count1589 b)))) else (if i < 1593 then (if i < 1591 then decide (2 ≤ count1589 b) else (if i < 1592 then decide (1 ≤ count1591 b) else decide (2 ≤ count1591 b))) else (if i < 1595 then (if i < 1594 then decide (1 ≤ count1593 b) else decide (2 ≤ count1593 b)) else (if i < 1596 then decide (3 ≤ count1593 b) else decide (4 ≤ count1593 b))))))) else (if i < 1624 then (if i < 1610 then (if i < 1603 then (if i < 1600 then (if i < 1598 then decide (1 ≤ count1597 b) else (if i < 1599 then decide (2 ≤ count1597 b) else decide (1 ≤ count1599 b))) else (if i < 1601 then decide (2 ≤ count1599 b) else (if i < 1602 then decide (1 ≤ count1601 b) else decide (2 ≤ count1601 b)))) else (if i < 1606 then (if i < 1604 then decide (3 ≤ count1601 b) else (if i < 1605 then decide (4 ≤ count1601 b) else decide (1 ≤ count1605 b))) else (if i < 1608 then (if i < 1607 then decide (2 ≤ count1605 b) else decide (3 ≤ count1605 b)) else (if i < 1609 then decide (4 ≤ count1605 b) else decide (5 ≤ count1605 b))))) else (if i < 1617 then (if i < 1613 then (if i < 1611 then decide (6 ≤ count1605 b) else (if i < 1612 then decide (7 ≤ count1605 b) else decide (8 ≤ count1605 b))) else (if i < 1615 then (if i < 1614 then decide (1 ≤ count1613 b) else decide (2 ≤ count1613 b)) else (if i < 1616 then decide (1 ≤ count1615 b) else decide (2 ≤ count1615 b)))) else (if i < 1620 then (if i < 1618 then decide (1 ≤ count1617 b) else (if i < 1619 then decide (2 ≤ count1617 b) else decide (3 ≤ count1617 b))) else (if i < 1622 then (if i < 1621 then decide (4 ≤ count1617 b) else decide (1 ≤ count1621 b)) else (if i < 1623 then decide (2 ≤ count1621 b) else decide (1 ≤ count1623 b)))))) else (if i < 1638 then (if i < 1631 then (if i < 1627 then (if i < 1625 then decide (2 ≤ count1623 b) else (if i < 1626 then decide (1 ≤ count1625 b) else decide (2 ≤ count1625 b))) else (if i < 1629 then (if i < 1628 then decide (3 ≤ count1625 b) else decide (4 ≤ count1625 b)) else (if i < 1630 then decide (1 ≤ count1629 b) else decide (2 ≤ count1629 b)))) else (if i < 1634 then (if i < 1632 then decide (3 ≤ count1629 b) else (if i < 1633 then decide (4 ≤ count1629 b) else decide (5 ≤ count1629 b))) else (if i < 1636 then (if i < 1635 then decide (6 ≤ count1629 b) else decide (7 ≤ count1629 b)) else (if i < 1637 then decide (8 ≤ count1629 b) else decide (1 ≤ count1637 b))))) else (if i < 1645 then (if i < 1641 then (if i < 1639 then decide (2 ≤ count1637 b) else (if i < 1640 then decide (3 ≤ count1637 b) else decide (4 ≤ count1637 b))) else (if i < 1643 then (if i < 1642 then decide (5 ≤ count1637 b) else decide (6 ≤ count1637 b)) else (if i < 1644 then decide (7 ≤ count1637 b) else decide (8 ≤ count1637 b)))) else (if i < 1648 then (if i < 1646 then decide (9 ≤ count1637 b) else (if i < 1647 then decide (10 ≤ count1637 b) else decide (11 ≤ count1637 b))) else (if i < 1650 then (if i < 1649 then decide (12 ≤ count1637 b) else decide (13 ≤ count1637 b)) else (if i < 1651 then decide (14 ≤ count1637 b) else decide (15 ≤ count1637 b)))))))) else (if i < 1707 then (if i < 1679 then (if i < 1665 then (if i < 1658 then (if i < 1655 then (if i < 1653 then decide (16 ≤ count1637 b) else (if i < 1654 then decide (1 ≤ count1653 b) else decide (2 ≤ count1653 b))) else (if i < 1656 then decide (1 ≤ count1655 b) else (if i < 1657 then decide (2 ≤ count1655 b) else decide (1 ≤ count1657 b)))) else (if i < 1661 then (if i < 1659 then decide (2 ≤ count1657 b) else (if i < 1660 then decide (3 ≤ count1657 b) else decide (4 ≤ count1657 b))) else (if i < 1663 then (if i < 1662 then decide (1 ≤ count1661 b) else decide (2 ≤ count1661 b)) else (if i < 1664 then decide (1 ≤ count1663 b) else decide (2 ≤ count1663 b))))) else (if i < 1672 then (if i < 1668 then (if i < 1666 then decide (1 ≤ count1665 b) else (if i < 1667 then decide (2 ≤ count1665 b) else decide (3 ≤ count1665 b))) else (if i < 1670 then (if i < 1669 then decide (4 ≤ count1665 b) else decide (1 ≤ count1669 b)) else (if i < 1671 then decide (2 ≤ count1669 b) else decide (3 ≤ count1669 b)))) else (if i < 1675 then (if i < 1673 then decide (4 ≤ count1669 b) else (if i < 1674 then decide (5 ≤ count1669 b) else decide (6 ≤ count1669 b))) else (if i < 1677 then (if i < 1676 then decide (7 ≤ count1669 b) else decide (8 ≤ count1669 b)) else (if i < 1678 then decide (1 ≤ count1677 b) else decide (2 ≤ count1677 b)))))) else (if i < 1693 then (if i < 1686 then (if i < 1682 then (if i < 1680 then decide (1 ≤ count1679 b) else (if i < 1681 then decide (2 ≤ count1679 b) else decide (1 ≤ count1681 b))) else (if i < 1684 then (if i < 1683 then decide (2 ≤ count1681 b) else decide (3 ≤ count1681 b)) else (if i < 1685 then decide (4 ≤ count1681 b) else decide (1 ≤ count1685 b)))) else (if i < 1689 then (if i < 1687 then decide (2 ≤ count1685 b) else (if i < 1688 then decide (1 ≤ count1687 b) else decide (2 ≤ count1687 b))) else (if i < 1691 then (if i < 1690 then decide (1 ≤ count1689 b) else decide (2 ≤ count1689 b)) else (if i < 1692 then decide (3 ≤ count1689 b) else decide (4 ≤ count1689 b))))) else (if i < 1700 then (if i < 1696 then (if i < 1694 then decide (1 ≤ count1693 b) else (if i < 1695 then decide (2 ≤ count1693 b) else decide (3 ≤ count1693 b))) else (if i < 1698 then (if i < 1697 then decide (4 ≤ count1693 b) else decide (5 ≤ count1693 b)) else (if i < 1699 then decide (6 ≤ count1693 b) else decide (7 ≤ count1693 b)))) else (if i < 1703 then (if i < 1701 then decide (8 ≤ count1693 b) else (if i < 1702 then decide (1 ≤ count1701 b) else decide (2 ≤ count1701 b))) else (if i < 1705 then (if i < 1704 then decide (3 ≤ count1701 b) else decide (4 ≤ count1701 b)) else (if i < 1706 then decide (5 ≤ count1701 b) else decide (6 ≤ count1701 b))))))) else (if i < 1735 then (if i < 1721 then (if i < 1714 then (if i < 1710 then (if i < 1708 then decide (7 ≤ count1701 b) else (if i < 1709 then decide (8 ≤ count1701 b) else decide (9 ≤ count1701 b))) else (if i < 1712 then (if i < 1711 then decide (10 ≤ count1701 b) else decide (11 ≤ count1701 b)) else (if i < 1713 then decide (12 ≤ count1701 b) else decide (13 ≤ count1701 b)))) else (if i < 1717 then (if i < 1715 then decide (14 ≤ count1701 b) else (if i < 1716 then decide (15 ≤ count1701 b) else decide (16 ≤ count1701 b))) else (if i < 1719 then (if i < 1718 then decide (1 ≤ count1717 b) else decide (2 ≤ count1717 b)) else (if i < 1720 then decide (3 ≤ count1717 b) else decide (4 ≤ count1717 b))))) else (if i < 1728 then (if i < 1724 then (if i < 1722 then decide (5 ≤ count1717 b) else (if i < 1723 then decide (6 ≤ count1717 b) else decide (7 ≤ count1717 b))) else (if i < 1726 then (if i < 1725 then decide (8 ≤ count1717 b) else decide (9 ≤ count1717 b)) else (if i < 1727 then decide (10 ≤ count1717 b) else decide (11 ≤ count1717 b)))) else (if i < 1731 then (if i < 1729 then decide (12 ≤ count1717 b) else (if i < 1730 then decide (13 ≤ count1717 b) else decide (14 ≤ count1717 b))) else (if i < 1733 then (if i < 1732 then decide (15 ≤ count1717 b) else decide (16 ≤ count1717 b)) else (if i < 1734 then decide (17 ≤ count1717 b) else decide (18 ≤ count1717 b)))))) else (if i < 1749 then (if i < 1742 then (if i < 1738 then (if i < 1736 then decide (19 ≤ count1717 b) else (if i < 1737 then decide (20 ≤ count1717 b) else decide (21 ≤ count1717 b))) else (if i < 1740 then (if i < 1739 then decide (22 ≤ count1717 b) else decide (23 ≤ count1717 b)) else (if i < 1741 then decide (1 ≤ count1740 b) else decide (2 ≤ count1740 b)))) else (if i < 1745 then (if i < 1743 then decide (3 ≤ count1740 b) else (if i < 1744 then decide (4 ≤ count1740 b) else decide (5 ≤ count1740 b))) else (if i < 1747 then (if i < 1746 then decide (6 ≤ count1740 b) else decide (7 ≤ count1740 b)) else (if i < 1748 then decide (8 ≤ count1740 b) else decide (9 ≤ count1740 b))))) else (if i < 1756 then (if i < 1752 then (if i < 1750 then decide (10 ≤ count1740 b) else (if i < 1751 then decide (11 ≤ count1740 b) else decide (12 ≤ count1740 b))) else (if i < 1754 then (if i < 1753 then decide (13 ≤ count1740 b) else decide (14 ≤ count1740 b)) else (if i < 1755 then decide (15 ≤ count1740 b) else decide (16 ≤ count1740 b)))) else (if i < 1759 then (if i < 1757 then decide (17 ≤ count1740 b) else (if i < 1758 then decide (18 ≤ count1740 b) else decide (19 ≤ count1740 b))) else (if i < 1761 then (if i < 1760 then decide (20 ≤ count1740 b) else decide (21 ≤ count1740 b)) else (if i < 1762 then decide (22 ≤ count1740 b) else decide (23 ≤ count1740 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (35 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (36 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (37 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (39 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (44 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (52 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (53 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (55 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (99 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (100 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (103 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (160 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (161 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (162 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (163 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (165 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (166 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (168 : Vertex)) := rfl
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
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (227 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (228 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (229 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (230 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (234 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (235 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (236 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (238 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (244 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (245 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (247 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (248 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (249 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (250 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (251 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (255 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (288 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (289 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (294 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (295 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (296 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (299 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (301 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (303 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (304 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (305 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (306 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (307 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (308 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (310 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (316 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (317 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (318 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (354 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (355 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (356 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (357 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (362 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (363 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (364 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (366 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (372 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (373 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (375 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (376 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (377 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (379 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (383 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (416 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (417 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (418 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (420 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (421 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (422 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (423 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (424 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (426 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (427 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (428 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (430 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (431 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (433 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (435 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (436 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (437 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (439 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (440 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (441 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (442 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (443 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (447 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (480 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (481 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (486 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (487 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (488 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (489 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (491 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (493 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (495 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (497 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (498 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (499 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (500 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (502 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (506 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (508 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (509 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (510 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (35 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (36 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (39 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (52 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (53 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (55 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (103 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (176 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (178 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (190 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (226 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (236 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (289 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (294 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (295 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (299 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (301 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (303 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (304 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (306 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (307 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (310 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (316 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (317 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (318 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (362 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (364 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (366 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (373 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (375 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (377 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (379 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (383 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (416 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (420 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (422 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (437 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (441 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (442 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (489 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value298 (q : Snake 81) : valuation q 298 = decide (2 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value300 (q : Snake 81) : valuation q 300 = decide (2 ≤ count299 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value356 (q : Snake 81) : valuation q 356 = decide (2 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value446 (q : Snake 81) : valuation q 446 = decide (2 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value474 (q : Snake 81) : valuation q 474 = decide (2 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value476 (q : Snake 81) : valuation q 476 = decide (2 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value478 (q : Snake 81) : valuation q 478 = decide (2 ≤ count477 (baseVal q)) := rfl
theorem value480 (q : Snake 81) : valuation q 480 = decide (2 ≤ count479 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (1 ≤ count1443 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (1 ≤ count1445 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (2 ≤ count1445 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (1 ≤ count1448 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (2 ≤ count1448 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (1 ≤ count1450 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (2 ≤ count1450 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (1 ≤ count1452 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (2 ≤ count1452 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (3 ≤ count1452 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (4 ≤ count1452 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (2 ≤ count1456 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (3 ≤ count1456 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (4 ≤ count1456 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (5 ≤ count1456 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (1 ≤ count1463 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (2 ≤ count1463 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (1 ≤ count1465 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (2 ≤ count1465 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (1 ≤ count1467 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (2 ≤ count1467 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (3 ≤ count1467 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (4 ≤ count1467 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (1 ≤ count1471 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (2 ≤ count1471 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (1 ≤ count1473 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (2 ≤ count1473 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (1 ≤ count1475 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (2 ≤ count1475 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (3 ≤ count1475 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (4 ≤ count1475 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (1 ≤ count1479 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (2 ≤ count1479 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (3 ≤ count1479 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (4 ≤ count1479 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (5 ≤ count1479 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (6 ≤ count1479 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (3 ≤ count1487 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (4 ≤ count1487 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (5 ≤ count1487 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (6 ≤ count1487 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (7 ≤ count1487 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (8 ≤ count1487 (baseVal q)) := rfl
theorem value1495 (q : Snake 81) : valuation q 1495 = decide (9 ≤ count1487 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (1 ≤ count1502 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (2 ≤ count1502 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (1 ≤ count1504 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (2 ≤ count1504 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (1 ≤ count1506 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (2 ≤ count1506 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (3 ≤ count1506 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (4 ≤ count1506 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (1 ≤ count1510 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (2 ≤ count1510 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (1 ≤ count1512 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (2 ≤ count1512 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (1 ≤ count1514 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (2 ≤ count1514 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (3 ≤ count1514 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (4 ≤ count1514 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (1 ≤ count1518 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (2 ≤ count1518 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (3 ≤ count1518 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (4 ≤ count1518 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (5 ≤ count1518 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (1 ≤ count1526 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (2 ≤ count1526 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (1 ≤ count1528 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (2 ≤ count1528 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (1 ≤ count1530 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (2 ≤ count1530 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (3 ≤ count1530 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (4 ≤ count1530 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (1 ≤ count1534 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (2 ≤ count1534 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (1 ≤ count1536 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (2 ≤ count1536 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (1 ≤ count1538 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (2 ≤ count1538 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (3 ≤ count1538 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (4 ≤ count1538 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (1 ≤ count1542 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (2 ≤ count1542 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (3 ≤ count1542 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (4 ≤ count1542 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (5 ≤ count1542 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (6 ≤ count1542 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (3 ≤ count1550 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (4 ≤ count1550 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (5 ≤ count1550 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (6 ≤ count1550 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (7 ≤ count1550 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (8 ≤ count1550 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (9 ≤ count1550 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (10 ≤ count1550 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (8 ≤ count1566 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (9 ≤ count1566 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (10 ≤ count1566 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (11 ≤ count1566 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (12 ≤ count1566 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (13 ≤ count1566 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (14 ≤ count1566 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (15 ≤ count1566 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (1 ≤ count1589 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (2 ≤ count1589 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (1 ≤ count1591 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (2 ≤ count1591 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (1 ≤ count1593 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (2 ≤ count1593 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (3 ≤ count1593 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (1 ≤ count1597 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (2 ≤ count1597 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (1 ≤ count1599 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (2 ≤ count1599 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (1 ≤ count1601 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (2 ≤ count1601 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (3 ≤ count1601 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (1 ≤ count1605 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (2 ≤ count1605 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (3 ≤ count1605 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (4 ≤ count1605 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (1 ≤ count1613 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (2 ≤ count1613 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (1 ≤ count1615 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (2 ≤ count1615 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (1 ≤ count1617 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (2 ≤ count1617 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (3 ≤ count1617 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (4 ≤ count1617 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (1 ≤ count1621 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (2 ≤ count1621 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (1 ≤ count1623 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (2 ≤ count1623 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (1 ≤ count1625 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (2 ≤ count1625 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (3 ≤ count1625 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (4 ≤ count1625 (baseVal q)) := rfl
theorem value1629 (q : Snake 81) : valuation q 1629 = decide (1 ≤ count1629 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (2 ≤ count1629 (baseVal q)) := rfl
theorem value1631 (q : Snake 81) : valuation q 1631 = decide (3 ≤ count1629 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (4 ≤ count1629 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (5 ≤ count1629 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (6 ≤ count1629 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (7 ≤ count1629 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (2 ≤ count1637 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (3 ≤ count1637 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (4 ≤ count1637 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (5 ≤ count1637 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (6 ≤ count1637 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (7 ≤ count1637 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (8 ≤ count1637 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (9 ≤ count1637 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (1 ≤ count1653 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (2 ≤ count1653 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (1 ≤ count1655 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (2 ≤ count1655 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (1 ≤ count1657 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (2 ≤ count1657 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (3 ≤ count1657 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (4 ≤ count1657 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (1 ≤ count1661 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (2 ≤ count1661 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (1 ≤ count1663 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (2 ≤ count1663 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (1 ≤ count1665 (baseVal q)) := rfl
theorem value1666 (q : Snake 81) : valuation q 1666 = decide (2 ≤ count1665 (baseVal q)) := rfl
theorem value1667 (q : Snake 81) : valuation q 1667 = decide (3 ≤ count1665 (baseVal q)) := rfl
theorem value1668 (q : Snake 81) : valuation q 1668 = decide (4 ≤ count1665 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (1 ≤ count1669 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (2 ≤ count1669 (baseVal q)) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (3 ≤ count1669 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (4 ≤ count1669 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (5 ≤ count1669 (baseVal q)) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (6 ≤ count1669 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (7 ≤ count1669 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (8 ≤ count1669 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (1 ≤ count1677 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (2 ≤ count1677 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (1 ≤ count1679 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (2 ≤ count1679 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (1 ≤ count1681 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (2 ≤ count1681 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (3 ≤ count1681 (baseVal q)) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (1 ≤ count1685 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (2 ≤ count1685 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (1 ≤ count1687 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (2 ≤ count1687 (baseVal q)) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (1 ≤ count1689 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (2 ≤ count1689 (baseVal q)) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (3 ≤ count1689 (baseVal q)) := rfl
theorem value1693 (q : Snake 81) : valuation q 1693 = decide (1 ≤ count1693 (baseVal q)) := rfl
theorem value1694 (q : Snake 81) : valuation q 1694 = decide (2 ≤ count1693 (baseVal q)) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (3 ≤ count1693 (baseVal q)) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (4 ≤ count1693 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (5 ≤ count1693 (baseVal q)) := rfl
theorem value1698 (q : Snake 81) : valuation q 1698 = decide (6 ≤ count1693 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (3 ≤ count1701 (baseVal q)) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (4 ≤ count1701 (baseVal q)) := rfl
theorem value1705 (q : Snake 81) : valuation q 1705 = decide (5 ≤ count1701 (baseVal q)) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (6 ≤ count1701 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (7 ≤ count1701 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (8 ≤ count1701 (baseVal q)) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (9 ≤ count1701 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (10 ≤ count1701 (baseVal q)) := rfl
theorem value1724 (q : Snake 81) : valuation q 1724 = decide (8 ≤ count1717 (baseVal q)) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (9 ≤ count1717 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (10 ≤ count1717 (baseVal q)) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (11 ≤ count1717 (baseVal q)) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (12 ≤ count1717 (baseVal q)) := rfl
theorem value1729 (q : Snake 81) : valuation q 1729 = decide (13 ≤ count1717 (baseVal q)) := rfl
theorem value1730 (q : Snake 81) : valuation q 1730 = decide (14 ≤ count1717 (baseVal q)) := rfl
theorem value1731 (q : Snake 81) : valuation q 1731 = decide (15 ≤ count1717 (baseVal q)) := rfl
theorem value1762 (q : Snake 81) : valuation q 1762 = decide (23 ≤ count1740 (baseVal q)) := rfl
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
theorem meaningNeg105 (b : Nat → Bool) : literal (valuationOf b) (-105) = decide (1 ≤ countLit b [-105]) := by
  change literal b (-105) = decide (1 ≤ countLit b [-105])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-105) <;> decide
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
theorem meaningNeg67 (b : Nat → Bool) : literal (valuationOf b) (-67) = decide (1 ≤ countLit b [-67]) := by
  change literal b (-67) = decide (1 ≤ countLit b [-67])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-67) <;> decide
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
theorem meaningNeg60 (b : Nat → Bool) : literal (valuationOf b) (-60) = decide (1 ≤ countLit b [-60]) := by
  change literal b (-60) = decide (1 ≤ countLit b [-60])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-60) <;> decide
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
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning123 (b : Nat → Bool) : literal (valuationOf b) (123) = decide (1 ≤ countLit b [123]) := by
  change literal b (123) = decide (1 ≤ countLit b [123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (123) <;> decide
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
theorem meaning142 (b : Nat → Bool) : literal (valuationOf b) (142) = decide (1 ≤ countLit b [142]) := by
  change literal b (142) = decide (1 ≤ countLit b [142])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (142) <;> decide
theorem meaning144 (b : Nat → Bool) : literal (valuationOf b) (144) = decide (1 ≤ countLit b [144]) := by
  change literal b (144) = decide (1 ≤ countLit b [144])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (144) <;> decide
theorem meaning145 (b : Nat → Bool) : literal (valuationOf b) (145) = decide (1 ≤ countLit b [145]) := by
  change literal b (145) = decide (1 ≤ countLit b [145])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (145) <;> decide
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
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
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
theorem meaning199 (b : Nat → Bool) : literal (valuationOf b) (199) = decide (1 ≤ countLit b [199]) := by
  change literal b (199) = decide (1 ≤ countLit b [199])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (199) <;> decide
theorem meaning201 (b : Nat → Bool) : literal (valuationOf b) (201) = decide (1 ≤ countLit b [201]) := by
  change literal b (201) = decide (1 ≤ countLit b [201])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (201) <;> decide
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
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) (213) = decide (1 ≤ countLit b [213]) := by
  change literal b (213) = decide (1 ≤ countLit b [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (213) <;> decide
theorem meaning218 (b : Nat → Bool) : literal (valuationOf b) (218) = decide (1 ≤ countLit b [218]) := by
  change literal b (218) = decide (1 ≤ countLit b [218])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (218) <;> decide
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
theorem meaning224 (b : Nat → Bool) : literal (valuationOf b) (224) = decide (1 ≤ countLit b [224]) := by
  change literal b (224) = decide (1 ≤ countLit b [224])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (224) <;> decide
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) (225) = decide (1 ≤ countLit b [225]) := by
  change literal b (225) = decide (1 ≤ countLit b [225])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (225) <;> decide
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) (227) = decide (1 ≤ countLit b [227]) := by
  change literal b (227) = decide (1 ≤ countLit b [227])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (227) <;> decide
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) (230) = decide (1 ≤ countLit b [230]) := by
  change literal b (230) = decide (1 ≤ countLit b [230])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (230) <;> decide
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
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) (235) = decide (1 ≤ countLit b [235]) := by
  change literal b (235) = decide (1 ≤ countLit b [235])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (235) <;> decide
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) (241) = decide (1 ≤ countLit b [241]) := by
  change literal b (241) = decide (1 ≤ countLit b [241])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (241) <;> decide
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning298 (b : Nat → Bool) : literal (valuationOf b) 298 = decide (2 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning300 (b : Nat → Bool) : literal (valuationOf b) 300 = decide (2 ≤ count299 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning340 (b : Nat → Bool) : literal (valuationOf b) 340 = decide (2 ≤ count339 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning356 (b : Nat → Bool) : literal (valuationOf b) 356 = decide (2 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning418 (b : Nat → Bool) : literal (valuationOf b) 418 = decide (2 ≤ count417 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning446 (b : Nat → Bool) : literal (valuationOf b) 446 = decide (2 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning474 (b : Nat → Bool) : literal (valuationOf b) 474 = decide (2 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning476 (b : Nat → Bool) : literal (valuationOf b) 476 = decide (2 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning478 (b : Nat → Bool) : literal (valuationOf b) 478 = decide (2 ≤ count477 b) := rfl
theorem meaning480 (b : Nat → Bool) : literal (valuationOf b) 480 = decide (2 ≤ count479 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (1 ≤ count1443 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (1 ≤ count1445 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (2 ≤ count1445 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (1 ≤ count1448 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (2 ≤ count1448 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (1 ≤ count1450 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (2 ≤ count1450 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (1 ≤ count1452 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (2 ≤ count1452 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (3 ≤ count1452 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (4 ≤ count1452 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (2 ≤ count1456 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (3 ≤ count1456 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (4 ≤ count1456 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (5 ≤ count1456 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (1 ≤ count1463 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (2 ≤ count1463 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (1 ≤ count1465 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (2 ≤ count1465 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (1 ≤ count1467 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (2 ≤ count1467 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (3 ≤ count1467 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (4 ≤ count1467 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (1 ≤ count1471 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (2 ≤ count1471 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (1 ≤ count1473 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (2 ≤ count1473 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (1 ≤ count1475 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (2 ≤ count1475 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (3 ≤ count1475 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (4 ≤ count1475 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (1 ≤ count1479 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (2 ≤ count1479 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (3 ≤ count1479 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (4 ≤ count1479 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (5 ≤ count1479 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (6 ≤ count1479 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (3 ≤ count1487 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (4 ≤ count1487 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (5 ≤ count1487 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (6 ≤ count1487 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (7 ≤ count1487 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (8 ≤ count1487 b) := rfl
theorem meaning1495 (b : Nat → Bool) : literal (valuationOf b) 1495 = decide (9 ≤ count1487 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (1 ≤ count1502 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (2 ≤ count1502 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (1 ≤ count1504 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (2 ≤ count1504 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (1 ≤ count1506 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (2 ≤ count1506 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (3 ≤ count1506 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (4 ≤ count1506 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (1 ≤ count1510 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (2 ≤ count1510 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (1 ≤ count1512 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (2 ≤ count1512 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (1 ≤ count1514 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (2 ≤ count1514 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (3 ≤ count1514 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (4 ≤ count1514 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (1 ≤ count1518 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (2 ≤ count1518 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (3 ≤ count1518 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (4 ≤ count1518 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (5 ≤ count1518 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (1 ≤ count1526 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (2 ≤ count1526 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (1 ≤ count1528 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (2 ≤ count1528 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (1 ≤ count1530 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (2 ≤ count1530 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (3 ≤ count1530 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (4 ≤ count1530 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (1 ≤ count1534 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (2 ≤ count1534 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (1 ≤ count1536 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (2 ≤ count1536 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (1 ≤ count1538 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (2 ≤ count1538 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (3 ≤ count1538 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (4 ≤ count1538 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (1 ≤ count1542 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (2 ≤ count1542 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (3 ≤ count1542 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (4 ≤ count1542 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (5 ≤ count1542 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (6 ≤ count1542 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (3 ≤ count1550 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (4 ≤ count1550 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (5 ≤ count1550 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (6 ≤ count1550 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (7 ≤ count1550 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (8 ≤ count1550 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (9 ≤ count1550 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (10 ≤ count1550 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (8 ≤ count1566 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (9 ≤ count1566 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (10 ≤ count1566 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (11 ≤ count1566 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (12 ≤ count1566 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (13 ≤ count1566 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (14 ≤ count1566 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (15 ≤ count1566 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (1 ≤ count1589 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (2 ≤ count1589 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (1 ≤ count1591 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (2 ≤ count1591 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (1 ≤ count1593 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (2 ≤ count1593 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (3 ≤ count1593 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (1 ≤ count1597 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (2 ≤ count1597 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (1 ≤ count1599 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (2 ≤ count1599 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (1 ≤ count1601 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (2 ≤ count1601 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (3 ≤ count1601 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (1 ≤ count1605 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (2 ≤ count1605 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (3 ≤ count1605 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (4 ≤ count1605 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (1 ≤ count1613 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (2 ≤ count1613 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (1 ≤ count1615 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (2 ≤ count1615 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (1 ≤ count1617 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (2 ≤ count1617 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (3 ≤ count1617 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (4 ≤ count1617 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (1 ≤ count1621 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (2 ≤ count1621 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (1 ≤ count1623 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (2 ≤ count1623 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (1 ≤ count1625 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (2 ≤ count1625 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (3 ≤ count1625 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (4 ≤ count1625 b) := rfl
theorem meaning1629 (b : Nat → Bool) : literal (valuationOf b) 1629 = decide (1 ≤ count1629 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (2 ≤ count1629 b) := rfl
theorem meaning1631 (b : Nat → Bool) : literal (valuationOf b) 1631 = decide (3 ≤ count1629 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (4 ≤ count1629 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (5 ≤ count1629 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (6 ≤ count1629 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (7 ≤ count1629 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (2 ≤ count1637 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (3 ≤ count1637 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (4 ≤ count1637 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (5 ≤ count1637 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (6 ≤ count1637 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (7 ≤ count1637 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (8 ≤ count1637 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (9 ≤ count1637 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (1 ≤ count1653 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (2 ≤ count1653 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (1 ≤ count1655 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (2 ≤ count1655 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (1 ≤ count1657 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (2 ≤ count1657 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (3 ≤ count1657 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (4 ≤ count1657 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (1 ≤ count1661 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (2 ≤ count1661 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (1 ≤ count1663 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (2 ≤ count1663 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (1 ≤ count1665 b) := rfl
theorem meaning1666 (b : Nat → Bool) : literal (valuationOf b) 1666 = decide (2 ≤ count1665 b) := rfl
theorem meaning1667 (b : Nat → Bool) : literal (valuationOf b) 1667 = decide (3 ≤ count1665 b) := rfl
theorem meaning1668 (b : Nat → Bool) : literal (valuationOf b) 1668 = decide (4 ≤ count1665 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (1 ≤ count1669 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (2 ≤ count1669 b) := rfl
theorem meaning1671 (b : Nat → Bool) : literal (valuationOf b) 1671 = decide (3 ≤ count1669 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (4 ≤ count1669 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (5 ≤ count1669 b) := rfl
theorem meaning1674 (b : Nat → Bool) : literal (valuationOf b) 1674 = decide (6 ≤ count1669 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (7 ≤ count1669 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (8 ≤ count1669 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (1 ≤ count1677 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (2 ≤ count1677 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (1 ≤ count1679 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (2 ≤ count1679 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (1 ≤ count1681 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (2 ≤ count1681 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (3 ≤ count1681 b) := rfl
theorem meaning1685 (b : Nat → Bool) : literal (valuationOf b) 1685 = decide (1 ≤ count1685 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (2 ≤ count1685 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (1 ≤ count1687 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (2 ≤ count1687 b) := rfl
theorem meaning1689 (b : Nat → Bool) : literal (valuationOf b) 1689 = decide (1 ≤ count1689 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (2 ≤ count1689 b) := rfl
theorem meaning1691 (b : Nat → Bool) : literal (valuationOf b) 1691 = decide (3 ≤ count1689 b) := rfl
theorem meaning1693 (b : Nat → Bool) : literal (valuationOf b) 1693 = decide (1 ≤ count1693 b) := rfl
theorem meaning1694 (b : Nat → Bool) : literal (valuationOf b) 1694 = decide (2 ≤ count1693 b) := rfl
theorem meaning1695 (b : Nat → Bool) : literal (valuationOf b) 1695 = decide (3 ≤ count1693 b) := rfl
theorem meaning1696 (b : Nat → Bool) : literal (valuationOf b) 1696 = decide (4 ≤ count1693 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (5 ≤ count1693 b) := rfl
theorem meaning1698 (b : Nat → Bool) : literal (valuationOf b) 1698 = decide (6 ≤ count1693 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (3 ≤ count1701 b) := rfl
theorem meaning1704 (b : Nat → Bool) : literal (valuationOf b) 1704 = decide (4 ≤ count1701 b) := rfl
theorem meaning1705 (b : Nat → Bool) : literal (valuationOf b) 1705 = decide (5 ≤ count1701 b) := rfl
theorem meaning1706 (b : Nat → Bool) : literal (valuationOf b) 1706 = decide (6 ≤ count1701 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (7 ≤ count1701 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (8 ≤ count1701 b) := rfl
theorem meaning1709 (b : Nat → Bool) : literal (valuationOf b) 1709 = decide (9 ≤ count1701 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (10 ≤ count1701 b) := rfl
theorem meaning1724 (b : Nat → Bool) : literal (valuationOf b) 1724 = decide (8 ≤ count1717 b) := rfl
theorem meaning1725 (b : Nat → Bool) : literal (valuationOf b) 1725 = decide (9 ≤ count1717 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (10 ≤ count1717 b) := rfl
theorem meaning1727 (b : Nat → Bool) : literal (valuationOf b) 1727 = decide (11 ≤ count1717 b) := rfl
theorem meaning1728 (b : Nat → Bool) : literal (valuationOf b) 1728 = decide (12 ≤ count1717 b) := rfl
theorem meaning1729 (b : Nat → Bool) : literal (valuationOf b) 1729 = decide (13 ≤ count1717 b) := rfl
theorem meaning1730 (b : Nat → Bool) : literal (valuationOf b) 1730 = decide (14 ≤ count1717 b) := rfl
theorem meaning1731 (b : Nat → Bool) : literal (valuationOf b) 1731 = decide (15 ≤ count1717 b) := rfl
theorem meaning1762 (b : Nat → Bool) : literal (valuationOf b) 1762 = decide (23 ≤ count1740 b) := rfl
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
end Snake9.Regrowth.E112026
