import First112Data
namespace Snake9.Regrowth.First112
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 122 then (if i < 61 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (34 : Vertex)) else decide (InPath q (35 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (36 : Vertex)) else decide (InPath q (37 : Vertex))) else (if i < 6 then decide (InPath q (40 : Vertex)) else decide (InPath q (42 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (43 : Vertex)) else decide (InPath q (44 : Vertex))) else (if i < 10 then decide (InPath q (46 : Vertex)) else decide (InPath q (52 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (53 : Vertex)) else decide (InPath q (55 : Vertex))) else (if i < 14 then decide (InPath q (56 : Vertex)) else decide (InPath q (57 : Vertex)))))) else (if i < 22 then (if i < 18 then (if i < 16 then decide (InPath q (59 : Vertex)) else (if i < 17 then decide (InPath q (63 : Vertex)) else decide (InPath q (99 : Vertex)))) else (if i < 20 then (if i < 19 then decide (InPath q (100 : Vertex)) else decide (InPath q (103 : Vertex))) else (if i < 21 then decide (InPath q (160 : Vertex)) else decide (InPath q (161 : Vertex))))) else (if i < 26 then (if i < 24 then (if i < 23 then decide (InPath q (166 : Vertex)) else decide (InPath q (167 : Vertex))) else (if i < 25 then decide (InPath q (168 : Vertex)) else decide (InPath q (169 : Vertex)))) else (if i < 28 then (if i < 27 then decide (InPath q (171 : Vertex)) else decide (InPath q (173 : Vertex))) else (if i < 29 then decide (InPath q (175 : Vertex)) else decide (InPath q (177 : Vertex))))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then decide (InPath q (178 : Vertex)) else (if i < 32 then decide (InPath q (179 : Vertex)) else decide (InPath q (180 : Vertex)))) else (if i < 35 then (if i < 34 then decide (InPath q (182 : Vertex)) else decide (InPath q (186 : Vertex))) else (if i < 36 then decide (InPath q (188 : Vertex)) else decide (InPath q (189 : Vertex))))) else (if i < 41 then (if i < 39 then (if i < 38 then decide (InPath q (190 : Vertex)) else decide (InPath q (226 : Vertex))) else (if i < 40 then decide (InPath q (227 : Vertex)) else decide (InPath q (228 : Vertex)))) else (if i < 43 then (if i < 42 then decide (InPath q (229 : Vertex)) else decide (InPath q (230 : Vertex))) else (if i < 44 then decide (InPath q (234 : Vertex)) else decide (InPath q (235 : Vertex)))))) else (if i < 53 then (if i < 49 then (if i < 47 then (if i < 46 then decide (InPath q (236 : Vertex)) else decide (InPath q (238 : Vertex))) else (if i < 48 then decide (InPath q (244 : Vertex)) else decide (InPath q (245 : Vertex)))) else (if i < 51 then (if i < 50 then decide (InPath q (247 : Vertex)) else decide (InPath q (248 : Vertex))) else (if i < 52 then decide (InPath q (249 : Vertex)) else decide (InPath q (250 : Vertex))))) else (if i < 57 then (if i < 55 then (if i < 54 then decide (InPath q (251 : Vertex)) else decide (InPath q (255 : Vertex))) else (if i < 56 then decide (InPath q (288 : Vertex)) else decide (InPath q (289 : Vertex)))) else (if i < 59 then (if i < 58 then decide (InPath q (293 : Vertex)) else decide (InPath q (294 : Vertex))) else (if i < 60 then decide (InPath q (295 : Vertex)) else decide (InPath q (296 : Vertex)))))))) else (if i < 91 then (if i < 76 then (if i < 68 then (if i < 64 then (if i < 62 then decide (InPath q (299 : Vertex)) else (if i < 63 then decide (InPath q (301 : Vertex)) else decide (InPath q (303 : Vertex)))) else (if i < 66 then (if i < 65 then decide (InPath q (304 : Vertex)) else decide (InPath q (305 : Vertex))) else (if i < 67 then decide (InPath q (306 : Vertex)) else decide (InPath q (307 : Vertex))))) else (if i < 72 then (if i < 70 then (if i < 69 then decide (InPath q (310 : Vertex)) else decide (InPath q (316 : Vertex))) else (if i < 71 then decide (InPath q (317 : Vertex)) else decide (InPath q (318 : Vertex)))) else (if i < 74 then (if i < 73 then decide (InPath q (352 : Vertex)) else decide (InPath q (355 : Vertex))) else (if i < 75 then decide (InPath q (356 : Vertex)) else decide (InPath q (359 : Vertex)))))) else (if i < 83 then (if i < 79 then (if i < 77 then decide (InPath q (364 : Vertex)) else (if i < 78 then decide (InPath q (372 : Vertex)) else decide (InPath q (373 : Vertex)))) else (if i < 81 then (if i < 80 then decide (InPath q (375 : Vertex)) else decide (InPath q (416 : Vertex))) else (if i < 82 then decide (InPath q (417 : Vertex)) else decide (InPath q (418 : Vertex))))) else (if i < 87 then (if i < 85 then (if i < 84 then decide (InPath q (420 : Vertex)) else decide (InPath q (421 : Vertex))) else (if i < 86 then decide (InPath q (422 : Vertex)) else decide (InPath q (423 : Vertex)))) else (if i < 89 then (if i < 88 then decide (InPath q (424 : Vertex)) else decide (InPath q (426 : Vertex))) else (if i < 90 then decide (InPath q (427 : Vertex)) else decide (InPath q (428 : Vertex))))))) else (if i < 106 then (if i < 98 then (if i < 94 then (if i < 92 then decide (InPath q (430 : Vertex)) else (if i < 93 then decide (InPath q (431 : Vertex)) else decide (InPath q (433 : Vertex)))) else (if i < 96 then (if i < 95 then decide (InPath q (435 : Vertex)) else decide (InPath q (436 : Vertex))) else (if i < 97 then decide (InPath q (437 : Vertex)) else decide (InPath q (439 : Vertex))))) else (if i < 102 then (if i < 100 then (if i < 99 then decide (InPath q (440 : Vertex)) else decide (InPath q (441 : Vertex))) else (if i < 101 then decide (InPath q (442 : Vertex)) else decide (InPath q (443 : Vertex)))) else (if i < 104 then (if i < 103 then decide (InPath q (447 : Vertex)) else decide (InPath q (480 : Vertex))) else (if i < 105 then decide (InPath q (481 : Vertex)) else decide (InPath q (482 : Vertex)))))) else (if i < 114 then (if i < 110 then (if i < 108 then (if i < 107 then decide (InPath q (483 : Vertex)) else decide (InPath q (485 : Vertex))) else (if i < 109 then decide (InPath q (486 : Vertex)) else decide (InPath q (488 : Vertex)))) else (if i < 112 then (if i < 111 then decide (InPath q (491 : Vertex)) else decide (InPath q (493 : Vertex))) else (if i < 113 then decide (InPath q (495 : Vertex)) else decide (InPath q (496 : Vertex))))) else (if i < 118 then (if i < 116 then (if i < 115 then decide (InPath q (497 : Vertex)) else decide (InPath q (498 : Vertex))) else (if i < 117 then decide (InPath q (499 : Vertex)) else decide (InPath q (502 : Vertex)))) else (if i < 120 then (if i < 119 then decide (InPath q (504 : Vertex)) else decide (InPath q (508 : Vertex))) else (if i < 121 then decide (InPath q (509 : Vertex)) else decide (InPath q (510 : Vertex))))))))) else (if i < 183 then (if i < 152 then (if i < 137 then (if i < 129 then (if i < 125 then (if i < 123 then decide (InPath q (511 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (34 : Vertex)) else decide (BallClauseLogic.Endpoint q (35 : Vertex)))) else (if i < 127 then (if i < 126 then decide (BallClauseLogic.Endpoint q (36 : Vertex)) else decide (BallClauseLogic.Endpoint q (37 : Vertex))) else (if i < 128 then decide (BallClauseLogic.Endpoint q (40 : Vertex)) else decide (BallClauseLogic.Endpoint q (42 : Vertex))))) else (if i < 133 then (if i < 131 then (if i < 130 then decide (BallClauseLogic.Endpoint q (43 : Vertex)) else decide (BallClauseLogic.Endpoint q (44 : Vertex))) else (if i < 132 then decide (BallClauseLogic.Endpoint q (46 : Vertex)) else decide (BallClauseLogic.Endpoint q (52 : Vertex)))) else (if i < 135 then (if i < 134 then decide (BallClauseLogic.Endpoint q (53 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (56 : Vertex)) else decide (BallClauseLogic.Endpoint q (57 : Vertex)))))) else (if i < 144 then (if i < 140 then (if i < 138 then decide (BallClauseLogic.Endpoint q (59 : Vertex)) else (if i < 139 then decide (BallClauseLogic.Endpoint q (63 : Vertex)) else decide (BallClauseLogic.Endpoint q (99 : Vertex)))) else (if i < 142 then (if i < 141 then decide (BallClauseLogic.Endpoint q (100 : Vertex)) else decide (BallClauseLogic.Endpoint q (103 : Vertex))) else (if i < 143 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (161 : Vertex))))) else (if i < 148 then (if i < 146 then (if i < 145 then decide (BallClauseLogic.Endpoint q (166 : Vertex)) else decide (BallClauseLogic.Endpoint q (167 : Vertex))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else decide (BallClauseLogic.Endpoint q (169 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (171 : Vertex)) else decide (BallClauseLogic.Endpoint q (173 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else decide (BallClauseLogic.Endpoint q (177 : Vertex))))))) else (if i < 167 then (if i < 159 then (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (178 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (180 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (182 : Vertex)) else decide (BallClauseLogic.Endpoint q (186 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (188 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex))))) else (if i < 163 then (if i < 161 then (if i < 160 then decide (BallClauseLogic.Endpoint q (190 : Vertex)) else decide (BallClauseLogic.Endpoint q (226 : Vertex))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (227 : Vertex)) else decide (BallClauseLogic.Endpoint q (228 : Vertex)))) else (if i < 165 then (if i < 164 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (230 : Vertex))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (234 : Vertex)) else decide (BallClauseLogic.Endpoint q (235 : Vertex)))))) else (if i < 175 then (if i < 171 then (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (236 : Vertex)) else decide (BallClauseLogic.Endpoint q (238 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (245 : Vertex)))) else (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (247 : Vertex)) else decide (BallClauseLogic.Endpoint q (248 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (249 : Vertex)) else decide (BallClauseLogic.Endpoint q (250 : Vertex))))) else (if i < 179 then (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else decide (BallClauseLogic.Endpoint q (289 : Vertex)))) else (if i < 181 then (if i < 180 then decide (BallClauseLogic.Endpoint q (293 : Vertex)) else decide (BallClauseLogic.Endpoint q (294 : Vertex))) else (if i < 182 then decide (BallClauseLogic.Endpoint q (295 : Vertex)) else decide (BallClauseLogic.Endpoint q (296 : Vertex)))))))) else (if i < 214 then (if i < 198 then (if i < 190 then (if i < 186 then (if i < 184 then decide (BallClauseLogic.Endpoint q (299 : Vertex)) else (if i < 185 then decide (BallClauseLogic.Endpoint q (301 : Vertex)) else decide (BallClauseLogic.Endpoint q (303 : Vertex)))) else (if i < 188 then (if i < 187 then decide (BallClauseLogic.Endpoint q (304 : Vertex)) else decide (BallClauseLogic.Endpoint q (305 : Vertex))) else (if i < 189 then decide (BallClauseLogic.Endpoint q (306 : Vertex)) else decide (BallClauseLogic.Endpoint q (307 : Vertex))))) else (if i < 194 then (if i < 192 then (if i < 191 then decide (BallClauseLogic.Endpoint q (310 : Vertex)) else decide (BallClauseLogic.Endpoint q (316 : Vertex))) else (if i < 193 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (318 : Vertex)))) else (if i < 196 then (if i < 195 then decide (BallClauseLogic.Endpoint q (352 : Vertex)) else decide (BallClauseLogic.Endpoint q (355 : Vertex))) else (if i < 197 then decide (BallClauseLogic.Endpoint q (356 : Vertex)) else decide (BallClauseLogic.Endpoint q (359 : Vertex)))))) else (if i < 206 then (if i < 202 then (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (364 : Vertex)) else decide (BallClauseLogic.Endpoint q (372 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (373 : Vertex)) else decide (BallClauseLogic.Endpoint q (375 : Vertex)))) else (if i < 204 then (if i < 203 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex))) else (if i < 205 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (420 : Vertex))))) else (if i < 210 then (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex)))) else (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else decide (BallClauseLogic.Endpoint q (430 : Vertex))))))) else (if i < 229 then (if i < 221 then (if i < 217 then (if i < 215 then decide (BallClauseLogic.Endpoint q (431 : Vertex)) else (if i < 216 then decide (BallClauseLogic.Endpoint q (433 : Vertex)) else decide (BallClauseLogic.Endpoint q (435 : Vertex)))) else (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (437 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (439 : Vertex)) else decide (BallClauseLogic.Endpoint q (440 : Vertex))))) else (if i < 225 then (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (441 : Vertex)) else decide (BallClauseLogic.Endpoint q (442 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex)))) else (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (482 : Vertex)) else decide (BallClauseLogic.Endpoint q (483 : Vertex)))))) else (if i < 237 then (if i < 233 then (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (485 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (488 : Vertex)) else decide (BallClauseLogic.Endpoint q (491 : Vertex)))) else (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else decide (BallClauseLogic.Endpoint q (495 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (496 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 241 then (if i < 239 then (if i < 238 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else decide (BallClauseLogic.Endpoint q (499 : Vertex))) else (if i < 240 then decide (BallClauseLogic.Endpoint q (502 : Vertex)) else decide (BallClauseLogic.Endpoint q (504 : Vertex)))) else (if i < 243 then (if i < 242 then decide (BallClauseLogic.Endpoint q (508 : Vertex)) else decide (BallClauseLogic.Endpoint q (509 : Vertex))) else (if i < 244 then decide (BallClauseLogic.Endpoint q (510 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex))))))))))
def countLit (q : Snake 81) (xs : List Int) : Nat := xs.countP (literal (baseVal q))
def count245 (q : Snake 81) : Nat := countLit q [124, 125]
def count247 (q : Snake 81) : Nat := countLit q [123, 124, 125]
def count249 (q : Snake 81) : Nat := countLit q [126, 127]
def count251 (q : Snake 81) : Nat := countLit q [128, 129]
def count253 (q : Snake 81) : Nat := countLit q [126, 127, 128, 129]
def count255 (q : Snake 81) : Nat := countLit q [123, 124, 125, 126, 127, 128, 129]
def count257 (q : Snake 81) : Nat := countLit q [130, 131]
def count259 (q : Snake 81) : Nat := countLit q [132, 133]
def count261 (q : Snake 81) : Nat := countLit q [130, 131, 132, 133]
def count263 (q : Snake 81) : Nat := countLit q [134, 135]
def count265 (q : Snake 81) : Nat := countLit q [136, 137]
def count267 (q : Snake 81) : Nat := countLit q [134, 135, 136, 137]
def count269 (q : Snake 81) : Nat := countLit q [130, 131, 132, 133, 134, 135, 136, 137]
def count271 (q : Snake 81) : Nat := countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
def count273 (q : Snake 81) : Nat := countLit q [139, 140]
def count275 (q : Snake 81) : Nat := countLit q [138, 139, 140]
def count277 (q : Snake 81) : Nat := countLit q [141, 142]
def count279 (q : Snake 81) : Nat := countLit q [143, 144]
def count281 (q : Snake 81) : Nat := countLit q [141, 142, 143, 144]
def count283 (q : Snake 81) : Nat := countLit q [138, 139, 140, 141, 142, 143, 144]
def count285 (q : Snake 81) : Nat := countLit q [145, 146]
def count287 (q : Snake 81) : Nat := countLit q [147, 148]
def count289 (q : Snake 81) : Nat := countLit q [145, 146, 147, 148]
def count291 (q : Snake 81) : Nat := countLit q [149, 150]
def count293 (q : Snake 81) : Nat := countLit q [151, 152]
def count295 (q : Snake 81) : Nat := countLit q [149, 150, 151, 152]
def count297 (q : Snake 81) : Nat := countLit q [145, 146, 147, 148, 149, 150, 151, 152]
def count299 (q : Snake 81) : Nat := countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count301 (q : Snake 81) : Nat := countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count303 (q : Snake 81) : Nat := countLit q [154, 155]
def count305 (q : Snake 81) : Nat := countLit q [153, 154, 155]
def count307 (q : Snake 81) : Nat := countLit q [156, 157]
def count309 (q : Snake 81) : Nat := countLit q [158, 159]
def count311 (q : Snake 81) : Nat := countLit q [156, 157, 158, 159]
def count313 (q : Snake 81) : Nat := countLit q [153, 154, 155, 156, 157, 158, 159]
def count315 (q : Snake 81) : Nat := countLit q [160, 161]
def count317 (q : Snake 81) : Nat := countLit q [162, 163]
def count319 (q : Snake 81) : Nat := countLit q [160, 161, 162, 163]
def count321 (q : Snake 81) : Nat := countLit q [164, 165]
def count323 (q : Snake 81) : Nat := countLit q [166, 167]
def count325 (q : Snake 81) : Nat := countLit q [164, 165, 166, 167]
def count327 (q : Snake 81) : Nat := countLit q [160, 161, 162, 163, 164, 165, 166, 167]
def count329 (q : Snake 81) : Nat := countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]
def count331 (q : Snake 81) : Nat := countLit q [169, 170]
def count333 (q : Snake 81) : Nat := countLit q [168, 169, 170]
def count335 (q : Snake 81) : Nat := countLit q [171, 172]
def count337 (q : Snake 81) : Nat := countLit q [173, 174]
def count339 (q : Snake 81) : Nat := countLit q [171, 172, 173, 174]
def count341 (q : Snake 81) : Nat := countLit q [168, 169, 170, 171, 172, 173, 174]
def count343 (q : Snake 81) : Nat := countLit q [175, 176]
def count345 (q : Snake 81) : Nat := countLit q [177, 178]
def count347 (q : Snake 81) : Nat := countLit q [175, 176, 177, 178]
def count349 (q : Snake 81) : Nat := countLit q [179, 180]
def count351 (q : Snake 81) : Nat := countLit q [181, 182]
def count353 (q : Snake 81) : Nat := countLit q [179, 180, 181, 182]
def count355 (q : Snake 81) : Nat := countLit q [175, 176, 177, 178, 179, 180, 181, 182]
def count357 (q : Snake 81) : Nat := countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count359 (q : Snake 81) : Nat := countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count361 (q : Snake 81) : Nat := countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count363 (q : Snake 81) : Nat := countLit q [184, 185]
def count365 (q : Snake 81) : Nat := countLit q [183, 184, 185]
def count367 (q : Snake 81) : Nat := countLit q [186, 187]
def count369 (q : Snake 81) : Nat := countLit q [188, 189]
def count371 (q : Snake 81) : Nat := countLit q [186, 187, 188, 189]
def count373 (q : Snake 81) : Nat := countLit q [183, 184, 185, 186, 187, 188, 189]
def count375 (q : Snake 81) : Nat := countLit q [190, 191]
def count377 (q : Snake 81) : Nat := countLit q [192, 193]
def count379 (q : Snake 81) : Nat := countLit q [190, 191, 192, 193]
def count381 (q : Snake 81) : Nat := countLit q [194, 195]
def count383 (q : Snake 81) : Nat := countLit q [196, 197]
def count385 (q : Snake 81) : Nat := countLit q [194, 195, 196, 197]
def count387 (q : Snake 81) : Nat := countLit q [190, 191, 192, 193, 194, 195, 196, 197]
def count389 (q : Snake 81) : Nat := countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]
def count391 (q : Snake 81) : Nat := countLit q [200, 201]
def count393 (q : Snake 81) : Nat := countLit q [199, 200, 201]
def count395 (q : Snake 81) : Nat := countLit q [202, 203]
def count397 (q : Snake 81) : Nat := countLit q [204, 205]
def count399 (q : Snake 81) : Nat := countLit q [202, 203, 204, 205]
def count401 (q : Snake 81) : Nat := countLit q [199, 200, 201, 202, 203, 204, 205]
def count403 (q : Snake 81) : Nat := countLit q [206, 207]
def count405 (q : Snake 81) : Nat := countLit q [208, 209]
def count407 (q : Snake 81) : Nat := countLit q [206, 207, 208, 209]
def count409 (q : Snake 81) : Nat := countLit q [210, 211]
def count411 (q : Snake 81) : Nat := countLit q [212, 213]
def count413 (q : Snake 81) : Nat := countLit q [210, 211, 212, 213]
def count415 (q : Snake 81) : Nat := countLit q [206, 207, 208, 209, 210, 211, 212, 213]
def count417 (q : Snake 81) : Nat := countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]
def count419 (q : Snake 81) : Nat := countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]
def count421 (q : Snake 81) : Nat := countLit q [215, 216]
def count423 (q : Snake 81) : Nat := countLit q [214, 215, 216]
def count425 (q : Snake 81) : Nat := countLit q [217, 218]
def count427 (q : Snake 81) : Nat := countLit q [219, 220]
def count429 (q : Snake 81) : Nat := countLit q [217, 218, 219, 220]
def count431 (q : Snake 81) : Nat := countLit q [214, 215, 216, 217, 218, 219, 220]
def count433 (q : Snake 81) : Nat := countLit q [221, 222]
def count435 (q : Snake 81) : Nat := countLit q [223, 224]
def count437 (q : Snake 81) : Nat := countLit q [221, 222, 223, 224]
def count439 (q : Snake 81) : Nat := countLit q [225, 226]
def count441 (q : Snake 81) : Nat := countLit q [227, 228]
def count443 (q : Snake 81) : Nat := countLit q [225, 226, 227, 228]
def count445 (q : Snake 81) : Nat := countLit q [221, 222, 223, 224, 225, 226, 227, 228]
def count447 (q : Snake 81) : Nat := countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]
def count449 (q : Snake 81) : Nat := countLit q [229, 230]
def count451 (q : Snake 81) : Nat := countLit q [231, 232]
def count453 (q : Snake 81) : Nat := countLit q [229, 230, 231, 232]
def count455 (q : Snake 81) : Nat := countLit q [233, 234]
def count457 (q : Snake 81) : Nat := countLit q [235, 236]
def count459 (q : Snake 81) : Nat := countLit q [233, 234, 235, 236]
def count461 (q : Snake 81) : Nat := countLit q [229, 230, 231, 232, 233, 234, 235, 236]
def count463 (q : Snake 81) : Nat := countLit q [237, 238]
def count465 (q : Snake 81) : Nat := countLit q [239, 240]
def count467 (q : Snake 81) : Nat := countLit q [237, 238, 239, 240]
def count469 (q : Snake 81) : Nat := countLit q [241, 242]
def count471 (q : Snake 81) : Nat := countLit q [243, 244]
def count473 (q : Snake 81) : Nat := countLit q [241, 242, 243, 244]
def count475 (q : Snake 81) : Nat := countLit q [237, 238, 239, 240, 241, 242, 243, 244]
def count477 (q : Snake 81) : Nat := countLit q [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]
def count479 (q : Snake 81) : Nat := countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]
def count481 (q : Snake 81) : Nat := countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]
def count483 (q : Snake 81) : Nat := countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]
def count485 (q : Snake 81) : Nat := countLit q [3, 5]
def count487 (q : Snake 81) : Nat := countLit q [1, 3, 5]
def count490 (q : Snake 81) : Nat := countLit q [7, 9]
def count492 (q : Snake 81) : Nat := countLit q [11, 14]
def count494 (q : Snake 81) : Nat := countLit q [7, 9, 11, 14]
def count498 (q : Snake 81) : Nat := countLit q [1, 3, 5, 7, 9, 11, 14]
def count505 (q : Snake 81) : Nat := countLit q [17, 20]
def count507 (q : Snake 81) : Nat := countLit q [16, 17, 20]
def count510 (q : Snake 81) : Nat := countLit q [22, 25]
def count512 (q : Snake 81) : Nat := countLit q [28, 29]
def count514 (q : Snake 81) : Nat := countLit q [22, 25, 28, 29]
def count518 (q : Snake 81) : Nat := countLit q [16, 17, 20, 22, 25, 28, 29]
def count525 (q : Snake 81) : Nat := countLit q [1, 3, 5, 7, 9, 11, 14, 16, 17, 20, 22, 25, 28, 29]
def count539 (q : Snake 81) : Nat := countLit q [32, 36]
def count541 (q : Snake 81) : Nat := countLit q [30, 32, 36]
def count544 (q : Snake 81) : Nat := countLit q [37, 38]
def count546 (q : Snake 81) : Nat := countLit q [40, 44]
def count548 (q : Snake 81) : Nat := countLit q [37, 38, 40, 44]
def count552 (q : Snake 81) : Nat := countLit q [30, 32, 36, 37, 38, 40, 44]
def count559 (q : Snake 81) : Nat := countLit q [46, 48]
def count561 (q : Snake 81) : Nat := countLit q [51, 52]
def count563 (q : Snake 81) : Nat := countLit q [46, 48, 51, 52]
def count567 (q : Snake 81) : Nat := countLit q [54, 55]
def count569 (q : Snake 81) : Nat := countLit q [57, 58]
def count571 (q : Snake 81) : Nat := countLit q [54, 55, 57, 58]
def count575 (q : Snake 81) : Nat := countLit q [46, 48, 51, 52, 54, 55, 57, 58]
def count583 (q : Snake 81) : Nat := countLit q [30, 32, 36, 37, 38, 40, 44, 46, 48, 51, 52, 54, 55, 57, 58]
def count598 (q : Snake 81) : Nat := countLit q [1, 3, 5, 7, 9, 11, 14, 16, 17, 20, 22, 25, 28, 29, 30, 32, 36, 37, 38, 40, 44, 46, 48, 51, 52, 54, 55, 57, 58]
def count627 (q : Snake 81) : Nat := countLit q [65, 66]
def count629 (q : Snake 81) : Nat := countLit q [63, 65, 66]
def count632 (q : Snake 81) : Nat := countLit q [70, 71]
def count634 (q : Snake 81) : Nat := countLit q [74, 75]
def count636 (q : Snake 81) : Nat := countLit q [70, 71, 74, 75]
def count640 (q : Snake 81) : Nat := countLit q [63, 65, 66, 70, 71, 74, 75]
def count647 (q : Snake 81) : Nat := countLit q [78, 81]
def count649 (q : Snake 81) : Nat := countLit q [82, 83]
def count651 (q : Snake 81) : Nat := countLit q [78, 81, 82, 83]
def count655 (q : Snake 81) : Nat := countLit q [86, 87]
def count657 (q : Snake 81) : Nat := countLit q [89, 91]
def count659 (q : Snake 81) : Nat := countLit q [86, 87, 89, 91]
def count663 (q : Snake 81) : Nat := countLit q [78, 81, 82, 83, 86, 87, 89, 91]
def count671 (q : Snake 81) : Nat := countLit q [63, 65, 66, 70, 71, 74, 75, 78, 81, 82, 83, 86, 87, 89, 91]
def count686 (q : Snake 81) : Nat := countLit q [96, 99]
def count688 (q : Snake 81) : Nat := countLit q [94, 96, 99]
def count691 (q : Snake 81) : Nat := countLit q [100, 102]
def count693 (q : Snake 81) : Nat := countLit q [103, 106]
def count695 (q : Snake 81) : Nat := countLit q [100, 102, 103, 106]
def count699 (q : Snake 81) : Nat := countLit q [94, 96, 99, 100, 102, 103, 106]
def count706 (q : Snake 81) : Nat := countLit q [107, 108]
def count708 (q : Snake 81) : Nat := countLit q [112, 114]
def count710 (q : Snake 81) : Nat := countLit q [107, 108, 112, 114]
def count714 (q : Snake 81) : Nat := countLit q [115, 118]
def count716 (q : Snake 81) : Nat := countLit q [120, 121]
def count718 (q : Snake 81) : Nat := countLit q [115, 118, 120, 121]
def count722 (q : Snake 81) : Nat := countLit q [107, 108, 112, 114, 115, 118, 120, 121]
def count730 (q : Snake 81) : Nat := countLit q [94, 96, 99, 100, 102, 103, 106, 107, 108, 112, 114, 115, 118, 120, 121]
def count745 (q : Snake 81) : Nat := countLit q [63, 65, 66, 70, 71, 74, 75, 78, 81, 82, 83, 86, 87, 89, 91, 94, 96, 99, 100, 102, 103, 106, 107, 108, 112, 114, 115, 118, 120, 121]
def count775 (q : Snake 81) : Nat := countLit q [1, 3, 5, 7, 9, 11, 14, 16, 17, 20, 22, 25, 28, 29, 30, 32, 36, 37, 38, 40, 44, 46, 48, 51, 52, 54, 55, 57, 58, 63, 65, 66, 70, 71, 74, 75, 78, 81, 82, 83, 86, 87, 89, 91, 94, 96, 99, 100, 102, 103, 106, 107, 108, 112, 114, 115, 118, 120, 121]
def count817 (q : Snake 81) : Nat := countLit q [-3, -5]
def count819 (q : Snake 81) : Nat := countLit q [-1, -3, -5]
def count822 (q : Snake 81) : Nat := countLit q [-7, -9]
def count824 (q : Snake 81) : Nat := countLit q [-11, -14]
def count826 (q : Snake 81) : Nat := countLit q [-7, -9, -11, -14]
def count830 (q : Snake 81) : Nat := countLit q [-1, -3, -5, -7, -9, -11, -14]
def count837 (q : Snake 81) : Nat := countLit q [-17, -20]
def count839 (q : Snake 81) : Nat := countLit q [-16, -17, -20]
def count842 (q : Snake 81) : Nat := countLit q [-22, -25]
def count844 (q : Snake 81) : Nat := countLit q [-28, -29]
def count846 (q : Snake 81) : Nat := countLit q [-22, -25, -28, -29]
def count850 (q : Snake 81) : Nat := countLit q [-16, -17, -20, -22, -25, -28, -29]
def count857 (q : Snake 81) : Nat := countLit q [-1, -3, -5, -7, -9, -11, -14, -16, -17, -20, -22, -25, -28, -29]
def count871 (q : Snake 81) : Nat := countLit q [-32, -36]
def count873 (q : Snake 81) : Nat := countLit q [-30, -32, -36]
def count876 (q : Snake 81) : Nat := countLit q [-37, -38]
def count878 (q : Snake 81) : Nat := countLit q [-40, -44]
def count880 (q : Snake 81) : Nat := countLit q [-37, -38, -40, -44]
def count884 (q : Snake 81) : Nat := countLit q [-30, -32, -36, -37, -38, -40, -44]
def count891 (q : Snake 81) : Nat := countLit q [-46, -48]
def count893 (q : Snake 81) : Nat := countLit q [-51, -52]
def count895 (q : Snake 81) : Nat := countLit q [-46, -48, -51, -52]
def count899 (q : Snake 81) : Nat := countLit q [-54, -55]
def count901 (q : Snake 81) : Nat := countLit q [-57, -58]
def count903 (q : Snake 81) : Nat := countLit q [-54, -55, -57, -58]
def count907 (q : Snake 81) : Nat := countLit q [-46, -48, -51, -52, -54, -55, -57, -58]
def count915 (q : Snake 81) : Nat := countLit q [-30, -32, -36, -37, -38, -40, -44, -46, -48, -51, -52, -54, -55, -57, -58]
def count930 (q : Snake 81) : Nat := countLit q [-1, -3, -5, -7, -9, -11, -14, -16, -17, -20, -22, -25, -28, -29, -30, -32, -36, -37, -38, -40, -44, -46, -48, -51, -52, -54, -55, -57, -58]
def count949 (q : Snake 81) : Nat := countLit q [-65, -66]
def count951 (q : Snake 81) : Nat := countLit q [-63, -65, -66]
def count954 (q : Snake 81) : Nat := countLit q [-70, -71]
def count956 (q : Snake 81) : Nat := countLit q [-74, -75]
def count958 (q : Snake 81) : Nat := countLit q [-70, -71, -74, -75]
def count962 (q : Snake 81) : Nat := countLit q [-63, -65, -66, -70, -71, -74, -75]
def count969 (q : Snake 81) : Nat := countLit q [-78, -81]
def count971 (q : Snake 81) : Nat := countLit q [-82, -83]
def count973 (q : Snake 81) : Nat := countLit q [-78, -81, -82, -83]
def count977 (q : Snake 81) : Nat := countLit q [-86, -87]
def count979 (q : Snake 81) : Nat := countLit q [-89, -91]
def count981 (q : Snake 81) : Nat := countLit q [-86, -87, -89, -91]
def count985 (q : Snake 81) : Nat := countLit q [-78, -81, -82, -83, -86, -87, -89, -91]
def count993 (q : Snake 81) : Nat := countLit q [-63, -65, -66, -70, -71, -74, -75, -78, -81, -82, -83, -86, -87, -89, -91]
def count1008 (q : Snake 81) : Nat := countLit q [-96, -99]
def count1010 (q : Snake 81) : Nat := countLit q [-94, -96, -99]
def count1013 (q : Snake 81) : Nat := countLit q [-100, -102]
def count1015 (q : Snake 81) : Nat := countLit q [-103, -106]
def count1017 (q : Snake 81) : Nat := countLit q [-100, -102, -103, -106]
def count1021 (q : Snake 81) : Nat := countLit q [-94, -96, -99, -100, -102, -103, -106]
def count1028 (q : Snake 81) : Nat := countLit q [-107, -108]
def count1030 (q : Snake 81) : Nat := countLit q [-112, -114]
def count1032 (q : Snake 81) : Nat := countLit q [-107, -108, -112, -114]
def count1036 (q : Snake 81) : Nat := countLit q [-115, -118]
def count1038 (q : Snake 81) : Nat := countLit q [-120, -121]
def count1040 (q : Snake 81) : Nat := countLit q [-115, -118, -120, -121]
def count1044 (q : Snake 81) : Nat := countLit q [-107, -108, -112, -114, -115, -118, -120, -121]
def count1052 (q : Snake 81) : Nat := countLit q [-94, -96, -99, -100, -102, -103, -106, -107, -108, -112, -114, -115, -118, -120, -121]
def count1067 (q : Snake 81) : Nat := countLit q [-63, -65, -66, -70, -71, -74, -75, -78, -81, -82, -83, -86, -87, -89, -91, -94, -96, -99, -100, -102, -103, -106, -107, -108, -112, -114, -115, -118, -120, -121]
def count1086 (q : Snake 81) : Nat := countLit q [-1, -3, -5, -7, -9, -11, -14, -16, -17, -20, -22, -25, -28, -29, -30, -32, -36, -37, -38, -40, -44, -46, -48, -51, -52, -54, -55, -57, -58, -63, -65, -66, -70, -71, -74, -75, -78, -81, -82, -83, -86, -87, -89, -91, -94, -96, -99, -100, -102, -103, -106, -107, -108, -112, -114, -115, -118, -120, -121]
def count1105 (q : Snake 81) : Nat := countLit q [4, 6]
def count1107 (q : Snake 81) : Nat := countLit q [2, 4, 6]
def count1110 (q : Snake 81) : Nat := countLit q [8, 10]
def count1112 (q : Snake 81) : Nat := countLit q [12, 13]
def count1114 (q : Snake 81) : Nat := countLit q [8, 10, 12, 13]
def count1118 (q : Snake 81) : Nat := countLit q [2, 4, 6, 8, 10, 12, 13]
def count1125 (q : Snake 81) : Nat := countLit q [15, 18]
def count1127 (q : Snake 81) : Nat := countLit q [19, 21]
def count1129 (q : Snake 81) : Nat := countLit q [15, 18, 19, 21]
def count1133 (q : Snake 81) : Nat := countLit q [23, 24]
def count1135 (q : Snake 81) : Nat := countLit q [26, 27]
def count1137 (q : Snake 81) : Nat := countLit q [23, 24, 26, 27]
def count1141 (q : Snake 81) : Nat := countLit q [15, 18, 19, 21, 23, 24, 26, 27]
def count1149 (q : Snake 81) : Nat := countLit q [2, 4, 6, 8, 10, 12, 13, 15, 18, 19, 21, 23, 24, 26, 27]
def count1164 (q : Snake 81) : Nat := countLit q [31, 33]
def count1166 (q : Snake 81) : Nat := countLit q [34, 35]
def count1168 (q : Snake 81) : Nat := countLit q [31, 33, 34, 35]
def count1172 (q : Snake 81) : Nat := countLit q [39, 41]
def count1174 (q : Snake 81) : Nat := countLit q [42, 43]
def count1176 (q : Snake 81) : Nat := countLit q [39, 41, 42, 43]
def count1180 (q : Snake 81) : Nat := countLit q [31, 33, 34, 35, 39, 41, 42, 43]
def count1188 (q : Snake 81) : Nat := countLit q [45, 47]
def count1190 (q : Snake 81) : Nat := countLit q [49, 50]
def count1192 (q : Snake 81) : Nat := countLit q [45, 47, 49, 50]
def count1196 (q : Snake 81) : Nat := countLit q [53, 56]
def count1198 (q : Snake 81) : Nat := countLit q [59, 60]
def count1200 (q : Snake 81) : Nat := countLit q [53, 56, 59, 60]
def count1204 (q : Snake 81) : Nat := countLit q [45, 47, 49, 50, 53, 56, 59, 60]
def count1212 (q : Snake 81) : Nat := countLit q [31, 33, 34, 35, 39, 41, 42, 43, 45, 47, 49, 50, 53, 56, 59, 60]
def count1228 (q : Snake 81) : Nat := countLit q [2, 4, 6, 8, 10, 12, 13, 15, 18, 19, 21, 23, 24, 26, 27, 31, 33, 34, 35, 39, 41, 42, 43, 45, 47, 49, 50, 53, 56, 59, 60]
def count1259 (q : Snake 81) : Nat := countLit q [61, 62]
def count1261 (q : Snake 81) : Nat := countLit q [64, 67]
def count1263 (q : Snake 81) : Nat := countLit q [61, 62, 64, 67]
def count1267 (q : Snake 81) : Nat := countLit q [68, 69]
def count1269 (q : Snake 81) : Nat := countLit q [72, 73]
def count1271 (q : Snake 81) : Nat := countLit q [68, 69, 72, 73]
def count1275 (q : Snake 81) : Nat := countLit q [61, 62, 64, 67, 68, 69, 72, 73]
def count1283 (q : Snake 81) : Nat := countLit q [76, 77]
def count1285 (q : Snake 81) : Nat := countLit q [79, 80]
def count1287 (q : Snake 81) : Nat := countLit q [76, 77, 79, 80]
def count1291 (q : Snake 81) : Nat := countLit q [84, 85]
def count1293 (q : Snake 81) : Nat := countLit q [88, 90]
def count1295 (q : Snake 81) : Nat := countLit q [84, 85, 88, 90]
def count1299 (q : Snake 81) : Nat := countLit q [76, 77, 79, 80, 84, 85, 88, 90]
def count1307 (q : Snake 81) : Nat := countLit q [61, 62, 64, 67, 68, 69, 72, 73, 76, 77, 79, 80, 84, 85, 88, 90]
def count1323 (q : Snake 81) : Nat := countLit q [92, 93]
def count1325 (q : Snake 81) : Nat := countLit q [95, 97]
def count1327 (q : Snake 81) : Nat := countLit q [92, 93, 95, 97]
def count1331 (q : Snake 81) : Nat := countLit q [98, 101]
def count1333 (q : Snake 81) : Nat := countLit q [104, 105]
def count1335 (q : Snake 81) : Nat := countLit q [98, 101, 104, 105]
def count1339 (q : Snake 81) : Nat := countLit q [92, 93, 95, 97, 98, 101, 104, 105]
def count1347 (q : Snake 81) : Nat := countLit q [109, 110]
def count1349 (q : Snake 81) : Nat := countLit q [111, 113]
def count1351 (q : Snake 81) : Nat := countLit q [109, 110, 111, 113]
def count1355 (q : Snake 81) : Nat := countLit q [116, 117]
def count1357 (q : Snake 81) : Nat := countLit q [119, 122]
def count1359 (q : Snake 81) : Nat := countLit q [116, 117, 119, 122]
def count1363 (q : Snake 81) : Nat := countLit q [109, 110, 111, 113, 116, 117, 119, 122]
def count1371 (q : Snake 81) : Nat := countLit q [92, 93, 95, 97, 98, 101, 104, 105, 109, 110, 111, 113, 116, 117, 119, 122]
def count1387 (q : Snake 81) : Nat := countLit q [61, 62, 64, 67, 68, 69, 72, 73, 76, 77, 79, 80, 84, 85, 88, 90, 92, 93, 95, 97, 98, 101, 104, 105, 109, 110, 111, 113, 116, 117, 119, 122]
def count1419 (q : Snake 81) : Nat := countLit q [2, 4, 6, 8, 10, 12, 13, 15, 18, 19, 21, 23, 24, 26, 27, 31, 33, 34, 35, 39, 41, 42, 43, 45, 47, 49, 50, 53, 56, 59, 60, 61, 62, 64, 67, 68, 69, 72, 73, 76, 77, 79, 80, 84, 85, 88, 90, 92, 93, 95, 97, 98, 101, 104, 105, 109, 110, 111, 113, 116, 117, 119, 122]
def count1461 (q : Snake 81) : Nat := countLit q [-4, -6]
def count1463 (q : Snake 81) : Nat := countLit q [-2, -4, -6]
def count1466 (q : Snake 81) : Nat := countLit q [-8, -10]
def count1468 (q : Snake 81) : Nat := countLit q [-12, -13]
def count1470 (q : Snake 81) : Nat := countLit q [-8, -10, -12, -13]
def count1474 (q : Snake 81) : Nat := countLit q [-2, -4, -6, -8, -10, -12, -13]
def count1481 (q : Snake 81) : Nat := countLit q [-15, -18]
def count1483 (q : Snake 81) : Nat := countLit q [-19, -21]
def count1485 (q : Snake 81) : Nat := countLit q [-15, -18, -19, -21]
def count1489 (q : Snake 81) : Nat := countLit q [-23, -24]
def count1491 (q : Snake 81) : Nat := countLit q [-26, -27]
def count1493 (q : Snake 81) : Nat := countLit q [-23, -24, -26, -27]
def count1497 (q : Snake 81) : Nat := countLit q [-15, -18, -19, -21, -23, -24, -26, -27]
def count1505 (q : Snake 81) : Nat := countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]
def count1520 (q : Snake 81) : Nat := countLit q [-31, -33]
def count1522 (q : Snake 81) : Nat := countLit q [-34, -35]
def count1524 (q : Snake 81) : Nat := countLit q [-31, -33, -34, -35]
def count1528 (q : Snake 81) : Nat := countLit q [-39, -41]
def count1530 (q : Snake 81) : Nat := countLit q [-42, -43]
def count1532 (q : Snake 81) : Nat := countLit q [-39, -41, -42, -43]
def count1536 (q : Snake 81) : Nat := countLit q [-31, -33, -34, -35, -39, -41, -42, -43]
def count1544 (q : Snake 81) : Nat := countLit q [-45, -47]
def count1546 (q : Snake 81) : Nat := countLit q [-49, -50]
def count1548 (q : Snake 81) : Nat := countLit q [-45, -47, -49, -50]
def count1552 (q : Snake 81) : Nat := countLit q [-53, -56]
def count1554 (q : Snake 81) : Nat := countLit q [-59, -60]
def count1556 (q : Snake 81) : Nat := countLit q [-53, -56, -59, -60]
def count1560 (q : Snake 81) : Nat := countLit q [-45, -47, -49, -50, -53, -56, -59, -60]
def count1568 (q : Snake 81) : Nat := countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]
def count1584 (q : Snake 81) : Nat := countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]
def count1607 (q : Snake 81) : Nat := countLit q [-61, -62]
def count1609 (q : Snake 81) : Nat := countLit q [-64, -67]
def count1611 (q : Snake 81) : Nat := countLit q [-61, -62, -64, -67]
def count1615 (q : Snake 81) : Nat := countLit q [-68, -69]
def count1617 (q : Snake 81) : Nat := countLit q [-72, -73]
def count1619 (q : Snake 81) : Nat := countLit q [-68, -69, -72, -73]
def count1623 (q : Snake 81) : Nat := countLit q [-61, -62, -64, -67, -68, -69, -72, -73]
def count1631 (q : Snake 81) : Nat := countLit q [-76, -77]
def count1633 (q : Snake 81) : Nat := countLit q [-79, -80]
def count1635 (q : Snake 81) : Nat := countLit q [-76, -77, -79, -80]
def count1639 (q : Snake 81) : Nat := countLit q [-84, -85]
def count1641 (q : Snake 81) : Nat := countLit q [-88, -90]
def count1643 (q : Snake 81) : Nat := countLit q [-84, -85, -88, -90]
def count1647 (q : Snake 81) : Nat := countLit q [-76, -77, -79, -80, -84, -85, -88, -90]
def count1655 (q : Snake 81) : Nat := countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90]
def count1671 (q : Snake 81) : Nat := countLit q [-92, -93]
def count1673 (q : Snake 81) : Nat := countLit q [-95, -97]
def count1675 (q : Snake 81) : Nat := countLit q [-92, -93, -95, -97]
def count1679 (q : Snake 81) : Nat := countLit q [-98, -101]
def count1681 (q : Snake 81) : Nat := countLit q [-104, -105]
def count1683 (q : Snake 81) : Nat := countLit q [-98, -101, -104, -105]
def count1687 (q : Snake 81) : Nat := countLit q [-92, -93, -95, -97, -98, -101, -104, -105]
def count1695 (q : Snake 81) : Nat := countLit q [-109, -110]
def count1697 (q : Snake 81) : Nat := countLit q [-111, -113]
def count1699 (q : Snake 81) : Nat := countLit q [-109, -110, -111, -113]
def count1703 (q : Snake 81) : Nat := countLit q [-116, -117]
def count1705 (q : Snake 81) : Nat := countLit q [-119, -122]
def count1707 (q : Snake 81) : Nat := countLit q [-116, -117, -119, -122]
def count1711 (q : Snake 81) : Nat := countLit q [-109, -110, -111, -113, -116, -117, -119, -122]
def count1719 (q : Snake 81) : Nat := countLit q [-92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]
def count1735 (q : Snake 81) : Nat := countLit q [-61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]
def count1758 (q : Snake 81) : Nat := countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27, -31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60, -61, -62, -64, -67, -68, -69, -72, -73, -76, -77, -79, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -105, -109, -110, -111, -113, -116, -117, -119, -122]
def valuation (q : Snake 81) (i : Nat) : Bool := (if i < 890 then (if i < 445 then (if i < 222 then (if i < 111 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (34 : Vertex)) else decide (InPath q (35 : Vertex)))) else (if i < 4 then decide (InPath q (36 : Vertex)) else (if i < 5 then decide (InPath q (37 : Vertex)) else decide (InPath q (40 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (42 : Vertex)) else (if i < 8 then decide (InPath q (43 : Vertex)) else decide (InPath q (44 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (46 : Vertex)) else decide (InPath q (52 : Vertex))) else (if i < 12 then decide (InPath q (53 : Vertex)) else decide (InPath q (55 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (56 : Vertex)) else (if i < 15 then decide (InPath q (57 : Vertex)) else decide (InPath q (59 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (63 : Vertex)) else decide (InPath q (99 : Vertex))) else (if i < 19 then decide (InPath q (100 : Vertex)) else decide (InPath q (103 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (160 : Vertex)) else (if i < 22 then decide (InPath q (161 : Vertex)) else decide (InPath q (166 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (167 : Vertex)) else decide (InPath q (168 : Vertex))) else (if i < 26 then decide (InPath q (169 : Vertex)) else decide (InPath q (171 : Vertex))))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then decide (InPath q (173 : Vertex)) else (if i < 29 then decide (InPath q (175 : Vertex)) else decide (InPath q (177 : Vertex)))) else (if i < 32 then (if i < 31 then decide (InPath q (178 : Vertex)) else decide (InPath q (179 : Vertex))) else (if i < 33 then decide (InPath q (180 : Vertex)) else decide (InPath q (182 : Vertex))))) else (if i < 37 then (if i < 35 then decide (InPath q (186 : Vertex)) else (if i < 36 then decide (InPath q (188 : Vertex)) else decide (InPath q (189 : Vertex)))) else (if i < 39 then (if i < 38 then decide (InPath q (190 : Vertex)) else decide (InPath q (226 : Vertex))) else (if i < 40 then decide (InPath q (227 : Vertex)) else decide (InPath q (228 : Vertex)))))) else (if i < 48 then (if i < 44 then (if i < 42 then decide (InPath q (229 : Vertex)) else (if i < 43 then decide (InPath q (230 : Vertex)) else decide (InPath q (234 : Vertex)))) else (if i < 46 then (if i < 45 then decide (InPath q (235 : Vertex)) else decide (InPath q (236 : Vertex))) else (if i < 47 then decide (InPath q (238 : Vertex)) else decide (InPath q (244 : Vertex))))) else (if i < 51 then (if i < 49 then decide (InPath q (245 : Vertex)) else (if i < 50 then decide (InPath q (247 : Vertex)) else decide (InPath q (248 : Vertex)))) else (if i < 53 then (if i < 52 then decide (InPath q (249 : Vertex)) else decide (InPath q (250 : Vertex))) else (if i < 54 then decide (InPath q (251 : Vertex)) else decide (InPath q (255 : Vertex)))))))) else (if i < 83 then (if i < 69 then (if i < 62 then (if i < 58 then (if i < 56 then decide (InPath q (288 : Vertex)) else (if i < 57 then decide (InPath q (289 : Vertex)) else decide (InPath q (293 : Vertex)))) else (if i < 60 then (if i < 59 then decide (InPath q (294 : Vertex)) else decide (InPath q (295 : Vertex))) else (if i < 61 then decide (InPath q (296 : Vertex)) else decide (InPath q (299 : Vertex))))) else (if i < 65 then (if i < 63 then decide (InPath q (301 : Vertex)) else (if i < 64 then decide (InPath q (303 : Vertex)) else decide (InPath q (304 : Vertex)))) else (if i < 67 then (if i < 66 then decide (InPath q (305 : Vertex)) else decide (InPath q (306 : Vertex))) else (if i < 68 then decide (InPath q (307 : Vertex)) else decide (InPath q (310 : Vertex)))))) else (if i < 76 then (if i < 72 then (if i < 70 then decide (InPath q (316 : Vertex)) else (if i < 71 then decide (InPath q (317 : Vertex)) else decide (InPath q (318 : Vertex)))) else (if i < 74 then (if i < 73 then decide (InPath q (352 : Vertex)) else decide (InPath q (355 : Vertex))) else (if i < 75 then decide (InPath q (356 : Vertex)) else decide (InPath q (359 : Vertex))))) else (if i < 79 then (if i < 77 then decide (InPath q (364 : Vertex)) else (if i < 78 then decide (InPath q (372 : Vertex)) else decide (InPath q (373 : Vertex)))) else (if i < 81 then (if i < 80 then decide (InPath q (375 : Vertex)) else decide (InPath q (416 : Vertex))) else (if i < 82 then decide (InPath q (417 : Vertex)) else decide (InPath q (418 : Vertex))))))) else (if i < 97 then (if i < 90 then (if i < 86 then (if i < 84 then decide (InPath q (420 : Vertex)) else (if i < 85 then decide (InPath q (421 : Vertex)) else decide (InPath q (422 : Vertex)))) else (if i < 88 then (if i < 87 then decide (InPath q (423 : Vertex)) else decide (InPath q (424 : Vertex))) else (if i < 89 then decide (InPath q (426 : Vertex)) else decide (InPath q (427 : Vertex))))) else (if i < 93 then (if i < 91 then decide (InPath q (428 : Vertex)) else (if i < 92 then decide (InPath q (430 : Vertex)) else decide (InPath q (431 : Vertex)))) else (if i < 95 then (if i < 94 then decide (InPath q (433 : Vertex)) else decide (InPath q (435 : Vertex))) else (if i < 96 then decide (InPath q (436 : Vertex)) else decide (InPath q (437 : Vertex)))))) else (if i < 104 then (if i < 100 then (if i < 98 then decide (InPath q (439 : Vertex)) else (if i < 99 then decide (InPath q (440 : Vertex)) else decide (InPath q (441 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (442 : Vertex)) else decide (InPath q (443 : Vertex))) else (if i < 103 then decide (InPath q (447 : Vertex)) else decide (InPath q (480 : Vertex))))) else (if i < 107 then (if i < 105 then decide (InPath q (481 : Vertex)) else (if i < 106 then decide (InPath q (482 : Vertex)) else decide (InPath q (483 : Vertex)))) else (if i < 109 then (if i < 108 then decide (InPath q (485 : Vertex)) else decide (InPath q (486 : Vertex))) else (if i < 110 then decide (InPath q (488 : Vertex)) else decide (InPath q (491 : Vertex))))))))) else (if i < 166 then (if i < 138 then (if i < 124 then (if i < 117 then (if i < 114 then (if i < 112 then decide (InPath q (493 : Vertex)) else (if i < 113 then decide (InPath q (495 : Vertex)) else decide (InPath q (496 : Vertex)))) else (if i < 115 then decide (InPath q (497 : Vertex)) else (if i < 116 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex))))) else (if i < 120 then (if i < 118 then decide (InPath q (502 : Vertex)) else (if i < 119 then decide (InPath q (504 : Vertex)) else decide (InPath q (508 : Vertex)))) else (if i < 122 then (if i < 121 then decide (InPath q (509 : Vertex)) else decide (InPath q (510 : Vertex))) else (if i < 123 then decide (InPath q (511 : Vertex)) else decide (BallClauseLogic.Endpoint q (34 : Vertex)))))) else (if i < 131 then (if i < 127 then (if i < 125 then decide (BallClauseLogic.Endpoint q (35 : Vertex)) else (if i < 126 then decide (BallClauseLogic.Endpoint q (36 : Vertex)) else decide (BallClauseLogic.Endpoint q (37 : Vertex)))) else (if i < 129 then (if i < 128 then decide (BallClauseLogic.Endpoint q (40 : Vertex)) else decide (BallClauseLogic.Endpoint q (42 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (43 : Vertex)) else decide (BallClauseLogic.Endpoint q (44 : Vertex))))) else (if i < 134 then (if i < 132 then decide (BallClauseLogic.Endpoint q (46 : Vertex)) else (if i < 133 then decide (BallClauseLogic.Endpoint q (52 : Vertex)) else decide (BallClauseLogic.Endpoint q (53 : Vertex)))) else (if i < 136 then (if i < 135 then decide (BallClauseLogic.Endpoint q (55 : Vertex)) else decide (BallClauseLogic.Endpoint q (56 : Vertex))) else (if i < 137 then decide (BallClauseLogic.Endpoint q (57 : Vertex)) else decide (BallClauseLogic.Endpoint q (59 : Vertex))))))) else (if i < 152 then (if i < 145 then (if i < 141 then (if i < 139 then decide (BallClauseLogic.Endpoint q (63 : Vertex)) else (if i < 140 then decide (BallClauseLogic.Endpoint q (99 : Vertex)) else decide (BallClauseLogic.Endpoint q (100 : Vertex)))) else (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (103 : Vertex)) else decide (BallClauseLogic.Endpoint q (160 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (161 : Vertex)) else decide (BallClauseLogic.Endpoint q (166 : Vertex))))) else (if i < 148 then (if i < 146 then decide (BallClauseLogic.Endpoint q (167 : Vertex)) else (if i < 147 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else decide (BallClauseLogic.Endpoint q (169 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (171 : Vertex)) else decide (BallClauseLogic.Endpoint q (173 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else decide (BallClauseLogic.Endpoint q (177 : Vertex)))))) else (if i < 159 then (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (178 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (180 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (182 : Vertex)) else decide (BallClauseLogic.Endpoint q (186 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (188 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex))))) else (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (190 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else decide (BallClauseLogic.Endpoint q (227 : Vertex)))) else (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (228 : Vertex)) else decide (BallClauseLogic.Endpoint q (229 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (230 : Vertex)) else decide (BallClauseLogic.Endpoint q (234 : Vertex)))))))) else (if i < 194 then (if i < 180 then (if i < 173 then (if i < 169 then (if i < 167 then decide (BallClauseLogic.Endpoint q (235 : Vertex)) else (if i < 168 then decide (BallClauseLogic.Endpoint q (236 : Vertex)) else decide (BallClauseLogic.Endpoint q (238 : Vertex)))) else (if i < 171 then (if i < 170 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (245 : Vertex))) else (if i < 172 then decide (BallClauseLogic.Endpoint q (247 : Vertex)) else decide (BallClauseLogic.Endpoint q (248 : Vertex))))) else (if i < 176 then (if i < 174 then decide (BallClauseLogic.Endpoint q (249 : Vertex)) else (if i < 175 then decide (BallClauseLogic.Endpoint q (250 : Vertex)) else decide (BallClauseLogic.Endpoint q (251 : Vertex)))) else (if i < 178 then (if i < 177 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else decide (BallClauseLogic.Endpoint q (288 : Vertex))) else (if i < 179 then decide (BallClauseLogic.Endpoint q (289 : Vertex)) else decide (BallClauseLogic.Endpoint q (293 : Vertex)))))) else (if i < 187 then (if i < 183 then (if i < 181 then decide (BallClauseLogic.Endpoint q (294 : Vertex)) else (if i < 182 then decide (BallClauseLogic.Endpoint q (295 : Vertex)) else decide (BallClauseLogic.Endpoint q (296 : Vertex)))) else (if i < 185 then (if i < 184 then decide (BallClauseLogic.Endpoint q (299 : Vertex)) else decide (BallClauseLogic.Endpoint q (301 : Vertex))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (303 : Vertex)) else decide (BallClauseLogic.Endpoint q (304 : Vertex))))) else (if i < 190 then (if i < 188 then decide (BallClauseLogic.Endpoint q (305 : Vertex)) else (if i < 189 then decide (BallClauseLogic.Endpoint q (306 : Vertex)) else decide (BallClauseLogic.Endpoint q (307 : Vertex)))) else (if i < 192 then (if i < 191 then decide (BallClauseLogic.Endpoint q (310 : Vertex)) else decide (BallClauseLogic.Endpoint q (316 : Vertex))) else (if i < 193 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (318 : Vertex))))))) else (if i < 208 then (if i < 201 then (if i < 197 then (if i < 195 then decide (BallClauseLogic.Endpoint q (352 : Vertex)) else (if i < 196 then decide (BallClauseLogic.Endpoint q (355 : Vertex)) else decide (BallClauseLogic.Endpoint q (356 : Vertex)))) else (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (364 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (372 : Vertex)) else decide (BallClauseLogic.Endpoint q (373 : Vertex))))) else (if i < 204 then (if i < 202 then decide (BallClauseLogic.Endpoint q (375 : Vertex)) else (if i < 203 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex)))) else (if i < 206 then (if i < 205 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (420 : Vertex))) else (if i < 207 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex)))))) else (if i < 215 then (if i < 211 then (if i < 209 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else (if i < 210 then decide (BallClauseLogic.Endpoint q (424 : Vertex)) else decide (BallClauseLogic.Endpoint q (426 : Vertex)))) else (if i < 213 then (if i < 212 then decide (BallClauseLogic.Endpoint q (427 : Vertex)) else decide (BallClauseLogic.Endpoint q (428 : Vertex))) else (if i < 214 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (431 : Vertex))))) else (if i < 218 then (if i < 216 then decide (BallClauseLogic.Endpoint q (433 : Vertex)) else (if i < 217 then decide (BallClauseLogic.Endpoint q (435 : Vertex)) else decide (BallClauseLogic.Endpoint q (436 : Vertex)))) else (if i < 220 then (if i < 219 then decide (BallClauseLogic.Endpoint q (437 : Vertex)) else decide (BallClauseLogic.Endpoint q (439 : Vertex))) else (if i < 221 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else decide (BallClauseLogic.Endpoint q (441 : Vertex)))))))))) else (if i < 333 then (if i < 277 then (if i < 249 then (if i < 235 then (if i < 228 then (if i < 225 then (if i < 223 then decide (BallClauseLogic.Endpoint q (442 : Vertex)) else (if i < 224 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex)))) else (if i < 226 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else (if i < 227 then decide (BallClauseLogic.Endpoint q (481 : Vertex)) else decide (BallClauseLogic.Endpoint q (482 : Vertex))))) else (if i < 231 then (if i < 229 then decide (BallClauseLogic.Endpoint q (483 : Vertex)) else (if i < 230 then decide (BallClauseLogic.Endpoint q (485 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex)))) else (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (488 : Vertex)) else decide (BallClauseLogic.Endpoint q (491 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else decide (BallClauseLogic.Endpoint q (495 : Vertex)))))) else (if i < 242 then (if i < 238 then (if i < 236 then decide (BallClauseLogic.Endpoint q (496 : Vertex)) else (if i < 237 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex)))) else (if i < 240 then (if i < 239 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex))) else (if i < 241 then decide (BallClauseLogic.Endpoint q (504 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))))) else (if i < 245 then (if i < 243 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else (if i < 244 then decide (BallClauseLogic.Endpoint q (510 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex)))) else (if i < 247 then (if i < 246 then decide (1 ≤ count245 q) else decide (2 ≤ count245 q)) else (if i < 248 then decide (1 ≤ count247 q) else decide (2 ≤ count247 q)))))) else (if i < 263 then (if i < 256 then (if i < 252 then (if i < 250 then decide (1 ≤ count249 q) else (if i < 251 then decide (2 ≤ count249 q) else decide (1 ≤ count251 q))) else (if i < 254 then (if i < 253 then decide (2 ≤ count251 q) else decide (1 ≤ count253 q)) else (if i < 255 then decide (2 ≤ count253 q) else decide (1 ≤ count255 q)))) else (if i < 259 then (if i < 257 then decide (2 ≤ count255 q) else (if i < 258 then decide (1 ≤ count257 q) else decide (2 ≤ count257 q))) else (if i < 261 then (if i < 260 then decide (1 ≤ count259 q) else decide (2 ≤ count259 q)) else (if i < 262 then decide (1 ≤ count261 q) else decide (2 ≤ count261 q))))) else (if i < 270 then (if i < 266 then (if i < 264 then decide (1 ≤ count263 q) else (if i < 265 then decide (2 ≤ count263 q) else decide (1 ≤ count265 q))) else (if i < 268 then (if i < 267 then decide (2 ≤ count265 q) else decide (1 ≤ count267 q)) else (if i < 269 then decide (2 ≤ count267 q) else decide (1 ≤ count269 q)))) else (if i < 273 then (if i < 271 then decide (2 ≤ count269 q) else (if i < 272 then decide (1 ≤ count271 q) else decide (2 ≤ count271 q))) else (if i < 275 then (if i < 274 then decide (1 ≤ count273 q) else decide (2 ≤ count273 q)) else (if i < 276 then decide (1 ≤ count275 q) else decide (2 ≤ count275 q))))))) else (if i < 305 then (if i < 291 then (if i < 284 then (if i < 280 then (if i < 278 then decide (1 ≤ count277 q) else (if i < 279 then decide (2 ≤ count277 q) else decide (1 ≤ count279 q))) else (if i < 282 then (if i < 281 then decide (2 ≤ count279 q) else decide (1 ≤ count281 q)) else (if i < 283 then decide (2 ≤ count281 q) else decide (1 ≤ count283 q)))) else (if i < 287 then (if i < 285 then decide (2 ≤ count283 q) else (if i < 286 then decide (1 ≤ count285 q) else decide (2 ≤ count285 q))) else (if i < 289 then (if i < 288 then decide (1 ≤ count287 q) else decide (2 ≤ count287 q)) else (if i < 290 then decide (1 ≤ count289 q) else decide (2 ≤ count289 q))))) else (if i < 298 then (if i < 294 then (if i < 292 then decide (1 ≤ count291 q) else (if i < 293 then decide (2 ≤ count291 q) else decide (1 ≤ count293 q))) else (if i < 296 then (if i < 295 then decide (2 ≤ count293 q) else decide (1 ≤ count295 q)) else (if i < 297 then decide (2 ≤ count295 q) else decide (1 ≤ count297 q)))) else (if i < 301 then (if i < 299 then decide (2 ≤ count297 q) else (if i < 300 then decide (1 ≤ count299 q) else decide (2 ≤ count299 q))) else (if i < 303 then (if i < 302 then decide (1 ≤ count301 q) else decide (2 ≤ count301 q)) else (if i < 304 then decide (1 ≤ count303 q) else decide (2 ≤ count303 q)))))) else (if i < 319 then (if i < 312 then (if i < 308 then (if i < 306 then decide (1 ≤ count305 q) else (if i < 307 then decide (2 ≤ count305 q) else decide (1 ≤ count307 q))) else (if i < 310 then (if i < 309 then decide (2 ≤ count307 q) else decide (1 ≤ count309 q)) else (if i < 311 then decide (2 ≤ count309 q) else decide (1 ≤ count311 q)))) else (if i < 315 then (if i < 313 then decide (2 ≤ count311 q) else (if i < 314 then decide (1 ≤ count313 q) else decide (2 ≤ count313 q))) else (if i < 317 then (if i < 316 then decide (1 ≤ count315 q) else decide (2 ≤ count315 q)) else (if i < 318 then decide (1 ≤ count317 q) else decide (2 ≤ count317 q))))) else (if i < 326 then (if i < 322 then (if i < 320 then decide (1 ≤ count319 q) else (if i < 321 then decide (2 ≤ count319 q) else decide (1 ≤ count321 q))) else (if i < 324 then (if i < 323 then decide (2 ≤ count321 q) else decide (1 ≤ count323 q)) else (if i < 325 then decide (2 ≤ count323 q) else decide (1 ≤ count325 q)))) else (if i < 329 then (if i < 327 then decide (2 ≤ count325 q) else (if i < 328 then decide (1 ≤ count327 q) else decide (2 ≤ count327 q))) else (if i < 331 then (if i < 330 then decide (1 ≤ count329 q) else decide (2 ≤ count329 q)) else (if i < 332 then decide (1 ≤ count331 q) else decide (2 ≤ count331 q)))))))) else (if i < 389 then (if i < 361 then (if i < 347 then (if i < 340 then (if i < 336 then (if i < 334 then decide (1 ≤ count333 q) else (if i < 335 then decide (2 ≤ count333 q) else decide (1 ≤ count335 q))) else (if i < 338 then (if i < 337 then decide (2 ≤ count335 q) else decide (1 ≤ count337 q)) else (if i < 339 then decide (2 ≤ count337 q) else decide (1 ≤ count339 q)))) else (if i < 343 then (if i < 341 then decide (2 ≤ count339 q) else (if i < 342 then decide (1 ≤ count341 q) else decide (2 ≤ count341 q))) else (if i < 345 then (if i < 344 then decide (1 ≤ count343 q) else decide (2 ≤ count343 q)) else (if i < 346 then decide (1 ≤ count345 q) else decide (2 ≤ count345 q))))) else (if i < 354 then (if i < 350 then (if i < 348 then decide (1 ≤ count347 q) else (if i < 349 then decide (2 ≤ count347 q) else decide (1 ≤ count349 q))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 q) else decide (1 ≤ count351 q)) else (if i < 353 then decide (2 ≤ count351 q) else decide (1 ≤ count353 q)))) else (if i < 357 then (if i < 355 then decide (2 ≤ count353 q) else (if i < 356 then decide (1 ≤ count355 q) else decide (2 ≤ count355 q))) else (if i < 359 then (if i < 358 then decide (1 ≤ count357 q) else decide (2 ≤ count357 q)) else (if i < 360 then decide (1 ≤ count359 q) else decide (2 ≤ count359 q)))))) else (if i < 375 then (if i < 368 then (if i < 364 then (if i < 362 then decide (1 ≤ count361 q) else (if i < 363 then decide (2 ≤ count361 q) else decide (1 ≤ count363 q))) else (if i < 366 then (if i < 365 then decide (2 ≤ count363 q) else decide (1 ≤ count365 q)) else (if i < 367 then decide (2 ≤ count365 q) else decide (1 ≤ count367 q)))) else (if i < 371 then (if i < 369 then decide (2 ≤ count367 q) else (if i < 370 then decide (1 ≤ count369 q) else decide (2 ≤ count369 q))) else (if i < 373 then (if i < 372 then decide (1 ≤ count371 q) else decide (2 ≤ count371 q)) else (if i < 374 then decide (1 ≤ count373 q) else decide (2 ≤ count373 q))))) else (if i < 382 then (if i < 378 then (if i < 376 then decide (1 ≤ count375 q) else (if i < 377 then decide (2 ≤ count375 q) else decide (1 ≤ count377 q))) else (if i < 380 then (if i < 379 then decide (2 ≤ count377 q) else decide (1 ≤ count379 q)) else (if i < 381 then decide (2 ≤ count379 q) else decide (1 ≤ count381 q)))) else (if i < 385 then (if i < 383 then decide (2 ≤ count381 q) else (if i < 384 then decide (1 ≤ count383 q) else decide (2 ≤ count383 q))) else (if i < 387 then (if i < 386 then decide (1 ≤ count385 q) else decide (2 ≤ count385 q)) else (if i < 388 then decide (1 ≤ count387 q) else decide (2 ≤ count387 q))))))) else (if i < 417 then (if i < 403 then (if i < 396 then (if i < 392 then (if i < 390 then decide (1 ≤ count389 q) else (if i < 391 then decide (2 ≤ count389 q) else decide (1 ≤ count391 q))) else (if i < 394 then (if i < 393 then decide (2 ≤ count391 q) else decide (1 ≤ count393 q)) else (if i < 395 then decide (2 ≤ count393 q) else decide (1 ≤ count395 q)))) else (if i < 399 then (if i < 397 then decide (2 ≤ count395 q) else (if i < 398 then decide (1 ≤ count397 q) else decide (2 ≤ count397 q))) else (if i < 401 then (if i < 400 then decide (1 ≤ count399 q) else decide (2 ≤ count399 q)) else (if i < 402 then decide (1 ≤ count401 q) else decide (2 ≤ count401 q))))) else (if i < 410 then (if i < 406 then (if i < 404 then decide (1 ≤ count403 q) else (if i < 405 then decide (2 ≤ count403 q) else decide (1 ≤ count405 q))) else (if i < 408 then (if i < 407 then decide (2 ≤ count405 q) else decide (1 ≤ count407 q)) else (if i < 409 then decide (2 ≤ count407 q) else decide (1 ≤ count409 q)))) else (if i < 413 then (if i < 411 then decide (2 ≤ count409 q) else (if i < 412 then decide (1 ≤ count411 q) else decide (2 ≤ count411 q))) else (if i < 415 then (if i < 414 then decide (1 ≤ count413 q) else decide (2 ≤ count413 q)) else (if i < 416 then decide (1 ≤ count415 q) else decide (2 ≤ count415 q)))))) else (if i < 431 then (if i < 424 then (if i < 420 then (if i < 418 then decide (1 ≤ count417 q) else (if i < 419 then decide (2 ≤ count417 q) else decide (1 ≤ count419 q))) else (if i < 422 then (if i < 421 then decide (2 ≤ count419 q) else decide (1 ≤ count421 q)) else (if i < 423 then decide (2 ≤ count421 q) else decide (1 ≤ count423 q)))) else (if i < 427 then (if i < 425 then decide (2 ≤ count423 q) else (if i < 426 then decide (1 ≤ count425 q) else decide (2 ≤ count425 q))) else (if i < 429 then (if i < 428 then decide (1 ≤ count427 q) else decide (2 ≤ count427 q)) else (if i < 430 then decide (1 ≤ count429 q) else decide (2 ≤ count429 q))))) else (if i < 438 then (if i < 434 then (if i < 432 then decide (1 ≤ count431 q) else (if i < 433 then decide (2 ≤ count431 q) else decide (1 ≤ count433 q))) else (if i < 436 then (if i < 435 then decide (2 ≤ count433 q) else decide (1 ≤ count435 q)) else (if i < 437 then decide (2 ≤ count435 q) else decide (1 ≤ count437 q)))) else (if i < 441 then (if i < 439 then decide (2 ≤ count437 q) else (if i < 440 then decide (1 ≤ count439 q) else decide (2 ≤ count439 q))) else (if i < 443 then (if i < 442 then decide (1 ≤ count441 q) else decide (2 ≤ count441 q)) else (if i < 444 then decide (1 ≤ count443 q) else decide (2 ≤ count443 q)))))))))) else (if i < 667 then (if i < 556 then (if i < 500 then (if i < 472 then (if i < 458 then (if i < 451 then (if i < 448 then (if i < 446 then decide (1 ≤ count445 q) else (if i < 447 then decide (2 ≤ count445 q) else decide (1 ≤ count447 q))) else (if i < 449 then decide (2 ≤ count447 q) else (if i < 450 then decide (1 ≤ count449 q) else decide (2 ≤ count449 q)))) else (if i < 454 then (if i < 452 then decide (1 ≤ count451 q) else (if i < 453 then decide (2 ≤ count451 q) else decide (1 ≤ count453 q))) else (if i < 456 then (if i < 455 then decide (2 ≤ count453 q) else decide (1 ≤ count455 q)) else (if i < 457 then decide (2 ≤ count455 q) else decide (1 ≤ count457 q))))) else (if i < 465 then (if i < 461 then (if i < 459 then decide (2 ≤ count457 q) else (if i < 460 then decide (1 ≤ count459 q) else decide (2 ≤ count459 q))) else (if i < 463 then (if i < 462 then decide (1 ≤ count461 q) else decide (2 ≤ count461 q)) else (if i < 464 then decide (1 ≤ count463 q) else decide (2 ≤ count463 q)))) else (if i < 468 then (if i < 466 then decide (1 ≤ count465 q) else (if i < 467 then decide (2 ≤ count465 q) else decide (1 ≤ count467 q))) else (if i < 470 then (if i < 469 then decide (2 ≤ count467 q) else decide (1 ≤ count469 q)) else (if i < 471 then decide (2 ≤ count469 q) else decide (1 ≤ count471 q)))))) else (if i < 486 then (if i < 479 then (if i < 475 then (if i < 473 then decide (2 ≤ count471 q) else (if i < 474 then decide (1 ≤ count473 q) else decide (2 ≤ count473 q))) else (if i < 477 then (if i < 476 then decide (1 ≤ count475 q) else decide (2 ≤ count475 q)) else (if i < 478 then decide (1 ≤ count477 q) else decide (2 ≤ count477 q)))) else (if i < 482 then (if i < 480 then decide (1 ≤ count479 q) else (if i < 481 then decide (2 ≤ count479 q) else decide (1 ≤ count481 q))) else (if i < 484 then (if i < 483 then decide (2 ≤ count481 q) else decide (1 ≤ count483 q)) else (if i < 485 then decide (2 ≤ count483 q) else decide (1 ≤ count485 q))))) else (if i < 493 then (if i < 489 then (if i < 487 then decide (2 ≤ count485 q) else (if i < 488 then decide (1 ≤ count487 q) else decide (2 ≤ count487 q))) else (if i < 491 then (if i < 490 then decide (3 ≤ count487 q) else decide (1 ≤ count490 q)) else (if i < 492 then decide (2 ≤ count490 q) else decide (1 ≤ count492 q)))) else (if i < 496 then (if i < 494 then decide (2 ≤ count492 q) else (if i < 495 then decide (1 ≤ count494 q) else decide (2 ≤ count494 q))) else (if i < 498 then (if i < 497 then decide (3 ≤ count494 q) else decide (4 ≤ count494 q)) else (if i < 499 then decide (1 ≤ count498 q) else decide (2 ≤ count498 q))))))) else (if i < 528 then (if i < 514 then (if i < 507 then (if i < 503 then (if i < 501 then decide (3 ≤ count498 q) else (if i < 502 then decide (4 ≤ count498 q) else decide (5 ≤ count498 q))) else (if i < 505 then (if i < 504 then decide (6 ≤ count498 q) else decide (7 ≤ count498 q)) else (if i < 506 then decide (1 ≤ count505 q) else decide (2 ≤ count505 q)))) else (if i < 510 then (if i < 508 then decide (1 ≤ count507 q) else (if i < 509 then decide (2 ≤ count507 q) else decide (3 ≤ count507 q))) else (if i < 512 then (if i < 511 then decide (1 ≤ count510 q) else decide (2 ≤ count510 q)) else (if i < 513 then decide (1 ≤ count512 q) else decide (2 ≤ count512 q))))) else (if i < 521 then (if i < 517 then (if i < 515 then decide (1 ≤ count514 q) else (if i < 516 then decide (2 ≤ count514 q) else decide (3 ≤ count514 q))) else (if i < 519 then (if i < 518 then decide (4 ≤ count514 q) else decide (1 ≤ count518 q)) else (if i < 520 then decide (2 ≤ count518 q) else decide (3 ≤ count518 q)))) else (if i < 524 then (if i < 522 then decide (4 ≤ count518 q) else (if i < 523 then decide (5 ≤ count518 q) else decide (6 ≤ count518 q))) else (if i < 526 then (if i < 525 then decide (7 ≤ count518 q) else decide (1 ≤ count525 q)) else (if i < 527 then decide (2 ≤ count525 q) else decide (3 ≤ count525 q)))))) else (if i < 542 then (if i < 535 then (if i < 531 then (if i < 529 then decide (4 ≤ count525 q) else (if i < 530 then decide (5 ≤ count525 q) else decide (6 ≤ count525 q))) else (if i < 533 then (if i < 532 then decide (7 ≤ count525 q) else decide (8 ≤ count525 q)) else (if i < 534 then decide (9 ≤ count525 q) else decide (10 ≤ count525 q)))) else (if i < 538 then (if i < 536 then decide (11 ≤ count525 q) else (if i < 537 then decide (12 ≤ count525 q) else decide (13 ≤ count525 q))) else (if i < 540 then (if i < 539 then decide (14 ≤ count525 q) else decide (1 ≤ count539 q)) else (if i < 541 then decide (2 ≤ count539 q) else decide (1 ≤ count541 q))))) else (if i < 549 then (if i < 545 then (if i < 543 then decide (2 ≤ count541 q) else (if i < 544 then decide (3 ≤ count541 q) else decide (1 ≤ count544 q))) else (if i < 547 then (if i < 546 then decide (2 ≤ count544 q) else decide (1 ≤ count546 q)) else (if i < 548 then decide (2 ≤ count546 q) else decide (1 ≤ count548 q)))) else (if i < 552 then (if i < 550 then decide (2 ≤ count548 q) else (if i < 551 then decide (3 ≤ count548 q) else decide (4 ≤ count548 q))) else (if i < 554 then (if i < 553 then decide (1 ≤ count552 q) else decide (2 ≤ count552 q)) else (if i < 555 then decide (3 ≤ count552 q) else decide (4 ≤ count552 q)))))))) else (if i < 611 then (if i < 583 then (if i < 569 then (if i < 562 then (if i < 559 then (if i < 557 then decide (5 ≤ count552 q) else (if i < 558 then decide (6 ≤ count552 q) else decide (7 ≤ count552 q))) else (if i < 560 then decide (1 ≤ count559 q) else (if i < 561 then decide (2 ≤ count559 q) else decide (1 ≤ count561 q)))) else (if i < 565 then (if i < 563 then decide (2 ≤ count561 q) else (if i < 564 then decide (1 ≤ count563 q) else decide (2 ≤ count563 q))) else (if i < 567 then (if i < 566 then decide (3 ≤ count563 q) else decide (4 ≤ count563 q)) else (if i < 568 then decide (1 ≤ count567 q) else decide (2 ≤ count567 q))))) else (if i < 576 then (if i < 572 then (if i < 570 then decide (1 ≤ count569 q) else (if i < 571 then decide (2 ≤ count569 q) else decide (1 ≤ count571 q))) else (if i < 574 then (if i < 573 then decide (2 ≤ count571 q) else decide (3 ≤ count571 q)) else (if i < 575 then decide (4 ≤ count571 q) else decide (1 ≤ count575 q)))) else (if i < 579 then (if i < 577 then decide (2 ≤ count575 q) else (if i < 578 then decide (3 ≤ count575 q) else decide (4 ≤ count575 q))) else (if i < 581 then (if i < 580 then decide (5 ≤ count575 q) else decide (6 ≤ count575 q)) else (if i < 582 then decide (7 ≤ count575 q) else decide (8 ≤ count575 q)))))) else (if i < 597 then (if i < 590 then (if i < 586 then (if i < 584 then decide (1 ≤ count583 q) else (if i < 585 then decide (2 ≤ count583 q) else decide (3 ≤ count583 q))) else (if i < 588 then (if i < 587 then decide (4 ≤ count583 q) else decide (5 ≤ count583 q)) else (if i < 589 then decide (6 ≤ count583 q) else decide (7 ≤ count583 q)))) else (if i < 593 then (if i < 591 then decide (8 ≤ count583 q) else (if i < 592 then decide (9 ≤ count583 q) else decide (10 ≤ count583 q))) else (if i < 595 then (if i < 594 then decide (11 ≤ count583 q) else decide (12 ≤ count583 q)) else (if i < 596 then decide (13 ≤ count583 q) else decide (14 ≤ count583 q))))) else (if i < 604 then (if i < 600 then (if i < 598 then decide (15 ≤ count583 q) else (if i < 599 then decide (1 ≤ count598 q) else decide (2 ≤ count598 q))) else (if i < 602 then (if i < 601 then decide (3 ≤ count598 q) else decide (4 ≤ count598 q)) else (if i < 603 then decide (5 ≤ count598 q) else decide (6 ≤ count598 q)))) else (if i < 607 then (if i < 605 then decide (7 ≤ count598 q) else (if i < 606 then decide (8 ≤ count598 q) else decide (9 ≤ count598 q))) else (if i < 609 then (if i < 608 then decide (10 ≤ count598 q) else decide (11 ≤ count598 q)) else (if i < 610 then decide (12 ≤ count598 q) else decide (13 ≤ count598 q))))))) else (if i < 639 then (if i < 625 then (if i < 618 then (if i < 614 then (if i < 612 then decide (14 ≤ count598 q) else (if i < 613 then decide (15 ≤ count598 q) else decide (16 ≤ count598 q))) else (if i < 616 then (if i < 615 then decide (17 ≤ count598 q) else decide (18 ≤ count598 q)) else (if i < 617 then decide (19 ≤ count598 q) else decide (20 ≤ count598 q)))) else (if i < 621 then (if i < 619 then decide (21 ≤ count598 q) else (if i < 620 then decide (22 ≤ count598 q) else decide (23 ≤ count598 q))) else (if i < 623 then (if i < 622 then decide (24 ≤ count598 q) else decide (25 ≤ count598 q)) else (if i < 624 then decide (26 ≤ count598 q) else decide (27 ≤ count598 q))))) else (if i < 632 then (if i < 628 then (if i < 626 then decide (28 ≤ count598 q) else (if i < 627 then decide (29 ≤ count598 q) else decide (1 ≤ count627 q))) else (if i < 630 then (if i < 629 then decide (2 ≤ count627 q) else decide (1 ≤ count629 q)) else (if i < 631 then decide (2 ≤ count629 q) else decide (3 ≤ count629 q)))) else (if i < 635 then (if i < 633 then decide (1 ≤ count632 q) else (if i < 634 then decide (2 ≤ count632 q) else decide (1 ≤ count634 q))) else (if i < 637 then (if i < 636 then decide (2 ≤ count634 q) else decide (1 ≤ count636 q)) else (if i < 638 then decide (2 ≤ count636 q) else decide (3 ≤ count636 q)))))) else (if i < 653 then (if i < 646 then (if i < 642 then (if i < 640 then decide (4 ≤ count636 q) else (if i < 641 then decide (1 ≤ count640 q) else decide (2 ≤ count640 q))) else (if i < 644 then (if i < 643 then decide (3 ≤ count640 q) else decide (4 ≤ count640 q)) else (if i < 645 then decide (5 ≤ count640 q) else decide (6 ≤ count640 q)))) else (if i < 649 then (if i < 647 then decide (7 ≤ count640 q) else (if i < 648 then decide (1 ≤ count647 q) else decide (2 ≤ count647 q))) else (if i < 651 then (if i < 650 then decide (1 ≤ count649 q) else decide (2 ≤ count649 q)) else (if i < 652 then decide (1 ≤ count651 q) else decide (2 ≤ count651 q))))) else (if i < 660 then (if i < 656 then (if i < 654 then decide (3 ≤ count651 q) else (if i < 655 then decide (4 ≤ count651 q) else decide (1 ≤ count655 q))) else (if i < 658 then (if i < 657 then decide (2 ≤ count655 q) else decide (1 ≤ count657 q)) else (if i < 659 then decide (2 ≤ count657 q) else decide (1 ≤ count659 q)))) else (if i < 663 then (if i < 661 then decide (2 ≤ count659 q) else (if i < 662 then decide (3 ≤ count659 q) else decide (4 ≤ count659 q))) else (if i < 665 then (if i < 664 then decide (1 ≤ count663 q) else decide (2 ≤ count663 q)) else (if i < 666 then decide (3 ≤ count663 q) else decide (4 ≤ count663 q))))))))) else (if i < 778 then (if i < 722 then (if i < 694 then (if i < 680 then (if i < 673 then (if i < 670 then (if i < 668 then decide (5 ≤ count663 q) else (if i < 669 then decide (6 ≤ count663 q) else decide (7 ≤ count663 q))) else (if i < 671 then decide (8 ≤ count663 q) else (if i < 672 then decide (1 ≤ count671 q) else decide (2 ≤ count671 q)))) else (if i < 676 then (if i < 674 then decide (3 ≤ count671 q) else (if i < 675 then decide (4 ≤ count671 q) else decide (5 ≤ count671 q))) else (if i < 678 then (if i < 677 then decide (6 ≤ count671 q) else decide (7 ≤ count671 q)) else (if i < 679 then decide (8 ≤ count671 q) else decide (9 ≤ count671 q))))) else (if i < 687 then (if i < 683 then (if i < 681 then decide (10 ≤ count671 q) else (if i < 682 then decide (11 ≤ count671 q) else decide (12 ≤ count671 q))) else (if i < 685 then (if i < 684 then decide (13 ≤ count671 q) else decide (14 ≤ count671 q)) else (if i < 686 then decide (15 ≤ count671 q) else decide (1 ≤ count686 q)))) else (if i < 690 then (if i < 688 then decide (2 ≤ count686 q) else (if i < 689 then decide (1 ≤ count688 q) else decide (2 ≤ count688 q))) else (if i < 692 then (if i < 691 then decide (3 ≤ count688 q) else decide (1 ≤ count691 q)) else (if i < 693 then decide (2 ≤ count691 q) else decide (1 ≤ count693 q)))))) else (if i < 708 then (if i < 701 then (if i < 697 then (if i < 695 then decide (2 ≤ count693 q) else (if i < 696 then decide (1 ≤ count695 q) else decide (2 ≤ count695 q))) else (if i < 699 then (if i < 698 then decide (3 ≤ count695 q) else decide (4 ≤ count695 q)) else (if i < 700 then decide (1 ≤ count699 q) else decide (2 ≤ count699 q)))) else (if i < 704 then (if i < 702 then decide (3 ≤ count699 q) else (if i < 703 then decide (4 ≤ count699 q) else decide (5 ≤ count699 q))) else (if i < 706 then (if i < 705 then decide (6 ≤ count699 q) else decide (7 ≤ count699 q)) else (if i < 707 then decide (1 ≤ count706 q) else decide (2 ≤ count706 q))))) else (if i < 715 then (if i < 711 then (if i < 709 then decide (1 ≤ count708 q) else (if i < 710 then decide (2 ≤ count708 q) else decide (1 ≤ count710 q))) else (if i < 713 then (if i < 712 then decide (2 ≤ count710 q) else decide (3 ≤ count710 q)) else (if i < 714 then decide (4 ≤ count710 q) else decide (1 ≤ count714 q)))) else (if i < 718 then (if i < 716 then decide (2 ≤ count714 q) else (if i < 717 then decide (1 ≤ count716 q) else decide (2 ≤ count716 q))) else (if i < 720 then (if i < 719 then decide (1 ≤ count718 q) else decide (2 ≤ count718 q)) else (if i < 721 then decide (3 ≤ count718 q) else decide (4 ≤ count718 q))))))) else (if i < 750 then (if i < 736 then (if i < 729 then (if i < 725 then (if i < 723 then decide (1 ≤ count722 q) else (if i < 724 then decide (2 ≤ count722 q) else decide (3 ≤ count722 q))) else (if i < 727 then (if i < 726 then decide (4 ≤ count722 q) else decide (5 ≤ count722 q)) else (if i < 728 then decide (6 ≤ count722 q) else decide (7 ≤ count722 q)))) else (if i < 732 then (if i < 730 then decide (8 ≤ count722 q) else (if i < 731 then decide (1 ≤ count730 q) else decide (2 ≤ count730 q))) else (if i < 734 then (if i < 733 then decide (3 ≤ count730 q) else decide (4 ≤ count730 q)) else (if i < 735 then decide (5 ≤ count730 q) else decide (6 ≤ count730 q))))) else (if i < 743 then (if i < 739 then (if i < 737 then decide (7 ≤ count730 q) else (if i < 738 then decide (8 ≤ count730 q) else decide (9 ≤ count730 q))) else (if i < 741 then (if i < 740 then decide (10 ≤ count730 q) else decide (11 ≤ count730 q)) else (if i < 742 then decide (12 ≤ count730 q) else decide (13 ≤ count730 q)))) else (if i < 746 then (if i < 744 then decide (14 ≤ count730 q) else (if i < 745 then decide (15 ≤ count730 q) else decide (1 ≤ count745 q))) else (if i < 748 then (if i < 747 then decide (2 ≤ count745 q) else decide (3 ≤ count745 q)) else (if i < 749 then decide (4 ≤ count745 q) else decide (5 ≤ count745 q)))))) else (if i < 764 then (if i < 757 then (if i < 753 then (if i < 751 then decide (6 ≤ count745 q) else (if i < 752 then decide (7 ≤ count745 q) else decide (8 ≤ count745 q))) else (if i < 755 then (if i < 754 then decide (9 ≤ count745 q) else decide (10 ≤ count745 q)) else (if i < 756 then decide (11 ≤ count745 q) else decide (12 ≤ count745 q)))) else (if i < 760 then (if i < 758 then decide (13 ≤ count745 q) else (if i < 759 then decide (14 ≤ count745 q) else decide (15 ≤ count745 q))) else (if i < 762 then (if i < 761 then decide (16 ≤ count745 q) else decide (17 ≤ count745 q)) else (if i < 763 then decide (18 ≤ count745 q) else decide (19 ≤ count745 q))))) else (if i < 771 then (if i < 767 then (if i < 765 then decide (20 ≤ count745 q) else (if i < 766 then decide (21 ≤ count745 q) else decide (22 ≤ count745 q))) else (if i < 769 then (if i < 768 then decide (23 ≤ count745 q) else decide (24 ≤ count745 q)) else (if i < 770 then decide (25 ≤ count745 q) else decide (26 ≤ count745 q)))) else (if i < 774 then (if i < 772 then decide (27 ≤ count745 q) else (if i < 773 then decide (28 ≤ count745 q) else decide (29 ≤ count745 q))) else (if i < 776 then (if i < 775 then decide (30 ≤ count745 q) else decide (1 ≤ count775 q)) else (if i < 777 then decide (2 ≤ count775 q) else decide (3 ≤ count775 q)))))))) else (if i < 834 then (if i < 806 then (if i < 792 then (if i < 785 then (if i < 781 then (if i < 779 then decide (4 ≤ count775 q) else (if i < 780 then decide (5 ≤ count775 q) else decide (6 ≤ count775 q))) else (if i < 783 then (if i < 782 then decide (7 ≤ count775 q) else decide (8 ≤ count775 q)) else (if i < 784 then decide (9 ≤ count775 q) else decide (10 ≤ count775 q)))) else (if i < 788 then (if i < 786 then decide (11 ≤ count775 q) else (if i < 787 then decide (12 ≤ count775 q) else decide (13 ≤ count775 q))) else (if i < 790 then (if i < 789 then decide (14 ≤ count775 q) else decide (15 ≤ count775 q)) else (if i < 791 then decide (16 ≤ count775 q) else decide (17 ≤ count775 q))))) else (if i < 799 then (if i < 795 then (if i < 793 then decide (18 ≤ count775 q) else (if i < 794 then decide (19 ≤ count775 q) else decide (20 ≤ count775 q))) else (if i < 797 then (if i < 796 then decide (21 ≤ count775 q) else decide (22 ≤ count775 q)) else (if i < 798 then decide (23 ≤ count775 q) else decide (24 ≤ count775 q)))) else (if i < 802 then (if i < 800 then decide (25 ≤ count775 q) else (if i < 801 then decide (26 ≤ count775 q) else decide (27 ≤ count775 q))) else (if i < 804 then (if i < 803 then decide (28 ≤ count775 q) else decide (29 ≤ count775 q)) else (if i < 805 then decide (30 ≤ count775 q) else decide (31 ≤ count775 q)))))) else (if i < 820 then (if i < 813 then (if i < 809 then (if i < 807 then decide (32 ≤ count775 q) else (if i < 808 then decide (33 ≤ count775 q) else decide (34 ≤ count775 q))) else (if i < 811 then (if i < 810 then decide (35 ≤ count775 q) else decide (36 ≤ count775 q)) else (if i < 812 then decide (37 ≤ count775 q) else decide (38 ≤ count775 q)))) else (if i < 816 then (if i < 814 then decide (39 ≤ count775 q) else (if i < 815 then decide (40 ≤ count775 q) else decide (41 ≤ count775 q))) else (if i < 818 then (if i < 817 then decide (42 ≤ count775 q) else decide (1 ≤ count817 q)) else (if i < 819 then decide (2 ≤ count817 q) else decide (1 ≤ count819 q))))) else (if i < 827 then (if i < 823 then (if i < 821 then decide (2 ≤ count819 q) else (if i < 822 then decide (3 ≤ count819 q) else decide (1 ≤ count822 q))) else (if i < 825 then (if i < 824 then decide (2 ≤ count822 q) else decide (1 ≤ count824 q)) else (if i < 826 then decide (2 ≤ count824 q) else decide (1 ≤ count826 q)))) else (if i < 830 then (if i < 828 then decide (2 ≤ count826 q) else (if i < 829 then decide (3 ≤ count826 q) else decide (4 ≤ count826 q))) else (if i < 832 then (if i < 831 then decide (1 ≤ count830 q) else decide (2 ≤ count830 q)) else (if i < 833 then decide (3 ≤ count830 q) else decide (4 ≤ count830 q))))))) else (if i < 862 then (if i < 848 then (if i < 841 then (if i < 837 then (if i < 835 then decide (5 ≤ count830 q) else (if i < 836 then decide (6 ≤ count830 q) else decide (7 ≤ count830 q))) else (if i < 839 then (if i < 838 then decide (1 ≤ count837 q) else decide (2 ≤ count837 q)) else (if i < 840 then decide (1 ≤ count839 q) else decide (2 ≤ count839 q)))) else (if i < 844 then (if i < 842 then decide (3 ≤ count839 q) else (if i < 843 then decide (1 ≤ count842 q) else decide (2 ≤ count842 q))) else (if i < 846 then (if i < 845 then decide (1 ≤ count844 q) else decide (2 ≤ count844 q)) else (if i < 847 then decide (1 ≤ count846 q) else decide (2 ≤ count846 q))))) else (if i < 855 then (if i < 851 then (if i < 849 then decide (3 ≤ count846 q) else (if i < 850 then decide (4 ≤ count846 q) else decide (1 ≤ count850 q))) else (if i < 853 then (if i < 852 then decide (2 ≤ count850 q) else decide (3 ≤ count850 q)) else (if i < 854 then decide (4 ≤ count850 q) else decide (5 ≤ count850 q)))) else (if i < 858 then (if i < 856 then decide (6 ≤ count850 q) else (if i < 857 then decide (7 ≤ count850 q) else decide (1 ≤ count857 q))) else (if i < 860 then (if i < 859 then decide (2 ≤ count857 q) else decide (3 ≤ count857 q)) else (if i < 861 then decide (4 ≤ count857 q) else decide (5 ≤ count857 q)))))) else (if i < 876 then (if i < 869 then (if i < 865 then (if i < 863 then decide (6 ≤ count857 q) else (if i < 864 then decide (7 ≤ count857 q) else decide (8 ≤ count857 q))) else (if i < 867 then (if i < 866 then decide (9 ≤ count857 q) else decide (10 ≤ count857 q)) else (if i < 868 then decide (11 ≤ count857 q) else decide (12 ≤ count857 q)))) else (if i < 872 then (if i < 870 then decide (13 ≤ count857 q) else (if i < 871 then decide (14 ≤ count857 q) else decide (1 ≤ count871 q))) else (if i < 874 then (if i < 873 then decide (2 ≤ count871 q) else decide (1 ≤ count873 q)) else (if i < 875 then decide (2 ≤ count873 q) else decide (3 ≤ count873 q))))) else (if i < 883 then (if i < 879 then (if i < 877 then decide (1 ≤ count876 q) else (if i < 878 then decide (2 ≤ count876 q) else decide (1 ≤ count878 q))) else (if i < 881 then (if i < 880 then decide (2 ≤ count878 q) else decide (1 ≤ count880 q)) else (if i < 882 then decide (2 ≤ count880 q) else decide (3 ≤ count880 q)))) else (if i < 886 then (if i < 884 then decide (4 ≤ count880 q) else (if i < 885 then decide (1 ≤ count884 q) else decide (2 ≤ count884 q))) else (if i < 888 then (if i < 887 then decide (3 ≤ count884 q) else decide (4 ≤ count884 q)) else (if i < 889 then decide (5 ≤ count884 q) else decide (6 ≤ count884 q))))))))))) else (if i < 1335 then (if i < 1112 then (if i < 1001 then (if i < 945 then (if i < 917 then (if i < 903 then (if i < 896 then (if i < 893 then (if i < 891 then decide (7 ≤ count884 q) else (if i < 892 then decide (1 ≤ count891 q) else decide (2 ≤ count891 q))) else (if i < 894 then decide (1 ≤ count893 q) else (if i < 895 then decide (2 ≤ count893 q) else decide (1 ≤ count895 q)))) else (if i < 899 then (if i < 897 then decide (2 ≤ count895 q) else (if i < 898 then decide (3 ≤ count895 q) else decide (4 ≤ count895 q))) else (if i < 901 then (if i < 900 then decide (1 ≤ count899 q) else decide (2 ≤ count899 q)) else (if i < 902 then decide (1 ≤ count901 q) else decide (2 ≤ count901 q))))) else (if i < 910 then (if i < 906 then (if i < 904 then decide (1 ≤ count903 q) else (if i < 905 then decide (2 ≤ count903 q) else decide (3 ≤ count903 q))) else (if i < 908 then (if i < 907 then decide (4 ≤ count903 q) else decide (1 ≤ count907 q)) else (if i < 909 then decide (2 ≤ count907 q) else decide (3 ≤ count907 q)))) else (if i < 913 then (if i < 911 then decide (4 ≤ count907 q) else (if i < 912 then decide (5 ≤ count907 q) else decide (6 ≤ count907 q))) else (if i < 915 then (if i < 914 then decide (7 ≤ count907 q) else decide (8 ≤ count907 q)) else (if i < 916 then decide (1 ≤ count915 q) else decide (2 ≤ count915 q)))))) else (if i < 931 then (if i < 924 then (if i < 920 then (if i < 918 then decide (3 ≤ count915 q) else (if i < 919 then decide (4 ≤ count915 q) else decide (5 ≤ count915 q))) else (if i < 922 then (if i < 921 then decide (6 ≤ count915 q) else decide (7 ≤ count915 q)) else (if i < 923 then decide (8 ≤ count915 q) else decide (9 ≤ count915 q)))) else (if i < 927 then (if i < 925 then decide (10 ≤ count915 q) else (if i < 926 then decide (11 ≤ count915 q) else decide (12 ≤ count915 q))) else (if i < 929 then (if i < 928 then decide (13 ≤ count915 q) else decide (14 ≤ count915 q)) else (if i < 930 then decide (15 ≤ count915 q) else decide (1 ≤ count930 q))))) else (if i < 938 then (if i < 934 then (if i < 932 then decide (2 ≤ count930 q) else (if i < 933 then decide (3 ≤ count930 q) else decide (4 ≤ count930 q))) else (if i < 936 then (if i < 935 then decide (5 ≤ count930 q) else decide (6 ≤ count930 q)) else (if i < 937 then decide (7 ≤ count930 q) else decide (8 ≤ count930 q)))) else (if i < 941 then (if i < 939 then decide (9 ≤ count930 q) else (if i < 940 then decide (10 ≤ count930 q) else decide (11 ≤ count930 q))) else (if i < 943 then (if i < 942 then decide (12 ≤ count930 q) else decide (13 ≤ count930 q)) else (if i < 944 then decide (14 ≤ count930 q) else decide (15 ≤ count930 q))))))) else (if i < 973 then (if i < 959 then (if i < 952 then (if i < 948 then (if i < 946 then decide (16 ≤ count930 q) else (if i < 947 then decide (17 ≤ count930 q) else decide (18 ≤ count930 q))) else (if i < 950 then (if i < 949 then decide (19 ≤ count930 q) else decide (1 ≤ count949 q)) else (if i < 951 then decide (2 ≤ count949 q) else decide (1 ≤ count951 q)))) else (if i < 955 then (if i < 953 then decide (2 ≤ count951 q) else (if i < 954 then decide (3 ≤ count951 q) else decide (1 ≤ count954 q))) else (if i < 957 then (if i < 956 then decide (2 ≤ count954 q) else decide (1 ≤ count956 q)) else (if i < 958 then decide (2 ≤ count956 q) else decide (1 ≤ count958 q))))) else (if i < 966 then (if i < 962 then (if i < 960 then decide (2 ≤ count958 q) else (if i < 961 then decide (3 ≤ count958 q) else decide (4 ≤ count958 q))) else (if i < 964 then (if i < 963 then decide (1 ≤ count962 q) else decide (2 ≤ count962 q)) else (if i < 965 then decide (3 ≤ count962 q) else decide (4 ≤ count962 q)))) else (if i < 969 then (if i < 967 then decide (5 ≤ count962 q) else (if i < 968 then decide (6 ≤ count962 q) else decide (7 ≤ count962 q))) else (if i < 971 then (if i < 970 then decide (1 ≤ count969 q) else decide (2 ≤ count969 q)) else (if i < 972 then decide (1 ≤ count971 q) else decide (2 ≤ count971 q)))))) else (if i < 987 then (if i < 980 then (if i < 976 then (if i < 974 then decide (1 ≤ count973 q) else (if i < 975 then decide (2 ≤ count973 q) else decide (3 ≤ count973 q))) else (if i < 978 then (if i < 977 then decide (4 ≤ count973 q) else decide (1 ≤ count977 q)) else (if i < 979 then decide (2 ≤ count977 q) else decide (1 ≤ count979 q)))) else (if i < 983 then (if i < 981 then decide (2 ≤ count979 q) else (if i < 982 then decide (1 ≤ count981 q) else decide (2 ≤ count981 q))) else (if i < 985 then (if i < 984 then decide (3 ≤ count981 q) else decide (4 ≤ count981 q)) else (if i < 986 then decide (1 ≤ count985 q) else decide (2 ≤ count985 q))))) else (if i < 994 then (if i < 990 then (if i < 988 then decide (3 ≤ count985 q) else (if i < 989 then decide (4 ≤ count985 q) else decide (5 ≤ count985 q))) else (if i < 992 then (if i < 991 then decide (6 ≤ count985 q) else decide (7 ≤ count985 q)) else (if i < 993 then decide (8 ≤ count985 q) else decide (1 ≤ count993 q)))) else (if i < 997 then (if i < 995 then decide (2 ≤ count993 q) else (if i < 996 then decide (3 ≤ count993 q) else decide (4 ≤ count993 q))) else (if i < 999 then (if i < 998 then decide (5 ≤ count993 q) else decide (6 ≤ count993 q)) else (if i < 1000 then decide (7 ≤ count993 q) else decide (8 ≤ count993 q)))))))) else (if i < 1056 then (if i < 1028 then (if i < 1014 then (if i < 1007 then (if i < 1004 then (if i < 1002 then decide (9 ≤ count993 q) else (if i < 1003 then decide (10 ≤ count993 q) else decide (11 ≤ count993 q))) else (if i < 1005 then decide (12 ≤ count993 q) else (if i < 1006 then decide (13 ≤ count993 q) else decide (14 ≤ count993 q)))) else (if i < 1010 then (if i < 1008 then decide (15 ≤ count993 q) else (if i < 1009 then decide (1 ≤ count1008 q) else decide (2 ≤ count1008 q))) else (if i < 1012 then (if i < 1011 then decide (1 ≤ count1010 q) else decide (2 ≤ count1010 q)) else (if i < 1013 then decide (3 ≤ count1010 q) else decide (1 ≤ count1013 q))))) else (if i < 1021 then (if i < 1017 then (if i < 1015 then decide (2 ≤ count1013 q) else (if i < 1016 then decide (1 ≤ count1015 q) else decide (2 ≤ count1015 q))) else (if i < 1019 then (if i < 1018 then decide (1 ≤ count1017 q) else decide (2 ≤ count1017 q)) else (if i < 1020 then decide (3 ≤ count1017 q) else decide (4 ≤ count1017 q)))) else (if i < 1024 then (if i < 1022 then decide (1 ≤ count1021 q) else (if i < 1023 then decide (2 ≤ count1021 q) else decide (3 ≤ count1021 q))) else (if i < 1026 then (if i < 1025 then decide (4 ≤ count1021 q) else decide (5 ≤ count1021 q)) else (if i < 1027 then decide (6 ≤ count1021 q) else decide (7 ≤ count1021 q)))))) else (if i < 1042 then (if i < 1035 then (if i < 1031 then (if i < 1029 then decide (1 ≤ count1028 q) else (if i < 1030 then decide (2 ≤ count1028 q) else decide (1 ≤ count1030 q))) else (if i < 1033 then (if i < 1032 then decide (2 ≤ count1030 q) else decide (1 ≤ count1032 q)) else (if i < 1034 then decide (2 ≤ count1032 q) else decide (3 ≤ count1032 q)))) else (if i < 1038 then (if i < 1036 then decide (4 ≤ count1032 q) else (if i < 1037 then decide (1 ≤ count1036 q) else decide (2 ≤ count1036 q))) else (if i < 1040 then (if i < 1039 then decide (1 ≤ count1038 q) else decide (2 ≤ count1038 q)) else (if i < 1041 then decide (1 ≤ count1040 q) else decide (2 ≤ count1040 q))))) else (if i < 1049 then (if i < 1045 then (if i < 1043 then decide (3 ≤ count1040 q) else (if i < 1044 then decide (4 ≤ count1040 q) else decide (1 ≤ count1044 q))) else (if i < 1047 then (if i < 1046 then decide (2 ≤ count1044 q) else decide (3 ≤ count1044 q)) else (if i < 1048 then decide (4 ≤ count1044 q) else decide (5 ≤ count1044 q)))) else (if i < 1052 then (if i < 1050 then decide (6 ≤ count1044 q) else (if i < 1051 then decide (7 ≤ count1044 q) else decide (8 ≤ count1044 q))) else (if i < 1054 then (if i < 1053 then decide (1 ≤ count1052 q) else decide (2 ≤ count1052 q)) else (if i < 1055 then decide (3 ≤ count1052 q) else decide (4 ≤ count1052 q))))))) else (if i < 1084 then (if i < 1070 then (if i < 1063 then (if i < 1059 then (if i < 1057 then decide (5 ≤ count1052 q) else (if i < 1058 then decide (6 ≤ count1052 q) else decide (7 ≤ count1052 q))) else (if i < 1061 then (if i < 1060 then decide (8 ≤ count1052 q) else decide (9 ≤ count1052 q)) else (if i < 1062 then decide (10 ≤ count1052 q) else decide (11 ≤ count1052 q)))) else (if i < 1066 then (if i < 1064 then decide (12 ≤ count1052 q) else (if i < 1065 then decide (13 ≤ count1052 q) else decide (14 ≤ count1052 q))) else (if i < 1068 then (if i < 1067 then decide (15 ≤ count1052 q) else decide (1 ≤ count1067 q)) else (if i < 1069 then decide (2 ≤ count1067 q) else decide (3 ≤ count1067 q))))) else (if i < 1077 then (if i < 1073 then (if i < 1071 then decide (4 ≤ count1067 q) else (if i < 1072 then decide (5 ≤ count1067 q) else decide (6 ≤ count1067 q))) else (if i < 1075 then (if i < 1074 then decide (7 ≤ count1067 q) else decide (8 ≤ count1067 q)) else (if i < 1076 then decide (9 ≤ count1067 q) else decide (10 ≤ count1067 q)))) else (if i < 1080 then (if i < 1078 then decide (11 ≤ count1067 q) else (if i < 1079 then decide (12 ≤ count1067 q) else decide (13 ≤ count1067 q))) else (if i < 1082 then (if i < 1081 then decide (14 ≤ count1067 q) else decide (15 ≤ count1067 q)) else (if i < 1083 then decide (16 ≤ count1067 q) else decide (17 ≤ count1067 q)))))) else (if i < 1098 then (if i < 1091 then (if i < 1087 then (if i < 1085 then decide (18 ≤ count1067 q) else (if i < 1086 then decide (19 ≤ count1067 q) else decide (1 ≤ count1086 q))) else (if i < 1089 then (if i < 1088 then decide (2 ≤ count1086 q) else decide (3 ≤ count1086 q)) else (if i < 1090 then decide (4 ≤ count1086 q) else decide (5 ≤ count1086 q)))) else (if i < 1094 then (if i < 1092 then decide (6 ≤ count1086 q) else (if i < 1093 then decide (7 ≤ count1086 q) else decide (8 ≤ count1086 q))) else (if i < 1096 then (if i < 1095 then decide (9 ≤ count1086 q) else decide (10 ≤ count1086 q)) else (if i < 1097 then decide (11 ≤ count1086 q) else decide (12 ≤ count1086 q))))) else (if i < 1105 then (if i < 1101 then (if i < 1099 then decide (13 ≤ count1086 q) else (if i < 1100 then decide (14 ≤ count1086 q) else decide (15 ≤ count1086 q))) else (if i < 1103 then (if i < 1102 then decide (16 ≤ count1086 q) else decide (17 ≤ count1086 q)) else (if i < 1104 then decide (18 ≤ count1086 q) else decide (19 ≤ count1086 q)))) else (if i < 1108 then (if i < 1106 then decide (1 ≤ count1105 q) else (if i < 1107 then decide (2 ≤ count1105 q) else decide (1 ≤ count1107 q))) else (if i < 1110 then (if i < 1109 then decide (2 ≤ count1107 q) else decide (3 ≤ count1107 q)) else (if i < 1111 then decide (1 ≤ count1110 q) else decide (2 ≤ count1110 q))))))))) else (if i < 1223 then (if i < 1167 then (if i < 1139 then (if i < 1125 then (if i < 1118 then (if i < 1115 then (if i < 1113 then decide (1 ≤ count1112 q) else (if i < 1114 then decide (2 ≤ count1112 q) else decide (1 ≤ count1114 q))) else (if i < 1116 then decide (2 ≤ count1114 q) else (if i < 1117 then decide (3 ≤ count1114 q) else decide (4 ≤ count1114 q)))) else (if i < 1121 then (if i < 1119 then decide (1 ≤ count1118 q) else (if i < 1120 then decide (2 ≤ count1118 q) else decide (3 ≤ count1118 q))) else (if i < 1123 then (if i < 1122 then decide (4 ≤ count1118 q) else decide (5 ≤ count1118 q)) else (if i < 1124 then decide (6 ≤ count1118 q) else decide (7 ≤ count1118 q))))) else (if i < 1132 then (if i < 1128 then (if i < 1126 then decide (1 ≤ count1125 q) else (if i < 1127 then decide (2 ≤ count1125 q) else decide (1 ≤ count1127 q))) else (if i < 1130 then (if i < 1129 then decide (2 ≤ count1127 q) else decide (1 ≤ count1129 q)) else (if i < 1131 then decide (2 ≤ count1129 q) else decide (3 ≤ count1129 q)))) else (if i < 1135 then (if i < 1133 then decide (4 ≤ count1129 q) else (if i < 1134 then decide (1 ≤ count1133 q) else decide (2 ≤ count1133 q))) else (if i < 1137 then (if i < 1136 then decide (1 ≤ count1135 q) else decide (2 ≤ count1135 q)) else (if i < 1138 then decide (1 ≤ count1137 q) else decide (2 ≤ count1137 q)))))) else (if i < 1153 then (if i < 1146 then (if i < 1142 then (if i < 1140 then decide (3 ≤ count1137 q) else (if i < 1141 then decide (4 ≤ count1137 q) else decide (1 ≤ count1141 q))) else (if i < 1144 then (if i < 1143 then decide (2 ≤ count1141 q) else decide (3 ≤ count1141 q)) else (if i < 1145 then decide (4 ≤ count1141 q) else decide (5 ≤ count1141 q)))) else (if i < 1149 then (if i < 1147 then decide (6 ≤ count1141 q) else (if i < 1148 then decide (7 ≤ count1141 q) else decide (8 ≤ count1141 q))) else (if i < 1151 then (if i < 1150 then decide (1 ≤ count1149 q) else decide (2 ≤ count1149 q)) else (if i < 1152 then decide (3 ≤ count1149 q) else decide (4 ≤ count1149 q))))) else (if i < 1160 then (if i < 1156 then (if i < 1154 then decide (5 ≤ count1149 q) else (if i < 1155 then decide (6 ≤ count1149 q) else decide (7 ≤ count1149 q))) else (if i < 1158 then (if i < 1157 then decide (8 ≤ count1149 q) else decide (9 ≤ count1149 q)) else (if i < 1159 then decide (10 ≤ count1149 q) else decide (11 ≤ count1149 q)))) else (if i < 1163 then (if i < 1161 then decide (12 ≤ count1149 q) else (if i < 1162 then decide (13 ≤ count1149 q) else decide (14 ≤ count1149 q))) else (if i < 1165 then (if i < 1164 then decide (15 ≤ count1149 q) else decide (1 ≤ count1164 q)) else (if i < 1166 then decide (2 ≤ count1164 q) else decide (1 ≤ count1166 q))))))) else (if i < 1195 then (if i < 1181 then (if i < 1174 then (if i < 1170 then (if i < 1168 then decide (2 ≤ count1166 q) else (if i < 1169 then decide (1 ≤ count1168 q) else decide (2 ≤ count1168 q))) else (if i < 1172 then (if i < 1171 then decide (3 ≤ count1168 q) else decide (4 ≤ count1168 q)) else (if i < 1173 then decide (1 ≤ count1172 q) else decide (2 ≤ count1172 q)))) else (if i < 1177 then (if i < 1175 then decide (1 ≤ count1174 q) else (if i < 1176 then decide (2 ≤ count1174 q) else decide (1 ≤ count1176 q))) else (if i < 1179 then (if i < 1178 then decide (2 ≤ count1176 q) else decide (3 ≤ count1176 q)) else (if i < 1180 then decide (4 ≤ count1176 q) else decide (1 ≤ count1180 q))))) else (if i < 1188 then (if i < 1184 then (if i < 1182 then decide (2 ≤ count1180 q) else (if i < 1183 then decide (3 ≤ count1180 q) else decide (4 ≤ count1180 q))) else (if i < 1186 then (if i < 1185 then decide (5 ≤ count1180 q) else decide (6 ≤ count1180 q)) else (if i < 1187 then decide (7 ≤ count1180 q) else decide (8 ≤ count1180 q)))) else (if i < 1191 then (if i < 1189 then decide (1 ≤ count1188 q) else (if i < 1190 then decide (2 ≤ count1188 q) else decide (1 ≤ count1190 q))) else (if i < 1193 then (if i < 1192 then decide (2 ≤ count1190 q) else decide (1 ≤ count1192 q)) else (if i < 1194 then decide (2 ≤ count1192 q) else decide (3 ≤ count1192 q)))))) else (if i < 1209 then (if i < 1202 then (if i < 1198 then (if i < 1196 then decide (4 ≤ count1192 q) else (if i < 1197 then decide (1 ≤ count1196 q) else decide (2 ≤ count1196 q))) else (if i < 1200 then (if i < 1199 then decide (1 ≤ count1198 q) else decide (2 ≤ count1198 q)) else (if i < 1201 then decide (1 ≤ count1200 q) else decide (2 ≤ count1200 q)))) else (if i < 1205 then (if i < 1203 then decide (3 ≤ count1200 q) else (if i < 1204 then decide (4 ≤ count1200 q) else decide (1 ≤ count1204 q))) else (if i < 1207 then (if i < 1206 then decide (2 ≤ count1204 q) else decide (3 ≤ count1204 q)) else (if i < 1208 then decide (4 ≤ count1204 q) else decide (5 ≤ count1204 q))))) else (if i < 1216 then (if i < 1212 then (if i < 1210 then decide (6 ≤ count1204 q) else (if i < 1211 then decide (7 ≤ count1204 q) else decide (8 ≤ count1204 q))) else (if i < 1214 then (if i < 1213 then decide (1 ≤ count1212 q) else decide (2 ≤ count1212 q)) else (if i < 1215 then decide (3 ≤ count1212 q) else decide (4 ≤ count1212 q)))) else (if i < 1219 then (if i < 1217 then decide (5 ≤ count1212 q) else (if i < 1218 then decide (6 ≤ count1212 q) else decide (7 ≤ count1212 q))) else (if i < 1221 then (if i < 1220 then decide (8 ≤ count1212 q) else decide (9 ≤ count1212 q)) else (if i < 1222 then decide (10 ≤ count1212 q) else decide (11 ≤ count1212 q)))))))) else (if i < 1279 then (if i < 1251 then (if i < 1237 then (if i < 1230 then (if i < 1226 then (if i < 1224 then decide (12 ≤ count1212 q) else (if i < 1225 then decide (13 ≤ count1212 q) else decide (14 ≤ count1212 q))) else (if i < 1228 then (if i < 1227 then decide (15 ≤ count1212 q) else decide (16 ≤ count1212 q)) else (if i < 1229 then decide (1 ≤ count1228 q) else decide (2 ≤ count1228 q)))) else (if i < 1233 then (if i < 1231 then decide (3 ≤ count1228 q) else (if i < 1232 then decide (4 ≤ count1228 q) else decide (5 ≤ count1228 q))) else (if i < 1235 then (if i < 1234 then decide (6 ≤ count1228 q) else decide (7 ≤ count1228 q)) else (if i < 1236 then decide (8 ≤ count1228 q) else decide (9 ≤ count1228 q))))) else (if i < 1244 then (if i < 1240 then (if i < 1238 then decide (10 ≤ count1228 q) else (if i < 1239 then decide (11 ≤ count1228 q) else decide (12 ≤ count1228 q))) else (if i < 1242 then (if i < 1241 then decide (13 ≤ count1228 q) else decide (14 ≤ count1228 q)) else (if i < 1243 then decide (15 ≤ count1228 q) else decide (16 ≤ count1228 q)))) else (if i < 1247 then (if i < 1245 then decide (17 ≤ count1228 q) else (if i < 1246 then decide (18 ≤ count1228 q) else decide (19 ≤ count1228 q))) else (if i < 1249 then (if i < 1248 then decide (20 ≤ count1228 q) else decide (21 ≤ count1228 q)) else (if i < 1250 then decide (22 ≤ count1228 q) else decide (23 ≤ count1228 q)))))) else (if i < 1265 then (if i < 1258 then (if i < 1254 then (if i < 1252 then decide (24 ≤ count1228 q) else (if i < 1253 then decide (25 ≤ count1228 q) else decide (26 ≤ count1228 q))) else (if i < 1256 then (if i < 1255 then decide (27 ≤ count1228 q) else decide (28 ≤ count1228 q)) else (if i < 1257 then decide (29 ≤ count1228 q) else decide (30 ≤ count1228 q)))) else (if i < 1261 then (if i < 1259 then decide (31 ≤ count1228 q) else (if i < 1260 then decide (1 ≤ count1259 q) else decide (2 ≤ count1259 q))) else (if i < 1263 then (if i < 1262 then decide (1 ≤ count1261 q) else decide (2 ≤ count1261 q)) else (if i < 1264 then decide (1 ≤ count1263 q) else decide (2 ≤ count1263 q))))) else (if i < 1272 then (if i < 1268 then (if i < 1266 then decide (3 ≤ count1263 q) else (if i < 1267 then decide (4 ≤ count1263 q) else decide (1 ≤ count1267 q))) else (if i < 1270 then (if i < 1269 then decide (2 ≤ count1267 q) else decide (1 ≤ count1269 q)) else (if i < 1271 then decide (2 ≤ count1269 q) else decide (1 ≤ count1271 q)))) else (if i < 1275 then (if i < 1273 then decide (2 ≤ count1271 q) else (if i < 1274 then decide (3 ≤ count1271 q) else decide (4 ≤ count1271 q))) else (if i < 1277 then (if i < 1276 then decide (1 ≤ count1275 q) else decide (2 ≤ count1275 q)) else (if i < 1278 then decide (3 ≤ count1275 q) else decide (4 ≤ count1275 q))))))) else (if i < 1307 then (if i < 1293 then (if i < 1286 then (if i < 1282 then (if i < 1280 then decide (5 ≤ count1275 q) else (if i < 1281 then decide (6 ≤ count1275 q) else decide (7 ≤ count1275 q))) else (if i < 1284 then (if i < 1283 then decide (8 ≤ count1275 q) else decide (1 ≤ count1283 q)) else (if i < 1285 then decide (2 ≤ count1283 q) else decide (1 ≤ count1285 q)))) else (if i < 1289 then (if i < 1287 then decide (2 ≤ count1285 q) else (if i < 1288 then decide (1 ≤ count1287 q) else decide (2 ≤ count1287 q))) else (if i < 1291 then (if i < 1290 then decide (3 ≤ count1287 q) else decide (4 ≤ count1287 q)) else (if i < 1292 then decide (1 ≤ count1291 q) else decide (2 ≤ count1291 q))))) else (if i < 1300 then (if i < 1296 then (if i < 1294 then decide (1 ≤ count1293 q) else (if i < 1295 then decide (2 ≤ count1293 q) else decide (1 ≤ count1295 q))) else (if i < 1298 then (if i < 1297 then decide (2 ≤ count1295 q) else decide (3 ≤ count1295 q)) else (if i < 1299 then decide (4 ≤ count1295 q) else decide (1 ≤ count1299 q)))) else (if i < 1303 then (if i < 1301 then decide (2 ≤ count1299 q) else (if i < 1302 then decide (3 ≤ count1299 q) else decide (4 ≤ count1299 q))) else (if i < 1305 then (if i < 1304 then decide (5 ≤ count1299 q) else decide (6 ≤ count1299 q)) else (if i < 1306 then decide (7 ≤ count1299 q) else decide (8 ≤ count1299 q)))))) else (if i < 1321 then (if i < 1314 then (if i < 1310 then (if i < 1308 then decide (1 ≤ count1307 q) else (if i < 1309 then decide (2 ≤ count1307 q) else decide (3 ≤ count1307 q))) else (if i < 1312 then (if i < 1311 then decide (4 ≤ count1307 q) else decide (5 ≤ count1307 q)) else (if i < 1313 then decide (6 ≤ count1307 q) else decide (7 ≤ count1307 q)))) else (if i < 1317 then (if i < 1315 then decide (8 ≤ count1307 q) else (if i < 1316 then decide (9 ≤ count1307 q) else decide (10 ≤ count1307 q))) else (if i < 1319 then (if i < 1318 then decide (11 ≤ count1307 q) else decide (12 ≤ count1307 q)) else (if i < 1320 then decide (13 ≤ count1307 q) else decide (14 ≤ count1307 q))))) else (if i < 1328 then (if i < 1324 then (if i < 1322 then decide (15 ≤ count1307 q) else (if i < 1323 then decide (16 ≤ count1307 q) else decide (1 ≤ count1323 q))) else (if i < 1326 then (if i < 1325 then decide (2 ≤ count1323 q) else decide (1 ≤ count1325 q)) else (if i < 1327 then decide (2 ≤ count1325 q) else decide (1 ≤ count1327 q)))) else (if i < 1331 then (if i < 1329 then decide (2 ≤ count1327 q) else (if i < 1330 then decide (3 ≤ count1327 q) else decide (4 ≤ count1327 q))) else (if i < 1333 then (if i < 1332 then decide (1 ≤ count1331 q) else decide (2 ≤ count1331 q)) else (if i < 1334 then decide (1 ≤ count1333 q) else decide (2 ≤ count1333 q)))))))))) else (if i < 1558 then (if i < 1446 then (if i < 1390 then (if i < 1362 then (if i < 1348 then (if i < 1341 then (if i < 1338 then (if i < 1336 then decide (1 ≤ count1335 q) else (if i < 1337 then decide (2 ≤ count1335 q) else decide (3 ≤ count1335 q))) else (if i < 1339 then decide (4 ≤ count1335 q) else (if i < 1340 then decide (1 ≤ count1339 q) else decide (2 ≤ count1339 q)))) else (if i < 1344 then (if i < 1342 then decide (3 ≤ count1339 q) else (if i < 1343 then decide (4 ≤ count1339 q) else decide (5 ≤ count1339 q))) else (if i < 1346 then (if i < 1345 then decide (6 ≤ count1339 q) else decide (7 ≤ count1339 q)) else (if i < 1347 then decide (8 ≤ count1339 q) else decide (1 ≤ count1347 q))))) else (if i < 1355 then (if i < 1351 then (if i < 1349 then decide (2 ≤ count1347 q) else (if i < 1350 then decide (1 ≤ count1349 q) else decide (2 ≤ count1349 q))) else (if i < 1353 then (if i < 1352 then decide (1 ≤ count1351 q) else decide (2 ≤ count1351 q)) else (if i < 1354 then decide (3 ≤ count1351 q) else decide (4 ≤ count1351 q)))) else (if i < 1358 then (if i < 1356 then decide (1 ≤ count1355 q) else (if i < 1357 then decide (2 ≤ count1355 q) else decide (1 ≤ count1357 q))) else (if i < 1360 then (if i < 1359 then decide (2 ≤ count1357 q) else decide (1 ≤ count1359 q)) else (if i < 1361 then decide (2 ≤ count1359 q) else decide (3 ≤ count1359 q)))))) else (if i < 1376 then (if i < 1369 then (if i < 1365 then (if i < 1363 then decide (4 ≤ count1359 q) else (if i < 1364 then decide (1 ≤ count1363 q) else decide (2 ≤ count1363 q))) else (if i < 1367 then (if i < 1366 then decide (3 ≤ count1363 q) else decide (4 ≤ count1363 q)) else (if i < 1368 then decide (5 ≤ count1363 q) else decide (6 ≤ count1363 q)))) else (if i < 1372 then (if i < 1370 then decide (7 ≤ count1363 q) else (if i < 1371 then decide (8 ≤ count1363 q) else decide (1 ≤ count1371 q))) else (if i < 1374 then (if i < 1373 then decide (2 ≤ count1371 q) else decide (3 ≤ count1371 q)) else (if i < 1375 then decide (4 ≤ count1371 q) else decide (5 ≤ count1371 q))))) else (if i < 1383 then (if i < 1379 then (if i < 1377 then decide (6 ≤ count1371 q) else (if i < 1378 then decide (7 ≤ count1371 q) else decide (8 ≤ count1371 q))) else (if i < 1381 then (if i < 1380 then decide (9 ≤ count1371 q) else decide (10 ≤ count1371 q)) else (if i < 1382 then decide (11 ≤ count1371 q) else decide (12 ≤ count1371 q)))) else (if i < 1386 then (if i < 1384 then decide (13 ≤ count1371 q) else (if i < 1385 then decide (14 ≤ count1371 q) else decide (15 ≤ count1371 q))) else (if i < 1388 then (if i < 1387 then decide (16 ≤ count1371 q) else decide (1 ≤ count1387 q)) else (if i < 1389 then decide (2 ≤ count1387 q) else decide (3 ≤ count1387 q))))))) else (if i < 1418 then (if i < 1404 then (if i < 1397 then (if i < 1393 then (if i < 1391 then decide (4 ≤ count1387 q) else (if i < 1392 then decide (5 ≤ count1387 q) else decide (6 ≤ count1387 q))) else (if i < 1395 then (if i < 1394 then decide (7 ≤ count1387 q) else decide (8 ≤ count1387 q)) else (if i < 1396 then decide (9 ≤ count1387 q) else decide (10 ≤ count1387 q)))) else (if i < 1400 then (if i < 1398 then decide (11 ≤ count1387 q) else (if i < 1399 then decide (12 ≤ count1387 q) else decide (13 ≤ count1387 q))) else (if i < 1402 then (if i < 1401 then decide (14 ≤ count1387 q) else decide (15 ≤ count1387 q)) else (if i < 1403 then decide (16 ≤ count1387 q) else decide (17 ≤ count1387 q))))) else (if i < 1411 then (if i < 1407 then (if i < 1405 then decide (18 ≤ count1387 q) else (if i < 1406 then decide (19 ≤ count1387 q) else decide (20 ≤ count1387 q))) else (if i < 1409 then (if i < 1408 then decide (21 ≤ count1387 q) else decide (22 ≤ count1387 q)) else (if i < 1410 then decide (23 ≤ count1387 q) else decide (24 ≤ count1387 q)))) else (if i < 1414 then (if i < 1412 then decide (25 ≤ count1387 q) else (if i < 1413 then decide (26 ≤ count1387 q) else decide (27 ≤ count1387 q))) else (if i < 1416 then (if i < 1415 then decide (28 ≤ count1387 q) else decide (29 ≤ count1387 q)) else (if i < 1417 then decide (30 ≤ count1387 q) else decide (31 ≤ count1387 q)))))) else (if i < 1432 then (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (32 ≤ count1387 q) else (if i < 1420 then decide (1 ≤ count1419 q) else decide (2 ≤ count1419 q))) else (if i < 1423 then (if i < 1422 then decide (3 ≤ count1419 q) else decide (4 ≤ count1419 q)) else (if i < 1424 then decide (5 ≤ count1419 q) else decide (6 ≤ count1419 q)))) else (if i < 1428 then (if i < 1426 then decide (7 ≤ count1419 q) else (if i < 1427 then decide (8 ≤ count1419 q) else decide (9 ≤ count1419 q))) else (if i < 1430 then (if i < 1429 then decide (10 ≤ count1419 q) else decide (11 ≤ count1419 q)) else (if i < 1431 then decide (12 ≤ count1419 q) else decide (13 ≤ count1419 q))))) else (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (14 ≤ count1419 q) else (if i < 1434 then decide (15 ≤ count1419 q) else decide (16 ≤ count1419 q))) else (if i < 1437 then (if i < 1436 then decide (17 ≤ count1419 q) else decide (18 ≤ count1419 q)) else (if i < 1438 then decide (19 ≤ count1419 q) else decide (20 ≤ count1419 q)))) else (if i < 1442 then (if i < 1440 then decide (21 ≤ count1419 q) else (if i < 1441 then decide (22 ≤ count1419 q) else decide (23 ≤ count1419 q))) else (if i < 1444 then (if i < 1443 then decide (24 ≤ count1419 q) else decide (25 ≤ count1419 q)) else (if i < 1445 then decide (26 ≤ count1419 q) else decide (27 ≤ count1419 q)))))))) else (if i < 1502 then (if i < 1474 then (if i < 1460 then (if i < 1453 then (if i < 1449 then (if i < 1447 then decide (28 ≤ count1419 q) else (if i < 1448 then decide (29 ≤ count1419 q) else decide (30 ≤ count1419 q))) else (if i < 1451 then (if i < 1450 then decide (31 ≤ count1419 q) else decide (32 ≤ count1419 q)) else (if i < 1452 then decide (33 ≤ count1419 q) else decide (34 ≤ count1419 q)))) else (if i < 1456 then (if i < 1454 then decide (35 ≤ count1419 q) else (if i < 1455 then decide (36 ≤ count1419 q) else decide (37 ≤ count1419 q))) else (if i < 1458 then (if i < 1457 then decide (38 ≤ count1419 q) else decide (39 ≤ count1419 q)) else (if i < 1459 then decide (40 ≤ count1419 q) else decide (41 ≤ count1419 q))))) else (if i < 1467 then (if i < 1463 then (if i < 1461 then decide (42 ≤ count1419 q) else (if i < 1462 then decide (1 ≤ count1461 q) else decide (2 ≤ count1461 q))) else (if i < 1465 then (if i < 1464 then decide (1 ≤ count1463 q) else decide (2 ≤ count1463 q)) else (if i < 1466 then decide (3 ≤ count1463 q) else decide (1 ≤ count1466 q)))) else (if i < 1470 then (if i < 1468 then decide (2 ≤ count1466 q) else (if i < 1469 then decide (1 ≤ count1468 q) else decide (2 ≤ count1468 q))) else (if i < 1472 then (if i < 1471 then decide (1 ≤ count1470 q) else decide (2 ≤ count1470 q)) else (if i < 1473 then decide (3 ≤ count1470 q) else decide (4 ≤ count1470 q)))))) else (if i < 1488 then (if i < 1481 then (if i < 1477 then (if i < 1475 then decide (1 ≤ count1474 q) else (if i < 1476 then decide (2 ≤ count1474 q) else decide (3 ≤ count1474 q))) else (if i < 1479 then (if i < 1478 then decide (4 ≤ count1474 q) else decide (5 ≤ count1474 q)) else (if i < 1480 then decide (6 ≤ count1474 q) else decide (7 ≤ count1474 q)))) else (if i < 1484 then (if i < 1482 then decide (1 ≤ count1481 q) else (if i < 1483 then decide (2 ≤ count1481 q) else decide (1 ≤ count1483 q))) else (if i < 1486 then (if i < 1485 then decide (2 ≤ count1483 q) else decide (1 ≤ count1485 q)) else (if i < 1487 then decide (2 ≤ count1485 q) else decide (3 ≤ count1485 q))))) else (if i < 1495 then (if i < 1491 then (if i < 1489 then decide (4 ≤ count1485 q) else (if i < 1490 then decide (1 ≤ count1489 q) else decide (2 ≤ count1489 q))) else (if i < 1493 then (if i < 1492 then decide (1 ≤ count1491 q) else decide (2 ≤ count1491 q)) else (if i < 1494 then decide (1 ≤ count1493 q) else decide (2 ≤ count1493 q)))) else (if i < 1498 then (if i < 1496 then decide (3 ≤ count1493 q) else (if i < 1497 then decide (4 ≤ count1493 q) else decide (1 ≤ count1497 q))) else (if i < 1500 then (if i < 1499 then decide (2 ≤ count1497 q) else decide (3 ≤ count1497 q)) else (if i < 1501 then decide (4 ≤ count1497 q) else decide (5 ≤ count1497 q))))))) else (if i < 1530 then (if i < 1516 then (if i < 1509 then (if i < 1505 then (if i < 1503 then decide (6 ≤ count1497 q) else (if i < 1504 then decide (7 ≤ count1497 q) else decide (8 ≤ count1497 q))) else (if i < 1507 then (if i < 1506 then decide (1 ≤ count1505 q) else decide (2 ≤ count1505 q)) else (if i < 1508 then decide (3 ≤ count1505 q) else decide (4 ≤ count1505 q)))) else (if i < 1512 then (if i < 1510 then decide (5 ≤ count1505 q) else (if i < 1511 then decide (6 ≤ count1505 q) else decide (7 ≤ count1505 q))) else (if i < 1514 then (if i < 1513 then decide (8 ≤ count1505 q) else decide (9 ≤ count1505 q)) else (if i < 1515 then decide (10 ≤ count1505 q) else decide (11 ≤ count1505 q))))) else (if i < 1523 then (if i < 1519 then (if i < 1517 then decide (12 ≤ count1505 q) else (if i < 1518 then decide (13 ≤ count1505 q) else decide (14 ≤ count1505 q))) else (if i < 1521 then (if i < 1520 then decide (15 ≤ count1505 q) else decide (1 ≤ count1520 q)) else (if i < 1522 then decide (2 ≤ count1520 q) else decide (1 ≤ count1522 q)))) else (if i < 1526 then (if i < 1524 then decide (2 ≤ count1522 q) else (if i < 1525 then decide (1 ≤ count1524 q) else decide (2 ≤ count1524 q))) else (if i < 1528 then (if i < 1527 then decide (3 ≤ count1524 q) else decide (4 ≤ count1524 q)) else (if i < 1529 then decide (1 ≤ count1528 q) else decide (2 ≤ count1528 q)))))) else (if i < 1544 then (if i < 1537 then (if i < 1533 then (if i < 1531 then decide (1 ≤ count1530 q) else (if i < 1532 then decide (2 ≤ count1530 q) else decide (1 ≤ count1532 q))) else (if i < 1535 then (if i < 1534 then decide (2 ≤ count1532 q) else decide (3 ≤ count1532 q)) else (if i < 1536 then decide (4 ≤ count1532 q) else decide (1 ≤ count1536 q)))) else (if i < 1540 then (if i < 1538 then decide (2 ≤ count1536 q) else (if i < 1539 then decide (3 ≤ count1536 q) else decide (4 ≤ count1536 q))) else (if i < 1542 then (if i < 1541 then decide (5 ≤ count1536 q) else decide (6 ≤ count1536 q)) else (if i < 1543 then decide (7 ≤ count1536 q) else decide (8 ≤ count1536 q))))) else (if i < 1551 then (if i < 1547 then (if i < 1545 then decide (1 ≤ count1544 q) else (if i < 1546 then decide (2 ≤ count1544 q) else decide (1 ≤ count1546 q))) else (if i < 1549 then (if i < 1548 then decide (2 ≤ count1546 q) else decide (1 ≤ count1548 q)) else (if i < 1550 then decide (2 ≤ count1548 q) else decide (3 ≤ count1548 q)))) else (if i < 1554 then (if i < 1552 then decide (4 ≤ count1548 q) else (if i < 1553 then decide (1 ≤ count1552 q) else decide (2 ≤ count1552 q))) else (if i < 1556 then (if i < 1555 then decide (1 ≤ count1554 q) else decide (2 ≤ count1554 q)) else (if i < 1557 then decide (1 ≤ count1556 q) else decide (2 ≤ count1556 q))))))))) else (if i < 1669 then (if i < 1613 then (if i < 1585 then (if i < 1571 then (if i < 1564 then (if i < 1561 then (if i < 1559 then decide (3 ≤ count1556 q) else (if i < 1560 then decide (4 ≤ count1556 q) else decide (1 ≤ count1560 q))) else (if i < 1562 then decide (2 ≤ count1560 q) else (if i < 1563 then decide (3 ≤ count1560 q) else decide (4 ≤ count1560 q)))) else (if i < 1567 then (if i < 1565 then decide (5 ≤ count1560 q) else (if i < 1566 then decide (6 ≤ count1560 q) else decide (7 ≤ count1560 q))) else (if i < 1569 then (if i < 1568 then decide (8 ≤ count1560 q) else decide (1 ≤ count1568 q)) else (if i < 1570 then decide (2 ≤ count1568 q) else decide (3 ≤ count1568 q))))) else (if i < 1578 then (if i < 1574 then (if i < 1572 then decide (4 ≤ count1568 q) else (if i < 1573 then decide (5 ≤ count1568 q) else decide (6 ≤ count1568 q))) else (if i < 1576 then (if i < 1575 then decide (7 ≤ count1568 q) else decide (8 ≤ count1568 q)) else (if i < 1577 then decide (9 ≤ count1568 q) else decide (10 ≤ count1568 q)))) else (if i < 1581 then (if i < 1579 then decide (11 ≤ count1568 q) else (if i < 1580 then decide (12 ≤ count1568 q) else decide (13 ≤ count1568 q))) else (if i < 1583 then (if i < 1582 then decide (14 ≤ count1568 q) else decide (15 ≤ count1568 q)) else (if i < 1584 then decide (16 ≤ count1568 q) else decide (1 ≤ count1584 q)))))) else (if i < 1599 then (if i < 1592 then (if i < 1588 then (if i < 1586 then decide (2 ≤ count1584 q) else (if i < 1587 then decide (3 ≤ count1584 q) else decide (4 ≤ count1584 q))) else (if i < 1590 then (if i < 1589 then decide (5 ≤ count1584 q) else decide (6 ≤ count1584 q)) else (if i < 1591 then decide (7 ≤ count1584 q) else decide (8 ≤ count1584 q)))) else (if i < 1595 then (if i < 1593 then decide (9 ≤ count1584 q) else (if i < 1594 then decide (10 ≤ count1584 q) else decide (11 ≤ count1584 q))) else (if i < 1597 then (if i < 1596 then decide (12 ≤ count1584 q) else decide (13 ≤ count1584 q)) else (if i < 1598 then decide (14 ≤ count1584 q) else decide (15 ≤ count1584 q))))) else (if i < 1606 then (if i < 1602 then (if i < 1600 then decide (16 ≤ count1584 q) else (if i < 1601 then decide (17 ≤ count1584 q) else decide (18 ≤ count1584 q))) else (if i < 1604 then (if i < 1603 then decide (19 ≤ count1584 q) else decide (20 ≤ count1584 q)) else (if i < 1605 then decide (21 ≤ count1584 q) else decide (22 ≤ count1584 q)))) else (if i < 1609 then (if i < 1607 then decide (23 ≤ count1584 q) else (if i < 1608 then decide (1 ≤ count1607 q) else decide (2 ≤ count1607 q))) else (if i < 1611 then (if i < 1610 then decide (1 ≤ count1609 q) else decide (2 ≤ count1609 q)) else (if i < 1612 then decide (1 ≤ count1611 q) else decide (2 ≤ count1611 q))))))) else (if i < 1641 then (if i < 1627 then (if i < 1620 then (if i < 1616 then (if i < 1614 then decide (3 ≤ count1611 q) else (if i < 1615 then decide (4 ≤ count1611 q) else decide (1 ≤ count1615 q))) else (if i < 1618 then (if i < 1617 then decide (2 ≤ count1615 q) else decide (1 ≤ count1617 q)) else (if i < 1619 then decide (2 ≤ count1617 q) else decide (1 ≤ count1619 q)))) else (if i < 1623 then (if i < 1621 then decide (2 ≤ count1619 q) else (if i < 1622 then decide (3 ≤ count1619 q) else decide (4 ≤ count1619 q))) else (if i < 1625 then (if i < 1624 then decide (1 ≤ count1623 q) else decide (2 ≤ count1623 q)) else (if i < 1626 then decide (3 ≤ count1623 q) else decide (4 ≤ count1623 q))))) else (if i < 1634 then (if i < 1630 then (if i < 1628 then decide (5 ≤ count1623 q) else (if i < 1629 then decide (6 ≤ count1623 q) else decide (7 ≤ count1623 q))) else (if i < 1632 then (if i < 1631 then decide (8 ≤ count1623 q) else decide (1 ≤ count1631 q)) else (if i < 1633 then decide (2 ≤ count1631 q) else decide (1 ≤ count1633 q)))) else (if i < 1637 then (if i < 1635 then decide (2 ≤ count1633 q) else (if i < 1636 then decide (1 ≤ count1635 q) else decide (2 ≤ count1635 q))) else (if i < 1639 then (if i < 1638 then decide (3 ≤ count1635 q) else decide (4 ≤ count1635 q)) else (if i < 1640 then decide (1 ≤ count1639 q) else decide (2 ≤ count1639 q)))))) else (if i < 1655 then (if i < 1648 then (if i < 1644 then (if i < 1642 then decide (1 ≤ count1641 q) else (if i < 1643 then decide (2 ≤ count1641 q) else decide (1 ≤ count1643 q))) else (if i < 1646 then (if i < 1645 then decide (2 ≤ count1643 q) else decide (3 ≤ count1643 q)) else (if i < 1647 then decide (4 ≤ count1643 q) else decide (1 ≤ count1647 q)))) else (if i < 1651 then (if i < 1649 then decide (2 ≤ count1647 q) else (if i < 1650 then decide (3 ≤ count1647 q) else decide (4 ≤ count1647 q))) else (if i < 1653 then (if i < 1652 then decide (5 ≤ count1647 q) else decide (6 ≤ count1647 q)) else (if i < 1654 then decide (7 ≤ count1647 q) else decide (8 ≤ count1647 q))))) else (if i < 1662 then (if i < 1658 then (if i < 1656 then decide (1 ≤ count1655 q) else (if i < 1657 then decide (2 ≤ count1655 q) else decide (3 ≤ count1655 q))) else (if i < 1660 then (if i < 1659 then decide (4 ≤ count1655 q) else decide (5 ≤ count1655 q)) else (if i < 1661 then decide (6 ≤ count1655 q) else decide (7 ≤ count1655 q)))) else (if i < 1665 then (if i < 1663 then decide (8 ≤ count1655 q) else (if i < 1664 then decide (9 ≤ count1655 q) else decide (10 ≤ count1655 q))) else (if i < 1667 then (if i < 1666 then decide (11 ≤ count1655 q) else decide (12 ≤ count1655 q)) else (if i < 1668 then decide (13 ≤ count1655 q) else decide (14 ≤ count1655 q)))))))) else (if i < 1725 then (if i < 1697 then (if i < 1683 then (if i < 1676 then (if i < 1672 then (if i < 1670 then decide (15 ≤ count1655 q) else (if i < 1671 then decide (16 ≤ count1655 q) else decide (1 ≤ count1671 q))) else (if i < 1674 then (if i < 1673 then decide (2 ≤ count1671 q) else decide (1 ≤ count1673 q)) else (if i < 1675 then decide (2 ≤ count1673 q) else decide (1 ≤ count1675 q)))) else (if i < 1679 then (if i < 1677 then decide (2 ≤ count1675 q) else (if i < 1678 then decide (3 ≤ count1675 q) else decide (4 ≤ count1675 q))) else (if i < 1681 then (if i < 1680 then decide (1 ≤ count1679 q) else decide (2 ≤ count1679 q)) else (if i < 1682 then decide (1 ≤ count1681 q) else decide (2 ≤ count1681 q))))) else (if i < 1690 then (if i < 1686 then (if i < 1684 then decide (1 ≤ count1683 q) else (if i < 1685 then decide (2 ≤ count1683 q) else decide (3 ≤ count1683 q))) else (if i < 1688 then (if i < 1687 then decide (4 ≤ count1683 q) else decide (1 ≤ count1687 q)) else (if i < 1689 then decide (2 ≤ count1687 q) else decide (3 ≤ count1687 q)))) else (if i < 1693 then (if i < 1691 then decide (4 ≤ count1687 q) else (if i < 1692 then decide (5 ≤ count1687 q) else decide (6 ≤ count1687 q))) else (if i < 1695 then (if i < 1694 then decide (7 ≤ count1687 q) else decide (8 ≤ count1687 q)) else (if i < 1696 then decide (1 ≤ count1695 q) else decide (2 ≤ count1695 q)))))) else (if i < 1711 then (if i < 1704 then (if i < 1700 then (if i < 1698 then decide (1 ≤ count1697 q) else (if i < 1699 then decide (2 ≤ count1697 q) else decide (1 ≤ count1699 q))) else (if i < 1702 then (if i < 1701 then decide (2 ≤ count1699 q) else decide (3 ≤ count1699 q)) else (if i < 1703 then decide (4 ≤ count1699 q) else decide (1 ≤ count1703 q)))) else (if i < 1707 then (if i < 1705 then decide (2 ≤ count1703 q) else (if i < 1706 then decide (1 ≤ count1705 q) else decide (2 ≤ count1705 q))) else (if i < 1709 then (if i < 1708 then decide (1 ≤ count1707 q) else decide (2 ≤ count1707 q)) else (if i < 1710 then decide (3 ≤ count1707 q) else decide (4 ≤ count1707 q))))) else (if i < 1718 then (if i < 1714 then (if i < 1712 then decide (1 ≤ count1711 q) else (if i < 1713 then decide (2 ≤ count1711 q) else decide (3 ≤ count1711 q))) else (if i < 1716 then (if i < 1715 then decide (4 ≤ count1711 q) else decide (5 ≤ count1711 q)) else (if i < 1717 then decide (6 ≤ count1711 q) else decide (7 ≤ count1711 q)))) else (if i < 1721 then (if i < 1719 then decide (8 ≤ count1711 q) else (if i < 1720 then decide (1 ≤ count1719 q) else decide (2 ≤ count1719 q))) else (if i < 1723 then (if i < 1722 then decide (3 ≤ count1719 q) else decide (4 ≤ count1719 q)) else (if i < 1724 then decide (5 ≤ count1719 q) else decide (6 ≤ count1719 q))))))) else (if i < 1753 then (if i < 1739 then (if i < 1732 then (if i < 1728 then (if i < 1726 then decide (7 ≤ count1719 q) else (if i < 1727 then decide (8 ≤ count1719 q) else decide (9 ≤ count1719 q))) else (if i < 1730 then (if i < 1729 then decide (10 ≤ count1719 q) else decide (11 ≤ count1719 q)) else (if i < 1731 then decide (12 ≤ count1719 q) else decide (13 ≤ count1719 q)))) else (if i < 1735 then (if i < 1733 then decide (14 ≤ count1719 q) else (if i < 1734 then decide (15 ≤ count1719 q) else decide (16 ≤ count1719 q))) else (if i < 1737 then (if i < 1736 then decide (1 ≤ count1735 q) else decide (2 ≤ count1735 q)) else (if i < 1738 then decide (3 ≤ count1735 q) else decide (4 ≤ count1735 q))))) else (if i < 1746 then (if i < 1742 then (if i < 1740 then decide (5 ≤ count1735 q) else (if i < 1741 then decide (6 ≤ count1735 q) else decide (7 ≤ count1735 q))) else (if i < 1744 then (if i < 1743 then decide (8 ≤ count1735 q) else decide (9 ≤ count1735 q)) else (if i < 1745 then decide (10 ≤ count1735 q) else decide (11 ≤ count1735 q)))) else (if i < 1749 then (if i < 1747 then decide (12 ≤ count1735 q) else (if i < 1748 then decide (13 ≤ count1735 q) else decide (14 ≤ count1735 q))) else (if i < 1751 then (if i < 1750 then decide (15 ≤ count1735 q) else decide (16 ≤ count1735 q)) else (if i < 1752 then decide (17 ≤ count1735 q) else decide (18 ≤ count1735 q)))))) else (if i < 1767 then (if i < 1760 then (if i < 1756 then (if i < 1754 then decide (19 ≤ count1735 q) else (if i < 1755 then decide (20 ≤ count1735 q) else decide (21 ≤ count1735 q))) else (if i < 1758 then (if i < 1757 then decide (22 ≤ count1735 q) else decide (23 ≤ count1735 q)) else (if i < 1759 then decide (1 ≤ count1758 q) else decide (2 ≤ count1758 q)))) else (if i < 1763 then (if i < 1761 then decide (3 ≤ count1758 q) else (if i < 1762 then decide (4 ≤ count1758 q) else decide (5 ≤ count1758 q))) else (if i < 1765 then (if i < 1764 then decide (6 ≤ count1758 q) else decide (7 ≤ count1758 q)) else (if i < 1766 then decide (8 ≤ count1758 q) else decide (9 ≤ count1758 q))))) else (if i < 1774 then (if i < 1770 then (if i < 1768 then decide (10 ≤ count1758 q) else (if i < 1769 then decide (11 ≤ count1758 q) else decide (12 ≤ count1758 q))) else (if i < 1772 then (if i < 1771 then decide (13 ≤ count1758 q) else decide (14 ≤ count1758 q)) else (if i < 1773 then decide (15 ≤ count1758 q) else decide (16 ≤ count1758 q)))) else (if i < 1777 then (if i < 1775 then decide (17 ≤ count1758 q) else (if i < 1776 then decide (18 ≤ count1758 q) else decide (19 ≤ count1758 q))) else (if i < 1779 then (if i < 1778 then decide (20 ≤ count1758 q) else decide (21 ≤ count1758 q)) else (if i < 1780 then decide (22 ≤ count1758 q) else decide (23 ≤ count1758 q))))))))))))
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (34 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (35 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (36 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (37 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (40 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (42 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (43 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (44 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (46 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (52 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (53 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (55 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (56 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (57 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (59 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (63 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (99 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (100 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (103 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (160 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (161 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (166 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (167 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (168 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (169 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (171 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (173 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (175 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (177 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (178 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (179 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (180 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (182 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (186 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (188 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (189 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (190 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (226 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (227 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (228 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (229 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (230 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (234 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (235 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (236 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (238 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (244 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (245 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (247 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (248 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (249 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (250 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (251 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (255 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (288 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (289 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (293 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (294 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (295 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (296 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (299 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (301 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (303 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (304 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (305 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (306 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (307 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (310 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (316 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (317 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (318 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (352 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (355 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (356 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (359 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (364 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (372 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (373 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (375 : Vertex)) := rfl
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
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (482 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (483 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (485 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (486 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (488 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (491 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (493 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (495 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (496 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (497 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (498 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (499 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (502 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (504 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (508 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (509 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (510 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (511 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (34 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (35 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (36 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (37 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (40 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (42 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (43 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (44 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (46 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (52 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (53 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (55 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (56 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (57 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (59 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (63 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (99 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (100 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (103 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (166 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (169 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (178 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (180 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (190 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (226 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (228 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (235 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (236 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (250 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (289 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (293 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (294 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (295 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (299 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (301 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (303 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (304 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (306 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (307 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (310 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (316 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (317 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (318 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (352 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (356 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (359 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (372 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (373 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (375 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (416 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (418 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (420 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (422 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (423 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (424 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (431 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (433 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
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
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (483 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (485 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (496 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (504 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (510 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (511 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 q) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 q) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (2 ≤ count247 q) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 q) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 q) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 q) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 q) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 q) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 q) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 q) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 q) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 q) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 q) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 q) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 q) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 q) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 q) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 q) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 q) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 q) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 q) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 q) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 q) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 q) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 q) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 q) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 q) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 q) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 q) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 q) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 q) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 q) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 q) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 q) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 q) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 q) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 q) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 q) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 q) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 q) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 q) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 q) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 q) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 q) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 q) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 q) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 q) := rfl
theorem value338 (q : Snake 81) : valuation q 338 = decide (2 ≤ count337 q) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 q) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 q) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 q) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 q) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 q) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 q) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 q) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 q) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 q) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 q) := rfl
theorem value356 (q : Snake 81) : valuation q 356 = decide (2 ≤ count355 q) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 q) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 q) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 q) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 q) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 q) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 q) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 q) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 q) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 q) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 q) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 q) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 q) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 q) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 q) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 q) := rfl
theorem value380 (q : Snake 81) : valuation q 380 = decide (2 ≤ count379 q) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 q) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 q) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 q) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 q) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 q) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 q) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 q) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 q) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 q) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 q) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 q) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 q) := rfl
theorem value402 (q : Snake 81) : valuation q 402 = decide (2 ≤ count401 q) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 q) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 q) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 q) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 q) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 q) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 q) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 q) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 q) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 q) := rfl
theorem value420 (q : Snake 81) : valuation q 420 = decide (2 ≤ count419 q) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 q) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 q) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 q) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 q) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 q) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 q) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 q) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 q) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 q) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 q) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 q) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 q) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 q) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 q) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 q) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 q) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 q) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 q) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 q) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 q) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 q) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 q) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 q) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 q) := rfl
theorem value474 (q : Snake 81) : valuation q 474 = decide (2 ≤ count473 q) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 q) := rfl
theorem value476 (q : Snake 81) : valuation q 476 = decide (2 ≤ count475 q) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 q) := rfl
theorem value478 (q : Snake 81) : valuation q 478 = decide (2 ≤ count477 q) := rfl
theorem value479 (q : Snake 81) : valuation q 479 = decide (1 ≤ count479 q) := rfl
theorem value480 (q : Snake 81) : valuation q 480 = decide (2 ≤ count479 q) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 q) := rfl
theorem value482 (q : Snake 81) : valuation q 482 = decide (2 ≤ count481 q) := rfl
theorem value484 (q : Snake 81) : valuation q 484 = decide (2 ≤ count483 q) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (1 ≤ count1461 q) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (2 ≤ count1461 q) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (1 ≤ count1463 q) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (2 ≤ count1463 q) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (3 ≤ count1463 q) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (1 ≤ count1466 q) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (2 ≤ count1466 q) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (1 ≤ count1468 q) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (2 ≤ count1468 q) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (1 ≤ count1470 q) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (2 ≤ count1470 q) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (3 ≤ count1470 q) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (4 ≤ count1470 q) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (1 ≤ count1474 q) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (2 ≤ count1474 q) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (3 ≤ count1474 q) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (4 ≤ count1474 q) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (5 ≤ count1474 q) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (6 ≤ count1474 q) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (1 ≤ count1481 q) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (2 ≤ count1481 q) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (1 ≤ count1483 q) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (2 ≤ count1483 q) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (1 ≤ count1485 q) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (2 ≤ count1485 q) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (3 ≤ count1485 q) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (4 ≤ count1485 q) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (1 ≤ count1489 q) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (2 ≤ count1489 q) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (1 ≤ count1491 q) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (2 ≤ count1491 q) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (1 ≤ count1493 q) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (2 ≤ count1493 q) := rfl
theorem value1495 (q : Snake 81) : valuation q 1495 = decide (3 ≤ count1493 q) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (1 ≤ count1497 q) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (2 ≤ count1497 q) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (3 ≤ count1497 q) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (4 ≤ count1497 q) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (5 ≤ count1497 q) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (6 ≤ count1497 q) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (3 ≤ count1505 q) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (4 ≤ count1505 q) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (5 ≤ count1505 q) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (6 ≤ count1505 q) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (7 ≤ count1505 q) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (8 ≤ count1505 q) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (9 ≤ count1505 q) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (1 ≤ count1520 q) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (2 ≤ count1520 q) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (1 ≤ count1522 q) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (2 ≤ count1522 q) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (1 ≤ count1524 q) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (2 ≤ count1524 q) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (1 ≤ count1528 q) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (2 ≤ count1528 q) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (1 ≤ count1530 q) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (2 ≤ count1530 q) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (1 ≤ count1532 q) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (2 ≤ count1532 q) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (3 ≤ count1532 q) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (4 ≤ count1532 q) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (1 ≤ count1536 q) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (2 ≤ count1536 q) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (3 ≤ count1536 q) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (4 ≤ count1536 q) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (5 ≤ count1536 q) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (1 ≤ count1544 q) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (2 ≤ count1544 q) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (1 ≤ count1546 q) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (2 ≤ count1546 q) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (1 ≤ count1548 q) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (2 ≤ count1548 q) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (3 ≤ count1548 q) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (4 ≤ count1548 q) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (1 ≤ count1552 q) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (2 ≤ count1552 q) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (1 ≤ count1554 q) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (2 ≤ count1554 q) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (1 ≤ count1556 q) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (2 ≤ count1556 q) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (3 ≤ count1556 q) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (4 ≤ count1556 q) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (1 ≤ count1560 q) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (2 ≤ count1560 q) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (3 ≤ count1560 q) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (4 ≤ count1560 q) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (5 ≤ count1560 q) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (6 ≤ count1560 q) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (7 ≤ count1560 q) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (3 ≤ count1568 q) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (4 ≤ count1568 q) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (5 ≤ count1568 q) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (6 ≤ count1568 q) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (7 ≤ count1568 q) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (8 ≤ count1568 q) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (9 ≤ count1568 q) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (10 ≤ count1568 q) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (7 ≤ count1584 q) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (8 ≤ count1584 q) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (9 ≤ count1584 q) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (10 ≤ count1584 q) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (11 ≤ count1584 q) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (12 ≤ count1584 q) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (13 ≤ count1584 q) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (14 ≤ count1584 q) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (1 ≤ count1607 q) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (2 ≤ count1607 q) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (1 ≤ count1609 q) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (2 ≤ count1609 q) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (1 ≤ count1611 q) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (2 ≤ count1611 q) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (3 ≤ count1611 q) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (4 ≤ count1611 q) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (1 ≤ count1615 q) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (2 ≤ count1615 q) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (1 ≤ count1617 q) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (2 ≤ count1617 q) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (1 ≤ count1619 q) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (2 ≤ count1619 q) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (3 ≤ count1619 q) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (4 ≤ count1619 q) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (1 ≤ count1623 q) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (2 ≤ count1623 q) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (3 ≤ count1623 q) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (4 ≤ count1623 q) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (5 ≤ count1623 q) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (6 ≤ count1623 q) := rfl
theorem value1631 (q : Snake 81) : valuation q 1631 = decide (1 ≤ count1631 q) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (1 ≤ count1633 q) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (2 ≤ count1633 q) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (1 ≤ count1635 q) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (2 ≤ count1635 q) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (3 ≤ count1635 q) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (1 ≤ count1639 q) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (2 ≤ count1639 q) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (1 ≤ count1641 q) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (2 ≤ count1641 q) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (1 ≤ count1643 q) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (2 ≤ count1643 q) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (3 ≤ count1643 q) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (4 ≤ count1643 q) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (1 ≤ count1647 q) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (2 ≤ count1647 q) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (3 ≤ count1647 q) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (4 ≤ count1647 q) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (5 ≤ count1647 q) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (6 ≤ count1647 q) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (7 ≤ count1647 q) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (2 ≤ count1655 q) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (3 ≤ count1655 q) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (4 ≤ count1655 q) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (5 ≤ count1655 q) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (6 ≤ count1655 q) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (7 ≤ count1655 q) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (8 ≤ count1655 q) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (9 ≤ count1655 q) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (10 ≤ count1655 q) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (1 ≤ count1671 q) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (2 ≤ count1671 q) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (1 ≤ count1673 q) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (2 ≤ count1673 q) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (1 ≤ count1675 q) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (2 ≤ count1675 q) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (3 ≤ count1675 q) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (4 ≤ count1675 q) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (1 ≤ count1679 q) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (2 ≤ count1679 q) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (1 ≤ count1681 q) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (2 ≤ count1681 q) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (1 ≤ count1683 q) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (2 ≤ count1683 q) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (3 ≤ count1683 q) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (4 ≤ count1683 q) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (1 ≤ count1687 q) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (2 ≤ count1687 q) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (3 ≤ count1687 q) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (4 ≤ count1687 q) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (5 ≤ count1687 q) := rfl
theorem value1692 (q : Snake 81) : valuation q 1692 = decide (6 ≤ count1687 q) := rfl
theorem value1693 (q : Snake 81) : valuation q 1693 = decide (7 ≤ count1687 q) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (1 ≤ count1695 q) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (2 ≤ count1695 q) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (1 ≤ count1697 q) := rfl
theorem value1698 (q : Snake 81) : valuation q 1698 = decide (2 ≤ count1697 q) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (1 ≤ count1699 q) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (2 ≤ count1699 q) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (3 ≤ count1699 q) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (4 ≤ count1699 q) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (1 ≤ count1703 q) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (2 ≤ count1703 q) := rfl
theorem value1705 (q : Snake 81) : valuation q 1705 = decide (1 ≤ count1705 q) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (2 ≤ count1705 q) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (1 ≤ count1707 q) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (2 ≤ count1707 q) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (3 ≤ count1707 q) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (4 ≤ count1707 q) := rfl
theorem value1711 (q : Snake 81) : valuation q 1711 = decide (1 ≤ count1711 q) := rfl
theorem value1712 (q : Snake 81) : valuation q 1712 = decide (2 ≤ count1711 q) := rfl
theorem value1713 (q : Snake 81) : valuation q 1713 = decide (3 ≤ count1711 q) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (4 ≤ count1711 q) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (5 ≤ count1711 q) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (6 ≤ count1711 q) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (3 ≤ count1719 q) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (4 ≤ count1719 q) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (5 ≤ count1719 q) := rfl
theorem value1724 (q : Snake 81) : valuation q 1724 = decide (6 ≤ count1719 q) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (7 ≤ count1719 q) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (8 ≤ count1719 q) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (9 ≤ count1719 q) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (10 ≤ count1719 q) := rfl
theorem value1743 (q : Snake 81) : valuation q 1743 = decide (9 ≤ count1735 q) := rfl
theorem value1744 (q : Snake 81) : valuation q 1744 = decide (10 ≤ count1735 q) := rfl
theorem value1745 (q : Snake 81) : valuation q 1745 = decide (11 ≤ count1735 q) := rfl
theorem value1746 (q : Snake 81) : valuation q 1746 = decide (12 ≤ count1735 q) := rfl
theorem value1747 (q : Snake 81) : valuation q 1747 = decide (13 ≤ count1735 q) := rfl
theorem value1748 (q : Snake 81) : valuation q 1748 = decide (14 ≤ count1735 q) := rfl
theorem value1749 (q : Snake 81) : valuation q 1749 = decide (15 ≤ count1735 q) := rfl
theorem value1750 (q : Snake 81) : valuation q 1750 = decide (16 ≤ count1735 q) := rfl
theorem value1780 (q : Snake 81) : valuation q 1780 = decide (23 ≤ count1758 q) := rfl
theorem meaningNeg122 (q : Snake 81) : literal (valuation q) (-122) = decide (1 ≤ countLit q [-122]) := by
  change literal (baseVal q) (-122) = decide (1 ≤ countLit q [-122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-122) <;> decide
theorem meaningNeg119 (q : Snake 81) : literal (valuation q) (-119) = decide (1 ≤ countLit q [-119]) := by
  change literal (baseVal q) (-119) = decide (1 ≤ countLit q [-119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-119) <;> decide
theorem meaningNeg117 (q : Snake 81) : literal (valuation q) (-117) = decide (1 ≤ countLit q [-117]) := by
  change literal (baseVal q) (-117) = decide (1 ≤ countLit q [-117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-117) <;> decide
theorem meaningNeg116 (q : Snake 81) : literal (valuation q) (-116) = decide (1 ≤ countLit q [-116]) := by
  change literal (baseVal q) (-116) = decide (1 ≤ countLit q [-116])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-116) <;> decide
theorem meaningNeg113 (q : Snake 81) : literal (valuation q) (-113) = decide (1 ≤ countLit q [-113]) := by
  change literal (baseVal q) (-113) = decide (1 ≤ countLit q [-113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-113) <;> decide
theorem meaningNeg111 (q : Snake 81) : literal (valuation q) (-111) = decide (1 ≤ countLit q [-111]) := by
  change literal (baseVal q) (-111) = decide (1 ≤ countLit q [-111])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-111) <;> decide
theorem meaningNeg110 (q : Snake 81) : literal (valuation q) (-110) = decide (1 ≤ countLit q [-110]) := by
  change literal (baseVal q) (-110) = decide (1 ≤ countLit q [-110])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-110) <;> decide
theorem meaningNeg109 (q : Snake 81) : literal (valuation q) (-109) = decide (1 ≤ countLit q [-109]) := by
  change literal (baseVal q) (-109) = decide (1 ≤ countLit q [-109])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-109) <;> decide
theorem meaningNeg105 (q : Snake 81) : literal (valuation q) (-105) = decide (1 ≤ countLit q [-105]) := by
  change literal (baseVal q) (-105) = decide (1 ≤ countLit q [-105])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-105) <;> decide
theorem meaningNeg104 (q : Snake 81) : literal (valuation q) (-104) = decide (1 ≤ countLit q [-104]) := by
  change literal (baseVal q) (-104) = decide (1 ≤ countLit q [-104])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-104) <;> decide
theorem meaningNeg101 (q : Snake 81) : literal (valuation q) (-101) = decide (1 ≤ countLit q [-101]) := by
  change literal (baseVal q) (-101) = decide (1 ≤ countLit q [-101])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-101) <;> decide
theorem meaningNeg98 (q : Snake 81) : literal (valuation q) (-98) = decide (1 ≤ countLit q [-98]) := by
  change literal (baseVal q) (-98) = decide (1 ≤ countLit q [-98])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-98) <;> decide
theorem meaningNeg97 (q : Snake 81) : literal (valuation q) (-97) = decide (1 ≤ countLit q [-97]) := by
  change literal (baseVal q) (-97) = decide (1 ≤ countLit q [-97])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-97) <;> decide
theorem meaningNeg95 (q : Snake 81) : literal (valuation q) (-95) = decide (1 ≤ countLit q [-95]) := by
  change literal (baseVal q) (-95) = decide (1 ≤ countLit q [-95])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-95) <;> decide
theorem meaningNeg93 (q : Snake 81) : literal (valuation q) (-93) = decide (1 ≤ countLit q [-93]) := by
  change literal (baseVal q) (-93) = decide (1 ≤ countLit q [-93])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-93) <;> decide
theorem meaningNeg92 (q : Snake 81) : literal (valuation q) (-92) = decide (1 ≤ countLit q [-92]) := by
  change literal (baseVal q) (-92) = decide (1 ≤ countLit q [-92])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-92) <;> decide
theorem meaningNeg90 (q : Snake 81) : literal (valuation q) (-90) = decide (1 ≤ countLit q [-90]) := by
  change literal (baseVal q) (-90) = decide (1 ≤ countLit q [-90])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-90) <;> decide
theorem meaningNeg88 (q : Snake 81) : literal (valuation q) (-88) = decide (1 ≤ countLit q [-88]) := by
  change literal (baseVal q) (-88) = decide (1 ≤ countLit q [-88])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-88) <;> decide
theorem meaningNeg85 (q : Snake 81) : literal (valuation q) (-85) = decide (1 ≤ countLit q [-85]) := by
  change literal (baseVal q) (-85) = decide (1 ≤ countLit q [-85])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-85) <;> decide
theorem meaningNeg84 (q : Snake 81) : literal (valuation q) (-84) = decide (1 ≤ countLit q [-84]) := by
  change literal (baseVal q) (-84) = decide (1 ≤ countLit q [-84])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-84) <;> decide
theorem meaningNeg80 (q : Snake 81) : literal (valuation q) (-80) = decide (1 ≤ countLit q [-80]) := by
  change literal (baseVal q) (-80) = decide (1 ≤ countLit q [-80])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-80) <;> decide
theorem meaningNeg79 (q : Snake 81) : literal (valuation q) (-79) = decide (1 ≤ countLit q [-79]) := by
  change literal (baseVal q) (-79) = decide (1 ≤ countLit q [-79])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-79) <;> decide
theorem meaningNeg77 (q : Snake 81) : literal (valuation q) (-77) = decide (1 ≤ countLit q [-77]) := by
  change literal (baseVal q) (-77) = decide (1 ≤ countLit q [-77])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-77) <;> decide
theorem meaningNeg73 (q : Snake 81) : literal (valuation q) (-73) = decide (1 ≤ countLit q [-73]) := by
  change literal (baseVal q) (-73) = decide (1 ≤ countLit q [-73])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-73) <;> decide
theorem meaningNeg72 (q : Snake 81) : literal (valuation q) (-72) = decide (1 ≤ countLit q [-72]) := by
  change literal (baseVal q) (-72) = decide (1 ≤ countLit q [-72])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-72) <;> decide
theorem meaningNeg69 (q : Snake 81) : literal (valuation q) (-69) = decide (1 ≤ countLit q [-69]) := by
  change literal (baseVal q) (-69) = decide (1 ≤ countLit q [-69])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-69) <;> decide
theorem meaningNeg68 (q : Snake 81) : literal (valuation q) (-68) = decide (1 ≤ countLit q [-68]) := by
  change literal (baseVal q) (-68) = decide (1 ≤ countLit q [-68])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-68) <;> decide
theorem meaningNeg67 (q : Snake 81) : literal (valuation q) (-67) = decide (1 ≤ countLit q [-67]) := by
  change literal (baseVal q) (-67) = decide (1 ≤ countLit q [-67])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-67) <;> decide
theorem meaningNeg64 (q : Snake 81) : literal (valuation q) (-64) = decide (1 ≤ countLit q [-64]) := by
  change literal (baseVal q) (-64) = decide (1 ≤ countLit q [-64])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-64) <;> decide
theorem meaningNeg62 (q : Snake 81) : literal (valuation q) (-62) = decide (1 ≤ countLit q [-62]) := by
  change literal (baseVal q) (-62) = decide (1 ≤ countLit q [-62])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-62) <;> decide
theorem meaningNeg61 (q : Snake 81) : literal (valuation q) (-61) = decide (1 ≤ countLit q [-61]) := by
  change literal (baseVal q) (-61) = decide (1 ≤ countLit q [-61])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-61) <;> decide
theorem meaningNeg60 (q : Snake 81) : literal (valuation q) (-60) = decide (1 ≤ countLit q [-60]) := by
  change literal (baseVal q) (-60) = decide (1 ≤ countLit q [-60])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-60) <;> decide
theorem meaningNeg59 (q : Snake 81) : literal (valuation q) (-59) = decide (1 ≤ countLit q [-59]) := by
  change literal (baseVal q) (-59) = decide (1 ≤ countLit q [-59])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-59) <;> decide
theorem meaningNeg56 (q : Snake 81) : literal (valuation q) (-56) = decide (1 ≤ countLit q [-56]) := by
  change literal (baseVal q) (-56) = decide (1 ≤ countLit q [-56])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-56) <;> decide
theorem meaningNeg53 (q : Snake 81) : literal (valuation q) (-53) = decide (1 ≤ countLit q [-53]) := by
  change literal (baseVal q) (-53) = decide (1 ≤ countLit q [-53])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-53) <;> decide
theorem meaningNeg50 (q : Snake 81) : literal (valuation q) (-50) = decide (1 ≤ countLit q [-50]) := by
  change literal (baseVal q) (-50) = decide (1 ≤ countLit q [-50])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-50) <;> decide
theorem meaningNeg49 (q : Snake 81) : literal (valuation q) (-49) = decide (1 ≤ countLit q [-49]) := by
  change literal (baseVal q) (-49) = decide (1 ≤ countLit q [-49])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-49) <;> decide
theorem meaningNeg47 (q : Snake 81) : literal (valuation q) (-47) = decide (1 ≤ countLit q [-47]) := by
  change literal (baseVal q) (-47) = decide (1 ≤ countLit q [-47])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-47) <;> decide
theorem meaningNeg45 (q : Snake 81) : literal (valuation q) (-45) = decide (1 ≤ countLit q [-45]) := by
  change literal (baseVal q) (-45) = decide (1 ≤ countLit q [-45])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-45) <;> decide
theorem meaningNeg43 (q : Snake 81) : literal (valuation q) (-43) = decide (1 ≤ countLit q [-43]) := by
  change literal (baseVal q) (-43) = decide (1 ≤ countLit q [-43])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-43) <;> decide
theorem meaningNeg42 (q : Snake 81) : literal (valuation q) (-42) = decide (1 ≤ countLit q [-42]) := by
  change literal (baseVal q) (-42) = decide (1 ≤ countLit q [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-42) <;> decide
theorem meaningNeg41 (q : Snake 81) : literal (valuation q) (-41) = decide (1 ≤ countLit q [-41]) := by
  change literal (baseVal q) (-41) = decide (1 ≤ countLit q [-41])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-41) <;> decide
theorem meaningNeg39 (q : Snake 81) : literal (valuation q) (-39) = decide (1 ≤ countLit q [-39]) := by
  change literal (baseVal q) (-39) = decide (1 ≤ countLit q [-39])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-39) <;> decide
theorem meaningNeg35 (q : Snake 81) : literal (valuation q) (-35) = decide (1 ≤ countLit q [-35]) := by
  change literal (baseVal q) (-35) = decide (1 ≤ countLit q [-35])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-35) <;> decide
theorem meaningNeg34 (q : Snake 81) : literal (valuation q) (-34) = decide (1 ≤ countLit q [-34]) := by
  change literal (baseVal q) (-34) = decide (1 ≤ countLit q [-34])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-34) <;> decide
theorem meaningNeg33 (q : Snake 81) : literal (valuation q) (-33) = decide (1 ≤ countLit q [-33]) := by
  change literal (baseVal q) (-33) = decide (1 ≤ countLit q [-33])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-33) <;> decide
theorem meaningNeg31 (q : Snake 81) : literal (valuation q) (-31) = decide (1 ≤ countLit q [-31]) := by
  change literal (baseVal q) (-31) = decide (1 ≤ countLit q [-31])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-31) <;> decide
theorem meaningNeg27 (q : Snake 81) : literal (valuation q) (-27) = decide (1 ≤ countLit q [-27]) := by
  change literal (baseVal q) (-27) = decide (1 ≤ countLit q [-27])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-27) <;> decide
theorem meaningNeg26 (q : Snake 81) : literal (valuation q) (-26) = decide (1 ≤ countLit q [-26]) := by
  change literal (baseVal q) (-26) = decide (1 ≤ countLit q [-26])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-26) <;> decide
theorem meaningNeg24 (q : Snake 81) : literal (valuation q) (-24) = decide (1 ≤ countLit q [-24]) := by
  change literal (baseVal q) (-24) = decide (1 ≤ countLit q [-24])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-24) <;> decide
theorem meaningNeg23 (q : Snake 81) : literal (valuation q) (-23) = decide (1 ≤ countLit q [-23]) := by
  change literal (baseVal q) (-23) = decide (1 ≤ countLit q [-23])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-23) <;> decide
theorem meaningNeg21 (q : Snake 81) : literal (valuation q) (-21) = decide (1 ≤ countLit q [-21]) := by
  change literal (baseVal q) (-21) = decide (1 ≤ countLit q [-21])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-21) <;> decide
theorem meaningNeg19 (q : Snake 81) : literal (valuation q) (-19) = decide (1 ≤ countLit q [-19]) := by
  change literal (baseVal q) (-19) = decide (1 ≤ countLit q [-19])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-19) <;> decide
theorem meaningNeg18 (q : Snake 81) : literal (valuation q) (-18) = decide (1 ≤ countLit q [-18]) := by
  change literal (baseVal q) (-18) = decide (1 ≤ countLit q [-18])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-18) <;> decide
theorem meaningNeg15 (q : Snake 81) : literal (valuation q) (-15) = decide (1 ≤ countLit q [-15]) := by
  change literal (baseVal q) (-15) = decide (1 ≤ countLit q [-15])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-15) <;> decide
theorem meaningNeg13 (q : Snake 81) : literal (valuation q) (-13) = decide (1 ≤ countLit q [-13]) := by
  change literal (baseVal q) (-13) = decide (1 ≤ countLit q [-13])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-13) <;> decide
theorem meaningNeg12 (q : Snake 81) : literal (valuation q) (-12) = decide (1 ≤ countLit q [-12]) := by
  change literal (baseVal q) (-12) = decide (1 ≤ countLit q [-12])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-12) <;> decide
theorem meaningNeg10 (q : Snake 81) : literal (valuation q) (-10) = decide (1 ≤ countLit q [-10]) := by
  change literal (baseVal q) (-10) = decide (1 ≤ countLit q [-10])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-10) <;> decide
theorem meaningNeg8 (q : Snake 81) : literal (valuation q) (-8) = decide (1 ≤ countLit q [-8]) := by
  change literal (baseVal q) (-8) = decide (1 ≤ countLit q [-8])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-8) <;> decide
theorem meaningNeg6 (q : Snake 81) : literal (valuation q) (-6) = decide (1 ≤ countLit q [-6]) := by
  change literal (baseVal q) (-6) = decide (1 ≤ countLit q [-6])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-6) <;> decide
theorem meaningNeg4 (q : Snake 81) : literal (valuation q) (-4) = decide (1 ≤ countLit q [-4]) := by
  change literal (baseVal q) (-4) = decide (1 ≤ countLit q [-4])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-4) <;> decide
theorem meaningNeg2 (q : Snake 81) : literal (valuation q) (-2) = decide (1 ≤ countLit q [-2]) := by
  change literal (baseVal q) (-2) = decide (1 ≤ countLit q [-2])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (-2) <;> decide
theorem meaning123 (q : Snake 81) : literal (valuation q) (123) = decide (1 ≤ countLit q [123]) := by
  change literal (baseVal q) (123) = decide (1 ≤ countLit q [123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (123) <;> decide
theorem meaning125 (q : Snake 81) : literal (valuation q) (125) = decide (1 ≤ countLit q [125]) := by
  change literal (baseVal q) (125) = decide (1 ≤ countLit q [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (125) <;> decide
theorem meaning127 (q : Snake 81) : literal (valuation q) (127) = decide (1 ≤ countLit q [127]) := by
  change literal (baseVal q) (127) = decide (1 ≤ countLit q [127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (127) <;> decide
theorem meaning129 (q : Snake 81) : literal (valuation q) (129) = decide (1 ≤ countLit q [129]) := by
  change literal (baseVal q) (129) = decide (1 ≤ countLit q [129])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (129) <;> decide
theorem meaning131 (q : Snake 81) : literal (valuation q) (131) = decide (1 ≤ countLit q [131]) := by
  change literal (baseVal q) (131) = decide (1 ≤ countLit q [131])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (131) <;> decide
theorem meaning133 (q : Snake 81) : literal (valuation q) (133) = decide (1 ≤ countLit q [133]) := by
  change literal (baseVal q) (133) = decide (1 ≤ countLit q [133])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (133) <;> decide
theorem meaning136 (q : Snake 81) : literal (valuation q) (136) = decide (1 ≤ countLit q [136]) := by
  change literal (baseVal q) (136) = decide (1 ≤ countLit q [136])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (136) <;> decide
theorem meaning138 (q : Snake 81) : literal (valuation q) (138) = decide (1 ≤ countLit q [138]) := by
  change literal (baseVal q) (138) = decide (1 ≤ countLit q [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (138) <;> decide
theorem meaning139 (q : Snake 81) : literal (valuation q) (139) = decide (1 ≤ countLit q [139]) := by
  change literal (baseVal q) (139) = decide (1 ≤ countLit q [139])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (139) <;> decide
theorem meaning142 (q : Snake 81) : literal (valuation q) (142) = decide (1 ≤ countLit q [142]) := by
  change literal (baseVal q) (142) = decide (1 ≤ countLit q [142])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (142) <;> decide
theorem meaning144 (q : Snake 81) : literal (valuation q) (144) = decide (1 ≤ countLit q [144]) := by
  change literal (baseVal q) (144) = decide (1 ≤ countLit q [144])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (144) <;> decide
theorem meaning147 (q : Snake 81) : literal (valuation q) (147) = decide (1 ≤ countLit q [147]) := by
  change literal (baseVal q) (147) = decide (1 ≤ countLit q [147])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (147) <;> decide
theorem meaning150 (q : Snake 81) : literal (valuation q) (150) = decide (1 ≤ countLit q [150]) := by
  change literal (baseVal q) (150) = decide (1 ≤ countLit q [150])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (150) <;> decide
theorem meaning151 (q : Snake 81) : literal (valuation q) (151) = decide (1 ≤ countLit q [151]) := by
  change literal (baseVal q) (151) = decide (1 ≤ countLit q [151])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (151) <;> decide
theorem meaning152 (q : Snake 81) : literal (valuation q) (152) = decide (1 ≤ countLit q [152]) := by
  change literal (baseVal q) (152) = decide (1 ≤ countLit q [152])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (152) <;> decide
theorem meaning154 (q : Snake 81) : literal (valuation q) (154) = decide (1 ≤ countLit q [154]) := by
  change literal (baseVal q) (154) = decide (1 ≤ countLit q [154])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (154) <;> decide
theorem meaning158 (q : Snake 81) : literal (valuation q) (158) = decide (1 ≤ countLit q [158]) := by
  change literal (baseVal q) (158) = decide (1 ≤ countLit q [158])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (158) <;> decide
theorem meaning159 (q : Snake 81) : literal (valuation q) (159) = decide (1 ≤ countLit q [159]) := by
  change literal (baseVal q) (159) = decide (1 ≤ countLit q [159])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (159) <;> decide
theorem meaning160 (q : Snake 81) : literal (valuation q) (160) = decide (1 ≤ countLit q [160]) := by
  change literal (baseVal q) (160) = decide (1 ≤ countLit q [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (160) <;> decide
theorem meaning162 (q : Snake 81) : literal (valuation q) (162) = decide (1 ≤ countLit q [162]) := by
  change literal (baseVal q) (162) = decide (1 ≤ countLit q [162])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (162) <;> decide
theorem meaning166 (q : Snake 81) : literal (valuation q) (166) = decide (1 ≤ countLit q [166]) := by
  change literal (baseVal q) (166) = decide (1 ≤ countLit q [166])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (166) <;> decide
theorem meaning168 (q : Snake 81) : literal (valuation q) (168) = decide (1 ≤ countLit q [168]) := by
  change literal (baseVal q) (168) = decide (1 ≤ countLit q [168])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (168) <;> decide
theorem meaning170 (q : Snake 81) : literal (valuation q) (170) = decide (1 ≤ countLit q [170]) := by
  change literal (baseVal q) (170) = decide (1 ≤ countLit q [170])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (170) <;> decide
theorem meaning173 (q : Snake 81) : literal (valuation q) (173) = decide (1 ≤ countLit q [173]) := by
  change literal (baseVal q) (173) = decide (1 ≤ countLit q [173])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (173) <;> decide
theorem meaning174 (q : Snake 81) : literal (valuation q) (174) = decide (1 ≤ countLit q [174]) := by
  change literal (baseVal q) (174) = decide (1 ≤ countLit q [174])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (174) <;> decide
theorem meaning176 (q : Snake 81) : literal (valuation q) (176) = decide (1 ≤ countLit q [176]) := by
  change literal (baseVal q) (176) = decide (1 ≤ countLit q [176])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (176) <;> decide
theorem meaning177 (q : Snake 81) : literal (valuation q) (177) = decide (1 ≤ countLit q [177]) := by
  change literal (baseVal q) (177) = decide (1 ≤ countLit q [177])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (177) <;> decide
theorem meaning180 (q : Snake 81) : literal (valuation q) (180) = decide (1 ≤ countLit q [180]) := by
  change literal (baseVal q) (180) = decide (1 ≤ countLit q [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (180) <;> decide
theorem meaning185 (q : Snake 81) : literal (valuation q) (185) = decide (1 ≤ countLit q [185]) := by
  change literal (baseVal q) (185) = decide (1 ≤ countLit q [185])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (185) <;> decide
theorem meaning187 (q : Snake 81) : literal (valuation q) (187) = decide (1 ≤ countLit q [187]) := by
  change literal (baseVal q) (187) = decide (1 ≤ countLit q [187])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (187) <;> decide
theorem meaning188 (q : Snake 81) : literal (valuation q) (188) = decide (1 ≤ countLit q [188]) := by
  change literal (baseVal q) (188) = decide (1 ≤ countLit q [188])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (188) <;> decide
theorem meaning192 (q : Snake 81) : literal (valuation q) (192) = decide (1 ≤ countLit q [192]) := by
  change literal (baseVal q) (192) = decide (1 ≤ countLit q [192])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (192) <;> decide
theorem meaning193 (q : Snake 81) : literal (valuation q) (193) = decide (1 ≤ countLit q [193]) := by
  change literal (baseVal q) (193) = decide (1 ≤ countLit q [193])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (193) <;> decide
theorem meaning196 (q : Snake 81) : literal (valuation q) (196) = decide (1 ≤ countLit q [196]) := by
  change literal (baseVal q) (196) = decide (1 ≤ countLit q [196])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (196) <;> decide
theorem meaning197 (q : Snake 81) : literal (valuation q) (197) = decide (1 ≤ countLit q [197]) := by
  change literal (baseVal q) (197) = decide (1 ≤ countLit q [197])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (197) <;> decide
theorem meaning200 (q : Snake 81) : literal (valuation q) (200) = decide (1 ≤ countLit q [200]) := by
  change literal (baseVal q) (200) = decide (1 ≤ countLit q [200])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (200) <;> decide
theorem meaning203 (q : Snake 81) : literal (valuation q) (203) = decide (1 ≤ countLit q [203]) := by
  change literal (baseVal q) (203) = decide (1 ≤ countLit q [203])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (203) <;> decide
theorem meaning204 (q : Snake 81) : literal (valuation q) (204) = decide (1 ≤ countLit q [204]) := by
  change literal (baseVal q) (204) = decide (1 ≤ countLit q [204])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (204) <;> decide
theorem meaning205 (q : Snake 81) : literal (valuation q) (205) = decide (1 ≤ countLit q [205]) := by
  change literal (baseVal q) (205) = decide (1 ≤ countLit q [205])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (205) <;> decide
theorem meaning208 (q : Snake 81) : literal (valuation q) (208) = decide (1 ≤ countLit q [208]) := by
  change literal (baseVal q) (208) = decide (1 ≤ countLit q [208])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (208) <;> decide
theorem meaning211 (q : Snake 81) : literal (valuation q) (211) = decide (1 ≤ countLit q [211]) := by
  change literal (baseVal q) (211) = decide (1 ≤ countLit q [211])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (211) <;> decide
theorem meaning213 (q : Snake 81) : literal (valuation q) (213) = decide (1 ≤ countLit q [213]) := by
  change literal (baseVal q) (213) = decide (1 ≤ countLit q [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (213) <;> decide
theorem meaning216 (q : Snake 81) : literal (valuation q) (216) = decide (1 ≤ countLit q [216]) := by
  change literal (baseVal q) (216) = decide (1 ≤ countLit q [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (216) <;> decide
theorem meaning218 (q : Snake 81) : literal (valuation q) (218) = decide (1 ≤ countLit q [218]) := by
  change literal (baseVal q) (218) = decide (1 ≤ countLit q [218])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (218) <;> decide
theorem meaning221 (q : Snake 81) : literal (valuation q) (221) = decide (1 ≤ countLit q [221]) := by
  change literal (baseVal q) (221) = decide (1 ≤ countLit q [221])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (221) <;> decide
theorem meaning222 (q : Snake 81) : literal (valuation q) (222) = decide (1 ≤ countLit q [222]) := by
  change literal (baseVal q) (222) = decide (1 ≤ countLit q [222])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (222) <;> decide
theorem meaning224 (q : Snake 81) : literal (valuation q) (224) = decide (1 ≤ countLit q [224]) := by
  change literal (baseVal q) (224) = decide (1 ≤ countLit q [224])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (224) <;> decide
theorem meaning225 (q : Snake 81) : literal (valuation q) (225) = decide (1 ≤ countLit q [225]) := by
  change literal (baseVal q) (225) = decide (1 ≤ countLit q [225])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (225) <;> decide
theorem meaning228 (q : Snake 81) : literal (valuation q) (228) = decide (1 ≤ countLit q [228]) := by
  change literal (baseVal q) (228) = decide (1 ≤ countLit q [228])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (228) <;> decide
theorem meaning229 (q : Snake 81) : literal (valuation q) (229) = decide (1 ≤ countLit q [229]) := by
  change literal (baseVal q) (229) = decide (1 ≤ countLit q [229])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (229) <;> decide
theorem meaning230 (q : Snake 81) : literal (valuation q) (230) = decide (1 ≤ countLit q [230]) := by
  change literal (baseVal q) (230) = decide (1 ≤ countLit q [230])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (230) <;> decide
theorem meaning234 (q : Snake 81) : literal (valuation q) (234) = decide (1 ≤ countLit q [234]) := by
  change literal (baseVal q) (234) = decide (1 ≤ countLit q [234])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (234) <;> decide
theorem meaning236 (q : Snake 81) : literal (valuation q) (236) = decide (1 ≤ countLit q [236]) := by
  change literal (baseVal q) (236) = decide (1 ≤ countLit q [236])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (236) <;> decide
theorem meaning237 (q : Snake 81) : literal (valuation q) (237) = decide (1 ≤ countLit q [237]) := by
  change literal (baseVal q) (237) = decide (1 ≤ countLit q [237])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (237) <;> decide
theorem meaning242 (q : Snake 81) : literal (valuation q) (242) = decide (1 ≤ countLit q [242]) := by
  change literal (baseVal q) (242) = decide (1 ≤ countLit q [242])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (242) <;> decide
theorem meaning243 (q : Snake 81) : literal (valuation q) (243) = decide (1 ≤ countLit q [243]) := by
  change literal (baseVal q) (243) = decide (1 ≤ countLit q [243])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) (243) <;> decide
theorem meaning245 (q : Snake 81) : literal (valuation q) 245 = decide (1 ≤ count245 q) := rfl
theorem meaning247 (q : Snake 81) : literal (valuation q) 247 = decide (1 ≤ count247 q) := rfl
theorem meaning248 (q : Snake 81) : literal (valuation q) 248 = decide (2 ≤ count247 q) := rfl
theorem meaning249 (q : Snake 81) : literal (valuation q) 249 = decide (1 ≤ count249 q) := rfl
theorem meaning251 (q : Snake 81) : literal (valuation q) 251 = decide (1 ≤ count251 q) := rfl
theorem meaning253 (q : Snake 81) : literal (valuation q) 253 = decide (1 ≤ count253 q) := rfl
theorem meaning255 (q : Snake 81) : literal (valuation q) 255 = decide (1 ≤ count255 q) := rfl
theorem meaning256 (q : Snake 81) : literal (valuation q) 256 = decide (2 ≤ count255 q) := rfl
theorem meaning257 (q : Snake 81) : literal (valuation q) 257 = decide (1 ≤ count257 q) := rfl
theorem meaning259 (q : Snake 81) : literal (valuation q) 259 = decide (1 ≤ count259 q) := rfl
theorem meaning261 (q : Snake 81) : literal (valuation q) 261 = decide (1 ≤ count261 q) := rfl
theorem meaning265 (q : Snake 81) : literal (valuation q) 265 = decide (1 ≤ count265 q) := rfl
theorem meaning267 (q : Snake 81) : literal (valuation q) 267 = decide (1 ≤ count267 q) := rfl
theorem meaning269 (q : Snake 81) : literal (valuation q) 269 = decide (1 ≤ count269 q) := rfl
theorem meaning270 (q : Snake 81) : literal (valuation q) 270 = decide (2 ≤ count269 q) := rfl
theorem meaning271 (q : Snake 81) : literal (valuation q) 271 = decide (1 ≤ count271 q) := rfl
theorem meaning272 (q : Snake 81) : literal (valuation q) 272 = decide (2 ≤ count271 q) := rfl
theorem meaning273 (q : Snake 81) : literal (valuation q) 273 = decide (1 ≤ count273 q) := rfl
theorem meaning275 (q : Snake 81) : literal (valuation q) 275 = decide (1 ≤ count275 q) := rfl
theorem meaning277 (q : Snake 81) : literal (valuation q) 277 = decide (1 ≤ count277 q) := rfl
theorem meaning279 (q : Snake 81) : literal (valuation q) 279 = decide (1 ≤ count279 q) := rfl
theorem meaning281 (q : Snake 81) : literal (valuation q) 281 = decide (1 ≤ count281 q) := rfl
theorem meaning283 (q : Snake 81) : literal (valuation q) 283 = decide (1 ≤ count283 q) := rfl
theorem meaning287 (q : Snake 81) : literal (valuation q) 287 = decide (1 ≤ count287 q) := rfl
theorem meaning289 (q : Snake 81) : literal (valuation q) 289 = decide (1 ≤ count289 q) := rfl
theorem meaning291 (q : Snake 81) : literal (valuation q) 291 = decide (1 ≤ count291 q) := rfl
theorem meaning293 (q : Snake 81) : literal (valuation q) 293 = decide (1 ≤ count293 q) := rfl
theorem meaning295 (q : Snake 81) : literal (valuation q) 295 = decide (1 ≤ count295 q) := rfl
theorem meaning297 (q : Snake 81) : literal (valuation q) 297 = decide (1 ≤ count297 q) := rfl
theorem meaning299 (q : Snake 81) : literal (valuation q) 299 = decide (1 ≤ count299 q) := rfl
theorem meaning301 (q : Snake 81) : literal (valuation q) 301 = decide (1 ≤ count301 q) := rfl
theorem meaning302 (q : Snake 81) : literal (valuation q) 302 = decide (2 ≤ count301 q) := rfl
theorem meaning303 (q : Snake 81) : literal (valuation q) 303 = decide (1 ≤ count303 q) := rfl
theorem meaning305 (q : Snake 81) : literal (valuation q) 305 = decide (1 ≤ count305 q) := rfl
theorem meaning309 (q : Snake 81) : literal (valuation q) 309 = decide (1 ≤ count309 q) := rfl
theorem meaning311 (q : Snake 81) : literal (valuation q) 311 = decide (1 ≤ count311 q) := rfl
theorem meaning313 (q : Snake 81) : literal (valuation q) 313 = decide (1 ≤ count313 q) := rfl
theorem meaning315 (q : Snake 81) : literal (valuation q) 315 = decide (1 ≤ count315 q) := rfl
theorem meaning317 (q : Snake 81) : literal (valuation q) 317 = decide (1 ≤ count317 q) := rfl
theorem meaning319 (q : Snake 81) : literal (valuation q) 319 = decide (1 ≤ count319 q) := rfl
theorem meaning323 (q : Snake 81) : literal (valuation q) 323 = decide (1 ≤ count323 q) := rfl
theorem meaning325 (q : Snake 81) : literal (valuation q) 325 = decide (1 ≤ count325 q) := rfl
theorem meaning327 (q : Snake 81) : literal (valuation q) 327 = decide (1 ≤ count327 q) := rfl
theorem meaning329 (q : Snake 81) : literal (valuation q) 329 = decide (1 ≤ count329 q) := rfl
theorem meaning331 (q : Snake 81) : literal (valuation q) 331 = decide (1 ≤ count331 q) := rfl
theorem meaning333 (q : Snake 81) : literal (valuation q) 333 = decide (1 ≤ count333 q) := rfl
theorem meaning337 (q : Snake 81) : literal (valuation q) 337 = decide (1 ≤ count337 q) := rfl
theorem meaning338 (q : Snake 81) : literal (valuation q) 338 = decide (2 ≤ count337 q) := rfl
theorem meaning339 (q : Snake 81) : literal (valuation q) 339 = decide (1 ≤ count339 q) := rfl
theorem meaning340 (q : Snake 81) : literal (valuation q) 340 = decide (2 ≤ count339 q) := rfl
theorem meaning341 (q : Snake 81) : literal (valuation q) 341 = decide (1 ≤ count341 q) := rfl
theorem meaning342 (q : Snake 81) : literal (valuation q) 342 = decide (2 ≤ count341 q) := rfl
theorem meaning343 (q : Snake 81) : literal (valuation q) 343 = decide (1 ≤ count343 q) := rfl
theorem meaning345 (q : Snake 81) : literal (valuation q) 345 = decide (1 ≤ count345 q) := rfl
theorem meaning347 (q : Snake 81) : literal (valuation q) 347 = decide (1 ≤ count347 q) := rfl
theorem meaning349 (q : Snake 81) : literal (valuation q) 349 = decide (1 ≤ count349 q) := rfl
theorem meaning353 (q : Snake 81) : literal (valuation q) 353 = decide (1 ≤ count353 q) := rfl
theorem meaning355 (q : Snake 81) : literal (valuation q) 355 = decide (1 ≤ count355 q) := rfl
theorem meaning356 (q : Snake 81) : literal (valuation q) 356 = decide (2 ≤ count355 q) := rfl
theorem meaning357 (q : Snake 81) : literal (valuation q) 357 = decide (1 ≤ count357 q) := rfl
theorem meaning358 (q : Snake 81) : literal (valuation q) 358 = decide (2 ≤ count357 q) := rfl
theorem meaning359 (q : Snake 81) : literal (valuation q) 359 = decide (1 ≤ count359 q) := rfl
theorem meaning360 (q : Snake 81) : literal (valuation q) 360 = decide (2 ≤ count359 q) := rfl
theorem meaning361 (q : Snake 81) : literal (valuation q) 361 = decide (1 ≤ count361 q) := rfl
theorem meaning362 (q : Snake 81) : literal (valuation q) 362 = decide (2 ≤ count361 q) := rfl
theorem meaning363 (q : Snake 81) : literal (valuation q) 363 = decide (1 ≤ count363 q) := rfl
theorem meaning365 (q : Snake 81) : literal (valuation q) 365 = decide (1 ≤ count365 q) := rfl
theorem meaning367 (q : Snake 81) : literal (valuation q) 367 = decide (1 ≤ count367 q) := rfl
theorem meaning369 (q : Snake 81) : literal (valuation q) 369 = decide (1 ≤ count369 q) := rfl
theorem meaning371 (q : Snake 81) : literal (valuation q) 371 = decide (1 ≤ count371 q) := rfl
theorem meaning373 (q : Snake 81) : literal (valuation q) 373 = decide (1 ≤ count373 q) := rfl
theorem meaning377 (q : Snake 81) : literal (valuation q) 377 = decide (1 ≤ count377 q) := rfl
theorem meaning378 (q : Snake 81) : literal (valuation q) 378 = decide (2 ≤ count377 q) := rfl
theorem meaning379 (q : Snake 81) : literal (valuation q) 379 = decide (1 ≤ count379 q) := rfl
theorem meaning380 (q : Snake 81) : literal (valuation q) 380 = decide (2 ≤ count379 q) := rfl
theorem meaning383 (q : Snake 81) : literal (valuation q) 383 = decide (1 ≤ count383 q) := rfl
theorem meaning385 (q : Snake 81) : literal (valuation q) 385 = decide (1 ≤ count385 q) := rfl
theorem meaning387 (q : Snake 81) : literal (valuation q) 387 = decide (1 ≤ count387 q) := rfl
theorem meaning388 (q : Snake 81) : literal (valuation q) 388 = decide (2 ≤ count387 q) := rfl
theorem meaning389 (q : Snake 81) : literal (valuation q) 389 = decide (1 ≤ count389 q) := rfl
theorem meaning390 (q : Snake 81) : literal (valuation q) 390 = decide (2 ≤ count389 q) := rfl
theorem meaning391 (q : Snake 81) : literal (valuation q) 391 = decide (1 ≤ count391 q) := rfl
theorem meaning393 (q : Snake 81) : literal (valuation q) 393 = decide (1 ≤ count393 q) := rfl
theorem meaning395 (q : Snake 81) : literal (valuation q) 395 = decide (1 ≤ count395 q) := rfl
theorem meaning397 (q : Snake 81) : literal (valuation q) 397 = decide (1 ≤ count397 q) := rfl
theorem meaning399 (q : Snake 81) : literal (valuation q) 399 = decide (1 ≤ count399 q) := rfl
theorem meaning401 (q : Snake 81) : literal (valuation q) 401 = decide (1 ≤ count401 q) := rfl
theorem meaning402 (q : Snake 81) : literal (valuation q) 402 = decide (2 ≤ count401 q) := rfl
theorem meaning405 (q : Snake 81) : literal (valuation q) 405 = decide (1 ≤ count405 q) := rfl
theorem meaning407 (q : Snake 81) : literal (valuation q) 407 = decide (1 ≤ count407 q) := rfl
theorem meaning409 (q : Snake 81) : literal (valuation q) 409 = decide (1 ≤ count409 q) := rfl
theorem meaning411 (q : Snake 81) : literal (valuation q) 411 = decide (1 ≤ count411 q) := rfl
theorem meaning413 (q : Snake 81) : literal (valuation q) 413 = decide (1 ≤ count413 q) := rfl
theorem meaning415 (q : Snake 81) : literal (valuation q) 415 = decide (1 ≤ count415 q) := rfl
theorem meaning417 (q : Snake 81) : literal (valuation q) 417 = decide (1 ≤ count417 q) := rfl
theorem meaning418 (q : Snake 81) : literal (valuation q) 418 = decide (2 ≤ count417 q) := rfl
theorem meaning419 (q : Snake 81) : literal (valuation q) 419 = decide (1 ≤ count419 q) := rfl
theorem meaning420 (q : Snake 81) : literal (valuation q) 420 = decide (2 ≤ count419 q) := rfl
theorem meaning421 (q : Snake 81) : literal (valuation q) 421 = decide (1 ≤ count421 q) := rfl
theorem meaning423 (q : Snake 81) : literal (valuation q) 423 = decide (1 ≤ count423 q) := rfl
theorem meaning425 (q : Snake 81) : literal (valuation q) 425 = decide (1 ≤ count425 q) := rfl
theorem meaning429 (q : Snake 81) : literal (valuation q) 429 = decide (1 ≤ count429 q) := rfl
theorem meaning431 (q : Snake 81) : literal (valuation q) 431 = decide (1 ≤ count431 q) := rfl
theorem meaning433 (q : Snake 81) : literal (valuation q) 433 = decide (1 ≤ count433 q) := rfl
theorem meaning435 (q : Snake 81) : literal (valuation q) 435 = decide (1 ≤ count435 q) := rfl
theorem meaning437 (q : Snake 81) : literal (valuation q) 437 = decide (1 ≤ count437 q) := rfl
theorem meaning439 (q : Snake 81) : literal (valuation q) 439 = decide (1 ≤ count439 q) := rfl
theorem meaning441 (q : Snake 81) : literal (valuation q) 441 = decide (1 ≤ count441 q) := rfl
theorem meaning443 (q : Snake 81) : literal (valuation q) 443 = decide (1 ≤ count443 q) := rfl
theorem meaning445 (q : Snake 81) : literal (valuation q) 445 = decide (1 ≤ count445 q) := rfl
theorem meaning447 (q : Snake 81) : literal (valuation q) 447 = decide (1 ≤ count447 q) := rfl
theorem meaning449 (q : Snake 81) : literal (valuation q) 449 = decide (1 ≤ count449 q) := rfl
theorem meaning453 (q : Snake 81) : literal (valuation q) 453 = decide (1 ≤ count453 q) := rfl
theorem meaning455 (q : Snake 81) : literal (valuation q) 455 = decide (1 ≤ count455 q) := rfl
theorem meaning457 (q : Snake 81) : literal (valuation q) 457 = decide (1 ≤ count457 q) := rfl
theorem meaning459 (q : Snake 81) : literal (valuation q) 459 = decide (1 ≤ count459 q) := rfl
theorem meaning461 (q : Snake 81) : literal (valuation q) 461 = decide (1 ≤ count461 q) := rfl
theorem meaning463 (q : Snake 81) : literal (valuation q) 463 = decide (1 ≤ count463 q) := rfl
theorem meaning467 (q : Snake 81) : literal (valuation q) 467 = decide (1 ≤ count467 q) := rfl
theorem meaning469 (q : Snake 81) : literal (valuation q) 469 = decide (1 ≤ count469 q) := rfl
theorem meaning471 (q : Snake 81) : literal (valuation q) 471 = decide (1 ≤ count471 q) := rfl
theorem meaning473 (q : Snake 81) : literal (valuation q) 473 = decide (1 ≤ count473 q) := rfl
theorem meaning474 (q : Snake 81) : literal (valuation q) 474 = decide (2 ≤ count473 q) := rfl
theorem meaning475 (q : Snake 81) : literal (valuation q) 475 = decide (1 ≤ count475 q) := rfl
theorem meaning476 (q : Snake 81) : literal (valuation q) 476 = decide (2 ≤ count475 q) := rfl
theorem meaning477 (q : Snake 81) : literal (valuation q) 477 = decide (1 ≤ count477 q) := rfl
theorem meaning478 (q : Snake 81) : literal (valuation q) 478 = decide (2 ≤ count477 q) := rfl
theorem meaning479 (q : Snake 81) : literal (valuation q) 479 = decide (1 ≤ count479 q) := rfl
theorem meaning480 (q : Snake 81) : literal (valuation q) 480 = decide (2 ≤ count479 q) := rfl
theorem meaning481 (q : Snake 81) : literal (valuation q) 481 = decide (1 ≤ count481 q) := rfl
theorem meaning482 (q : Snake 81) : literal (valuation q) 482 = decide (2 ≤ count481 q) := rfl
theorem meaning484 (q : Snake 81) : literal (valuation q) 484 = decide (2 ≤ count483 q) := rfl
theorem meaning1461 (q : Snake 81) : literal (valuation q) 1461 = decide (1 ≤ count1461 q) := rfl
theorem meaning1462 (q : Snake 81) : literal (valuation q) 1462 = decide (2 ≤ count1461 q) := rfl
theorem meaning1463 (q : Snake 81) : literal (valuation q) 1463 = decide (1 ≤ count1463 q) := rfl
theorem meaning1464 (q : Snake 81) : literal (valuation q) 1464 = decide (2 ≤ count1463 q) := rfl
theorem meaning1465 (q : Snake 81) : literal (valuation q) 1465 = decide (3 ≤ count1463 q) := rfl
theorem meaning1466 (q : Snake 81) : literal (valuation q) 1466 = decide (1 ≤ count1466 q) := rfl
theorem meaning1467 (q : Snake 81) : literal (valuation q) 1467 = decide (2 ≤ count1466 q) := rfl
theorem meaning1468 (q : Snake 81) : literal (valuation q) 1468 = decide (1 ≤ count1468 q) := rfl
theorem meaning1469 (q : Snake 81) : literal (valuation q) 1469 = decide (2 ≤ count1468 q) := rfl
theorem meaning1470 (q : Snake 81) : literal (valuation q) 1470 = decide (1 ≤ count1470 q) := rfl
theorem meaning1471 (q : Snake 81) : literal (valuation q) 1471 = decide (2 ≤ count1470 q) := rfl
theorem meaning1472 (q : Snake 81) : literal (valuation q) 1472 = decide (3 ≤ count1470 q) := rfl
theorem meaning1473 (q : Snake 81) : literal (valuation q) 1473 = decide (4 ≤ count1470 q) := rfl
theorem meaning1474 (q : Snake 81) : literal (valuation q) 1474 = decide (1 ≤ count1474 q) := rfl
theorem meaning1475 (q : Snake 81) : literal (valuation q) 1475 = decide (2 ≤ count1474 q) := rfl
theorem meaning1476 (q : Snake 81) : literal (valuation q) 1476 = decide (3 ≤ count1474 q) := rfl
theorem meaning1477 (q : Snake 81) : literal (valuation q) 1477 = decide (4 ≤ count1474 q) := rfl
theorem meaning1478 (q : Snake 81) : literal (valuation q) 1478 = decide (5 ≤ count1474 q) := rfl
theorem meaning1479 (q : Snake 81) : literal (valuation q) 1479 = decide (6 ≤ count1474 q) := rfl
theorem meaning1481 (q : Snake 81) : literal (valuation q) 1481 = decide (1 ≤ count1481 q) := rfl
theorem meaning1482 (q : Snake 81) : literal (valuation q) 1482 = decide (2 ≤ count1481 q) := rfl
theorem meaning1483 (q : Snake 81) : literal (valuation q) 1483 = decide (1 ≤ count1483 q) := rfl
theorem meaning1484 (q : Snake 81) : literal (valuation q) 1484 = decide (2 ≤ count1483 q) := rfl
theorem meaning1485 (q : Snake 81) : literal (valuation q) 1485 = decide (1 ≤ count1485 q) := rfl
theorem meaning1486 (q : Snake 81) : literal (valuation q) 1486 = decide (2 ≤ count1485 q) := rfl
theorem meaning1487 (q : Snake 81) : literal (valuation q) 1487 = decide (3 ≤ count1485 q) := rfl
theorem meaning1488 (q : Snake 81) : literal (valuation q) 1488 = decide (4 ≤ count1485 q) := rfl
theorem meaning1489 (q : Snake 81) : literal (valuation q) 1489 = decide (1 ≤ count1489 q) := rfl
theorem meaning1490 (q : Snake 81) : literal (valuation q) 1490 = decide (2 ≤ count1489 q) := rfl
theorem meaning1491 (q : Snake 81) : literal (valuation q) 1491 = decide (1 ≤ count1491 q) := rfl
theorem meaning1492 (q : Snake 81) : literal (valuation q) 1492 = decide (2 ≤ count1491 q) := rfl
theorem meaning1493 (q : Snake 81) : literal (valuation q) 1493 = decide (1 ≤ count1493 q) := rfl
theorem meaning1494 (q : Snake 81) : literal (valuation q) 1494 = decide (2 ≤ count1493 q) := rfl
theorem meaning1495 (q : Snake 81) : literal (valuation q) 1495 = decide (3 ≤ count1493 q) := rfl
theorem meaning1497 (q : Snake 81) : literal (valuation q) 1497 = decide (1 ≤ count1497 q) := rfl
theorem meaning1498 (q : Snake 81) : literal (valuation q) 1498 = decide (2 ≤ count1497 q) := rfl
theorem meaning1499 (q : Snake 81) : literal (valuation q) 1499 = decide (3 ≤ count1497 q) := rfl
theorem meaning1500 (q : Snake 81) : literal (valuation q) 1500 = decide (4 ≤ count1497 q) := rfl
theorem meaning1501 (q : Snake 81) : literal (valuation q) 1501 = decide (5 ≤ count1497 q) := rfl
theorem meaning1502 (q : Snake 81) : literal (valuation q) 1502 = decide (6 ≤ count1497 q) := rfl
theorem meaning1507 (q : Snake 81) : literal (valuation q) 1507 = decide (3 ≤ count1505 q) := rfl
theorem meaning1508 (q : Snake 81) : literal (valuation q) 1508 = decide (4 ≤ count1505 q) := rfl
theorem meaning1509 (q : Snake 81) : literal (valuation q) 1509 = decide (5 ≤ count1505 q) := rfl
theorem meaning1510 (q : Snake 81) : literal (valuation q) 1510 = decide (6 ≤ count1505 q) := rfl
theorem meaning1511 (q : Snake 81) : literal (valuation q) 1511 = decide (7 ≤ count1505 q) := rfl
theorem meaning1512 (q : Snake 81) : literal (valuation q) 1512 = decide (8 ≤ count1505 q) := rfl
theorem meaning1513 (q : Snake 81) : literal (valuation q) 1513 = decide (9 ≤ count1505 q) := rfl
theorem meaning1520 (q : Snake 81) : literal (valuation q) 1520 = decide (1 ≤ count1520 q) := rfl
theorem meaning1521 (q : Snake 81) : literal (valuation q) 1521 = decide (2 ≤ count1520 q) := rfl
theorem meaning1522 (q : Snake 81) : literal (valuation q) 1522 = decide (1 ≤ count1522 q) := rfl
theorem meaning1523 (q : Snake 81) : literal (valuation q) 1523 = decide (2 ≤ count1522 q) := rfl
theorem meaning1524 (q : Snake 81) : literal (valuation q) 1524 = decide (1 ≤ count1524 q) := rfl
theorem meaning1525 (q : Snake 81) : literal (valuation q) 1525 = decide (2 ≤ count1524 q) := rfl
theorem meaning1528 (q : Snake 81) : literal (valuation q) 1528 = decide (1 ≤ count1528 q) := rfl
theorem meaning1529 (q : Snake 81) : literal (valuation q) 1529 = decide (2 ≤ count1528 q) := rfl
theorem meaning1530 (q : Snake 81) : literal (valuation q) 1530 = decide (1 ≤ count1530 q) := rfl
theorem meaning1531 (q : Snake 81) : literal (valuation q) 1531 = decide (2 ≤ count1530 q) := rfl
theorem meaning1532 (q : Snake 81) : literal (valuation q) 1532 = decide (1 ≤ count1532 q) := rfl
theorem meaning1533 (q : Snake 81) : literal (valuation q) 1533 = decide (2 ≤ count1532 q) := rfl
theorem meaning1534 (q : Snake 81) : literal (valuation q) 1534 = decide (3 ≤ count1532 q) := rfl
theorem meaning1535 (q : Snake 81) : literal (valuation q) 1535 = decide (4 ≤ count1532 q) := rfl
theorem meaning1536 (q : Snake 81) : literal (valuation q) 1536 = decide (1 ≤ count1536 q) := rfl
theorem meaning1537 (q : Snake 81) : literal (valuation q) 1537 = decide (2 ≤ count1536 q) := rfl
theorem meaning1538 (q : Snake 81) : literal (valuation q) 1538 = decide (3 ≤ count1536 q) := rfl
theorem meaning1539 (q : Snake 81) : literal (valuation q) 1539 = decide (4 ≤ count1536 q) := rfl
theorem meaning1540 (q : Snake 81) : literal (valuation q) 1540 = decide (5 ≤ count1536 q) := rfl
theorem meaning1544 (q : Snake 81) : literal (valuation q) 1544 = decide (1 ≤ count1544 q) := rfl
theorem meaning1545 (q : Snake 81) : literal (valuation q) 1545 = decide (2 ≤ count1544 q) := rfl
theorem meaning1546 (q : Snake 81) : literal (valuation q) 1546 = decide (1 ≤ count1546 q) := rfl
theorem meaning1547 (q : Snake 81) : literal (valuation q) 1547 = decide (2 ≤ count1546 q) := rfl
theorem meaning1548 (q : Snake 81) : literal (valuation q) 1548 = decide (1 ≤ count1548 q) := rfl
theorem meaning1549 (q : Snake 81) : literal (valuation q) 1549 = decide (2 ≤ count1548 q) := rfl
theorem meaning1550 (q : Snake 81) : literal (valuation q) 1550 = decide (3 ≤ count1548 q) := rfl
theorem meaning1551 (q : Snake 81) : literal (valuation q) 1551 = decide (4 ≤ count1548 q) := rfl
theorem meaning1552 (q : Snake 81) : literal (valuation q) 1552 = decide (1 ≤ count1552 q) := rfl
theorem meaning1553 (q : Snake 81) : literal (valuation q) 1553 = decide (2 ≤ count1552 q) := rfl
theorem meaning1554 (q : Snake 81) : literal (valuation q) 1554 = decide (1 ≤ count1554 q) := rfl
theorem meaning1555 (q : Snake 81) : literal (valuation q) 1555 = decide (2 ≤ count1554 q) := rfl
theorem meaning1556 (q : Snake 81) : literal (valuation q) 1556 = decide (1 ≤ count1556 q) := rfl
theorem meaning1557 (q : Snake 81) : literal (valuation q) 1557 = decide (2 ≤ count1556 q) := rfl
theorem meaning1558 (q : Snake 81) : literal (valuation q) 1558 = decide (3 ≤ count1556 q) := rfl
theorem meaning1559 (q : Snake 81) : literal (valuation q) 1559 = decide (4 ≤ count1556 q) := rfl
theorem meaning1560 (q : Snake 81) : literal (valuation q) 1560 = decide (1 ≤ count1560 q) := rfl
theorem meaning1561 (q : Snake 81) : literal (valuation q) 1561 = decide (2 ≤ count1560 q) := rfl
theorem meaning1562 (q : Snake 81) : literal (valuation q) 1562 = decide (3 ≤ count1560 q) := rfl
theorem meaning1563 (q : Snake 81) : literal (valuation q) 1563 = decide (4 ≤ count1560 q) := rfl
theorem meaning1564 (q : Snake 81) : literal (valuation q) 1564 = decide (5 ≤ count1560 q) := rfl
theorem meaning1565 (q : Snake 81) : literal (valuation q) 1565 = decide (6 ≤ count1560 q) := rfl
theorem meaning1566 (q : Snake 81) : literal (valuation q) 1566 = decide (7 ≤ count1560 q) := rfl
theorem meaning1570 (q : Snake 81) : literal (valuation q) 1570 = decide (3 ≤ count1568 q) := rfl
theorem meaning1571 (q : Snake 81) : literal (valuation q) 1571 = decide (4 ≤ count1568 q) := rfl
theorem meaning1572 (q : Snake 81) : literal (valuation q) 1572 = decide (5 ≤ count1568 q) := rfl
theorem meaning1573 (q : Snake 81) : literal (valuation q) 1573 = decide (6 ≤ count1568 q) := rfl
theorem meaning1574 (q : Snake 81) : literal (valuation q) 1574 = decide (7 ≤ count1568 q) := rfl
theorem meaning1575 (q : Snake 81) : literal (valuation q) 1575 = decide (8 ≤ count1568 q) := rfl
theorem meaning1576 (q : Snake 81) : literal (valuation q) 1576 = decide (9 ≤ count1568 q) := rfl
theorem meaning1577 (q : Snake 81) : literal (valuation q) 1577 = decide (10 ≤ count1568 q) := rfl
theorem meaning1590 (q : Snake 81) : literal (valuation q) 1590 = decide (7 ≤ count1584 q) := rfl
theorem meaning1591 (q : Snake 81) : literal (valuation q) 1591 = decide (8 ≤ count1584 q) := rfl
theorem meaning1592 (q : Snake 81) : literal (valuation q) 1592 = decide (9 ≤ count1584 q) := rfl
theorem meaning1593 (q : Snake 81) : literal (valuation q) 1593 = decide (10 ≤ count1584 q) := rfl
theorem meaning1594 (q : Snake 81) : literal (valuation q) 1594 = decide (11 ≤ count1584 q) := rfl
theorem meaning1595 (q : Snake 81) : literal (valuation q) 1595 = decide (12 ≤ count1584 q) := rfl
theorem meaning1596 (q : Snake 81) : literal (valuation q) 1596 = decide (13 ≤ count1584 q) := rfl
theorem meaning1597 (q : Snake 81) : literal (valuation q) 1597 = decide (14 ≤ count1584 q) := rfl
theorem meaning1607 (q : Snake 81) : literal (valuation q) 1607 = decide (1 ≤ count1607 q) := rfl
theorem meaning1608 (q : Snake 81) : literal (valuation q) 1608 = decide (2 ≤ count1607 q) := rfl
theorem meaning1609 (q : Snake 81) : literal (valuation q) 1609 = decide (1 ≤ count1609 q) := rfl
theorem meaning1610 (q : Snake 81) : literal (valuation q) 1610 = decide (2 ≤ count1609 q) := rfl
theorem meaning1611 (q : Snake 81) : literal (valuation q) 1611 = decide (1 ≤ count1611 q) := rfl
theorem meaning1612 (q : Snake 81) : literal (valuation q) 1612 = decide (2 ≤ count1611 q) := rfl
theorem meaning1613 (q : Snake 81) : literal (valuation q) 1613 = decide (3 ≤ count1611 q) := rfl
theorem meaning1614 (q : Snake 81) : literal (valuation q) 1614 = decide (4 ≤ count1611 q) := rfl
theorem meaning1615 (q : Snake 81) : literal (valuation q) 1615 = decide (1 ≤ count1615 q) := rfl
theorem meaning1616 (q : Snake 81) : literal (valuation q) 1616 = decide (2 ≤ count1615 q) := rfl
theorem meaning1617 (q : Snake 81) : literal (valuation q) 1617 = decide (1 ≤ count1617 q) := rfl
theorem meaning1618 (q : Snake 81) : literal (valuation q) 1618 = decide (2 ≤ count1617 q) := rfl
theorem meaning1619 (q : Snake 81) : literal (valuation q) 1619 = decide (1 ≤ count1619 q) := rfl
theorem meaning1620 (q : Snake 81) : literal (valuation q) 1620 = decide (2 ≤ count1619 q) := rfl
theorem meaning1621 (q : Snake 81) : literal (valuation q) 1621 = decide (3 ≤ count1619 q) := rfl
theorem meaning1622 (q : Snake 81) : literal (valuation q) 1622 = decide (4 ≤ count1619 q) := rfl
theorem meaning1623 (q : Snake 81) : literal (valuation q) 1623 = decide (1 ≤ count1623 q) := rfl
theorem meaning1624 (q : Snake 81) : literal (valuation q) 1624 = decide (2 ≤ count1623 q) := rfl
theorem meaning1625 (q : Snake 81) : literal (valuation q) 1625 = decide (3 ≤ count1623 q) := rfl
theorem meaning1626 (q : Snake 81) : literal (valuation q) 1626 = decide (4 ≤ count1623 q) := rfl
theorem meaning1627 (q : Snake 81) : literal (valuation q) 1627 = decide (5 ≤ count1623 q) := rfl
theorem meaning1628 (q : Snake 81) : literal (valuation q) 1628 = decide (6 ≤ count1623 q) := rfl
theorem meaning1631 (q : Snake 81) : literal (valuation q) 1631 = decide (1 ≤ count1631 q) := rfl
theorem meaning1633 (q : Snake 81) : literal (valuation q) 1633 = decide (1 ≤ count1633 q) := rfl
theorem meaning1634 (q : Snake 81) : literal (valuation q) 1634 = decide (2 ≤ count1633 q) := rfl
theorem meaning1635 (q : Snake 81) : literal (valuation q) 1635 = decide (1 ≤ count1635 q) := rfl
theorem meaning1636 (q : Snake 81) : literal (valuation q) 1636 = decide (2 ≤ count1635 q) := rfl
theorem meaning1637 (q : Snake 81) : literal (valuation q) 1637 = decide (3 ≤ count1635 q) := rfl
theorem meaning1639 (q : Snake 81) : literal (valuation q) 1639 = decide (1 ≤ count1639 q) := rfl
theorem meaning1640 (q : Snake 81) : literal (valuation q) 1640 = decide (2 ≤ count1639 q) := rfl
theorem meaning1641 (q : Snake 81) : literal (valuation q) 1641 = decide (1 ≤ count1641 q) := rfl
theorem meaning1642 (q : Snake 81) : literal (valuation q) 1642 = decide (2 ≤ count1641 q) := rfl
theorem meaning1643 (q : Snake 81) : literal (valuation q) 1643 = decide (1 ≤ count1643 q) := rfl
theorem meaning1644 (q : Snake 81) : literal (valuation q) 1644 = decide (2 ≤ count1643 q) := rfl
theorem meaning1645 (q : Snake 81) : literal (valuation q) 1645 = decide (3 ≤ count1643 q) := rfl
theorem meaning1646 (q : Snake 81) : literal (valuation q) 1646 = decide (4 ≤ count1643 q) := rfl
theorem meaning1647 (q : Snake 81) : literal (valuation q) 1647 = decide (1 ≤ count1647 q) := rfl
theorem meaning1648 (q : Snake 81) : literal (valuation q) 1648 = decide (2 ≤ count1647 q) := rfl
theorem meaning1649 (q : Snake 81) : literal (valuation q) 1649 = decide (3 ≤ count1647 q) := rfl
theorem meaning1650 (q : Snake 81) : literal (valuation q) 1650 = decide (4 ≤ count1647 q) := rfl
theorem meaning1651 (q : Snake 81) : literal (valuation q) 1651 = decide (5 ≤ count1647 q) := rfl
theorem meaning1652 (q : Snake 81) : literal (valuation q) 1652 = decide (6 ≤ count1647 q) := rfl
theorem meaning1653 (q : Snake 81) : literal (valuation q) 1653 = decide (7 ≤ count1647 q) := rfl
theorem meaning1656 (q : Snake 81) : literal (valuation q) 1656 = decide (2 ≤ count1655 q) := rfl
theorem meaning1657 (q : Snake 81) : literal (valuation q) 1657 = decide (3 ≤ count1655 q) := rfl
theorem meaning1658 (q : Snake 81) : literal (valuation q) 1658 = decide (4 ≤ count1655 q) := rfl
theorem meaning1659 (q : Snake 81) : literal (valuation q) 1659 = decide (5 ≤ count1655 q) := rfl
theorem meaning1660 (q : Snake 81) : literal (valuation q) 1660 = decide (6 ≤ count1655 q) := rfl
theorem meaning1661 (q : Snake 81) : literal (valuation q) 1661 = decide (7 ≤ count1655 q) := rfl
theorem meaning1662 (q : Snake 81) : literal (valuation q) 1662 = decide (8 ≤ count1655 q) := rfl
theorem meaning1663 (q : Snake 81) : literal (valuation q) 1663 = decide (9 ≤ count1655 q) := rfl
theorem meaning1664 (q : Snake 81) : literal (valuation q) 1664 = decide (10 ≤ count1655 q) := rfl
theorem meaning1671 (q : Snake 81) : literal (valuation q) 1671 = decide (1 ≤ count1671 q) := rfl
theorem meaning1672 (q : Snake 81) : literal (valuation q) 1672 = decide (2 ≤ count1671 q) := rfl
theorem meaning1673 (q : Snake 81) : literal (valuation q) 1673 = decide (1 ≤ count1673 q) := rfl
theorem meaning1674 (q : Snake 81) : literal (valuation q) 1674 = decide (2 ≤ count1673 q) := rfl
theorem meaning1675 (q : Snake 81) : literal (valuation q) 1675 = decide (1 ≤ count1675 q) := rfl
theorem meaning1676 (q : Snake 81) : literal (valuation q) 1676 = decide (2 ≤ count1675 q) := rfl
theorem meaning1677 (q : Snake 81) : literal (valuation q) 1677 = decide (3 ≤ count1675 q) := rfl
theorem meaning1678 (q : Snake 81) : literal (valuation q) 1678 = decide (4 ≤ count1675 q) := rfl
theorem meaning1679 (q : Snake 81) : literal (valuation q) 1679 = decide (1 ≤ count1679 q) := rfl
theorem meaning1680 (q : Snake 81) : literal (valuation q) 1680 = decide (2 ≤ count1679 q) := rfl
theorem meaning1681 (q : Snake 81) : literal (valuation q) 1681 = decide (1 ≤ count1681 q) := rfl
theorem meaning1682 (q : Snake 81) : literal (valuation q) 1682 = decide (2 ≤ count1681 q) := rfl
theorem meaning1683 (q : Snake 81) : literal (valuation q) 1683 = decide (1 ≤ count1683 q) := rfl
theorem meaning1684 (q : Snake 81) : literal (valuation q) 1684 = decide (2 ≤ count1683 q) := rfl
theorem meaning1685 (q : Snake 81) : literal (valuation q) 1685 = decide (3 ≤ count1683 q) := rfl
theorem meaning1686 (q : Snake 81) : literal (valuation q) 1686 = decide (4 ≤ count1683 q) := rfl
theorem meaning1687 (q : Snake 81) : literal (valuation q) 1687 = decide (1 ≤ count1687 q) := rfl
theorem meaning1688 (q : Snake 81) : literal (valuation q) 1688 = decide (2 ≤ count1687 q) := rfl
theorem meaning1689 (q : Snake 81) : literal (valuation q) 1689 = decide (3 ≤ count1687 q) := rfl
theorem meaning1690 (q : Snake 81) : literal (valuation q) 1690 = decide (4 ≤ count1687 q) := rfl
theorem meaning1691 (q : Snake 81) : literal (valuation q) 1691 = decide (5 ≤ count1687 q) := rfl
theorem meaning1692 (q : Snake 81) : literal (valuation q) 1692 = decide (6 ≤ count1687 q) := rfl
theorem meaning1693 (q : Snake 81) : literal (valuation q) 1693 = decide (7 ≤ count1687 q) := rfl
theorem meaning1695 (q : Snake 81) : literal (valuation q) 1695 = decide (1 ≤ count1695 q) := rfl
theorem meaning1696 (q : Snake 81) : literal (valuation q) 1696 = decide (2 ≤ count1695 q) := rfl
theorem meaning1697 (q : Snake 81) : literal (valuation q) 1697 = decide (1 ≤ count1697 q) := rfl
theorem meaning1698 (q : Snake 81) : literal (valuation q) 1698 = decide (2 ≤ count1697 q) := rfl
theorem meaning1699 (q : Snake 81) : literal (valuation q) 1699 = decide (1 ≤ count1699 q) := rfl
theorem meaning1700 (q : Snake 81) : literal (valuation q) 1700 = decide (2 ≤ count1699 q) := rfl
theorem meaning1701 (q : Snake 81) : literal (valuation q) 1701 = decide (3 ≤ count1699 q) := rfl
theorem meaning1702 (q : Snake 81) : literal (valuation q) 1702 = decide (4 ≤ count1699 q) := rfl
theorem meaning1703 (q : Snake 81) : literal (valuation q) 1703 = decide (1 ≤ count1703 q) := rfl
theorem meaning1704 (q : Snake 81) : literal (valuation q) 1704 = decide (2 ≤ count1703 q) := rfl
theorem meaning1705 (q : Snake 81) : literal (valuation q) 1705 = decide (1 ≤ count1705 q) := rfl
theorem meaning1706 (q : Snake 81) : literal (valuation q) 1706 = decide (2 ≤ count1705 q) := rfl
theorem meaning1707 (q : Snake 81) : literal (valuation q) 1707 = decide (1 ≤ count1707 q) := rfl
theorem meaning1708 (q : Snake 81) : literal (valuation q) 1708 = decide (2 ≤ count1707 q) := rfl
theorem meaning1709 (q : Snake 81) : literal (valuation q) 1709 = decide (3 ≤ count1707 q) := rfl
theorem meaning1710 (q : Snake 81) : literal (valuation q) 1710 = decide (4 ≤ count1707 q) := rfl
theorem meaning1711 (q : Snake 81) : literal (valuation q) 1711 = decide (1 ≤ count1711 q) := rfl
theorem meaning1712 (q : Snake 81) : literal (valuation q) 1712 = decide (2 ≤ count1711 q) := rfl
theorem meaning1713 (q : Snake 81) : literal (valuation q) 1713 = decide (3 ≤ count1711 q) := rfl
theorem meaning1714 (q : Snake 81) : literal (valuation q) 1714 = decide (4 ≤ count1711 q) := rfl
theorem meaning1715 (q : Snake 81) : literal (valuation q) 1715 = decide (5 ≤ count1711 q) := rfl
theorem meaning1716 (q : Snake 81) : literal (valuation q) 1716 = decide (6 ≤ count1711 q) := rfl
theorem meaning1721 (q : Snake 81) : literal (valuation q) 1721 = decide (3 ≤ count1719 q) := rfl
theorem meaning1722 (q : Snake 81) : literal (valuation q) 1722 = decide (4 ≤ count1719 q) := rfl
theorem meaning1723 (q : Snake 81) : literal (valuation q) 1723 = decide (5 ≤ count1719 q) := rfl
theorem meaning1724 (q : Snake 81) : literal (valuation q) 1724 = decide (6 ≤ count1719 q) := rfl
theorem meaning1725 (q : Snake 81) : literal (valuation q) 1725 = decide (7 ≤ count1719 q) := rfl
theorem meaning1726 (q : Snake 81) : literal (valuation q) 1726 = decide (8 ≤ count1719 q) := rfl
theorem meaning1727 (q : Snake 81) : literal (valuation q) 1727 = decide (9 ≤ count1719 q) := rfl
theorem meaning1728 (q : Snake 81) : literal (valuation q) 1728 = decide (10 ≤ count1719 q) := rfl
theorem meaning1743 (q : Snake 81) : literal (valuation q) 1743 = decide (9 ≤ count1735 q) := rfl
theorem meaning1744 (q : Snake 81) : literal (valuation q) 1744 = decide (10 ≤ count1735 q) := rfl
theorem meaning1745 (q : Snake 81) : literal (valuation q) 1745 = decide (11 ≤ count1735 q) := rfl
theorem meaning1746 (q : Snake 81) : literal (valuation q) 1746 = decide (12 ≤ count1735 q) := rfl
theorem meaning1747 (q : Snake 81) : literal (valuation q) 1747 = decide (13 ≤ count1735 q) := rfl
theorem meaning1748 (q : Snake 81) : literal (valuation q) 1748 = decide (14 ≤ count1735 q) := rfl
theorem meaning1749 (q : Snake 81) : literal (valuation q) 1749 = decide (15 ≤ count1735 q) := rfl
theorem meaning1750 (q : Snake 81) : literal (valuation q) 1750 = decide (16 ≤ count1735 q) := rfl
theorem meaning1780 (q : Snake 81) : literal (valuation q) 1780 = decide (23 ≤ count1758 q) := rfl
structure Conditions (q : Snake 81) : Prop where
  head_fixed : q.vertex 0 = head
  covered : ∀ v, InPath q v → v ∈ region

theorem absent_odd_bound (q : Snake 81) (h : Conditions q) :
    (oddSide.filter (fun v => !(decide (InPath q v)))).length ≤ 22 := by
  have hb := absent_bound q oddSide (fun v hv hp => odd_mem v (h.covered v hv) hp)
  rw [oddSide_length] at hb
  exact hb

theorem other_count_bound (q : Snake 81) (h : Conditions q) :
    (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length ≤ 1 := by
  apply endpoint_count q others others_nodup
  rw [h.head_fixed]
  exact head_not_others

end
end Snake9.Regrowth.First112
