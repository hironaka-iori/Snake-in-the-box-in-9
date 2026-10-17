import E112075Data
namespace Snake9.Regrowth.E112075
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 105 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 4 then decide (InPath q (6 : Vertex)) else (if i < 5 then decide (InPath q (7 : Vertex)) else decide (InPath q (8 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (10 : Vertex)) else (if i < 8 then decide (InPath q (15 : Vertex)) else decide (InPath q (20 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (21 : Vertex)) else decide (InPath q (22 : Vertex))) else (if i < 12 then decide (InPath q (25 : Vertex)) else decide (InPath q (26 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (27 : Vertex)) else (if i < 15 then decide (InPath q (29 : Vertex)) else decide (InPath q (96 : Vertex)))) else (if i < 17 then decide (InPath q (97 : Vertex)) else (if i < 18 then decide (InPath q (102 : Vertex)) else decide (InPath q (103 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (104 : Vertex)) else (if i < 21 then decide (InPath q (106 : Vertex)) else decide (InPath q (110 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (111 : Vertex)) else decide (InPath q (116 : Vertex))) else (if i < 25 then decide (InPath q (117 : Vertex)) else decide (InPath q (118 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (121 : Vertex)) else (if i < 28 then decide (InPath q (122 : Vertex)) else decide (InPath q (123 : Vertex)))) else (if i < 30 then decide (InPath q (125 : Vertex)) else (if i < 31 then decide (InPath q (129 : Vertex)) else decide (InPath q (133 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (137 : Vertex)) else (if i < 34 then decide (InPath q (139 : Vertex)) else decide (InPath q (143 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (161 : Vertex)) else decide (InPath q (168 : Vertex))) else (if i < 38 then decide (InPath q (170 : Vertex)) else decide (InPath q (174 : Vertex)))))) else (if i < 45 then (if i < 42 then (if i < 40 then decide (InPath q (175 : Vertex)) else (if i < 41 then decide (InPath q (177 : Vertex)) else decide (InPath q (185 : Vertex)))) else (if i < 43 then decide (InPath q (186 : Vertex)) else (if i < 44 then decide (InPath q (187 : Vertex)) else decide (InPath q (189 : Vertex))))) else (if i < 48 then (if i < 46 then decide (InPath q (192 : Vertex)) else (if i < 47 then decide (InPath q (193 : Vertex)) else decide (InPath q (198 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (199 : Vertex)) else decide (InPath q (200 : Vertex))) else (if i < 51 then decide (InPath q (202 : Vertex)) else decide (InPath q (206 : Vertex)))))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then decide (InPath q (207 : Vertex)) else (if i < 54 then decide (InPath q (212 : Vertex)) else decide (InPath q (213 : Vertex)))) else (if i < 56 then decide (InPath q (214 : Vertex)) else (if i < 57 then decide (InPath q (217 : Vertex)) else decide (InPath q (218 : Vertex))))) else (if i < 61 then (if i < 59 then decide (InPath q (219 : Vertex)) else (if i < 60 then decide (InPath q (221 : Vertex)) else decide (InPath q (321 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (352 : Vertex)) else decide (InPath q (353 : Vertex))) else (if i < 64 then decide (InPath q (355 : Vertex)) else decide (InPath q (357 : Vertex)))))) else (if i < 71 then (if i < 68 then (if i < 66 then decide (InPath q (359 : Vertex)) else (if i < 67 then decide (InPath q (361 : Vertex)) else decide (InPath q (363 : Vertex)))) else (if i < 69 then decide (InPath q (367 : Vertex)) else (if i < 70 then decide (InPath q (368 : Vertex)) else decide (InPath q (370 : Vertex))))) else (if i < 74 then (if i < 72 then decide (InPath q (371 : Vertex)) else (if i < 73 then decide (InPath q (416 : Vertex)) else decide (InPath q (417 : Vertex)))) else (if i < 76 then (if i < 75 then decide (InPath q (419 : Vertex)) else decide (InPath q (421 : Vertex))) else (if i < 77 then decide (InPath q (423 : Vertex)) else decide (InPath q (425 : Vertex))))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then decide (InPath q (427 : Vertex)) else (if i < 80 then decide (InPath q (429 : Vertex)) else decide (InPath q (430 : Vertex)))) else (if i < 82 then decide (InPath q (431 : Vertex)) else (if i < 83 then decide (InPath q (432 : Vertex)) else decide (InPath q (434 : Vertex))))) else (if i < 87 then (if i < 85 then decide (InPath q (435 : Vertex)) else (if i < 86 then decide (InPath q (440 : Vertex)) else decide (InPath q (442 : Vertex)))) else (if i < 89 then (if i < 88 then decide (InPath q (444 : Vertex)) else decide (InPath q (445 : Vertex))) else (if i < 90 then decide (InPath q (446 : Vertex)) else decide (InPath q (480 : Vertex)))))) else (if i < 98 then (if i < 94 then (if i < 92 then decide (InPath q (481 : Vertex)) else (if i < 93 then decide (InPath q (486 : Vertex)) else decide (InPath q (487 : Vertex)))) else (if i < 96 then (if i < 95 then decide (InPath q (488 : Vertex)) else decide (InPath q (490 : Vertex))) else (if i < 97 then decide (InPath q (494 : Vertex)) else decide (InPath q (495 : Vertex))))) else (if i < 101 then (if i < 99 then decide (InPath q (497 : Vertex)) else (if i < 100 then decide (InPath q (500 : Vertex)) else decide (InPath q (501 : Vertex)))) else (if i < 103 then (if i < 102 then decide (InPath q (502 : Vertex)) else decide (InPath q (505 : Vertex))) else (if i < 104 then decide (InPath q (506 : Vertex)) else decide (InPath q (507 : Vertex))))))))) else (if i < 158 then (if i < 131 then (if i < 118 then (if i < 111 then (if i < 108 then (if i < 106 then decide (InPath q (509 : Vertex)) else (if i < 107 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 109 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else (if i < 110 then decide (BallClauseLogic.Endpoint q (7 : Vertex)) else decide (BallClauseLogic.Endpoint q (8 : Vertex))))) else (if i < 114 then (if i < 112 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else (if i < 113 then decide (BallClauseLogic.Endpoint q (15 : Vertex)) else decide (BallClauseLogic.Endpoint q (20 : Vertex)))) else (if i < 116 then (if i < 115 then decide (BallClauseLogic.Endpoint q (21 : Vertex)) else decide (BallClauseLogic.Endpoint q (22 : Vertex))) else (if i < 117 then decide (BallClauseLogic.Endpoint q (25 : Vertex)) else decide (BallClauseLogic.Endpoint q (26 : Vertex)))))) else (if i < 124 then (if i < 121 then (if i < 119 then decide (BallClauseLogic.Endpoint q (27 : Vertex)) else (if i < 120 then decide (BallClauseLogic.Endpoint q (29 : Vertex)) else decide (BallClauseLogic.Endpoint q (96 : Vertex)))) else (if i < 122 then decide (BallClauseLogic.Endpoint q (97 : Vertex)) else (if i < 123 then decide (BallClauseLogic.Endpoint q (102 : Vertex)) else decide (BallClauseLogic.Endpoint q (103 : Vertex))))) else (if i < 127 then (if i < 125 then decide (BallClauseLogic.Endpoint q (104 : Vertex)) else (if i < 126 then decide (BallClauseLogic.Endpoint q (106 : Vertex)) else decide (BallClauseLogic.Endpoint q (110 : Vertex)))) else (if i < 129 then (if i < 128 then decide (BallClauseLogic.Endpoint q (111 : Vertex)) else decide (BallClauseLogic.Endpoint q (116 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (117 : Vertex)) else decide (BallClauseLogic.Endpoint q (118 : Vertex))))))) else (if i < 144 then (if i < 137 then (if i < 134 then (if i < 132 then decide (BallClauseLogic.Endpoint q (121 : Vertex)) else (if i < 133 then decide (BallClauseLogic.Endpoint q (122 : Vertex)) else decide (BallClauseLogic.Endpoint q (123 : Vertex)))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (125 : Vertex)) else (if i < 136 then decide (BallClauseLogic.Endpoint q (129 : Vertex)) else decide (BallClauseLogic.Endpoint q (133 : Vertex))))) else (if i < 140 then (if i < 138 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else (if i < 139 then decide (BallClauseLogic.Endpoint q (139 : Vertex)) else decide (BallClauseLogic.Endpoint q (143 : Vertex)))) else (if i < 142 then (if i < 141 then decide (BallClauseLogic.Endpoint q (161 : Vertex)) else decide (BallClauseLogic.Endpoint q (168 : Vertex))) else (if i < 143 then decide (BallClauseLogic.Endpoint q (170 : Vertex)) else decide (BallClauseLogic.Endpoint q (174 : Vertex)))))) else (if i < 151 then (if i < 147 then (if i < 145 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else (if i < 146 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else decide (BallClauseLogic.Endpoint q (185 : Vertex)))) else (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (187 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (192 : Vertex))))) else (if i < 154 then (if i < 152 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else (if i < 153 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else decide (BallClauseLogic.Endpoint q (199 : Vertex)))) else (if i < 156 then (if i < 155 then decide (BallClauseLogic.Endpoint q (200 : Vertex)) else decide (BallClauseLogic.Endpoint q (202 : Vertex))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (206 : Vertex)) else decide (BallClauseLogic.Endpoint q (207 : Vertex)))))))) else (if i < 184 then (if i < 171 then (if i < 164 then (if i < 161 then (if i < 159 then decide (BallClauseLogic.Endpoint q (212 : Vertex)) else (if i < 160 then decide (BallClauseLogic.Endpoint q (213 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex)))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (217 : Vertex)) else (if i < 163 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (219 : Vertex))))) else (if i < 167 then (if i < 165 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else (if i < 166 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (352 : Vertex)))) else (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (353 : Vertex)) else decide (BallClauseLogic.Endpoint q (355 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else decide (BallClauseLogic.Endpoint q (359 : Vertex)))))) else (if i < 177 then (if i < 174 then (if i < 172 then decide (BallClauseLogic.Endpoint q (361 : Vertex)) else (if i < 173 then decide (BallClauseLogic.Endpoint q (363 : Vertex)) else decide (BallClauseLogic.Endpoint q (367 : Vertex)))) else (if i < 175 then decide (BallClauseLogic.Endpoint q (368 : Vertex)) else (if i < 176 then decide (BallClauseLogic.Endpoint q (370 : Vertex)) else decide (BallClauseLogic.Endpoint q (371 : Vertex))))) else (if i < 180 then (if i < 178 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else (if i < 179 then decide (BallClauseLogic.Endpoint q (417 : Vertex)) else decide (BallClauseLogic.Endpoint q (419 : Vertex)))) else (if i < 182 then (if i < 181 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (423 : Vertex))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))))))) else (if i < 197 then (if i < 190 then (if i < 187 then (if i < 185 then decide (BallClauseLogic.Endpoint q (429 : Vertex)) else (if i < 186 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (431 : Vertex)))) else (if i < 188 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else (if i < 189 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else decide (BallClauseLogic.Endpoint q (435 : Vertex))))) else (if i < 193 then (if i < 191 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else (if i < 192 then decide (BallClauseLogic.Endpoint q (442 : Vertex)) else decide (BallClauseLogic.Endpoint q (444 : Vertex)))) else (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (445 : Vertex)) else decide (BallClauseLogic.Endpoint q (446 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))))) else (if i < 204 then (if i < 200 then (if i < 198 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else (if i < 199 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))) else (if i < 202 then (if i < 201 then decide (BallClauseLogic.Endpoint q (490 : Vertex)) else decide (BallClauseLogic.Endpoint q (494 : Vertex))) else (if i < 203 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 207 then (if i < 205 then decide (BallClauseLogic.Endpoint q (500 : Vertex)) else (if i < 206 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 209 then (if i < 208 then decide (BallClauseLogic.Endpoint q (505 : Vertex)) else decide (BallClauseLogic.Endpoint q (506 : Vertex))) else (if i < 210 then decide (BallClauseLogic.Endpoint q (507 : Vertex)) else decide (BallClauseLogic.Endpoint q (509 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count211 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count213 (b : Nat → Bool) : Nat := countLit b [106, 107, 108]
def count215 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count217 (b : Nat → Bool) : Nat := countLit b [109, 110, 111]
def count219 (b : Nat → Bool) : Nat := countLit b [106, 107, 108, 109, 110, 111]
def count221 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count223 (b : Nat → Bool) : Nat := countLit b [112, 113, 114]
def count225 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count227 (b : Nat → Bool) : Nat := countLit b [117, 118]
def count229 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118]
def count231 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117, 118]
def count233 (b : Nat → Bool) : Nat := countLit b [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]
def count235 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count237 (b : Nat → Bool) : Nat := countLit b [119, 120, 121]
def count239 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count241 (b : Nat → Bool) : Nat := countLit b [122, 123, 124]
def count243 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122, 123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count247 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131]
def count255 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count267 (b : Nat → Bool) : Nat := countLit b [135, 136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]
def count285 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count291 (b : Nat → Bool) : Nat := countLit b [148, 149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152, 153]
def count299 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count303 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157]
def count305 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154, 155, 156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]
def count311 (b : Nat → Bool) : Nat := countLit b [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]
def count313 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count315 (b : Nat → Bool) : Nat := countLit b [158, 159, 160]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [161, 162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161, 162, 163]
def count323 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [164, 165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167, 168, 169, 170]
def count335 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]
def count337 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [171, 172, 173]
def count341 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count343 (b : Nat → Bool) : Nat := countLit b [175, 176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count349 (b : Nat → Bool) : Nat := countLit b [178, 179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count355 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184]
def count357 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]
def count363 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [185, 186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188, 189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192, 193]
def count377 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count379 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count381 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197]
def count383 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count389 (b : Nat → Bool) : Nat := countLit b [198, 199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202, 203]
def count395 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203]
def count397 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count399 (b : Nat → Bool) : Nat := countLit b [204, 205, 206]
def count401 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count403 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count405 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210]
def count407 (b : Nat → Bool) : Nat := countLit b [204, 205, 206, 207, 208, 209, 210]
def count409 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]
def count411 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]
def count413 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]
def count415 (b : Nat → Bool) : Nat := countLit b [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]
def count417 (b : Nat → Bool) : Nat := countLit b [3, 6]
def count419 (b : Nat → Bool) : Nat := countLit b [1, 3, 6]
def count422 (b : Nat → Bool) : Nat := countLit b [8, 13]
def count424 (b : Nat → Bool) : Nat := countLit b [7, 8, 13]
def count427 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 7, 8, 13]
def count433 (b : Nat → Bool) : Nat := countLit b [15, 17]
def count435 (b : Nat → Bool) : Nat := countLit b [14, 15, 17]
def count438 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count440 (b : Nat → Bool) : Nat := countLit b [20, 22, 23]
def count443 (b : Nat → Bool) : Nat := countLit b [14, 15, 17, 20, 22, 23]
def count449 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 7, 8, 13, 14, 15, 17, 20, 22, 23]
def count461 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count463 (b : Nat → Bool) : Nat := countLit b [28, 29, 30]
def count466 (b : Nat → Bool) : Nat := countLit b [37, 39]
def count468 (b : Nat → Bool) : Nat := countLit b [33, 37, 39]
def count471 (b : Nat → Bool) : Nat := countLit b [28, 29, 30, 33, 37, 39]
def count477 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count479 (b : Nat → Bool) : Nat := countLit b [40, 43, 44]
def count482 (b : Nat → Bool) : Nat := countLit b [45, 47]
def count484 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count486 (b : Nat → Bool) : Nat := countLit b [45, 47, 50, 52]
def count490 (b : Nat → Bool) : Nat := countLit b [40, 43, 44, 45, 47, 50, 52]
def count497 (b : Nat → Bool) : Nat := countLit b [28, 29, 30, 33, 37, 39, 40, 43, 44, 45, 47, 50, 52]
def count510 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 7, 8, 13, 14, 15, 17, 20, 22, 23, 28, 29, 30, 33, 37, 39, 40, 43, 44, 45, 47, 50, 52]
def count535 (b : Nat → Bool) : Nat := countLit b [58, 59]
def count537 (b : Nat → Bool) : Nat := countLit b [53, 58, 59]
def count540 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count542 (b : Nat → Bool) : Nat := countLit b [62, 65, 67]
def count545 (b : Nat → Bool) : Nat := countLit b [53, 58, 59, 62, 65, 67]
def count551 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count553 (b : Nat → Bool) : Nat := countLit b [69, 71, 73]
def count556 (b : Nat → Bool) : Nat := countLit b [78, 79]
def count558 (b : Nat → Bool) : Nat := countLit b [76, 78, 79]
def count561 (b : Nat → Bool) : Nat := countLit b [69, 71, 73, 76, 78, 79]
def count567 (b : Nat → Bool) : Nat := countLit b [53, 58, 59, 62, 65, 67, 69, 71, 73, 76, 78, 79]
def count579 (b : Nat → Bool) : Nat := countLit b [82, 84]
def count581 (b : Nat → Bool) : Nat := countLit b [80, 82, 84]
def count584 (b : Nat → Bool) : Nat := countLit b [87, 90]
def count586 (b : Nat → Bool) : Nat := countLit b [86, 87, 90]
def count589 (b : Nat → Bool) : Nat := countLit b [80, 82, 84, 86, 87, 90]
def count595 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count597 (b : Nat → Bool) : Nat := countLit b [92, 95, 97]
def count600 (b : Nat → Bool) : Nat := countLit b [98, 99]
def count602 (b : Nat → Bool) : Nat := countLit b [104, 105]
def count604 (b : Nat → Bool) : Nat := countLit b [98, 99, 104, 105]
def count608 (b : Nat → Bool) : Nat := countLit b [92, 95, 97, 98, 99, 104, 105]
def count615 (b : Nat → Bool) : Nat := countLit b [80, 82, 84, 86, 87, 90, 92, 95, 97, 98, 99, 104, 105]
def count628 (b : Nat → Bool) : Nat := countLit b [53, 58, 59, 62, 65, 67, 69, 71, 73, 76, 78, 79, 80, 82, 84, 86, 87, 90, 92, 95, 97, 98, 99, 104, 105]
def count653 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 7, 8, 13, 14, 15, 17, 20, 22, 23, 28, 29, 30, 33, 37, 39, 40, 43, 44, 45, 47, 50, 52, 53, 58, 59, 62, 65, 67, 69, 71, 73, 76, 78, 79, 80, 82, 84, 86, 87, 90, 92, 95, 97, 98, 99, 104, 105]
def count695 (b : Nat → Bool) : Nat := countLit b [-3, -6]
def count697 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6]
def count700 (b : Nat → Bool) : Nat := countLit b [-8, -13]
def count702 (b : Nat → Bool) : Nat := countLit b [-7, -8, -13]
def count705 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -7, -8, -13]
def count711 (b : Nat → Bool) : Nat := countLit b [-15, -17]
def count713 (b : Nat → Bool) : Nat := countLit b [-14, -15, -17]
def count716 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count718 (b : Nat → Bool) : Nat := countLit b [-20, -22, -23]
def count721 (b : Nat → Bool) : Nat := countLit b [-14, -15, -17, -20, -22, -23]
def count727 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]
def count737 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count739 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30]
def count742 (b : Nat → Bool) : Nat := countLit b [-37, -39]
def count744 (b : Nat → Bool) : Nat := countLit b [-33, -37, -39]
def count747 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30, -33, -37, -39]
def count753 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count755 (b : Nat → Bool) : Nat := countLit b [-40, -43, -44]
def count758 (b : Nat → Bool) : Nat := countLit b [-45, -47]
def count760 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count762 (b : Nat → Bool) : Nat := countLit b [-45, -47, -50, -52]
def count766 (b : Nat → Bool) : Nat := countLit b [-40, -43, -44, -45, -47, -50, -52]
def count773 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]
def count783 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]
def count793 (b : Nat → Bool) : Nat := countLit b [-58, -59]
def count795 (b : Nat → Bool) : Nat := countLit b [-53, -58, -59]
def count798 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count800 (b : Nat → Bool) : Nat := countLit b [-62, -65, -67]
def count803 (b : Nat → Bool) : Nat := countLit b [-53, -58, -59, -62, -65, -67]
def count809 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count811 (b : Nat → Bool) : Nat := countLit b [-69, -71, -73]
def count814 (b : Nat → Bool) : Nat := countLit b [-78, -79]
def count816 (b : Nat → Bool) : Nat := countLit b [-76, -78, -79]
def count819 (b : Nat → Bool) : Nat := countLit b [-69, -71, -73, -76, -78, -79]
def count825 (b : Nat → Bool) : Nat := countLit b [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79]
def count835 (b : Nat → Bool) : Nat := countLit b [-82, -84]
def count837 (b : Nat → Bool) : Nat := countLit b [-80, -82, -84]
def count840 (b : Nat → Bool) : Nat := countLit b [-87, -90]
def count842 (b : Nat → Bool) : Nat := countLit b [-86, -87, -90]
def count845 (b : Nat → Bool) : Nat := countLit b [-80, -82, -84, -86, -87, -90]
def count851 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count853 (b : Nat → Bool) : Nat := countLit b [-92, -95, -97]
def count856 (b : Nat → Bool) : Nat := countLit b [-98, -99]
def count858 (b : Nat → Bool) : Nat := countLit b [-104, -105]
def count860 (b : Nat → Bool) : Nat := countLit b [-98, -99, -104, -105]
def count864 (b : Nat → Bool) : Nat := countLit b [-92, -95, -97, -98, -99, -104, -105]
def count871 (b : Nat → Bool) : Nat := countLit b [-80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]
def count881 (b : Nat → Bool) : Nat := countLit b [-53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]
def count891 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23, -28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52, -53, -58, -59, -62, -65, -67, -69, -71, -73, -76, -78, -79, -80, -82, -84, -86, -87, -90, -92, -95, -97, -98, -99, -104, -105]
def count901 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count903 (b : Nat → Bool) : Nat := countLit b [2, 4, 5]
def count906 (b : Nat → Bool) : Nat := countLit b [10, 11]
def count908 (b : Nat → Bool) : Nat := countLit b [9, 10, 11]
def count911 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 9, 10, 11]
def count917 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count919 (b : Nat → Bool) : Nat := countLit b [12, 16, 18]
def count922 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count924 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count926 (b : Nat → Bool) : Nat := countLit b [19, 21, 24, 25]
def count930 (b : Nat → Bool) : Nat := countLit b [12, 16, 18, 19, 21, 24, 25]
def count937 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 9, 10, 11, 12, 16, 18, 19, 21, 24, 25]
def count950 (b : Nat → Bool) : Nat := countLit b [27, 31]
def count952 (b : Nat → Bool) : Nat := countLit b [26, 27, 31]
def count955 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count957 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count959 (b : Nat → Bool) : Nat := countLit b [32, 34, 35, 36]
def count963 (b : Nat → Bool) : Nat := countLit b [26, 27, 31, 32, 34, 35, 36]
def count970 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count972 (b : Nat → Bool) : Nat := countLit b [38, 41, 42]
def count975 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count977 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count979 (b : Nat → Bool) : Nat := countLit b [46, 48, 49, 51]
def count983 (b : Nat → Bool) : Nat := countLit b [38, 41, 42, 46, 48, 49, 51]
def count990 (b : Nat → Bool) : Nat := countLit b [26, 27, 31, 32, 34, 35, 36, 38, 41, 42, 46, 48, 49, 51]
def count1004 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 9, 10, 11, 12, 16, 18, 19, 21, 24, 25, 26, 27, 31, 32, 34, 35, 36, 38, 41, 42, 46, 48, 49, 51]
def count1031 (b : Nat → Bool) : Nat := countLit b [55, 56]
def count1033 (b : Nat → Bool) : Nat := countLit b [54, 55, 56]
def count1036 (b : Nat → Bool) : Nat := countLit b [57, 60]
def count1038 (b : Nat → Bool) : Nat := countLit b [61, 63]
def count1040 (b : Nat → Bool) : Nat := countLit b [57, 60, 61, 63]
def count1044 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 57, 60, 61, 63]
def count1051 (b : Nat → Bool) : Nat := countLit b [66, 68]
def count1053 (b : Nat → Bool) : Nat := countLit b [64, 66, 68]
def count1056 (b : Nat → Bool) : Nat := countLit b [70, 72]
def count1058 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count1060 (b : Nat → Bool) : Nat := countLit b [70, 72, 74, 75]
def count1064 (b : Nat → Bool) : Nat := countLit b [64, 66, 68, 70, 72, 74, 75]
def count1071 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 57, 60, 61, 63, 64, 66, 68, 70, 72, 74, 75]
def count1085 (b : Nat → Bool) : Nat := countLit b [81, 83]
def count1087 (b : Nat → Bool) : Nat := countLit b [77, 81, 83]
def count1090 (b : Nat → Bool) : Nat := countLit b [85, 88]
def count1092 (b : Nat → Bool) : Nat := countLit b [89, 91]
def count1094 (b : Nat → Bool) : Nat := countLit b [85, 88, 89, 91]
def count1098 (b : Nat → Bool) : Nat := countLit b [77, 81, 83, 85, 88, 89, 91]
def count1105 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count1107 (b : Nat → Bool) : Nat := countLit b [93, 94, 96]
def count1110 (b : Nat → Bool) : Nat := countLit b [100, 101]
def count1112 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count1114 (b : Nat → Bool) : Nat := countLit b [100, 101, 102, 103]
def count1118 (b : Nat → Bool) : Nat := countLit b [93, 94, 96, 100, 101, 102, 103]
def count1125 (b : Nat → Bool) : Nat := countLit b [77, 81, 83, 85, 88, 89, 91, 93, 94, 96, 100, 101, 102, 103]
def count1139 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 57, 60, 61, 63, 64, 66, 68, 70, 72, 74, 75, 77, 81, 83, 85, 88, 89, 91, 93, 94, 96, 100, 101, 102, 103]
def count1167 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 9, 10, 11, 12, 16, 18, 19, 21, 24, 25, 26, 27, 31, 32, 34, 35, 36, 38, 41, 42, 46, 48, 49, 51, 54, 55, 56, 57, 60, 61, 63, 64, 66, 68, 70, 72, 74, 75, 77, 81, 83, 85, 88, 89, 91, 93, 94, 96, 100, 101, 102, 103]
def count1209 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1211 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5]
def count1214 (b : Nat → Bool) : Nat := countLit b [-10, -11]
def count1216 (b : Nat → Bool) : Nat := countLit b [-9, -10, -11]
def count1219 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -9, -10, -11]
def count1225 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1227 (b : Nat → Bool) : Nat := countLit b [-12, -16, -18]
def count1230 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count1232 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count1234 (b : Nat → Bool) : Nat := countLit b [-19, -21, -24, -25]
def count1238 (b : Nat → Bool) : Nat := countLit b [-12, -16, -18, -19, -21, -24, -25]
def count1245 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -9, -10, -11, -12, -16, -18, -19, -21, -24, -25]
def count1258 (b : Nat → Bool) : Nat := countLit b [-27, -31]
def count1260 (b : Nat → Bool) : Nat := countLit b [-26, -27, -31]
def count1263 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count1265 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count1267 (b : Nat → Bool) : Nat := countLit b [-32, -34, -35, -36]
def count1271 (b : Nat → Bool) : Nat := countLit b [-26, -27, -31, -32, -34, -35, -36]
def count1278 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count1280 (b : Nat → Bool) : Nat := countLit b [-38, -41, -42]
def count1283 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count1285 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count1287 (b : Nat → Bool) : Nat := countLit b [-46, -48, -49, -51]
def count1291 (b : Nat → Bool) : Nat := countLit b [-38, -41, -42, -46, -48, -49, -51]
def count1298 (b : Nat → Bool) : Nat := countLit b [-26, -27, -31, -32, -34, -35, -36, -38, -41, -42, -46, -48, -49, -51]
def count1312 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -9, -10, -11, -12, -16, -18, -19, -21, -24, -25, -26, -27, -31, -32, -34, -35, -36, -38, -41, -42, -46, -48, -49, -51]
def count1327 (b : Nat → Bool) : Nat := countLit b [-55, -56]
def count1329 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56]
def count1332 (b : Nat → Bool) : Nat := countLit b [-57, -60]
def count1334 (b : Nat → Bool) : Nat := countLit b [-61, -63]
def count1336 (b : Nat → Bool) : Nat := countLit b [-57, -60, -61, -63]
def count1340 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -57, -60, -61, -63]
def count1347 (b : Nat → Bool) : Nat := countLit b [-66, -68]
def count1349 (b : Nat → Bool) : Nat := countLit b [-64, -66, -68]
def count1352 (b : Nat → Bool) : Nat := countLit b [-70, -72]
def count1354 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count1356 (b : Nat → Bool) : Nat := countLit b [-70, -72, -74, -75]
def count1360 (b : Nat → Bool) : Nat := countLit b [-64, -66, -68, -70, -72, -74, -75]
def count1367 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -57, -60, -61, -63, -64, -66, -68, -70, -72, -74, -75]
def count1381 (b : Nat → Bool) : Nat := countLit b [-81, -83]
def count1383 (b : Nat → Bool) : Nat := countLit b [-77, -81, -83]
def count1386 (b : Nat → Bool) : Nat := countLit b [-85, -88]
def count1388 (b : Nat → Bool) : Nat := countLit b [-89, -91]
def count1390 (b : Nat → Bool) : Nat := countLit b [-85, -88, -89, -91]
def count1394 (b : Nat → Bool) : Nat := countLit b [-77, -81, -83, -85, -88, -89, -91]
def count1401 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1403 (b : Nat → Bool) : Nat := countLit b [-93, -94, -96]
def count1406 (b : Nat → Bool) : Nat := countLit b [-100, -101]
def count1408 (b : Nat → Bool) : Nat := countLit b [-102, -103]
def count1410 (b : Nat → Bool) : Nat := countLit b [-100, -101, -102, -103]
def count1414 (b : Nat → Bool) : Nat := countLit b [-93, -94, -96, -100, -101, -102, -103]
def count1421 (b : Nat → Bool) : Nat := countLit b [-77, -81, -83, -85, -88, -89, -91, -93, -94, -96, -100, -101, -102, -103]
def count1435 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -57, -60, -61, -63, -64, -66, -68, -70, -72, -74, -75, -77, -81, -83, -85, -88, -89, -91, -93, -94, -96, -100, -101, -102, -103]
def count1450 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -9, -10, -11, -12, -16, -18, -19, -21, -24, -25, -26, -27, -31, -32, -34, -35, -36, -38, -41, -42, -46, -48, -49, -51, -54, -55, -56, -57, -60, -61, -63, -64, -66, -68, -70, -72, -74, -75, -77, -81, -83, -85, -88, -89, -91, -93, -94, -96, -100, -101, -102, -103]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 732 then (if i < 366 then (if i < 183 then (if i < 91 then (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 16 then (if i < 13 then (if i < 12 then b 11 else b 12) else (if i < 14 then b 13 else (if i < 15 then b 14 else b 15))) else (if i < 19 then (if i < 17 then b 16 else (if i < 18 then b 17 else b 18)) else (if i < 20 then b 19 else (if i < 21 then b 20 else b 21))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else (if i < 26 then b 25 else b 26))) else (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)))) else (if i < 39 then (if i < 36 then (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)) else (if i < 37 then b 36 else (if i < 38 then b 37 else b 38))) else (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)))))) else (if i < 68 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else (if i < 49 then b 48 else b 49))) else (if i < 53 then (if i < 51 then b 50 else (if i < 52 then b 51 else b 52)) else (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)))) else (if i < 62 then (if i < 59 then (if i < 57 then b 56 else (if i < 58 then b 57 else b 58)) else (if i < 60 then b 59 else (if i < 61 then b 60 else b 61))) else (if i < 65 then (if i < 63 then b 62 else (if i < 64 then b 63 else b 64)) else (if i < 66 then b 65 else (if i < 67 then b 66 else b 67))))) else (if i < 79 then (if i < 73 then (if i < 70 then (if i < 69 then b 68 else b 69) else (if i < 71 then b 70 else (if i < 72 then b 71 else b 72))) else (if i < 76 then (if i < 74 then b 73 else (if i < 75 then b 74 else b 75)) else (if i < 77 then b 76 else (if i < 78 then b 77 else b 78)))) else (if i < 85 then (if i < 82 then (if i < 80 then b 79 else (if i < 81 then b 80 else b 81)) else (if i < 83 then b 82 else (if i < 84 then b 83 else b 84))) else (if i < 88 then (if i < 86 then b 85 else (if i < 87 then b 86 else b 87)) else (if i < 89 then b 88 else (if i < 90 then b 89 else b 90))))))) else (if i < 137 then (if i < 114 then (if i < 102 then (if i < 96 then (if i < 93 then (if i < 92 then b 91 else b 92) else (if i < 94 then b 93 else (if i < 95 then b 94 else b 95))) else (if i < 99 then (if i < 97 then b 96 else (if i < 98 then b 97 else b 98)) else (if i < 100 then b 99 else (if i < 101 then b 100 else b 101)))) else (if i < 108 then (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 106 then b 105 else (if i < 107 then b 106 else b 107))) else (if i < 111 then (if i < 109 then b 108 else (if i < 110 then b 109 else b 110)) else (if i < 112 then b 111 else (if i < 113 then b 112 else b 113))))) else (if i < 125 then (if i < 119 then (if i < 116 then (if i < 115 then b 114 else b 115) else (if i < 117 then b 116 else (if i < 118 then b 117 else b 118))) else (if i < 122 then (if i < 120 then b 119 else (if i < 121 then b 120 else b 121)) else (if i < 123 then b 122 else (if i < 124 then b 123 else b 124)))) else (if i < 131 then (if i < 128 then (if i < 126 then b 125 else (if i < 127 then b 126 else b 127)) else (if i < 129 then b 128 else (if i < 130 then b 129 else b 130))) else (if i < 134 then (if i < 132 then b 131 else (if i < 133 then b 132 else b 133)) else (if i < 135 then b 134 else (if i < 136 then b 135 else b 136)))))) else (if i < 160 then (if i < 148 then (if i < 142 then (if i < 139 then (if i < 138 then b 137 else b 138) else (if i < 140 then b 139 else (if i < 141 then b 140 else b 141))) else (if i < 145 then (if i < 143 then b 142 else (if i < 144 then b 143 else b 144)) else (if i < 146 then b 145 else (if i < 147 then b 146 else b 147)))) else (if i < 154 then (if i < 151 then (if i < 149 then b 148 else (if i < 150 then b 149 else b 150)) else (if i < 152 then b 151 else (if i < 153 then b 152 else b 153))) else (if i < 157 then (if i < 155 then b 154 else (if i < 156 then b 155 else b 156)) else (if i < 158 then b 157 else (if i < 159 then b 158 else b 159))))) else (if i < 171 then (if i < 165 then (if i < 162 then (if i < 161 then b 160 else b 161) else (if i < 163 then b 162 else (if i < 164 then b 163 else b 164))) else (if i < 168 then (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)) else (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)))) else (if i < 177 then (if i < 174 then (if i < 172 then b 171 else (if i < 173 then b 172 else b 173)) else (if i < 175 then b 174 else (if i < 176 then b 175 else b 176))) else (if i < 180 then (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)) else (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)))))))) else (if i < 274 then (if i < 228 then (if i < 205 then (if i < 194 then (if i < 188 then (if i < 185 then (if i < 184 then b 183 else b 184) else (if i < 186 then b 185 else (if i < 187 then b 186 else b 187))) else (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)))) else (if i < 199 then (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else (if i < 198 then b 197 else b 198))) else (if i < 202 then (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)) else (if i < 203 then b 202 else (if i < 204 then b 203 else b 204))))) else (if i < 216 then (if i < 210 then (if i < 207 then (if i < 206 then b 205 else b 206) else (if i < 208 then b 207 else (if i < 209 then b 208 else b 209))) else (if i < 213 then (if i < 211 then b 210 else (if i < 212 then decide (1 ≤ count211 b) else decide (2 ≤ count211 b))) else (if i < 214 then decide (1 ≤ count213 b) else (if i < 215 then decide (2 ≤ count213 b) else decide (1 ≤ count215 b))))) else (if i < 222 then (if i < 219 then (if i < 217 then decide (2 ≤ count215 b) else (if i < 218 then decide (1 ≤ count217 b) else decide (2 ≤ count217 b))) else (if i < 220 then decide (1 ≤ count219 b) else (if i < 221 then decide (2 ≤ count219 b) else decide (1 ≤ count221 b)))) else (if i < 225 then (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b))) else (if i < 226 then decide (1 ≤ count225 b) else (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b))))))) else (if i < 251 then (if i < 239 then (if i < 233 then (if i < 230 then (if i < 229 then decide (2 ≤ count227 b) else decide (1 ≤ count229 b)) else (if i < 231 then decide (2 ≤ count229 b) else (if i < 232 then decide (1 ≤ count231 b) else decide (2 ≤ count231 b)))) else (if i < 236 then (if i < 234 then decide (1 ≤ count233 b) else (if i < 235 then decide (2 ≤ count233 b) else decide (1 ≤ count235 b))) else (if i < 237 then decide (2 ≤ count235 b) else (if i < 238 then decide (1 ≤ count237 b) else decide (2 ≤ count237 b))))) else (if i < 245 then (if i < 242 then (if i < 240 then decide (1 ≤ count239 b) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b))) else (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b)))) else (if i < 248 then (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b))) else (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b)))))) else (if i < 262 then (if i < 256 then (if i < 253 then (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)) else (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b)))) else (if i < 259 then (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b))) else (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))))) else (if i < 268 then (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)))) else (if i < 271 then (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b))) else (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)))))))) else (if i < 320 then (if i < 297 then (if i < 285 then (if i < 279 then (if i < 276 then (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)) else (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)))) else (if i < 282 then (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))) else (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))))) else (if i < 291 then (if i < 288 then (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))) else (if i < 289 then decide (2 ≤ count287 b) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b)))) else (if i < 294 then (if i < 292 then decide (1 ≤ count291 b) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b))) else (if i < 295 then decide (2 ≤ count293 b) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b)))))) else (if i < 308 then (if i < 302 then (if i < 299 then (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)) else (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))) else (if i < 305 then (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))) else (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))))) else (if i < 314 then (if i < 311 then (if i < 309 then decide (2 ≤ count307 b) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b))) else (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)))) else (if i < 317 then (if i < 315 then decide (2 ≤ count313 b) else (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b))) else (if i < 318 then decide (1 ≤ count317 b) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b))))))) else (if i < 343 then (if i < 331 then (if i < 325 then (if i < 322 then (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b)) else (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b)))) else (if i < 328 then (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b))) else (if i < 329 then decide (2 ≤ count327 b) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b))))) else (if i < 337 then (if i < 334 then (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b))) else (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)))) else (if i < 340 then (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))) else (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)))))) else (if i < 354 then (if i < 348 then (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)))) else (if i < 351 then (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b))) else (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))))) else (if i < 360 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b)))) else (if i < 363 then (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b))) else (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))))))))) else (if i < 549 then (if i < 457 then (if i < 411 then (if i < 388 then (if i < 377 then (if i < 371 then (if i < 368 then (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)) else (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b))))) else (if i < 382 then (if i < 379 then (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)) else (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b)))) else (if i < 385 then (if i < 383 then decide (2 ≤ count381 b) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)))))) else (if i < 399 then (if i < 393 then (if i < 390 then (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b)) else (if i < 391 then decide (2 ≤ count389 b) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b)))) else (if i < 396 then (if i < 394 then decide (1 ≤ count393 b) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b))) else (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b))))) else (if i < 405 then (if i < 402 then (if i < 400 then decide (1 ≤ count399 b) else (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b))) else (if i < 403 then decide (2 ≤ count401 b) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b)))) else (if i < 408 then (if i < 406 then decide (1 ≤ count405 b) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b))) else (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))))))) else (if i < 434 then (if i < 422 then (if i < 416 then (if i < 413 then (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b)) else (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)))) else (if i < 419 then (if i < 417 then decide (2 ≤ count415 b) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b))) else (if i < 420 then decide (1 ≤ count419 b) else (if i < 421 then decide (2 ≤ count419 b) else decide (3 ≤ count419 b))))) else (if i < 428 then (if i < 425 then (if i < 423 then decide (1 ≤ count422 b) else (if i < 424 then decide (2 ≤ count422 b) else decide (1 ≤ count424 b))) else (if i < 426 then decide (2 ≤ count424 b) else (if i < 427 then decide (3 ≤ count424 b) else decide (1 ≤ count427 b)))) else (if i < 431 then (if i < 429 then decide (2 ≤ count427 b) else (if i < 430 then decide (3 ≤ count427 b) else decide (4 ≤ count427 b))) else (if i < 432 then decide (5 ≤ count427 b) else (if i < 433 then decide (6 ≤ count427 b) else decide (1 ≤ count433 b)))))) else (if i < 445 then (if i < 439 then (if i < 436 then (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b)) else (if i < 437 then decide (2 ≤ count435 b) else (if i < 438 then decide (3 ≤ count435 b) else decide (1 ≤ count438 b)))) else (if i < 442 then (if i < 440 then decide (2 ≤ count438 b) else (if i < 441 then decide (1 ≤ count440 b) else decide (2 ≤ count440 b))) else (if i < 443 then decide (3 ≤ count440 b) else (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b))))) else (if i < 451 then (if i < 448 then (if i < 446 then decide (3 ≤ count443 b) else (if i < 447 then decide (4 ≤ count443 b) else decide (5 ≤ count443 b))) else (if i < 449 then decide (6 ≤ count443 b) else (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)))) else (if i < 454 then (if i < 452 then decide (3 ≤ count449 b) else (if i < 453 then decide (4 ≤ count449 b) else decide (5 ≤ count449 b))) else (if i < 455 then decide (6 ≤ count449 b) else (if i < 456 then decide (7 ≤ count449 b) else decide (8 ≤ count449 b)))))))) else (if i < 503 then (if i < 480 then (if i < 468 then (if i < 462 then (if i < 459 then (if i < 458 then decide (9 ≤ count449 b) else decide (10 ≤ count449 b)) else (if i < 460 then decide (11 ≤ count449 b) else (if i < 461 then decide (12 ≤ count449 b) else decide (1 ≤ count461 b)))) else (if i < 465 then (if i < 463 then decide (2 ≤ count461 b) else (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b))) else (if i < 466 then decide (3 ≤ count463 b) else (if i < 467 then decide (1 ≤ count466 b) else decide (2 ≤ count466 b))))) else (if i < 474 then (if i < 471 then (if i < 469 then decide (1 ≤ count468 b) else (if i < 470 then decide (2 ≤ count468 b) else decide (3 ≤ count468 b))) else (if i < 472 then decide (1 ≤ count471 b) else (if i < 473 then decide (2 ≤ count471 b) else decide (3 ≤ count471 b)))) else (if i < 477 then (if i < 475 then decide (4 ≤ count471 b) else (if i < 476 then decide (5 ≤ count471 b) else decide (6 ≤ count471 b))) else (if i < 478 then decide (1 ≤ count477 b) else (if i < 479 then decide (2 ≤ count477 b) else decide (1 ≤ count479 b)))))) else (if i < 491 then (if i < 485 then (if i < 482 then (if i < 481 then decide (2 ≤ count479 b) else decide (3 ≤ count479 b)) else (if i < 483 then decide (1 ≤ count482 b) else (if i < 484 then decide (2 ≤ count482 b) else decide (1 ≤ count484 b)))) else (if i < 488 then (if i < 486 then decide (2 ≤ count484 b) else (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b))) else (if i < 489 then decide (3 ≤ count486 b) else (if i < 490 then decide (4 ≤ count486 b) else decide (1 ≤ count490 b))))) else (if i < 497 then (if i < 494 then (if i < 492 then decide (2 ≤ count490 b) else (if i < 493 then decide (3 ≤ count490 b) else decide (4 ≤ count490 b))) else (if i < 495 then decide (5 ≤ count490 b) else (if i < 496 then decide (6 ≤ count490 b) else decide (7 ≤ count490 b)))) else (if i < 500 then (if i < 498 then decide (1 ≤ count497 b) else (if i < 499 then decide (2 ≤ count497 b) else decide (3 ≤ count497 b))) else (if i < 501 then decide (4 ≤ count497 b) else (if i < 502 then decide (5 ≤ count497 b) else decide (6 ≤ count497 b))))))) else (if i < 526 then (if i < 514 then (if i < 508 then (if i < 505 then (if i < 504 then decide (7 ≤ count497 b) else decide (8 ≤ count497 b)) else (if i < 506 then decide (9 ≤ count497 b) else (if i < 507 then decide (10 ≤ count497 b) else decide (11 ≤ count497 b)))) else (if i < 511 then (if i < 509 then decide (12 ≤ count497 b) else (if i < 510 then decide (13 ≤ count497 b) else decide (1 ≤ count510 b))) else (if i < 512 then decide (2 ≤ count510 b) else (if i < 513 then decide (3 ≤ count510 b) else decide (4 ≤ count510 b))))) else (if i < 520 then (if i < 517 then (if i < 515 then decide (5 ≤ count510 b) else (if i < 516 then decide (6 ≤ count510 b) else decide (7 ≤ count510 b))) else (if i < 518 then decide (8 ≤ count510 b) else (if i < 519 then decide (9 ≤ count510 b) else decide (10 ≤ count510 b)))) else (if i < 523 then (if i < 521 then decide (11 ≤ count510 b) else (if i < 522 then decide (12 ≤ count510 b) else decide (13 ≤ count510 b))) else (if i < 524 then decide (14 ≤ count510 b) else (if i < 525 then decide (15 ≤ count510 b) else decide (16 ≤ count510 b)))))) else (if i < 537 then (if i < 531 then (if i < 528 then (if i < 527 then decide (17 ≤ count510 b) else decide (18 ≤ count510 b)) else (if i < 529 then decide (19 ≤ count510 b) else (if i < 530 then decide (20 ≤ count510 b) else decide (21 ≤ count510 b)))) else (if i < 534 then (if i < 532 then decide (22 ≤ count510 b) else (if i < 533 then decide (23 ≤ count510 b) else decide (24 ≤ count510 b))) else (if i < 535 then decide (25 ≤ count510 b) else (if i < 536 then decide (1 ≤ count535 b) else decide (2 ≤ count535 b))))) else (if i < 543 then (if i < 540 then (if i < 538 then decide (1 ≤ count537 b) else (if i < 539 then decide (2 ≤ count537 b) else decide (3 ≤ count537 b))) else (if i < 541 then decide (1 ≤ count540 b) else (if i < 542 then decide (2 ≤ count540 b) else decide (1 ≤ count542 b)))) else (if i < 546 then (if i < 544 then decide (2 ≤ count542 b) else (if i < 545 then decide (3 ≤ count542 b) else decide (1 ≤ count545 b))) else (if i < 547 then decide (2 ≤ count545 b) else (if i < 548 then decide (3 ≤ count545 b) else decide (4 ≤ count545 b))))))))) else (if i < 640 then (if i < 594 then (if i < 571 then (if i < 560 then (if i < 554 then (if i < 551 then (if i < 550 then decide (5 ≤ count545 b) else decide (6 ≤ count545 b)) else (if i < 552 then decide (1 ≤ count551 b) else (if i < 553 then decide (2 ≤ count551 b) else decide (1 ≤ count553 b)))) else (if i < 557 then (if i < 555 then decide (2 ≤ count553 b) else (if i < 556 then decide (3 ≤ count553 b) else decide (1 ≤ count556 b))) else (if i < 558 then decide (2 ≤ count556 b) else (if i < 559 then decide (1 ≤ count558 b) else decide (2 ≤ count558 b))))) else (if i < 565 then (if i < 562 then (if i < 561 then decide (3 ≤ count558 b) else decide (1 ≤ count561 b)) else (if i < 563 then decide (2 ≤ count561 b) else (if i < 564 then decide (3 ≤ count561 b) else decide (4 ≤ count561 b)))) else (if i < 568 then (if i < 566 then decide (5 ≤ count561 b) else (if i < 567 then decide (6 ≤ count561 b) else decide (1 ≤ count567 b))) else (if i < 569 then decide (2 ≤ count567 b) else (if i < 570 then decide (3 ≤ count567 b) else decide (4 ≤ count567 b)))))) else (if i < 582 then (if i < 576 then (if i < 573 then (if i < 572 then decide (5 ≤ count567 b) else decide (6 ≤ count567 b)) else (if i < 574 then decide (7 ≤ count567 b) else (if i < 575 then decide (8 ≤ count567 b) else decide (9 ≤ count567 b)))) else (if i < 579 then (if i < 577 then decide (10 ≤ count567 b) else (if i < 578 then decide (11 ≤ count567 b) else decide (12 ≤ count567 b))) else (if i < 580 then decide (1 ≤ count579 b) else (if i < 581 then decide (2 ≤ count579 b) else decide (1 ≤ count581 b))))) else (if i < 588 then (if i < 585 then (if i < 583 then decide (2 ≤ count581 b) else (if i < 584 then decide (3 ≤ count581 b) else decide (1 ≤ count584 b))) else (if i < 586 then decide (2 ≤ count584 b) else (if i < 587 then decide (1 ≤ count586 b) else decide (2 ≤ count586 b)))) else (if i < 591 then (if i < 589 then decide (3 ≤ count586 b) else (if i < 590 then decide (1 ≤ count589 b) else decide (2 ≤ count589 b))) else (if i < 592 then decide (3 ≤ count589 b) else (if i < 593 then decide (4 ≤ count589 b) else decide (5 ≤ count589 b))))))) else (if i < 617 then (if i < 605 then (if i < 599 then (if i < 596 then (if i < 595 then decide (6 ≤ count589 b) else decide (1 ≤ count595 b)) else (if i < 597 then decide (2 ≤ count595 b) else (if i < 598 then decide (1 ≤ count597 b) else decide (2 ≤ count597 b)))) else (if i < 602 then (if i < 600 then decide (3 ≤ count597 b) else (if i < 601 then decide (1 ≤ count600 b) else decide (2 ≤ count600 b))) else (if i < 603 then decide (1 ≤ count602 b) else (if i < 604 then decide (2 ≤ count602 b) else decide (1 ≤ count604 b))))) else (if i < 611 then (if i < 608 then (if i < 606 then decide (2 ≤ count604 b) else (if i < 607 then decide (3 ≤ count604 b) else decide (4 ≤ count604 b))) else (if i < 609 then decide (1 ≤ count608 b) else (if i < 610 then decide (2 ≤ count608 b) else decide (3 ≤ count608 b)))) else (if i < 614 then (if i < 612 then decide (4 ≤ count608 b) else (if i < 613 then decide (5 ≤ count608 b) else decide (6 ≤ count608 b))) else (if i < 615 then decide (7 ≤ count608 b) else (if i < 616 then decide (1 ≤ count615 b) else decide (2 ≤ count615 b)))))) else (if i < 628 then (if i < 622 then (if i < 619 then (if i < 618 then decide (3 ≤ count615 b) else decide (4 ≤ count615 b)) else (if i < 620 then decide (5 ≤ count615 b) else (if i < 621 then decide (6 ≤ count615 b) else decide (7 ≤ count615 b)))) else (if i < 625 then (if i < 623 then decide (8 ≤ count615 b) else (if i < 624 then decide (9 ≤ count615 b) else decide (10 ≤ count615 b))) else (if i < 626 then decide (11 ≤ count615 b) else (if i < 627 then decide (12 ≤ count615 b) else decide (13 ≤ count615 b))))) else (if i < 634 then (if i < 631 then (if i < 629 then decide (1 ≤ count628 b) else (if i < 630 then decide (2 ≤ count628 b) else decide (3 ≤ count628 b))) else (if i < 632 then decide (4 ≤ count628 b) else (if i < 633 then decide (5 ≤ count628 b) else decide (6 ≤ count628 b)))) else (if i < 637 then (if i < 635 then decide (7 ≤ count628 b) else (if i < 636 then decide (8 ≤ count628 b) else decide (9 ≤ count628 b))) else (if i < 638 then decide (10 ≤ count628 b) else (if i < 639 then decide (11 ≤ count628 b) else decide (12 ≤ count628 b)))))))) else (if i < 686 then (if i < 663 then (if i < 651 then (if i < 645 then (if i < 642 then (if i < 641 then decide (13 ≤ count628 b) else decide (14 ≤ count628 b)) else (if i < 643 then decide (15 ≤ count628 b) else (if i < 644 then decide (16 ≤ count628 b) else decide (17 ≤ count628 b)))) else (if i < 648 then (if i < 646 then decide (18 ≤ count628 b) else (if i < 647 then decide (19 ≤ count628 b) else decide (20 ≤ count628 b))) else (if i < 649 then decide (21 ≤ count628 b) else (if i < 650 then decide (22 ≤ count628 b) else decide (23 ≤ count628 b))))) else (if i < 657 then (if i < 654 then (if i < 652 then decide (24 ≤ count628 b) else (if i < 653 then decide (25 ≤ count628 b) else decide (1 ≤ count653 b))) else (if i < 655 then decide (2 ≤ count653 b) else (if i < 656 then decide (3 ≤ count653 b) else decide (4 ≤ count653 b)))) else (if i < 660 then (if i < 658 then decide (5 ≤ count653 b) else (if i < 659 then decide (6 ≤ count653 b) else decide (7 ≤ count653 b))) else (if i < 661 then decide (8 ≤ count653 b) else (if i < 662 then decide (9 ≤ count653 b) else decide (10 ≤ count653 b)))))) else (if i < 674 then (if i < 668 then (if i < 665 then (if i < 664 then decide (11 ≤ count653 b) else decide (12 ≤ count653 b)) else (if i < 666 then decide (13 ≤ count653 b) else (if i < 667 then decide (14 ≤ count653 b) else decide (15 ≤ count653 b)))) else (if i < 671 then (if i < 669 then decide (16 ≤ count653 b) else (if i < 670 then decide (17 ≤ count653 b) else decide (18 ≤ count653 b))) else (if i < 672 then decide (19 ≤ count653 b) else (if i < 673 then decide (20 ≤ count653 b) else decide (21 ≤ count653 b))))) else (if i < 680 then (if i < 677 then (if i < 675 then decide (22 ≤ count653 b) else (if i < 676 then decide (23 ≤ count653 b) else decide (24 ≤ count653 b))) else (if i < 678 then decide (25 ≤ count653 b) else (if i < 679 then decide (26 ≤ count653 b) else decide (27 ≤ count653 b)))) else (if i < 683 then (if i < 681 then decide (28 ≤ count653 b) else (if i < 682 then decide (29 ≤ count653 b) else decide (30 ≤ count653 b))) else (if i < 684 then decide (31 ≤ count653 b) else (if i < 685 then decide (32 ≤ count653 b) else decide (33 ≤ count653 b))))))) else (if i < 709 then (if i < 697 then (if i < 691 then (if i < 688 then (if i < 687 then decide (34 ≤ count653 b) else decide (35 ≤ count653 b)) else (if i < 689 then decide (36 ≤ count653 b) else (if i < 690 then decide (37 ≤ count653 b) else decide (38 ≤ count653 b)))) else (if i < 694 then (if i < 692 then decide (39 ≤ count653 b) else (if i < 693 then decide (40 ≤ count653 b) else decide (41 ≤ count653 b))) else (if i < 695 then decide (42 ≤ count653 b) else (if i < 696 then decide (1 ≤ count695 b) else decide (2 ≤ count695 b))))) else (if i < 703 then (if i < 700 then (if i < 698 then decide (1 ≤ count697 b) else (if i < 699 then decide (2 ≤ count697 b) else decide (3 ≤ count697 b))) else (if i < 701 then decide (1 ≤ count700 b) else (if i < 702 then decide (2 ≤ count700 b) else decide (1 ≤ count702 b)))) else (if i < 706 then (if i < 704 then decide (2 ≤ count702 b) else (if i < 705 then decide (3 ≤ count702 b) else decide (1 ≤ count705 b))) else (if i < 707 then decide (2 ≤ count705 b) else (if i < 708 then decide (3 ≤ count705 b) else decide (4 ≤ count705 b)))))) else (if i < 720 then (if i < 714 then (if i < 711 then (if i < 710 then decide (5 ≤ count705 b) else decide (6 ≤ count705 b)) else (if i < 712 then decide (1 ≤ count711 b) else (if i < 713 then decide (2 ≤ count711 b) else decide (1 ≤ count713 b)))) else (if i < 717 then (if i < 715 then decide (2 ≤ count713 b) else (if i < 716 then decide (3 ≤ count713 b) else decide (1 ≤ count716 b))) else (if i < 718 then decide (2 ≤ count716 b) else (if i < 719 then decide (1 ≤ count718 b) else decide (2 ≤ count718 b))))) else (if i < 726 then (if i < 723 then (if i < 721 then decide (3 ≤ count718 b) else (if i < 722 then decide (1 ≤ count721 b) else decide (2 ≤ count721 b))) else (if i < 724 then decide (3 ≤ count721 b) else (if i < 725 then decide (4 ≤ count721 b) else decide (5 ≤ count721 b)))) else (if i < 729 then (if i < 727 then decide (6 ≤ count721 b) else (if i < 728 then decide (1 ≤ count727 b) else decide (2 ≤ count727 b))) else (if i < 730 then decide (3 ≤ count727 b) else (if i < 731 then decide (4 ≤ count727 b) else decide (5 ≤ count727 b))))))))))) else (if i < 1098 then (if i < 915 then (if i < 823 then (if i < 777 then (if i < 754 then (if i < 743 then (if i < 737 then (if i < 734 then (if i < 733 then decide (6 ≤ count727 b) else decide (7 ≤ count727 b)) else (if i < 735 then decide (8 ≤ count727 b) else (if i < 736 then decide (9 ≤ count727 b) else decide (10 ≤ count727 b)))) else (if i < 740 then (if i < 738 then decide (1 ≤ count737 b) else (if i < 739 then decide (2 ≤ count737 b) else decide (1 ≤ count739 b))) else (if i < 741 then decide (2 ≤ count739 b) else (if i < 742 then decide (3 ≤ count739 b) else decide (1 ≤ count742 b))))) else (if i < 748 then (if i < 745 then (if i < 744 then decide (2 ≤ count742 b) else decide (1 ≤ count744 b)) else (if i < 746 then decide (2 ≤ count744 b) else (if i < 747 then decide (3 ≤ count744 b) else decide (1 ≤ count747 b)))) else (if i < 751 then (if i < 749 then decide (2 ≤ count747 b) else (if i < 750 then decide (3 ≤ count747 b) else decide (4 ≤ count747 b))) else (if i < 752 then decide (5 ≤ count747 b) else (if i < 753 then decide (6 ≤ count747 b) else decide (1 ≤ count753 b)))))) else (if i < 765 then (if i < 759 then (if i < 756 then (if i < 755 then decide (2 ≤ count753 b) else decide (1 ≤ count755 b)) else (if i < 757 then decide (2 ≤ count755 b) else (if i < 758 then decide (3 ≤ count755 b) else decide (1 ≤ count758 b)))) else (if i < 762 then (if i < 760 then decide (2 ≤ count758 b) else (if i < 761 then decide (1 ≤ count760 b) else decide (2 ≤ count760 b))) else (if i < 763 then decide (1 ≤ count762 b) else (if i < 764 then decide (2 ≤ count762 b) else decide (3 ≤ count762 b))))) else (if i < 771 then (if i < 768 then (if i < 766 then decide (4 ≤ count762 b) else (if i < 767 then decide (1 ≤ count766 b) else decide (2 ≤ count766 b))) else (if i < 769 then decide (3 ≤ count766 b) else (if i < 770 then decide (4 ≤ count766 b) else decide (5 ≤ count766 b)))) else (if i < 774 then (if i < 772 then decide (6 ≤ count766 b) else (if i < 773 then decide (7 ≤ count766 b) else decide (1 ≤ count773 b))) else (if i < 775 then decide (2 ≤ count773 b) else (if i < 776 then decide (3 ≤ count773 b) else decide (4 ≤ count773 b))))))) else (if i < 800 then (if i < 788 then (if i < 782 then (if i < 779 then (if i < 778 then decide (5 ≤ count773 b) else decide (6 ≤ count773 b)) else (if i < 780 then decide (7 ≤ count773 b) else (if i < 781 then decide (8 ≤ count773 b) else decide (9 ≤ count773 b)))) else (if i < 785 then (if i < 783 then decide (10 ≤ count773 b) else (if i < 784 then decide (1 ≤ count783 b) else decide (2 ≤ count783 b))) else (if i < 786 then decide (3 ≤ count783 b) else (if i < 787 then decide (4 ≤ count783 b) else decide (5 ≤ count783 b))))) else (if i < 794 then (if i < 791 then (if i < 789 then decide (6 ≤ count783 b) else (if i < 790 then decide (7 ≤ count783 b) else decide (8 ≤ count783 b))) else (if i < 792 then decide (9 ≤ count783 b) else (if i < 793 then decide (10 ≤ count783 b) else decide (1 ≤ count793 b)))) else (if i < 797 then (if i < 795 then decide (2 ≤ count793 b) else (if i < 796 then decide (1 ≤ count795 b) else decide (2 ≤ count795 b))) else (if i < 798 then decide (3 ≤ count795 b) else (if i < 799 then decide (1 ≤ count798 b) else decide (2 ≤ count798 b)))))) else (if i < 811 then (if i < 805 then (if i < 802 then (if i < 801 then decide (1 ≤ count800 b) else decide (2 ≤ count800 b)) else (if i < 803 then decide (3 ≤ count800 b) else (if i < 804 then decide (1 ≤ count803 b) else decide (2 ≤ count803 b)))) else (if i < 808 then (if i < 806 then decide (3 ≤ count803 b) else (if i < 807 then decide (4 ≤ count803 b) else decide (5 ≤ count803 b))) else (if i < 809 then decide (6 ≤ count803 b) else (if i < 810 then decide (1 ≤ count809 b) else decide (2 ≤ count809 b))))) else (if i < 817 then (if i < 814 then (if i < 812 then decide (1 ≤ count811 b) else (if i < 813 then decide (2 ≤ count811 b) else decide (3 ≤ count811 b))) else (if i < 815 then decide (1 ≤ count814 b) else (if i < 816 then decide (2 ≤ count814 b) else decide (1 ≤ count816 b)))) else (if i < 820 then (if i < 818 then decide (2 ≤ count816 b) else (if i < 819 then decide (3 ≤ count816 b) else decide (1 ≤ count819 b))) else (if i < 821 then decide (2 ≤ count819 b) else (if i < 822 then decide (3 ≤ count819 b) else decide (4 ≤ count819 b)))))))) else (if i < 869 then (if i < 846 then (if i < 834 then (if i < 828 then (if i < 825 then (if i < 824 then decide (5 ≤ count819 b) else decide (6 ≤ count819 b)) else (if i < 826 then decide (1 ≤ count825 b) else (if i < 827 then decide (2 ≤ count825 b) else decide (3 ≤ count825 b)))) else (if i < 831 then (if i < 829 then decide (4 ≤ count825 b) else (if i < 830 then decide (5 ≤ count825 b) else decide (6 ≤ count825 b))) else (if i < 832 then decide (7 ≤ count825 b) else (if i < 833 then decide (8 ≤ count825 b) else decide (9 ≤ count825 b))))) else (if i < 840 then (if i < 837 then (if i < 835 then decide (10 ≤ count825 b) else (if i < 836 then decide (1 ≤ count835 b) else decide (2 ≤ count835 b))) else (if i < 838 then decide (1 ≤ count837 b) else (if i < 839 then decide (2 ≤ count837 b) else decide (3 ≤ count837 b)))) else (if i < 843 then (if i < 841 then decide (1 ≤ count840 b) else (if i < 842 then decide (2 ≤ count840 b) else decide (1 ≤ count842 b))) else (if i < 844 then decide (2 ≤ count842 b) else (if i < 845 then decide (3 ≤ count842 b) else decide (1 ≤ count845 b)))))) else (if i < 857 then (if i < 851 then (if i < 848 then (if i < 847 then decide (2 ≤ count845 b) else decide (3 ≤ count845 b)) else (if i < 849 then decide (4 ≤ count845 b) else (if i < 850 then decide (5 ≤ count845 b) else decide (6 ≤ count845 b)))) else (if i < 854 then (if i < 852 then decide (1 ≤ count851 b) else (if i < 853 then decide (2 ≤ count851 b) else decide (1 ≤ count853 b))) else (if i < 855 then decide (2 ≤ count853 b) else (if i < 856 then decide (3 ≤ count853 b) else decide (1 ≤ count856 b))))) else (if i < 863 then (if i < 860 then (if i < 858 then decide (2 ≤ count856 b) else (if i < 859 then decide (1 ≤ count858 b) else decide (2 ≤ count858 b))) else (if i < 861 then decide (1 ≤ count860 b) else (if i < 862 then decide (2 ≤ count860 b) else decide (3 ≤ count860 b)))) else (if i < 866 then (if i < 864 then decide (4 ≤ count860 b) else (if i < 865 then decide (1 ≤ count864 b) else decide (2 ≤ count864 b))) else (if i < 867 then decide (3 ≤ count864 b) else (if i < 868 then decide (4 ≤ count864 b) else decide (5 ≤ count864 b))))))) else (if i < 892 then (if i < 880 then (if i < 874 then (if i < 871 then (if i < 870 then decide (6 ≤ count864 b) else decide (7 ≤ count864 b)) else (if i < 872 then decide (1 ≤ count871 b) else (if i < 873 then decide (2 ≤ count871 b) else decide (3 ≤ count871 b)))) else (if i < 877 then (if i < 875 then decide (4 ≤ count871 b) else (if i < 876 then decide (5 ≤ count871 b) else decide (6 ≤ count871 b))) else (if i < 878 then decide (7 ≤ count871 b) else (if i < 879 then decide (8 ≤ count871 b) else decide (9 ≤ count871 b))))) else (if i < 886 then (if i < 883 then (if i < 881 then decide (10 ≤ count871 b) else (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b))) else (if i < 884 then decide (3 ≤ count881 b) else (if i < 885 then decide (4 ≤ count881 b) else decide (5 ≤ count881 b)))) else (if i < 889 then (if i < 887 then decide (6 ≤ count881 b) else (if i < 888 then decide (7 ≤ count881 b) else decide (8 ≤ count881 b))) else (if i < 890 then decide (9 ≤ count881 b) else (if i < 891 then decide (10 ≤ count881 b) else decide (1 ≤ count891 b)))))) else (if i < 903 then (if i < 897 then (if i < 894 then (if i < 893 then decide (2 ≤ count891 b) else decide (3 ≤ count891 b)) else (if i < 895 then decide (4 ≤ count891 b) else (if i < 896 then decide (5 ≤ count891 b) else decide (6 ≤ count891 b)))) else (if i < 900 then (if i < 898 then decide (7 ≤ count891 b) else (if i < 899 then decide (8 ≤ count891 b) else decide (9 ≤ count891 b))) else (if i < 901 then decide (10 ≤ count891 b) else (if i < 902 then decide (1 ≤ count901 b) else decide (2 ≤ count901 b))))) else (if i < 909 then (if i < 906 then (if i < 904 then decide (1 ≤ count903 b) else (if i < 905 then decide (2 ≤ count903 b) else decide (3 ≤ count903 b))) else (if i < 907 then decide (1 ≤ count906 b) else (if i < 908 then decide (2 ≤ count906 b) else decide (1 ≤ count908 b)))) else (if i < 912 then (if i < 910 then decide (2 ≤ count908 b) else (if i < 911 then decide (3 ≤ count908 b) else decide (1 ≤ count911 b))) else (if i < 913 then decide (2 ≤ count911 b) else (if i < 914 then decide (3 ≤ count911 b) else decide (4 ≤ count911 b))))))))) else (if i < 1006 then (if i < 960 then (if i < 937 then (if i < 926 then (if i < 920 then (if i < 917 then (if i < 916 then decide (5 ≤ count911 b) else decide (6 ≤ count911 b)) else (if i < 918 then decide (1 ≤ count917 b) else (if i < 919 then decide (2 ≤ count917 b) else decide (1 ≤ count919 b)))) else (if i < 923 then (if i < 921 then decide (2 ≤ count919 b) else (if i < 922 then decide (3 ≤ count919 b) else decide (1 ≤ count922 b))) else (if i < 924 then decide (2 ≤ count922 b) else (if i < 925 then decide (1 ≤ count924 b) else decide (2 ≤ count924 b))))) else (if i < 931 then (if i < 928 then (if i < 927 then decide (1 ≤ count926 b) else decide (2 ≤ count926 b)) else (if i < 929 then decide (3 ≤ count926 b) else (if i < 930 then decide (4 ≤ count926 b) else decide (1 ≤ count930 b)))) else (if i < 934 then (if i < 932 then decide (2 ≤ count930 b) else (if i < 933 then decide (3 ≤ count930 b) else decide (4 ≤ count930 b))) else (if i < 935 then decide (5 ≤ count930 b) else (if i < 936 then decide (6 ≤ count930 b) else decide (7 ≤ count930 b)))))) else (if i < 948 then (if i < 942 then (if i < 939 then (if i < 938 then decide (1 ≤ count937 b) else decide (2 ≤ count937 b)) else (if i < 940 then decide (3 ≤ count937 b) else (if i < 941 then decide (4 ≤ count937 b) else decide (5 ≤ count937 b)))) else (if i < 945 then (if i < 943 then decide (6 ≤ count937 b) else (if i < 944 then decide (7 ≤ count937 b) else decide (8 ≤ count937 b))) else (if i < 946 then decide (9 ≤ count937 b) else (if i < 947 then decide (10 ≤ count937 b) else decide (11 ≤ count937 b))))) else (if i < 954 then (if i < 951 then (if i < 949 then decide (12 ≤ count937 b) else (if i < 950 then decide (13 ≤ count937 b) else decide (1 ≤ count950 b))) else (if i < 952 then decide (2 ≤ count950 b) else (if i < 953 then decide (1 ≤ count952 b) else decide (2 ≤ count952 b)))) else (if i < 957 then (if i < 955 then decide (3 ≤ count952 b) else (if i < 956 then decide (1 ≤ count955 b) else decide (2 ≤ count955 b))) else (if i < 958 then decide (1 ≤ count957 b) else (if i < 959 then decide (2 ≤ count957 b) else decide (1 ≤ count959 b))))))) else (if i < 983 then (if i < 971 then (if i < 965 then (if i < 962 then (if i < 961 then decide (2 ≤ count959 b) else decide (3 ≤ count959 b)) else (if i < 963 then decide (4 ≤ count959 b) else (if i < 964 then decide (1 ≤ count963 b) else decide (2 ≤ count963 b)))) else (if i < 968 then (if i < 966 then decide (3 ≤ count963 b) else (if i < 967 then decide (4 ≤ count963 b) else decide (5 ≤ count963 b))) else (if i < 969 then decide (6 ≤ count963 b) else (if i < 970 then decide (7 ≤ count963 b) else decide (1 ≤ count970 b))))) else (if i < 977 then (if i < 974 then (if i < 972 then decide (2 ≤ count970 b) else (if i < 973 then decide (1 ≤ count972 b) else decide (2 ≤ count972 b))) else (if i < 975 then decide (3 ≤ count972 b) else (if i < 976 then decide (1 ≤ count975 b) else decide (2 ≤ count975 b)))) else (if i < 980 then (if i < 978 then decide (1 ≤ count977 b) else (if i < 979 then decide (2 ≤ count977 b) else decide (1 ≤ count979 b))) else (if i < 981 then decide (2 ≤ count979 b) else (if i < 982 then decide (3 ≤ count979 b) else decide (4 ≤ count979 b)))))) else (if i < 994 then (if i < 988 then (if i < 985 then (if i < 984 then decide (1 ≤ count983 b) else decide (2 ≤ count983 b)) else (if i < 986 then decide (3 ≤ count983 b) else (if i < 987 then decide (4 ≤ count983 b) else decide (5 ≤ count983 b)))) else (if i < 991 then (if i < 989 then decide (6 ≤ count983 b) else (if i < 990 then decide (7 ≤ count983 b) else decide (1 ≤ count990 b))) else (if i < 992 then decide (2 ≤ count990 b) else (if i < 993 then decide (3 ≤ count990 b) else decide (4 ≤ count990 b))))) else (if i < 1000 then (if i < 997 then (if i < 995 then decide (5 ≤ count990 b) else (if i < 996 then decide (6 ≤ count990 b) else decide (7 ≤ count990 b))) else (if i < 998 then decide (8 ≤ count990 b) else (if i < 999 then decide (9 ≤ count990 b) else decide (10 ≤ count990 b)))) else (if i < 1003 then (if i < 1001 then decide (11 ≤ count990 b) else (if i < 1002 then decide (12 ≤ count990 b) else decide (13 ≤ count990 b))) else (if i < 1004 then decide (14 ≤ count990 b) else (if i < 1005 then decide (1 ≤ count1004 b) else decide (2 ≤ count1004 b)))))))) else (if i < 1052 then (if i < 1029 then (if i < 1017 then (if i < 1011 then (if i < 1008 then (if i < 1007 then decide (3 ≤ count1004 b) else decide (4 ≤ count1004 b)) else (if i < 1009 then decide (5 ≤ count1004 b) else (if i < 1010 then decide (6 ≤ count1004 b) else decide (7 ≤ count1004 b)))) else (if i < 1014 then (if i < 1012 then decide (8 ≤ count1004 b) else (if i < 1013 then decide (9 ≤ count1004 b) else decide (10 ≤ count1004 b))) else (if i < 1015 then decide (11 ≤ count1004 b) else (if i < 1016 then decide (12 ≤ count1004 b) else decide (13 ≤ count1004 b))))) else (if i < 1023 then (if i < 1020 then (if i < 1018 then decide (14 ≤ count1004 b) else (if i < 1019 then decide (15 ≤ count1004 b) else decide (16 ≤ count1004 b))) else (if i < 1021 then decide (17 ≤ count1004 b) else (if i < 1022 then decide (18 ≤ count1004 b) else decide (19 ≤ count1004 b)))) else (if i < 1026 then (if i < 1024 then decide (20 ≤ count1004 b) else (if i < 1025 then decide (21 ≤ count1004 b) else decide (22 ≤ count1004 b))) else (if i < 1027 then decide (23 ≤ count1004 b) else (if i < 1028 then decide (24 ≤ count1004 b) else decide (25 ≤ count1004 b)))))) else (if i < 1040 then (if i < 1034 then (if i < 1031 then (if i < 1030 then decide (26 ≤ count1004 b) else decide (27 ≤ count1004 b)) else (if i < 1032 then decide (1 ≤ count1031 b) else (if i < 1033 then decide (2 ≤ count1031 b) else decide (1 ≤ count1033 b)))) else (if i < 1037 then (if i < 1035 then decide (2 ≤ count1033 b) else (if i < 1036 then decide (3 ≤ count1033 b) else decide (1 ≤ count1036 b))) else (if i < 1038 then decide (2 ≤ count1036 b) else (if i < 1039 then decide (1 ≤ count1038 b) else decide (2 ≤ count1038 b))))) else (if i < 1046 then (if i < 1043 then (if i < 1041 then decide (1 ≤ count1040 b) else (if i < 1042 then decide (2 ≤ count1040 b) else decide (3 ≤ count1040 b))) else (if i < 1044 then decide (4 ≤ count1040 b) else (if i < 1045 then decide (1 ≤ count1044 b) else decide (2 ≤ count1044 b)))) else (if i < 1049 then (if i < 1047 then decide (3 ≤ count1044 b) else (if i < 1048 then decide (4 ≤ count1044 b) else decide (5 ≤ count1044 b))) else (if i < 1050 then decide (6 ≤ count1044 b) else (if i < 1051 then decide (7 ≤ count1044 b) else decide (1 ≤ count1051 b))))))) else (if i < 1075 then (if i < 1063 then (if i < 1057 then (if i < 1054 then (if i < 1053 then decide (2 ≤ count1051 b) else decide (1 ≤ count1053 b)) else (if i < 1055 then decide (2 ≤ count1053 b) else (if i < 1056 then decide (3 ≤ count1053 b) else decide (1 ≤ count1056 b)))) else (if i < 1060 then (if i < 1058 then decide (2 ≤ count1056 b) else (if i < 1059 then decide (1 ≤ count1058 b) else decide (2 ≤ count1058 b))) else (if i < 1061 then decide (1 ≤ count1060 b) else (if i < 1062 then decide (2 ≤ count1060 b) else decide (3 ≤ count1060 b))))) else (if i < 1069 then (if i < 1066 then (if i < 1064 then decide (4 ≤ count1060 b) else (if i < 1065 then decide (1 ≤ count1064 b) else decide (2 ≤ count1064 b))) else (if i < 1067 then decide (3 ≤ count1064 b) else (if i < 1068 then decide (4 ≤ count1064 b) else decide (5 ≤ count1064 b)))) else (if i < 1072 then (if i < 1070 then decide (6 ≤ count1064 b) else (if i < 1071 then decide (7 ≤ count1064 b) else decide (1 ≤ count1071 b))) else (if i < 1073 then decide (2 ≤ count1071 b) else (if i < 1074 then decide (3 ≤ count1071 b) else decide (4 ≤ count1071 b)))))) else (if i < 1086 then (if i < 1080 then (if i < 1077 then (if i < 1076 then decide (5 ≤ count1071 b) else decide (6 ≤ count1071 b)) else (if i < 1078 then decide (7 ≤ count1071 b) else (if i < 1079 then decide (8 ≤ count1071 b) else decide (9 ≤ count1071 b)))) else (if i < 1083 then (if i < 1081 then decide (10 ≤ count1071 b) else (if i < 1082 then decide (11 ≤ count1071 b) else decide (12 ≤ count1071 b))) else (if i < 1084 then decide (13 ≤ count1071 b) else (if i < 1085 then decide (14 ≤ count1071 b) else decide (1 ≤ count1085 b))))) else (if i < 1092 then (if i < 1089 then (if i < 1087 then decide (2 ≤ count1085 b) else (if i < 1088 then decide (1 ≤ count1087 b) else decide (2 ≤ count1087 b))) else (if i < 1090 then decide (3 ≤ count1087 b) else (if i < 1091 then decide (1 ≤ count1090 b) else decide (2 ≤ count1090 b)))) else (if i < 1095 then (if i < 1093 then decide (1 ≤ count1092 b) else (if i < 1094 then decide (2 ≤ count1092 b) else decide (1 ≤ count1094 b))) else (if i < 1096 then decide (2 ≤ count1094 b) else (if i < 1097 then decide (3 ≤ count1094 b) else decide (4 ≤ count1094 b)))))))))) else (if i < 1281 then (if i < 1189 then (if i < 1143 then (if i < 1120 then (if i < 1109 then (if i < 1103 then (if i < 1100 then (if i < 1099 then decide (1 ≤ count1098 b) else decide (2 ≤ count1098 b)) else (if i < 1101 then decide (3 ≤ count1098 b) else (if i < 1102 then decide (4 ≤ count1098 b) else decide (5 ≤ count1098 b)))) else (if i < 1106 then (if i < 1104 then decide (6 ≤ count1098 b) else (if i < 1105 then decide (7 ≤ count1098 b) else decide (1 ≤ count1105 b))) else (if i < 1107 then decide (2 ≤ count1105 b) else (if i < 1108 then decide (1 ≤ count1107 b) else decide (2 ≤ count1107 b))))) else (if i < 1114 then (if i < 1111 then (if i < 1110 then decide (3 ≤ count1107 b) else decide (1 ≤ count1110 b)) else (if i < 1112 then decide (2 ≤ count1110 b) else (if i < 1113 then decide (1 ≤ count1112 b) else decide (2 ≤ count1112 b)))) else (if i < 1117 then (if i < 1115 then decide (1 ≤ count1114 b) else (if i < 1116 then decide (2 ≤ count1114 b) else decide (3 ≤ count1114 b))) else (if i < 1118 then decide (4 ≤ count1114 b) else (if i < 1119 then decide (1 ≤ count1118 b) else decide (2 ≤ count1118 b)))))) else (if i < 1131 then (if i < 1125 then (if i < 1122 then (if i < 1121 then decide (3 ≤ count1118 b) else decide (4 ≤ count1118 b)) else (if i < 1123 then decide (5 ≤ count1118 b) else (if i < 1124 then decide (6 ≤ count1118 b) else decide (7 ≤ count1118 b)))) else (if i < 1128 then (if i < 1126 then decide (1 ≤ count1125 b) else (if i < 1127 then decide (2 ≤ count1125 b) else decide (3 ≤ count1125 b))) else (if i < 1129 then decide (4 ≤ count1125 b) else (if i < 1130 then decide (5 ≤ count1125 b) else decide (6 ≤ count1125 b))))) else (if i < 1137 then (if i < 1134 then (if i < 1132 then decide (7 ≤ count1125 b) else (if i < 1133 then decide (8 ≤ count1125 b) else decide (9 ≤ count1125 b))) else (if i < 1135 then decide (10 ≤ count1125 b) else (if i < 1136 then decide (11 ≤ count1125 b) else decide (12 ≤ count1125 b)))) else (if i < 1140 then (if i < 1138 then decide (13 ≤ count1125 b) else (if i < 1139 then decide (14 ≤ count1125 b) else decide (1 ≤ count1139 b))) else (if i < 1141 then decide (2 ≤ count1139 b) else (if i < 1142 then decide (3 ≤ count1139 b) else decide (4 ≤ count1139 b))))))) else (if i < 1166 then (if i < 1154 then (if i < 1148 then (if i < 1145 then (if i < 1144 then decide (5 ≤ count1139 b) else decide (6 ≤ count1139 b)) else (if i < 1146 then decide (7 ≤ count1139 b) else (if i < 1147 then decide (8 ≤ count1139 b) else decide (9 ≤ count1139 b)))) else (if i < 1151 then (if i < 1149 then decide (10 ≤ count1139 b) else (if i < 1150 then decide (11 ≤ count1139 b) else decide (12 ≤ count1139 b))) else (if i < 1152 then decide (13 ≤ count1139 b) else (if i < 1153 then decide (14 ≤ count1139 b) else decide (15 ≤ count1139 b))))) else (if i < 1160 then (if i < 1157 then (if i < 1155 then decide (16 ≤ count1139 b) else (if i < 1156 then decide (17 ≤ count1139 b) else decide (18 ≤ count1139 b))) else (if i < 1158 then decide (19 ≤ count1139 b) else (if i < 1159 then decide (20 ≤ count1139 b) else decide (21 ≤ count1139 b)))) else (if i < 1163 then (if i < 1161 then decide (22 ≤ count1139 b) else (if i < 1162 then decide (23 ≤ count1139 b) else decide (24 ≤ count1139 b))) else (if i < 1164 then decide (25 ≤ count1139 b) else (if i < 1165 then decide (26 ≤ count1139 b) else decide (27 ≤ count1139 b)))))) else (if i < 1177 then (if i < 1171 then (if i < 1168 then (if i < 1167 then decide (28 ≤ count1139 b) else decide (1 ≤ count1167 b)) else (if i < 1169 then decide (2 ≤ count1167 b) else (if i < 1170 then decide (3 ≤ count1167 b) else decide (4 ≤ count1167 b)))) else (if i < 1174 then (if i < 1172 then decide (5 ≤ count1167 b) else (if i < 1173 then decide (6 ≤ count1167 b) else decide (7 ≤ count1167 b))) else (if i < 1175 then decide (8 ≤ count1167 b) else (if i < 1176 then decide (9 ≤ count1167 b) else decide (10 ≤ count1167 b))))) else (if i < 1183 then (if i < 1180 then (if i < 1178 then decide (11 ≤ count1167 b) else (if i < 1179 then decide (12 ≤ count1167 b) else decide (13 ≤ count1167 b))) else (if i < 1181 then decide (14 ≤ count1167 b) else (if i < 1182 then decide (15 ≤ count1167 b) else decide (16 ≤ count1167 b)))) else (if i < 1186 then (if i < 1184 then decide (17 ≤ count1167 b) else (if i < 1185 then decide (18 ≤ count1167 b) else decide (19 ≤ count1167 b))) else (if i < 1187 then decide (20 ≤ count1167 b) else (if i < 1188 then decide (21 ≤ count1167 b) else decide (22 ≤ count1167 b)))))))) else (if i < 1235 then (if i < 1212 then (if i < 1200 then (if i < 1194 then (if i < 1191 then (if i < 1190 then decide (23 ≤ count1167 b) else decide (24 ≤ count1167 b)) else (if i < 1192 then decide (25 ≤ count1167 b) else (if i < 1193 then decide (26 ≤ count1167 b) else decide (27 ≤ count1167 b)))) else (if i < 1197 then (if i < 1195 then decide (28 ≤ count1167 b) else (if i < 1196 then decide (29 ≤ count1167 b) else decide (30 ≤ count1167 b))) else (if i < 1198 then decide (31 ≤ count1167 b) else (if i < 1199 then decide (32 ≤ count1167 b) else decide (33 ≤ count1167 b))))) else (if i < 1206 then (if i < 1203 then (if i < 1201 then decide (34 ≤ count1167 b) else (if i < 1202 then decide (35 ≤ count1167 b) else decide (36 ≤ count1167 b))) else (if i < 1204 then decide (37 ≤ count1167 b) else (if i < 1205 then decide (38 ≤ count1167 b) else decide (39 ≤ count1167 b)))) else (if i < 1209 then (if i < 1207 then decide (40 ≤ count1167 b) else (if i < 1208 then decide (41 ≤ count1167 b) else decide (42 ≤ count1167 b))) else (if i < 1210 then decide (1 ≤ count1209 b) else (if i < 1211 then decide (2 ≤ count1209 b) else decide (1 ≤ count1211 b)))))) else (if i < 1223 then (if i < 1217 then (if i < 1214 then (if i < 1213 then decide (2 ≤ count1211 b) else decide (3 ≤ count1211 b)) else (if i < 1215 then decide (1 ≤ count1214 b) else (if i < 1216 then decide (2 ≤ count1214 b) else decide (1 ≤ count1216 b)))) else (if i < 1220 then (if i < 1218 then decide (2 ≤ count1216 b) else (if i < 1219 then decide (3 ≤ count1216 b) else decide (1 ≤ count1219 b))) else (if i < 1221 then decide (2 ≤ count1219 b) else (if i < 1222 then decide (3 ≤ count1219 b) else decide (4 ≤ count1219 b))))) else (if i < 1229 then (if i < 1226 then (if i < 1224 then decide (5 ≤ count1219 b) else (if i < 1225 then decide (6 ≤ count1219 b) else decide (1 ≤ count1225 b))) else (if i < 1227 then decide (2 ≤ count1225 b) else (if i < 1228 then decide (1 ≤ count1227 b) else decide (2 ≤ count1227 b)))) else (if i < 1232 then (if i < 1230 then decide (3 ≤ count1227 b) else (if i < 1231 then decide (1 ≤ count1230 b) else decide (2 ≤ count1230 b))) else (if i < 1233 then decide (1 ≤ count1232 b) else (if i < 1234 then decide (2 ≤ count1232 b) else decide (1 ≤ count1234 b))))))) else (if i < 1258 then (if i < 1246 then (if i < 1240 then (if i < 1237 then (if i < 1236 then decide (2 ≤ count1234 b) else decide (3 ≤ count1234 b)) else (if i < 1238 then decide (4 ≤ count1234 b) else (if i < 1239 then decide (1 ≤ count1238 b) else decide (2 ≤ count1238 b)))) else (if i < 1243 then (if i < 1241 then decide (3 ≤ count1238 b) else (if i < 1242 then decide (4 ≤ count1238 b) else decide (5 ≤ count1238 b))) else (if i < 1244 then decide (6 ≤ count1238 b) else (if i < 1245 then decide (7 ≤ count1238 b) else decide (1 ≤ count1245 b))))) else (if i < 1252 then (if i < 1249 then (if i < 1247 then decide (2 ≤ count1245 b) else (if i < 1248 then decide (3 ≤ count1245 b) else decide (4 ≤ count1245 b))) else (if i < 1250 then decide (5 ≤ count1245 b) else (if i < 1251 then decide (6 ≤ count1245 b) else decide (7 ≤ count1245 b)))) else (if i < 1255 then (if i < 1253 then decide (8 ≤ count1245 b) else (if i < 1254 then decide (9 ≤ count1245 b) else decide (10 ≤ count1245 b))) else (if i < 1256 then decide (11 ≤ count1245 b) else (if i < 1257 then decide (12 ≤ count1245 b) else decide (13 ≤ count1245 b)))))) else (if i < 1269 then (if i < 1263 then (if i < 1260 then (if i < 1259 then decide (1 ≤ count1258 b) else decide (2 ≤ count1258 b)) else (if i < 1261 then decide (1 ≤ count1260 b) else (if i < 1262 then decide (2 ≤ count1260 b) else decide (3 ≤ count1260 b)))) else (if i < 1266 then (if i < 1264 then decide (1 ≤ count1263 b) else (if i < 1265 then decide (2 ≤ count1263 b) else decide (1 ≤ count1265 b))) else (if i < 1267 then decide (2 ≤ count1265 b) else (if i < 1268 then decide (1 ≤ count1267 b) else decide (2 ≤ count1267 b))))) else (if i < 1275 then (if i < 1272 then (if i < 1270 then decide (3 ≤ count1267 b) else (if i < 1271 then decide (4 ≤ count1267 b) else decide (1 ≤ count1271 b))) else (if i < 1273 then decide (2 ≤ count1271 b) else (if i < 1274 then decide (3 ≤ count1271 b) else decide (4 ≤ count1271 b)))) else (if i < 1278 then (if i < 1276 then decide (5 ≤ count1271 b) else (if i < 1277 then decide (6 ≤ count1271 b) else decide (7 ≤ count1271 b))) else (if i < 1279 then decide (1 ≤ count1278 b) else (if i < 1280 then decide (2 ≤ count1278 b) else decide (1 ≤ count1280 b))))))))) else (if i < 1373 then (if i < 1327 then (if i < 1304 then (if i < 1292 then (if i < 1286 then (if i < 1283 then (if i < 1282 then decide (2 ≤ count1280 b) else decide (3 ≤ count1280 b)) else (if i < 1284 then decide (1 ≤ count1283 b) else (if i < 1285 then decide (2 ≤ count1283 b) else decide (1 ≤ count1285 b)))) else (if i < 1289 then (if i < 1287 then decide (2 ≤ count1285 b) else (if i < 1288 then decide (1 ≤ count1287 b) else decide (2 ≤ count1287 b))) else (if i < 1290 then decide (3 ≤ count1287 b) else (if i < 1291 then decide (4 ≤ count1287 b) else decide (1 ≤ count1291 b))))) else (if i < 1298 then (if i < 1295 then (if i < 1293 then decide (2 ≤ count1291 b) else (if i < 1294 then decide (3 ≤ count1291 b) else decide (4 ≤ count1291 b))) else (if i < 1296 then decide (5 ≤ count1291 b) else (if i < 1297 then decide (6 ≤ count1291 b) else decide (7 ≤ count1291 b)))) else (if i < 1301 then (if i < 1299 then decide (1 ≤ count1298 b) else (if i < 1300 then decide (2 ≤ count1298 b) else decide (3 ≤ count1298 b))) else (if i < 1302 then decide (4 ≤ count1298 b) else (if i < 1303 then decide (5 ≤ count1298 b) else decide (6 ≤ count1298 b)))))) else (if i < 1315 then (if i < 1309 then (if i < 1306 then (if i < 1305 then decide (7 ≤ count1298 b) else decide (8 ≤ count1298 b)) else (if i < 1307 then decide (9 ≤ count1298 b) else (if i < 1308 then decide (10 ≤ count1298 b) else decide (11 ≤ count1298 b)))) else (if i < 1312 then (if i < 1310 then decide (12 ≤ count1298 b) else (if i < 1311 then decide (13 ≤ count1298 b) else decide (14 ≤ count1298 b))) else (if i < 1313 then decide (1 ≤ count1312 b) else (if i < 1314 then decide (2 ≤ count1312 b) else decide (3 ≤ count1312 b))))) else (if i < 1321 then (if i < 1318 then (if i < 1316 then decide (4 ≤ count1312 b) else (if i < 1317 then decide (5 ≤ count1312 b) else decide (6 ≤ count1312 b))) else (if i < 1319 then decide (7 ≤ count1312 b) else (if i < 1320 then decide (8 ≤ count1312 b) else decide (9 ≤ count1312 b)))) else (if i < 1324 then (if i < 1322 then decide (10 ≤ count1312 b) else (if i < 1323 then decide (11 ≤ count1312 b) else decide (12 ≤ count1312 b))) else (if i < 1325 then decide (13 ≤ count1312 b) else (if i < 1326 then decide (14 ≤ count1312 b) else decide (15 ≤ count1312 b))))))) else (if i < 1350 then (if i < 1338 then (if i < 1332 then (if i < 1329 then (if i < 1328 then decide (1 ≤ count1327 b) else decide (2 ≤ count1327 b)) else (if i < 1330 then decide (1 ≤ count1329 b) else (if i < 1331 then decide (2 ≤ count1329 b) else decide (3 ≤ count1329 b)))) else (if i < 1335 then (if i < 1333 then decide (1 ≤ count1332 b) else (if i < 1334 then decide (2 ≤ count1332 b) else decide (1 ≤ count1334 b))) else (if i < 1336 then decide (2 ≤ count1334 b) else (if i < 1337 then decide (1 ≤ count1336 b) else decide (2 ≤ count1336 b))))) else (if i < 1344 then (if i < 1341 then (if i < 1339 then decide (3 ≤ count1336 b) else (if i < 1340 then decide (4 ≤ count1336 b) else decide (1 ≤ count1340 b))) else (if i < 1342 then decide (2 ≤ count1340 b) else (if i < 1343 then decide (3 ≤ count1340 b) else decide (4 ≤ count1340 b)))) else (if i < 1347 then (if i < 1345 then decide (5 ≤ count1340 b) else (if i < 1346 then decide (6 ≤ count1340 b) else decide (7 ≤ count1340 b))) else (if i < 1348 then decide (1 ≤ count1347 b) else (if i < 1349 then decide (2 ≤ count1347 b) else decide (1 ≤ count1349 b)))))) else (if i < 1361 then (if i < 1355 then (if i < 1352 then (if i < 1351 then decide (2 ≤ count1349 b) else decide (3 ≤ count1349 b)) else (if i < 1353 then decide (1 ≤ count1352 b) else (if i < 1354 then decide (2 ≤ count1352 b) else decide (1 ≤ count1354 b)))) else (if i < 1358 then (if i < 1356 then decide (2 ≤ count1354 b) else (if i < 1357 then decide (1 ≤ count1356 b) else decide (2 ≤ count1356 b))) else (if i < 1359 then decide (3 ≤ count1356 b) else (if i < 1360 then decide (4 ≤ count1356 b) else decide (1 ≤ count1360 b))))) else (if i < 1367 then (if i < 1364 then (if i < 1362 then decide (2 ≤ count1360 b) else (if i < 1363 then decide (3 ≤ count1360 b) else decide (4 ≤ count1360 b))) else (if i < 1365 then decide (5 ≤ count1360 b) else (if i < 1366 then decide (6 ≤ count1360 b) else decide (7 ≤ count1360 b)))) else (if i < 1370 then (if i < 1368 then decide (1 ≤ count1367 b) else (if i < 1369 then decide (2 ≤ count1367 b) else decide (3 ≤ count1367 b))) else (if i < 1371 then decide (4 ≤ count1367 b) else (if i < 1372 then decide (5 ≤ count1367 b) else decide (6 ≤ count1367 b)))))))) else (if i < 1419 then (if i < 1396 then (if i < 1384 then (if i < 1378 then (if i < 1375 then (if i < 1374 then decide (7 ≤ count1367 b) else decide (8 ≤ count1367 b)) else (if i < 1376 then decide (9 ≤ count1367 b) else (if i < 1377 then decide (10 ≤ count1367 b) else decide (11 ≤ count1367 b)))) else (if i < 1381 then (if i < 1379 then decide (12 ≤ count1367 b) else (if i < 1380 then decide (13 ≤ count1367 b) else decide (14 ≤ count1367 b))) else (if i < 1382 then decide (1 ≤ count1381 b) else (if i < 1383 then decide (2 ≤ count1381 b) else decide (1 ≤ count1383 b))))) else (if i < 1390 then (if i < 1387 then (if i < 1385 then decide (2 ≤ count1383 b) else (if i < 1386 then decide (3 ≤ count1383 b) else decide (1 ≤ count1386 b))) else (if i < 1388 then decide (2 ≤ count1386 b) else (if i < 1389 then decide (1 ≤ count1388 b) else decide (2 ≤ count1388 b)))) else (if i < 1393 then (if i < 1391 then decide (1 ≤ count1390 b) else (if i < 1392 then decide (2 ≤ count1390 b) else decide (3 ≤ count1390 b))) else (if i < 1394 then decide (4 ≤ count1390 b) else (if i < 1395 then decide (1 ≤ count1394 b) else decide (2 ≤ count1394 b)))))) else (if i < 1407 then (if i < 1401 then (if i < 1398 then (if i < 1397 then decide (3 ≤ count1394 b) else decide (4 ≤ count1394 b)) else (if i < 1399 then decide (5 ≤ count1394 b) else (if i < 1400 then decide (6 ≤ count1394 b) else decide (7 ≤ count1394 b)))) else (if i < 1404 then (if i < 1402 then decide (1 ≤ count1401 b) else (if i < 1403 then decide (2 ≤ count1401 b) else decide (1 ≤ count1403 b))) else (if i < 1405 then decide (2 ≤ count1403 b) else (if i < 1406 then decide (3 ≤ count1403 b) else decide (1 ≤ count1406 b))))) else (if i < 1413 then (if i < 1410 then (if i < 1408 then decide (2 ≤ count1406 b) else (if i < 1409 then decide (1 ≤ count1408 b) else decide (2 ≤ count1408 b))) else (if i < 1411 then decide (1 ≤ count1410 b) else (if i < 1412 then decide (2 ≤ count1410 b) else decide (3 ≤ count1410 b)))) else (if i < 1416 then (if i < 1414 then decide (4 ≤ count1410 b) else (if i < 1415 then decide (1 ≤ count1414 b) else decide (2 ≤ count1414 b))) else (if i < 1417 then decide (3 ≤ count1414 b) else (if i < 1418 then decide (4 ≤ count1414 b) else decide (5 ≤ count1414 b))))))) else (if i < 1442 then (if i < 1430 then (if i < 1424 then (if i < 1421 then (if i < 1420 then decide (6 ≤ count1414 b) else decide (7 ≤ count1414 b)) else (if i < 1422 then decide (1 ≤ count1421 b) else (if i < 1423 then decide (2 ≤ count1421 b) else decide (3 ≤ count1421 b)))) else (if i < 1427 then (if i < 1425 then decide (4 ≤ count1421 b) else (if i < 1426 then decide (5 ≤ count1421 b) else decide (6 ≤ count1421 b))) else (if i < 1428 then decide (7 ≤ count1421 b) else (if i < 1429 then decide (8 ≤ count1421 b) else decide (9 ≤ count1421 b))))) else (if i < 1436 then (if i < 1433 then (if i < 1431 then decide (10 ≤ count1421 b) else (if i < 1432 then decide (11 ≤ count1421 b) else decide (12 ≤ count1421 b))) else (if i < 1434 then decide (13 ≤ count1421 b) else (if i < 1435 then decide (14 ≤ count1421 b) else decide (1 ≤ count1435 b)))) else (if i < 1439 then (if i < 1437 then decide (2 ≤ count1435 b) else (if i < 1438 then decide (3 ≤ count1435 b) else decide (4 ≤ count1435 b))) else (if i < 1440 then decide (5 ≤ count1435 b) else (if i < 1441 then decide (6 ≤ count1435 b) else decide (7 ≤ count1435 b)))))) else (if i < 1453 then (if i < 1447 then (if i < 1444 then (if i < 1443 then decide (8 ≤ count1435 b) else decide (9 ≤ count1435 b)) else (if i < 1445 then decide (10 ≤ count1435 b) else (if i < 1446 then decide (11 ≤ count1435 b) else decide (12 ≤ count1435 b)))) else (if i < 1450 then (if i < 1448 then decide (13 ≤ count1435 b) else (if i < 1449 then decide (14 ≤ count1435 b) else decide (15 ≤ count1435 b))) else (if i < 1451 then decide (1 ≤ count1450 b) else (if i < 1452 then decide (2 ≤ count1450 b) else decide (3 ≤ count1450 b))))) else (if i < 1459 then (if i < 1456 then (if i < 1454 then decide (4 ≤ count1450 b) else (if i < 1455 then decide (5 ≤ count1450 b) else decide (6 ≤ count1450 b))) else (if i < 1457 then decide (7 ≤ count1450 b) else (if i < 1458 then decide (8 ≤ count1450 b) else decide (9 ≤ count1450 b)))) else (if i < 1462 then (if i < 1460 then decide (10 ≤ count1450 b) else (if i < 1461 then decide (11 ≤ count1450 b) else decide (12 ≤ count1450 b))) else (if i < 1463 then decide (13 ≤ count1450 b) else (if i < 1464 then decide (14 ≤ count1450 b) else decide (15 ≤ count1450 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (6 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (7 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (8 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (10 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (15 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (20 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (21 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (22 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (25 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (26 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (27 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (29 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (96 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (97 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (102 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (103 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (106 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (110 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (111 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (129 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (137 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (139 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (143 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (161 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (168 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (170 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (174 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (175 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (177 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (185 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (186 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (187 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (189 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (192 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (193 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (198 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (200 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (202 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (206 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (207 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (352 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (353 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (355 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (359 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (361 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (363 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (367 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (368 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (370 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (371 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (416 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (417 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (419 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (421 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (423 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (425 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (427 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (429 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (430 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (431 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (432 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (434 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (435 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (440 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (442 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (444 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (445 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (446 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (480 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (481 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (486 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (487 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (488 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (490 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (494 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (495 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (497 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (500 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (501 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (502 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (505 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (506 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (507 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (509 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (7 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (20 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (21 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (26 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (27 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (96 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (97 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (111 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (143 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (170 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (174 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (185 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (187 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (202 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (361 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (363 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (370 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (371 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (423 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (429 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (431 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (444 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (490 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (500 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (505 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (507 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (1 ≤ count211 (baseVal q)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (1 ≤ count213 (baseVal q)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (1 ≤ count215 (baseVal q)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (1 ≤ count217 (baseVal q)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value414 (q : Snake 81) : valuation q 414 = decide (2 ≤ count413 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value697 (q : Snake 81) : valuation q 697 = decide (1 ≤ count697 (baseVal q)) := rfl
theorem value701 (q : Snake 81) : valuation q 701 = decide (2 ≤ count700 (baseVal q)) := rfl
theorem value702 (q : Snake 81) : valuation q 702 = decide (1 ≤ count702 (baseVal q)) := rfl
theorem value704 (q : Snake 81) : valuation q 704 = decide (3 ≤ count702 (baseVal q)) := rfl
theorem value705 (q : Snake 81) : valuation q 705 = decide (1 ≤ count705 (baseVal q)) := rfl
theorem value706 (q : Snake 81) : valuation q 706 = decide (2 ≤ count705 (baseVal q)) := rfl
theorem value707 (q : Snake 81) : valuation q 707 = decide (3 ≤ count705 (baseVal q)) := rfl
theorem value711 (q : Snake 81) : valuation q 711 = decide (1 ≤ count711 (baseVal q)) := rfl
theorem value712 (q : Snake 81) : valuation q 712 = decide (2 ≤ count711 (baseVal q)) := rfl
theorem value713 (q : Snake 81) : valuation q 713 = decide (1 ≤ count713 (baseVal q)) := rfl
theorem value714 (q : Snake 81) : valuation q 714 = decide (2 ≤ count713 (baseVal q)) := rfl
theorem value716 (q : Snake 81) : valuation q 716 = decide (1 ≤ count716 (baseVal q)) := rfl
theorem value718 (q : Snake 81) : valuation q 718 = decide (1 ≤ count718 (baseVal q)) := rfl
theorem value721 (q : Snake 81) : valuation q 721 = decide (1 ≤ count721 (baseVal q)) := rfl
theorem value722 (q : Snake 81) : valuation q 722 = decide (2 ≤ count721 (baseVal q)) := rfl
theorem value727 (q : Snake 81) : valuation q 727 = decide (1 ≤ count727 (baseVal q)) := rfl
theorem value728 (q : Snake 81) : valuation q 728 = decide (2 ≤ count727 (baseVal q)) := rfl
theorem value729 (q : Snake 81) : valuation q 729 = decide (3 ≤ count727 (baseVal q)) := rfl
theorem value730 (q : Snake 81) : valuation q 730 = decide (4 ≤ count727 (baseVal q)) := rfl
theorem value737 (q : Snake 81) : valuation q 737 = decide (1 ≤ count737 (baseVal q)) := rfl
theorem value739 (q : Snake 81) : valuation q 739 = decide (1 ≤ count739 (baseVal q)) := rfl
theorem value742 (q : Snake 81) : valuation q 742 = decide (1 ≤ count742 (baseVal q)) := rfl
theorem value743 (q : Snake 81) : valuation q 743 = decide (2 ≤ count742 (baseVal q)) := rfl
theorem value744 (q : Snake 81) : valuation q 744 = decide (1 ≤ count744 (baseVal q)) := rfl
theorem value745 (q : Snake 81) : valuation q 745 = decide (2 ≤ count744 (baseVal q)) := rfl
theorem value747 (q : Snake 81) : valuation q 747 = decide (1 ≤ count747 (baseVal q)) := rfl
theorem value748 (q : Snake 81) : valuation q 748 = decide (2 ≤ count747 (baseVal q)) := rfl
theorem value749 (q : Snake 81) : valuation q 749 = decide (3 ≤ count747 (baseVal q)) := rfl
theorem value753 (q : Snake 81) : valuation q 753 = decide (1 ≤ count753 (baseVal q)) := rfl
theorem value754 (q : Snake 81) : valuation q 754 = decide (2 ≤ count753 (baseVal q)) := rfl
theorem value755 (q : Snake 81) : valuation q 755 = decide (1 ≤ count755 (baseVal q)) := rfl
theorem value756 (q : Snake 81) : valuation q 756 = decide (2 ≤ count755 (baseVal q)) := rfl
theorem value757 (q : Snake 81) : valuation q 757 = decide (3 ≤ count755 (baseVal q)) := rfl
theorem value758 (q : Snake 81) : valuation q 758 = decide (1 ≤ count758 (baseVal q)) := rfl
theorem value759 (q : Snake 81) : valuation q 759 = decide (2 ≤ count758 (baseVal q)) := rfl
theorem value760 (q : Snake 81) : valuation q 760 = decide (1 ≤ count760 (baseVal q)) := rfl
theorem value762 (q : Snake 81) : valuation q 762 = decide (1 ≤ count762 (baseVal q)) := rfl
theorem value763 (q : Snake 81) : valuation q 763 = decide (2 ≤ count762 (baseVal q)) := rfl
theorem value766 (q : Snake 81) : valuation q 766 = decide (1 ≤ count766 (baseVal q)) := rfl
theorem value767 (q : Snake 81) : valuation q 767 = decide (2 ≤ count766 (baseVal q)) := rfl
theorem value768 (q : Snake 81) : valuation q 768 = decide (3 ≤ count766 (baseVal q)) := rfl
theorem value773 (q : Snake 81) : valuation q 773 = decide (1 ≤ count773 (baseVal q)) := rfl
theorem value774 (q : Snake 81) : valuation q 774 = decide (2 ≤ count773 (baseVal q)) := rfl
theorem value775 (q : Snake 81) : valuation q 775 = decide (3 ≤ count773 (baseVal q)) := rfl
theorem value776 (q : Snake 81) : valuation q 776 = decide (4 ≤ count773 (baseVal q)) := rfl
theorem value777 (q : Snake 81) : valuation q 777 = decide (5 ≤ count773 (baseVal q)) := rfl
theorem value783 (q : Snake 81) : valuation q 783 = decide (1 ≤ count783 (baseVal q)) := rfl
theorem value784 (q : Snake 81) : valuation q 784 = decide (2 ≤ count783 (baseVal q)) := rfl
theorem value785 (q : Snake 81) : valuation q 785 = decide (3 ≤ count783 (baseVal q)) := rfl
theorem value786 (q : Snake 81) : valuation q 786 = decide (4 ≤ count783 (baseVal q)) := rfl
theorem value787 (q : Snake 81) : valuation q 787 = decide (5 ≤ count783 (baseVal q)) := rfl
theorem value789 (q : Snake 81) : valuation q 789 = decide (7 ≤ count783 (baseVal q)) := rfl
theorem value798 (q : Snake 81) : valuation q 798 = decide (1 ≤ count798 (baseVal q)) := rfl
theorem value799 (q : Snake 81) : valuation q 799 = decide (2 ≤ count798 (baseVal q)) := rfl
theorem value800 (q : Snake 81) : valuation q 800 = decide (1 ≤ count800 (baseVal q)) := rfl
theorem value801 (q : Snake 81) : valuation q 801 = decide (2 ≤ count800 (baseVal q)) := rfl
theorem value802 (q : Snake 81) : valuation q 802 = decide (3 ≤ count800 (baseVal q)) := rfl
theorem value803 (q : Snake 81) : valuation q 803 = decide (1 ≤ count803 (baseVal q)) := rfl
theorem value804 (q : Snake 81) : valuation q 804 = decide (2 ≤ count803 (baseVal q)) := rfl
theorem value805 (q : Snake 81) : valuation q 805 = decide (3 ≤ count803 (baseVal q)) := rfl
theorem value809 (q : Snake 81) : valuation q 809 = decide (1 ≤ count809 (baseVal q)) := rfl
theorem value810 (q : Snake 81) : valuation q 810 = decide (2 ≤ count809 (baseVal q)) := rfl
theorem value811 (q : Snake 81) : valuation q 811 = decide (1 ≤ count811 (baseVal q)) := rfl
theorem value812 (q : Snake 81) : valuation q 812 = decide (2 ≤ count811 (baseVal q)) := rfl
theorem value814 (q : Snake 81) : valuation q 814 = decide (1 ≤ count814 (baseVal q)) := rfl
theorem value815 (q : Snake 81) : valuation q 815 = decide (2 ≤ count814 (baseVal q)) := rfl
theorem value816 (q : Snake 81) : valuation q 816 = decide (1 ≤ count816 (baseVal q)) := rfl
theorem value817 (q : Snake 81) : valuation q 817 = decide (2 ≤ count816 (baseVal q)) := rfl
theorem value818 (q : Snake 81) : valuation q 818 = decide (3 ≤ count816 (baseVal q)) := rfl
theorem value819 (q : Snake 81) : valuation q 819 = decide (1 ≤ count819 (baseVal q)) := rfl
theorem value820 (q : Snake 81) : valuation q 820 = decide (2 ≤ count819 (baseVal q)) := rfl
theorem value821 (q : Snake 81) : valuation q 821 = decide (3 ≤ count819 (baseVal q)) := rfl
theorem value822 (q : Snake 81) : valuation q 822 = decide (4 ≤ count819 (baseVal q)) := rfl
theorem value826 (q : Snake 81) : valuation q 826 = decide (2 ≤ count825 (baseVal q)) := rfl
theorem value827 (q : Snake 81) : valuation q 827 = decide (3 ≤ count825 (baseVal q)) := rfl
theorem value828 (q : Snake 81) : valuation q 828 = decide (4 ≤ count825 (baseVal q)) := rfl
theorem value829 (q : Snake 81) : valuation q 829 = decide (5 ≤ count825 (baseVal q)) := rfl
theorem value835 (q : Snake 81) : valuation q 835 = decide (1 ≤ count835 (baseVal q)) := rfl
theorem value836 (q : Snake 81) : valuation q 836 = decide (2 ≤ count835 (baseVal q)) := rfl
theorem value837 (q : Snake 81) : valuation q 837 = decide (1 ≤ count837 (baseVal q)) := rfl
theorem value838 (q : Snake 81) : valuation q 838 = decide (2 ≤ count837 (baseVal q)) := rfl
theorem value840 (q : Snake 81) : valuation q 840 = decide (1 ≤ count840 (baseVal q)) := rfl
theorem value841 (q : Snake 81) : valuation q 841 = decide (2 ≤ count840 (baseVal q)) := rfl
theorem value842 (q : Snake 81) : valuation q 842 = decide (1 ≤ count842 (baseVal q)) := rfl
theorem value843 (q : Snake 81) : valuation q 843 = decide (2 ≤ count842 (baseVal q)) := rfl
theorem value845 (q : Snake 81) : valuation q 845 = decide (1 ≤ count845 (baseVal q)) := rfl
theorem value846 (q : Snake 81) : valuation q 846 = decide (2 ≤ count845 (baseVal q)) := rfl
theorem value847 (q : Snake 81) : valuation q 847 = decide (3 ≤ count845 (baseVal q)) := rfl
theorem value851 (q : Snake 81) : valuation q 851 = decide (1 ≤ count851 (baseVal q)) := rfl
theorem value852 (q : Snake 81) : valuation q 852 = decide (2 ≤ count851 (baseVal q)) := rfl
theorem value853 (q : Snake 81) : valuation q 853 = decide (1 ≤ count853 (baseVal q)) := rfl
theorem value854 (q : Snake 81) : valuation q 854 = decide (2 ≤ count853 (baseVal q)) := rfl
theorem value856 (q : Snake 81) : valuation q 856 = decide (1 ≤ count856 (baseVal q)) := rfl
theorem value858 (q : Snake 81) : valuation q 858 = decide (1 ≤ count858 (baseVal q)) := rfl
theorem value859 (q : Snake 81) : valuation q 859 = decide (2 ≤ count858 (baseVal q)) := rfl
theorem value860 (q : Snake 81) : valuation q 860 = decide (1 ≤ count860 (baseVal q)) := rfl
theorem value861 (q : Snake 81) : valuation q 861 = decide (2 ≤ count860 (baseVal q)) := rfl
theorem value864 (q : Snake 81) : valuation q 864 = decide (1 ≤ count864 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (2 ≤ count864 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (3 ≤ count864 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (1 ≤ count871 (baseVal q)) := rfl
theorem value872 (q : Snake 81) : valuation q 872 = decide (2 ≤ count871 (baseVal q)) := rfl
theorem value873 (q : Snake 81) : valuation q 873 = decide (3 ≤ count871 (baseVal q)) := rfl
theorem value874 (q : Snake 81) : valuation q 874 = decide (4 ≤ count871 (baseVal q)) := rfl
theorem value883 (q : Snake 81) : valuation q 883 = decide (3 ≤ count881 (baseVal q)) := rfl
theorem value885 (q : Snake 81) : valuation q 885 = decide (5 ≤ count881 (baseVal q)) := rfl
theorem value886 (q : Snake 81) : valuation q 886 = decide (6 ≤ count881 (baseVal q)) := rfl
theorem value887 (q : Snake 81) : valuation q 887 = decide (7 ≤ count881 (baseVal q)) := rfl
theorem value888 (q : Snake 81) : valuation q 888 = decide (8 ≤ count881 (baseVal q)) := rfl
theorem value889 (q : Snake 81) : valuation q 889 = decide (9 ≤ count881 (baseVal q)) := rfl
theorem value900 (q : Snake 81) : valuation q 900 = decide (10 ≤ count891 (baseVal q)) := rfl
theorem meaningNeg105 (b : Nat → Bool) : literal (valuationOf b) (-105) = decide (1 ≤ countLit b [-105]) := by
  change literal b (-105) = decide (1 ≤ countLit b [-105])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-105) <;> decide
theorem meaningNeg104 (b : Nat → Bool) : literal (valuationOf b) (-104) = decide (1 ≤ countLit b [-104]) := by
  change literal b (-104) = decide (1 ≤ countLit b [-104])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-104) <;> decide
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
theorem meaningNeg95 (b : Nat → Bool) : literal (valuationOf b) (-95) = decide (1 ≤ countLit b [-95]) := by
  change literal b (-95) = decide (1 ≤ countLit b [-95])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-95) <;> decide
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
theorem meaningNeg87 (b : Nat → Bool) : literal (valuationOf b) (-87) = decide (1 ≤ countLit b [-87]) := by
  change literal b (-87) = decide (1 ≤ countLit b [-87])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-87) <;> decide
theorem meaningNeg86 (b : Nat → Bool) : literal (valuationOf b) (-86) = decide (1 ≤ countLit b [-86]) := by
  change literal b (-86) = decide (1 ≤ countLit b [-86])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-86) <;> decide
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
theorem meaningNeg71 (b : Nat → Bool) : literal (valuationOf b) (-71) = decide (1 ≤ countLit b [-71]) := by
  change literal b (-71) = decide (1 ≤ countLit b [-71])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-71) <;> decide
theorem meaningNeg67 (b : Nat → Bool) : literal (valuationOf b) (-67) = decide (1 ≤ countLit b [-67]) := by
  change literal b (-67) = decide (1 ≤ countLit b [-67])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-67) <;> decide
theorem meaningNeg65 (b : Nat → Bool) : literal (valuationOf b) (-65) = decide (1 ≤ countLit b [-65]) := by
  change literal b (-65) = decide (1 ≤ countLit b [-65])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-65) <;> decide
theorem meaningNeg62 (b : Nat → Bool) : literal (valuationOf b) (-62) = decide (1 ≤ countLit b [-62]) := by
  change literal b (-62) = decide (1 ≤ countLit b [-62])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-62) <;> decide
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
theorem meaningNeg17 (b : Nat → Bool) : literal (valuationOf b) (-17) = decide (1 ≤ countLit b [-17]) := by
  change literal b (-17) = decide (1 ≤ countLit b [-17])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-17) <;> decide
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
theorem meaningNeg13 (b : Nat → Bool) : literal (valuationOf b) (-13) = decide (1 ≤ countLit b [-13]) := by
  change literal b (-13) = decide (1 ≤ countLit b [-13])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-13) <;> decide
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
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
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
theorem meaning110 (b : Nat → Bool) : literal (valuationOf b) (110) = decide (1 ≤ countLit b [110]) := by
  change literal b (110) = decide (1 ≤ countLit b [110])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (110) <;> decide
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
theorem meaning121 (b : Nat → Bool) : literal (valuationOf b) (121) = decide (1 ≤ countLit b [121]) := by
  change literal b (121) = decide (1 ≤ countLit b [121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (121) <;> decide
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
theorem meaning154 (b : Nat → Bool) : literal (valuationOf b) (154) = decide (1 ≤ countLit b [154]) := by
  change literal b (154) = decide (1 ≤ countLit b [154])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (154) <;> decide
theorem meaning168 (b : Nat → Bool) : literal (valuationOf b) (168) = decide (1 ≤ countLit b [168]) := by
  change literal b (168) = decide (1 ≤ countLit b [168])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (168) <;> decide
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
theorem meaning186 (b : Nat → Bool) : literal (valuationOf b) (186) = decide (1 ≤ countLit b [186]) := by
  change literal b (186) = decide (1 ≤ countLit b [186])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (186) <;> decide
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
theorem meaning207 (b : Nat → Bool) : literal (valuationOf b) (207) = decide (1 ≤ countLit b [207]) := by
  change literal b (207) = decide (1 ≤ countLit b [207])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (207) <;> decide
theorem meaning208 (b : Nat → Bool) : literal (valuationOf b) (208) = decide (1 ≤ countLit b [208]) := by
  change literal b (208) = decide (1 ≤ countLit b [208])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (208) <;> decide
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) 211 = decide (1 ≤ count211 b) := rfl
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) 213 = decide (1 ≤ count213 b) := rfl
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) 215 = decide (1 ≤ count215 b) := rfl
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) 217 = decide (1 ≤ count217 b) := rfl
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning414 (b : Nat → Bool) : literal (valuationOf b) 414 = decide (2 ≤ count413 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning697 (b : Nat → Bool) : literal (valuationOf b) 697 = decide (1 ≤ count697 b) := rfl
theorem meaning701 (b : Nat → Bool) : literal (valuationOf b) 701 = decide (2 ≤ count700 b) := rfl
theorem meaning702 (b : Nat → Bool) : literal (valuationOf b) 702 = decide (1 ≤ count702 b) := rfl
theorem meaning704 (b : Nat → Bool) : literal (valuationOf b) 704 = decide (3 ≤ count702 b) := rfl
theorem meaning705 (b : Nat → Bool) : literal (valuationOf b) 705 = decide (1 ≤ count705 b) := rfl
theorem meaning706 (b : Nat → Bool) : literal (valuationOf b) 706 = decide (2 ≤ count705 b) := rfl
theorem meaning707 (b : Nat → Bool) : literal (valuationOf b) 707 = decide (3 ≤ count705 b) := rfl
theorem meaning711 (b : Nat → Bool) : literal (valuationOf b) 711 = decide (1 ≤ count711 b) := rfl
theorem meaning712 (b : Nat → Bool) : literal (valuationOf b) 712 = decide (2 ≤ count711 b) := rfl
theorem meaning713 (b : Nat → Bool) : literal (valuationOf b) 713 = decide (1 ≤ count713 b) := rfl
theorem meaning714 (b : Nat → Bool) : literal (valuationOf b) 714 = decide (2 ≤ count713 b) := rfl
theorem meaning716 (b : Nat → Bool) : literal (valuationOf b) 716 = decide (1 ≤ count716 b) := rfl
theorem meaning718 (b : Nat → Bool) : literal (valuationOf b) 718 = decide (1 ≤ count718 b) := rfl
theorem meaning721 (b : Nat → Bool) : literal (valuationOf b) 721 = decide (1 ≤ count721 b) := rfl
theorem meaning722 (b : Nat → Bool) : literal (valuationOf b) 722 = decide (2 ≤ count721 b) := rfl
theorem meaning727 (b : Nat → Bool) : literal (valuationOf b) 727 = decide (1 ≤ count727 b) := rfl
theorem meaning728 (b : Nat → Bool) : literal (valuationOf b) 728 = decide (2 ≤ count727 b) := rfl
theorem meaning729 (b : Nat → Bool) : literal (valuationOf b) 729 = decide (3 ≤ count727 b) := rfl
theorem meaning730 (b : Nat → Bool) : literal (valuationOf b) 730 = decide (4 ≤ count727 b) := rfl
theorem meaning737 (b : Nat → Bool) : literal (valuationOf b) 737 = decide (1 ≤ count737 b) := rfl
theorem meaning739 (b : Nat → Bool) : literal (valuationOf b) 739 = decide (1 ≤ count739 b) := rfl
theorem meaning742 (b : Nat → Bool) : literal (valuationOf b) 742 = decide (1 ≤ count742 b) := rfl
theorem meaning743 (b : Nat → Bool) : literal (valuationOf b) 743 = decide (2 ≤ count742 b) := rfl
theorem meaning744 (b : Nat → Bool) : literal (valuationOf b) 744 = decide (1 ≤ count744 b) := rfl
theorem meaning745 (b : Nat → Bool) : literal (valuationOf b) 745 = decide (2 ≤ count744 b) := rfl
theorem meaning747 (b : Nat → Bool) : literal (valuationOf b) 747 = decide (1 ≤ count747 b) := rfl
theorem meaning748 (b : Nat → Bool) : literal (valuationOf b) 748 = decide (2 ≤ count747 b) := rfl
theorem meaning749 (b : Nat → Bool) : literal (valuationOf b) 749 = decide (3 ≤ count747 b) := rfl
theorem meaning753 (b : Nat → Bool) : literal (valuationOf b) 753 = decide (1 ≤ count753 b) := rfl
theorem meaning754 (b : Nat → Bool) : literal (valuationOf b) 754 = decide (2 ≤ count753 b) := rfl
theorem meaning755 (b : Nat → Bool) : literal (valuationOf b) 755 = decide (1 ≤ count755 b) := rfl
theorem meaning756 (b : Nat → Bool) : literal (valuationOf b) 756 = decide (2 ≤ count755 b) := rfl
theorem meaning757 (b : Nat → Bool) : literal (valuationOf b) 757 = decide (3 ≤ count755 b) := rfl
theorem meaning758 (b : Nat → Bool) : literal (valuationOf b) 758 = decide (1 ≤ count758 b) := rfl
theorem meaning759 (b : Nat → Bool) : literal (valuationOf b) 759 = decide (2 ≤ count758 b) := rfl
theorem meaning760 (b : Nat → Bool) : literal (valuationOf b) 760 = decide (1 ≤ count760 b) := rfl
theorem meaning762 (b : Nat → Bool) : literal (valuationOf b) 762 = decide (1 ≤ count762 b) := rfl
theorem meaning763 (b : Nat → Bool) : literal (valuationOf b) 763 = decide (2 ≤ count762 b) := rfl
theorem meaning766 (b : Nat → Bool) : literal (valuationOf b) 766 = decide (1 ≤ count766 b) := rfl
theorem meaning767 (b : Nat → Bool) : literal (valuationOf b) 767 = decide (2 ≤ count766 b) := rfl
theorem meaning768 (b : Nat → Bool) : literal (valuationOf b) 768 = decide (3 ≤ count766 b) := rfl
theorem meaning773 (b : Nat → Bool) : literal (valuationOf b) 773 = decide (1 ≤ count773 b) := rfl
theorem meaning774 (b : Nat → Bool) : literal (valuationOf b) 774 = decide (2 ≤ count773 b) := rfl
theorem meaning775 (b : Nat → Bool) : literal (valuationOf b) 775 = decide (3 ≤ count773 b) := rfl
theorem meaning776 (b : Nat → Bool) : literal (valuationOf b) 776 = decide (4 ≤ count773 b) := rfl
theorem meaning777 (b : Nat → Bool) : literal (valuationOf b) 777 = decide (5 ≤ count773 b) := rfl
theorem meaning783 (b : Nat → Bool) : literal (valuationOf b) 783 = decide (1 ≤ count783 b) := rfl
theorem meaning784 (b : Nat → Bool) : literal (valuationOf b) 784 = decide (2 ≤ count783 b) := rfl
theorem meaning785 (b : Nat → Bool) : literal (valuationOf b) 785 = decide (3 ≤ count783 b) := rfl
theorem meaning786 (b : Nat → Bool) : literal (valuationOf b) 786 = decide (4 ≤ count783 b) := rfl
theorem meaning787 (b : Nat → Bool) : literal (valuationOf b) 787 = decide (5 ≤ count783 b) := rfl
theorem meaning789 (b : Nat → Bool) : literal (valuationOf b) 789 = decide (7 ≤ count783 b) := rfl
theorem meaning798 (b : Nat → Bool) : literal (valuationOf b) 798 = decide (1 ≤ count798 b) := rfl
theorem meaning799 (b : Nat → Bool) : literal (valuationOf b) 799 = decide (2 ≤ count798 b) := rfl
theorem meaning800 (b : Nat → Bool) : literal (valuationOf b) 800 = decide (1 ≤ count800 b) := rfl
theorem meaning801 (b : Nat → Bool) : literal (valuationOf b) 801 = decide (2 ≤ count800 b) := rfl
theorem meaning802 (b : Nat → Bool) : literal (valuationOf b) 802 = decide (3 ≤ count800 b) := rfl
theorem meaning803 (b : Nat → Bool) : literal (valuationOf b) 803 = decide (1 ≤ count803 b) := rfl
theorem meaning804 (b : Nat → Bool) : literal (valuationOf b) 804 = decide (2 ≤ count803 b) := rfl
theorem meaning805 (b : Nat → Bool) : literal (valuationOf b) 805 = decide (3 ≤ count803 b) := rfl
theorem meaning809 (b : Nat → Bool) : literal (valuationOf b) 809 = decide (1 ≤ count809 b) := rfl
theorem meaning810 (b : Nat → Bool) : literal (valuationOf b) 810 = decide (2 ≤ count809 b) := rfl
theorem meaning811 (b : Nat → Bool) : literal (valuationOf b) 811 = decide (1 ≤ count811 b) := rfl
theorem meaning812 (b : Nat → Bool) : literal (valuationOf b) 812 = decide (2 ≤ count811 b) := rfl
theorem meaning814 (b : Nat → Bool) : literal (valuationOf b) 814 = decide (1 ≤ count814 b) := rfl
theorem meaning815 (b : Nat → Bool) : literal (valuationOf b) 815 = decide (2 ≤ count814 b) := rfl
theorem meaning816 (b : Nat → Bool) : literal (valuationOf b) 816 = decide (1 ≤ count816 b) := rfl
theorem meaning817 (b : Nat → Bool) : literal (valuationOf b) 817 = decide (2 ≤ count816 b) := rfl
theorem meaning818 (b : Nat → Bool) : literal (valuationOf b) 818 = decide (3 ≤ count816 b) := rfl
theorem meaning819 (b : Nat → Bool) : literal (valuationOf b) 819 = decide (1 ≤ count819 b) := rfl
theorem meaning820 (b : Nat → Bool) : literal (valuationOf b) 820 = decide (2 ≤ count819 b) := rfl
theorem meaning821 (b : Nat → Bool) : literal (valuationOf b) 821 = decide (3 ≤ count819 b) := rfl
theorem meaning822 (b : Nat → Bool) : literal (valuationOf b) 822 = decide (4 ≤ count819 b) := rfl
theorem meaning826 (b : Nat → Bool) : literal (valuationOf b) 826 = decide (2 ≤ count825 b) := rfl
theorem meaning827 (b : Nat → Bool) : literal (valuationOf b) 827 = decide (3 ≤ count825 b) := rfl
theorem meaning828 (b : Nat → Bool) : literal (valuationOf b) 828 = decide (4 ≤ count825 b) := rfl
theorem meaning829 (b : Nat → Bool) : literal (valuationOf b) 829 = decide (5 ≤ count825 b) := rfl
theorem meaning835 (b : Nat → Bool) : literal (valuationOf b) 835 = decide (1 ≤ count835 b) := rfl
theorem meaning836 (b : Nat → Bool) : literal (valuationOf b) 836 = decide (2 ≤ count835 b) := rfl
theorem meaning837 (b : Nat → Bool) : literal (valuationOf b) 837 = decide (1 ≤ count837 b) := rfl
theorem meaning838 (b : Nat → Bool) : literal (valuationOf b) 838 = decide (2 ≤ count837 b) := rfl
theorem meaning840 (b : Nat → Bool) : literal (valuationOf b) 840 = decide (1 ≤ count840 b) := rfl
theorem meaning841 (b : Nat → Bool) : literal (valuationOf b) 841 = decide (2 ≤ count840 b) := rfl
theorem meaning842 (b : Nat → Bool) : literal (valuationOf b) 842 = decide (1 ≤ count842 b) := rfl
theorem meaning843 (b : Nat → Bool) : literal (valuationOf b) 843 = decide (2 ≤ count842 b) := rfl
theorem meaning845 (b : Nat → Bool) : literal (valuationOf b) 845 = decide (1 ≤ count845 b) := rfl
theorem meaning846 (b : Nat → Bool) : literal (valuationOf b) 846 = decide (2 ≤ count845 b) := rfl
theorem meaning847 (b : Nat → Bool) : literal (valuationOf b) 847 = decide (3 ≤ count845 b) := rfl
theorem meaning851 (b : Nat → Bool) : literal (valuationOf b) 851 = decide (1 ≤ count851 b) := rfl
theorem meaning852 (b : Nat → Bool) : literal (valuationOf b) 852 = decide (2 ≤ count851 b) := rfl
theorem meaning853 (b : Nat → Bool) : literal (valuationOf b) 853 = decide (1 ≤ count853 b) := rfl
theorem meaning854 (b : Nat → Bool) : literal (valuationOf b) 854 = decide (2 ≤ count853 b) := rfl
theorem meaning856 (b : Nat → Bool) : literal (valuationOf b) 856 = decide (1 ≤ count856 b) := rfl
theorem meaning858 (b : Nat → Bool) : literal (valuationOf b) 858 = decide (1 ≤ count858 b) := rfl
theorem meaning859 (b : Nat → Bool) : literal (valuationOf b) 859 = decide (2 ≤ count858 b) := rfl
theorem meaning860 (b : Nat → Bool) : literal (valuationOf b) 860 = decide (1 ≤ count860 b) := rfl
theorem meaning861 (b : Nat → Bool) : literal (valuationOf b) 861 = decide (2 ≤ count860 b) := rfl
theorem meaning864 (b : Nat → Bool) : literal (valuationOf b) 864 = decide (1 ≤ count864 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (2 ≤ count864 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (3 ≤ count864 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (1 ≤ count871 b) := rfl
theorem meaning872 (b : Nat → Bool) : literal (valuationOf b) 872 = decide (2 ≤ count871 b) := rfl
theorem meaning873 (b : Nat → Bool) : literal (valuationOf b) 873 = decide (3 ≤ count871 b) := rfl
theorem meaning874 (b : Nat → Bool) : literal (valuationOf b) 874 = decide (4 ≤ count871 b) := rfl
theorem meaning883 (b : Nat → Bool) : literal (valuationOf b) 883 = decide (3 ≤ count881 b) := rfl
theorem meaning885 (b : Nat → Bool) : literal (valuationOf b) 885 = decide (5 ≤ count881 b) := rfl
theorem meaning886 (b : Nat → Bool) : literal (valuationOf b) 886 = decide (6 ≤ count881 b) := rfl
theorem meaning887 (b : Nat → Bool) : literal (valuationOf b) 887 = decide (7 ≤ count881 b) := rfl
theorem meaning888 (b : Nat → Bool) : literal (valuationOf b) 888 = decide (8 ≤ count881 b) := rfl
theorem meaning889 (b : Nat → Bool) : literal (valuationOf b) 889 = decide (9 ≤ count881 b) := rfl
theorem meaning900 (b : Nat → Bool) : literal (valuationOf b) 900 = decide (10 ≤ count891 b) := rfl
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
end Snake9.Regrowth.E112075
