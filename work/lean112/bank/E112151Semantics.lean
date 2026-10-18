import E112151Data
namespace Snake9.Regrowth.E112151
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 107 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (2 : Vertex)))) else (if i < 4 then decide (InPath q (18 : Vertex)) else (if i < 5 then decide (InPath q (26 : Vertex)) else decide (InPath q (58 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (115 : Vertex)) else (if i < 8 then decide (InPath q (119 : Vertex)) else decide (InPath q (122 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (123 : Vertex)) else decide (InPath q (160 : Vertex))) else (if i < 12 then decide (InPath q (161 : Vertex)) else decide (InPath q (162 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (166 : Vertex)) else (if i < 15 then decide (InPath q (172 : Vertex)) else decide (InPath q (173 : Vertex)))) else (if i < 17 then decide (InPath q (174 : Vertex)) else (if i < 18 then decide (InPath q (178 : Vertex)) else decide (InPath q (179 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (181 : Vertex)) else (if i < 21 then decide (InPath q (183 : Vertex)) else decide (InPath q (186 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (187 : Vertex)) else decide (InPath q (188 : Vertex))) else (if i < 25 then decide (InPath q (189 : Vertex)) else decide (InPath q (192 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (193 : Vertex)) else (if i < 28 then decide (InPath q (194 : Vertex)) else decide (InPath q (198 : Vertex)))) else (if i < 30 then decide (InPath q (201 : Vertex)) else (if i < 31 then decide (InPath q (204 : Vertex)) else decide (InPath q (205 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (206 : Vertex)) else (if i < 34 then decide (InPath q (210 : Vertex)) else decide (InPath q (211 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (213 : Vertex)) else decide (InPath q (215 : Vertex))) else (if i < 38 then decide (InPath q (218 : Vertex)) else decide (InPath q (219 : Vertex)))))) else (if i < 46 then (if i < 42 then (if i < 40 then decide (InPath q (220 : Vertex)) else (if i < 41 then decide (InPath q (221 : Vertex)) else decide (InPath q (257 : Vertex)))) else (if i < 44 then (if i < 43 then decide (InPath q (260 : Vertex)) else decide (InPath q (261 : Vertex))) else (if i < 45 then decide (InPath q (262 : Vertex)) else decide (InPath q (263 : Vertex))))) else (if i < 49 then (if i < 47 then decide (InPath q (264 : Vertex)) else (if i < 48 then decide (InPath q (265 : Vertex)) else decide (InPath q (266 : Vertex)))) else (if i < 51 then (if i < 50 then decide (InPath q (267 : Vertex)) else decide (InPath q (271 : Vertex))) else (if i < 52 then decide (InPath q (274 : Vertex)) else decide (InPath q (276 : Vertex)))))))) else (if i < 80 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then decide (InPath q (278 : Vertex)) else (if i < 55 then decide (InPath q (280 : Vertex)) else decide (InPath q (281 : Vertex)))) else (if i < 57 then decide (InPath q (282 : Vertex)) else (if i < 58 then decide (InPath q (283 : Vertex)) else decide (InPath q (284 : Vertex))))) else (if i < 62 then (if i < 60 then decide (InPath q (320 : Vertex)) else (if i < 61 then decide (InPath q (321 : Vertex)) else decide (InPath q (322 : Vertex)))) else (if i < 64 then (if i < 63 then decide (InPath q (326 : Vertex)) else decide (InPath q (329 : Vertex))) else (if i < 65 then decide (InPath q (332 : Vertex)) else decide (InPath q (333 : Vertex)))))) else (if i < 73 then (if i < 69 then (if i < 67 then decide (InPath q (334 : Vertex)) else (if i < 68 then decide (InPath q (338 : Vertex)) else decide (InPath q (339 : Vertex)))) else (if i < 71 then (if i < 70 then decide (InPath q (341 : Vertex)) else decide (InPath q (343 : Vertex))) else (if i < 72 then decide (InPath q (346 : Vertex)) else decide (InPath q (347 : Vertex))))) else (if i < 76 then (if i < 74 then decide (InPath q (348 : Vertex)) else (if i < 75 then decide (InPath q (349 : Vertex)) else decide (InPath q (417 : Vertex)))) else (if i < 78 then (if i < 77 then decide (InPath q (420 : Vertex)) else decide (InPath q (421 : Vertex))) else (if i < 79 then decide (InPath q (422 : Vertex)) else decide (InPath q (423 : Vertex))))))) else (if i < 93 then (if i < 86 then (if i < 83 then (if i < 81 then decide (InPath q (424 : Vertex)) else (if i < 82 then decide (InPath q (425 : Vertex)) else decide (InPath q (426 : Vertex)))) else (if i < 84 then decide (InPath q (427 : Vertex)) else (if i < 85 then decide (InPath q (431 : Vertex)) else decide (InPath q (434 : Vertex))))) else (if i < 89 then (if i < 87 then decide (InPath q (436 : Vertex)) else (if i < 88 then decide (InPath q (438 : Vertex)) else decide (InPath q (440 : Vertex)))) else (if i < 91 then (if i < 90 then decide (InPath q (441 : Vertex)) else decide (InPath q (442 : Vertex))) else (if i < 92 then decide (InPath q (443 : Vertex)) else decide (InPath q (444 : Vertex)))))) else (if i < 100 then (if i < 96 then (if i < 94 then decide (InPath q (456 : Vertex)) else (if i < 95 then decide (InPath q (457 : Vertex)) else decide (InPath q (458 : Vertex)))) else (if i < 98 then (if i < 97 then decide (InPath q (473 : Vertex)) else decide (InPath q (474 : Vertex))) else (if i < 99 then decide (InPath q (480 : Vertex)) else decide (InPath q (482 : Vertex))))) else (if i < 103 then (if i < 101 then decide (InPath q (486 : Vertex)) else (if i < 102 then decide (InPath q (489 : Vertex)) else decide (InPath q (492 : Vertex)))) else (if i < 105 then (if i < 104 then decide (InPath q (493 : Vertex)) else decide (InPath q (494 : Vertex))) else (if i < 106 then decide (InPath q (498 : Vertex)) else decide (InPath q (506 : Vertex))))))))) else (if i < 161 then (if i < 134 then (if i < 120 then (if i < 113 then (if i < 110 then (if i < 108 then decide (InPath q (508 : Vertex)) else (if i < 109 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (2 : Vertex)))) else (if i < 111 then decide (BallClauseLogic.Endpoint q (18 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (26 : Vertex)) else decide (BallClauseLogic.Endpoint q (58 : Vertex))))) else (if i < 116 then (if i < 114 then decide (BallClauseLogic.Endpoint q (115 : Vertex)) else (if i < 115 then decide (BallClauseLogic.Endpoint q (119 : Vertex)) else decide (BallClauseLogic.Endpoint q (122 : Vertex)))) else (if i < 118 then (if i < 117 then decide (BallClauseLogic.Endpoint q (123 : Vertex)) else decide (BallClauseLogic.Endpoint q (160 : Vertex))) else (if i < 119 then decide (BallClauseLogic.Endpoint q (161 : Vertex)) else decide (BallClauseLogic.Endpoint q (162 : Vertex)))))) else (if i < 127 then (if i < 123 then (if i < 121 then decide (BallClauseLogic.Endpoint q (166 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (172 : Vertex)) else decide (BallClauseLogic.Endpoint q (173 : Vertex)))) else (if i < 125 then (if i < 124 then decide (BallClauseLogic.Endpoint q (174 : Vertex)) else decide (BallClauseLogic.Endpoint q (178 : Vertex))) else (if i < 126 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (181 : Vertex))))) else (if i < 130 then (if i < 128 then decide (BallClauseLogic.Endpoint q (183 : Vertex)) else (if i < 129 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (187 : Vertex)))) else (if i < 132 then (if i < 131 then decide (BallClauseLogic.Endpoint q (188 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex))) else (if i < 133 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else decide (BallClauseLogic.Endpoint q (193 : Vertex))))))) else (if i < 147 then (if i < 140 then (if i < 137 then (if i < 135 then decide (BallClauseLogic.Endpoint q (194 : Vertex)) else (if i < 136 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else decide (BallClauseLogic.Endpoint q (201 : Vertex)))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (204 : Vertex)) else (if i < 139 then decide (BallClauseLogic.Endpoint q (205 : Vertex)) else decide (BallClauseLogic.Endpoint q (206 : Vertex))))) else (if i < 143 then (if i < 141 then decide (BallClauseLogic.Endpoint q (210 : Vertex)) else (if i < 142 then decide (BallClauseLogic.Endpoint q (211 : Vertex)) else decide (BallClauseLogic.Endpoint q (213 : Vertex)))) else (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (215 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (219 : Vertex)) else decide (BallClauseLogic.Endpoint q (220 : Vertex)))))) else (if i < 154 then (if i < 150 then (if i < 148 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else (if i < 149 then decide (BallClauseLogic.Endpoint q (257 : Vertex)) else decide (BallClauseLogic.Endpoint q (260 : Vertex)))) else (if i < 152 then (if i < 151 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (262 : Vertex))) else (if i < 153 then decide (BallClauseLogic.Endpoint q (263 : Vertex)) else decide (BallClauseLogic.Endpoint q (264 : Vertex))))) else (if i < 157 then (if i < 155 then decide (BallClauseLogic.Endpoint q (265 : Vertex)) else (if i < 156 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex)))) else (if i < 159 then (if i < 158 then decide (BallClauseLogic.Endpoint q (271 : Vertex)) else decide (BallClauseLogic.Endpoint q (274 : Vertex))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else decide (BallClauseLogic.Endpoint q (278 : Vertex)))))))) else (if i < 188 then (if i < 174 then (if i < 167 then (if i < 164 then (if i < 162 then decide (BallClauseLogic.Endpoint q (280 : Vertex)) else (if i < 163 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else decide (BallClauseLogic.Endpoint q (282 : Vertex)))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else (if i < 166 then decide (BallClauseLogic.Endpoint q (284 : Vertex)) else decide (BallClauseLogic.Endpoint q (320 : Vertex))))) else (if i < 170 then (if i < 168 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else (if i < 169 then decide (BallClauseLogic.Endpoint q (322 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex)))) else (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else decide (BallClauseLogic.Endpoint q (332 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (334 : Vertex)))))) else (if i < 181 then (if i < 177 then (if i < 175 then decide (BallClauseLogic.Endpoint q (338 : Vertex)) else (if i < 176 then decide (BallClauseLogic.Endpoint q (339 : Vertex)) else decide (BallClauseLogic.Endpoint q (341 : Vertex)))) else (if i < 179 then (if i < 178 then decide (BallClauseLogic.Endpoint q (343 : Vertex)) else decide (BallClauseLogic.Endpoint q (346 : Vertex))) else (if i < 180 then decide (BallClauseLogic.Endpoint q (347 : Vertex)) else decide (BallClauseLogic.Endpoint q (348 : Vertex))))) else (if i < 184 then (if i < 182 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else (if i < 183 then decide (BallClauseLogic.Endpoint q (417 : Vertex)) else decide (BallClauseLogic.Endpoint q (420 : Vertex)))) else (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex))))))) else (if i < 201 then (if i < 194 then (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex)))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (431 : Vertex)) else (if i < 193 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else decide (BallClauseLogic.Endpoint q (436 : Vertex))))) else (if i < 197 then (if i < 195 then decide (BallClauseLogic.Endpoint q (438 : Vertex)) else (if i < 196 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else decide (BallClauseLogic.Endpoint q (441 : Vertex)))) else (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (442 : Vertex)) else decide (BallClauseLogic.Endpoint q (443 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (444 : Vertex)) else decide (BallClauseLogic.Endpoint q (456 : Vertex)))))) else (if i < 208 then (if i < 204 then (if i < 202 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else (if i < 203 then decide (BallClauseLogic.Endpoint q (458 : Vertex)) else decide (BallClauseLogic.Endpoint q (473 : Vertex)))) else (if i < 206 then (if i < 205 then decide (BallClauseLogic.Endpoint q (474 : Vertex)) else decide (BallClauseLogic.Endpoint q (480 : Vertex))) else (if i < 207 then decide (BallClauseLogic.Endpoint q (482 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex))))) else (if i < 211 then (if i < 209 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else (if i < 210 then decide (BallClauseLogic.Endpoint q (492 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex)))) else (if i < 213 then (if i < 212 then decide (BallClauseLogic.Endpoint q (494 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex))) else (if i < 214 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count215 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count217 (b : Nat → Bool) : Nat := countLit b [108, 109, 110]
def count219 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count221 (b : Nat → Bool) : Nat := countLit b [111, 112, 113]
def count223 (b : Nat → Bool) : Nat := countLit b [108, 109, 110, 111, 112, 113]
def count225 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count227 (b : Nat → Bool) : Nat := countLit b [115, 116, 117]
def count229 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count231 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count233 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121]
def count235 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121]
def count237 (b : Nat → Bool) : Nat := countLit b [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]
def count239 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count241 (b : Nat → Bool) : Nat := countLit b [122, 123, 124]
def count243 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count245 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count247 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count251 (b : Nat → Bool) : Nat := countLit b [128, 129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count255 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count257 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134]
def count259 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count267 (b : Nat → Bool) : Nat := countLit b [135, 136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count271 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count277 (b : Nat → Bool) : Nat := countLit b [141, 142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count281 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count283 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count291 (b : Nat → Bool) : Nat := countLit b [148, 149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154]
def count299 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count303 (b : Nat → Bool) : Nat := countLit b [155, 156, 157]
def count305 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count307 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count309 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161]
def count311 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 159, 160, 161]
def count313 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [165, 166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count335 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count337 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
def count343 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count349 (b : Nat → Bool) : Nat := countLit b [178, 179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [181, 182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187]
def count363 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184, 185, 186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]
def count369 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [188, 189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192, 193]
def count377 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191, 192, 193]
def count379 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count381 (b : Nat → Bool) : Nat := countLit b [194, 195, 196]
def count383 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count387 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200]
def count389 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197, 198, 199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count395 (b : Nat → Bool) : Nat := countLit b [201, 202, 203]
def count397 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count399 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count401 (b : Nat → Bool) : Nat := countLit b [204, 205, 206, 207]
def count403 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204, 205, 206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count407 (b : Nat → Bool) : Nat := countLit b [208, 209, 210]
def count409 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count411 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count413 (b : Nat → Bool) : Nat := countLit b [211, 212, 213, 214]
def count415 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211, 212, 213, 214]
def count417 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214]
def count419 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214]
def count421 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214]
def count423 (b : Nat → Bool) : Nat := countLit b [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214]
def count425 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count427 (b : Nat → Bool) : Nat := countLit b [1, 3, 5]
def count430 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count432 (b : Nat → Bool) : Nat := countLit b [7, 9, 10]
def count435 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 9, 10]
def count441 (b : Nat → Bool) : Nat := countLit b [14, 17]
def count443 (b : Nat → Bool) : Nat := countLit b [13, 14, 17]
def count446 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count448 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count450 (b : Nat → Bool) : Nat := countLit b [20, 22, 24, 25]
def count454 (b : Nat → Bool) : Nat := countLit b [13, 14, 17, 20, 22, 24, 25]
def count461 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 9, 10, 13, 14, 17, 20, 22, 24, 25]
def count474 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count476 (b : Nat → Bool) : Nat := countLit b [28, 29, 30]
def count479 (b : Nat → Bool) : Nat := countLit b [33, 36]
def count481 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count483 (b : Nat → Bool) : Nat := countLit b [33, 36, 38, 40]
def count487 (b : Nat → Bool) : Nat := countLit b [28, 29, 30, 33, 36, 38, 40]
def count494 (b : Nat → Bool) : Nat := countLit b [42, 45]
def count496 (b : Nat → Bool) : Nat := countLit b [41, 42, 45]
def count499 (b : Nat → Bool) : Nat := countLit b [46, 49]
def count501 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count503 (b : Nat → Bool) : Nat := countLit b [46, 49, 53, 55]
def count507 (b : Nat → Bool) : Nat := countLit b [41, 42, 45, 46, 49, 53, 55]
def count514 (b : Nat → Bool) : Nat := countLit b [28, 29, 30, 33, 36, 38, 40, 41, 42, 45, 46, 49, 53, 55]
def count528 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 9, 10, 13, 14, 17, 20, 22, 24, 25, 28, 29, 30, 33, 36, 38, 40, 41, 42, 45, 46, 49, 53, 55]
def count555 (b : Nat → Bool) : Nat := countLit b [58, 59]
def count557 (b : Nat → Bool) : Nat := countLit b [56, 58, 59]
def count560 (b : Nat → Bool) : Nat := countLit b [63, 64]
def count562 (b : Nat → Bool) : Nat := countLit b [62, 63, 64]
def count565 (b : Nat → Bool) : Nat := countLit b [56, 58, 59, 62, 63, 64]
def count571 (b : Nat → Bool) : Nat := countLit b [70, 72]
def count573 (b : Nat → Bool) : Nat := countLit b [67, 70, 72]
def count576 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count578 (b : Nat → Bool) : Nat := countLit b [76, 79]
def count580 (b : Nat → Bool) : Nat := countLit b [74, 75, 76, 79]
def count584 (b : Nat → Bool) : Nat := countLit b [67, 70, 72, 74, 75, 76, 79]
def count591 (b : Nat → Bool) : Nat := countLit b [56, 58, 59, 62, 63, 64, 67, 70, 72, 74, 75, 76, 79]
def count604 (b : Nat → Bool) : Nat := countLit b [83, 87]
def count606 (b : Nat → Bool) : Nat := countLit b [80, 83, 87]
def count609 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count611 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count613 (b : Nat → Bool) : Nat := countLit b [89, 90, 92, 93]
def count617 (b : Nat → Bool) : Nat := countLit b [80, 83, 87, 89, 90, 92, 93]
def count624 (b : Nat → Bool) : Nat := countLit b [97, 98]
def count626 (b : Nat → Bool) : Nat := countLit b [96, 97, 98]
def count629 (b : Nat → Bool) : Nat := countLit b [100, 101]
def count631 (b : Nat → Bool) : Nat := countLit b [102, 105]
def count633 (b : Nat → Bool) : Nat := countLit b [100, 101, 102, 105]
def count637 (b : Nat → Bool) : Nat := countLit b [96, 97, 98, 100, 101, 102, 105]
def count644 (b : Nat → Bool) : Nat := countLit b [80, 83, 87, 89, 90, 92, 93, 96, 97, 98, 100, 101, 102, 105]
def count658 (b : Nat → Bool) : Nat := countLit b [56, 58, 59, 62, 63, 64, 67, 70, 72, 74, 75, 76, 79, 80, 83, 87, 89, 90, 92, 93, 96, 97, 98, 100, 101, 102, 105]
def count685 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 9, 10, 13, 14, 17, 20, 22, 24, 25, 28, 29, 30, 33, 36, 38, 40, 41, 42, 45, 46, 49, 53, 55, 56, 58, 59, 62, 63, 64, 67, 70, 72, 74, 75, 76, 79, 80, 83, 87, 89, 90, 92, 93, 96, 97, 98, 100, 101, 102, 105]
def count727 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count729 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5]
def count732 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count734 (b : Nat → Bool) : Nat := countLit b [-7, -9, -10]
def count737 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -9, -10]
def count743 (b : Nat → Bool) : Nat := countLit b [-14, -17]
def count745 (b : Nat → Bool) : Nat := countLit b [-13, -14, -17]
def count748 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count750 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count752 (b : Nat → Bool) : Nat := countLit b [-20, -22, -24, -25]
def count756 (b : Nat → Bool) : Nat := countLit b [-13, -14, -17, -20, -22, -24, -25]
def count763 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]
def count776 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count778 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30]
def count781 (b : Nat → Bool) : Nat := countLit b [-33, -36]
def count783 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count785 (b : Nat → Bool) : Nat := countLit b [-33, -36, -38, -40]
def count789 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30, -33, -36, -38, -40]
def count796 (b : Nat → Bool) : Nat := countLit b [-42, -45]
def count798 (b : Nat → Bool) : Nat := countLit b [-41, -42, -45]
def count801 (b : Nat → Bool) : Nat := countLit b [-46, -49]
def count803 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count805 (b : Nat → Bool) : Nat := countLit b [-46, -49, -53, -55]
def count809 (b : Nat → Bool) : Nat := countLit b [-41, -42, -45, -46, -49, -53, -55]
def count816 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]
def count830 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]
def count844 (b : Nat → Bool) : Nat := countLit b [-58, -59]
def count846 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59]
def count849 (b : Nat → Bool) : Nat := countLit b [-63, -64]
def count851 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64]
def count854 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59, -62, -63, -64]
def count860 (b : Nat → Bool) : Nat := countLit b [-70, -72]
def count862 (b : Nat → Bool) : Nat := countLit b [-67, -70, -72]
def count865 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count867 (b : Nat → Bool) : Nat := countLit b [-76, -79]
def count869 (b : Nat → Bool) : Nat := countLit b [-74, -75, -76, -79]
def count873 (b : Nat → Bool) : Nat := countLit b [-67, -70, -72, -74, -75, -76, -79]
def count880 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79]
def count893 (b : Nat → Bool) : Nat := countLit b [-83, -87]
def count895 (b : Nat → Bool) : Nat := countLit b [-80, -83, -87]
def count898 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count900 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count902 (b : Nat → Bool) : Nat := countLit b [-89, -90, -92, -93]
def count906 (b : Nat → Bool) : Nat := countLit b [-80, -83, -87, -89, -90, -92, -93]
def count913 (b : Nat → Bool) : Nat := countLit b [-97, -98]
def count915 (b : Nat → Bool) : Nat := countLit b [-96, -97, -98]
def count918 (b : Nat → Bool) : Nat := countLit b [-100, -101]
def count920 (b : Nat → Bool) : Nat := countLit b [-102, -105]
def count922 (b : Nat → Bool) : Nat := countLit b [-100, -101, -102, -105]
def count926 (b : Nat → Bool) : Nat := countLit b [-96, -97, -98, -100, -101, -102, -105]
def count933 (b : Nat → Bool) : Nat := countLit b [-80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]
def count947 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]
def count961 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25, -28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55, -56, -58, -59, -62, -63, -64, -67, -70, -72, -74, -75, -76, -79, -80, -83, -87, -89, -90, -92, -93, -96, -97, -98, -100, -101, -102, -105]
def count975 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count977 (b : Nat → Bool) : Nat := countLit b [2, 4, 6]
def count980 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count982 (b : Nat → Bool) : Nat := countLit b [8, 11, 12]
def count985 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 8, 11, 12]
def count991 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count993 (b : Nat → Bool) : Nat := countLit b [15, 16, 18]
def count996 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count998 (b : Nat → Bool) : Nat := countLit b [23, 26]
def count1000 (b : Nat → Bool) : Nat := countLit b [19, 21, 23, 26]
def count1004 (b : Nat → Bool) : Nat := countLit b [15, 16, 18, 19, 21, 23, 26]
def count1011 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 8, 11, 12, 15, 16, 18, 19, 21, 23, 26]
def count1024 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count1026 (b : Nat → Bool) : Nat := countLit b [27, 31, 32]
def count1029 (b : Nat → Bool) : Nat := countLit b [35, 37]
def count1031 (b : Nat → Bool) : Nat := countLit b [34, 35, 37]
def count1034 (b : Nat → Bool) : Nat := countLit b [27, 31, 32, 34, 35, 37]
def count1040 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count1042 (b : Nat → Bool) : Nat := countLit b [39, 43, 44]
def count1045 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count1047 (b : Nat → Bool) : Nat := countLit b [50, 51]
def count1049 (b : Nat → Bool) : Nat := countLit b [47, 48, 50, 51]
def count1053 (b : Nat → Bool) : Nat := countLit b [39, 43, 44, 47, 48, 50, 51]
def count1060 (b : Nat → Bool) : Nat := countLit b [27, 31, 32, 34, 35, 37, 39, 43, 44, 47, 48, 50, 51]
def count1073 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 8, 11, 12, 15, 16, 18, 19, 21, 23, 26, 27, 31, 32, 34, 35, 37, 39, 43, 44, 47, 48, 50, 51]
def count1099 (b : Nat → Bool) : Nat := countLit b [54, 57]
def count1101 (b : Nat → Bool) : Nat := countLit b [52, 54, 57]
def count1104 (b : Nat → Bool) : Nat := countLit b [61, 65]
def count1106 (b : Nat → Bool) : Nat := countLit b [60, 61, 65]
def count1109 (b : Nat → Bool) : Nat := countLit b [52, 54, 57, 60, 61, 65]
def count1115 (b : Nat → Bool) : Nat := countLit b [68, 69]
def count1117 (b : Nat → Bool) : Nat := countLit b [66, 68, 69]
def count1120 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count1122 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count1124 (b : Nat → Bool) : Nat := countLit b [71, 73, 77, 78]
def count1128 (b : Nat → Bool) : Nat := countLit b [66, 68, 69, 71, 73, 77, 78]
def count1135 (b : Nat → Bool) : Nat := countLit b [52, 54, 57, 60, 61, 65, 66, 68, 69, 71, 73, 77, 78]
def count1148 (b : Nat → Bool) : Nat := countLit b [82, 84]
def count1150 (b : Nat → Bool) : Nat := countLit b [81, 82, 84]
def count1153 (b : Nat → Bool) : Nat := countLit b [85, 86]
def count1155 (b : Nat → Bool) : Nat := countLit b [88, 91]
def count1157 (b : Nat → Bool) : Nat := countLit b [85, 86, 88, 91]
def count1161 (b : Nat → Bool) : Nat := countLit b [81, 82, 84, 85, 86, 88, 91]
def count1168 (b : Nat → Bool) : Nat := countLit b [95, 99]
def count1170 (b : Nat → Bool) : Nat := countLit b [94, 95, 99]
def count1173 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count1175 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count1177 (b : Nat → Bool) : Nat := countLit b [103, 104, 106, 107]
def count1181 (b : Nat → Bool) : Nat := countLit b [94, 95, 99, 103, 104, 106, 107]
def count1188 (b : Nat → Bool) : Nat := countLit b [81, 82, 84, 85, 86, 88, 91, 94, 95, 99, 103, 104, 106, 107]
def count1202 (b : Nat → Bool) : Nat := countLit b [52, 54, 57, 60, 61, 65, 66, 68, 69, 71, 73, 77, 78, 81, 82, 84, 85, 86, 88, 91, 94, 95, 99, 103, 104, 106, 107]
def count1229 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 8, 11, 12, 15, 16, 18, 19, 21, 23, 26, 27, 31, 32, 34, 35, 37, 39, 43, 44, 47, 48, 50, 51, 52, 54, 57, 60, 61, 65, 66, 68, 69, 71, 73, 77, 78, 81, 82, 84, 85, 86, 88, 91, 94, 95, 99, 103, 104, 106, 107]
def count1271 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count1273 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6]
def count1276 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count1278 (b : Nat → Bool) : Nat := countLit b [-8, -11, -12]
def count1281 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -8, -11, -12]
def count1287 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1289 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18]
def count1292 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count1294 (b : Nat → Bool) : Nat := countLit b [-23, -26]
def count1296 (b : Nat → Bool) : Nat := countLit b [-19, -21, -23, -26]
def count1300 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18, -19, -21, -23, -26]
def count1307 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -8, -11, -12, -15, -16, -18, -19, -21, -23, -26]
def count1320 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count1322 (b : Nat → Bool) : Nat := countLit b [-27, -31, -32]
def count1325 (b : Nat → Bool) : Nat := countLit b [-35, -37]
def count1327 (b : Nat → Bool) : Nat := countLit b [-34, -35, -37]
def count1330 (b : Nat → Bool) : Nat := countLit b [-27, -31, -32, -34, -35, -37]
def count1336 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count1338 (b : Nat → Bool) : Nat := countLit b [-39, -43, -44]
def count1341 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count1343 (b : Nat → Bool) : Nat := countLit b [-50, -51]
def count1345 (b : Nat → Bool) : Nat := countLit b [-47, -48, -50, -51]
def count1349 (b : Nat → Bool) : Nat := countLit b [-39, -43, -44, -47, -48, -50, -51]
def count1356 (b : Nat → Bool) : Nat := countLit b [-27, -31, -32, -34, -35, -37, -39, -43, -44, -47, -48, -50, -51]
def count1369 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -8, -11, -12, -15, -16, -18, -19, -21, -23, -26, -27, -31, -32, -34, -35, -37, -39, -43, -44, -47, -48, -50, -51]
def count1382 (b : Nat → Bool) : Nat := countLit b [-54, -57]
def count1384 (b : Nat → Bool) : Nat := countLit b [-52, -54, -57]
def count1387 (b : Nat → Bool) : Nat := countLit b [-61, -65]
def count1389 (b : Nat → Bool) : Nat := countLit b [-60, -61, -65]
def count1392 (b : Nat → Bool) : Nat := countLit b [-52, -54, -57, -60, -61, -65]
def count1398 (b : Nat → Bool) : Nat := countLit b [-68, -69]
def count1400 (b : Nat → Bool) : Nat := countLit b [-66, -68, -69]
def count1403 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count1405 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count1407 (b : Nat → Bool) : Nat := countLit b [-71, -73, -77, -78]
def count1411 (b : Nat → Bool) : Nat := countLit b [-66, -68, -69, -71, -73, -77, -78]
def count1418 (b : Nat → Bool) : Nat := countLit b [-52, -54, -57, -60, -61, -65, -66, -68, -69, -71, -73, -77, -78]
def count1431 (b : Nat → Bool) : Nat := countLit b [-82, -84]
def count1433 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84]
def count1436 (b : Nat → Bool) : Nat := countLit b [-85, -86]
def count1438 (b : Nat → Bool) : Nat := countLit b [-88, -91]
def count1440 (b : Nat → Bool) : Nat := countLit b [-85, -86, -88, -91]
def count1444 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84, -85, -86, -88, -91]
def count1451 (b : Nat → Bool) : Nat := countLit b [-95, -99]
def count1453 (b : Nat → Bool) : Nat := countLit b [-94, -95, -99]
def count1456 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1458 (b : Nat → Bool) : Nat := countLit b [-106, -107]
def count1460 (b : Nat → Bool) : Nat := countLit b [-103, -104, -106, -107]
def count1464 (b : Nat → Bool) : Nat := countLit b [-94, -95, -99, -103, -104, -106, -107]
def count1471 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84, -85, -86, -88, -91, -94, -95, -99, -103, -104, -106, -107]
def count1484 (b : Nat → Bool) : Nat := countLit b [-52, -54, -57, -60, -61, -65, -66, -68, -69, -71, -73, -77, -78, -81, -82, -84, -85, -86, -88, -91, -94, -95, -99, -103, -104, -106, -107]
def count1497 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -8, -11, -12, -15, -16, -18, -19, -21, -23, -26, -27, -31, -32, -34, -35, -37, -39, -43, -44, -47, -48, -50, -51, -52, -54, -57, -60, -61, -65, -66, -68, -69, -71, -73, -77, -78, -81, -82, -84, -85, -86, -88, -91, -94, -95, -99, -103, -104, -106, -107]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 755 then (if i < 377 then (if i < 188 then (if i < 94 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 17 then (if i < 14 then (if i < 12 then b 11 else (if i < 13 then b 12 else b 13)) else (if i < 15 then b 14 else (if i < 16 then b 15 else b 16))) else (if i < 20 then (if i < 18 then b 17 else (if i < 19 then b 18 else b 19)) else (if i < 21 then b 20 else (if i < 22 then b 21 else b 22))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then b 23 else (if i < 25 then b 24 else b 25)) else (if i < 27 then b 26 else (if i < 28 then b 27 else b 28))) else (if i < 32 then (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)) else (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)))) else (if i < 41 then (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 39 then b 38 else (if i < 40 then b 39 else b 40))) else (if i < 44 then (if i < 42 then b 41 else (if i < 43 then b 42 else b 43)) else (if i < 45 then b 44 else (if i < 46 then b 45 else b 46)))))) else (if i < 70 then (if i < 58 then (if i < 52 then (if i < 49 then (if i < 48 then b 47 else b 48) else (if i < 50 then b 49 else (if i < 51 then b 50 else b 51))) else (if i < 55 then (if i < 53 then b 52 else (if i < 54 then b 53 else b 54)) else (if i < 56 then b 55 else (if i < 57 then b 56 else b 57)))) else (if i < 64 then (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 62 then b 61 else (if i < 63 then b 62 else b 63))) else (if i < 67 then (if i < 65 then b 64 else (if i < 66 then b 65 else b 66)) else (if i < 68 then b 67 else (if i < 69 then b 68 else b 69))))) else (if i < 82 then (if i < 76 then (if i < 73 then (if i < 71 then b 70 else (if i < 72 then b 71 else b 72)) else (if i < 74 then b 73 else (if i < 75 then b 74 else b 75))) else (if i < 79 then (if i < 77 then b 76 else (if i < 78 then b 77 else b 78)) else (if i < 80 then b 79 else (if i < 81 then b 80 else b 81)))) else (if i < 88 then (if i < 85 then (if i < 83 then b 82 else (if i < 84 then b 83 else b 84)) else (if i < 86 then b 85 else (if i < 87 then b 86 else b 87))) else (if i < 91 then (if i < 89 then b 88 else (if i < 90 then b 89 else b 90)) else (if i < 92 then b 91 else (if i < 93 then b 92 else b 93))))))) else (if i < 141 then (if i < 117 then (if i < 105 then (if i < 99 then (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else (if i < 98 then b 97 else b 98))) else (if i < 102 then (if i < 100 then b 99 else (if i < 101 then b 100 else b 101)) else (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)))) else (if i < 111 then (if i < 108 then (if i < 106 then b 105 else (if i < 107 then b 106 else b 107)) else (if i < 109 then b 108 else (if i < 110 then b 109 else b 110))) else (if i < 114 then (if i < 112 then b 111 else (if i < 113 then b 112 else b 113)) else (if i < 115 then b 114 else (if i < 116 then b 115 else b 116))))) else (if i < 129 then (if i < 123 then (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122))) else (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 127 then b 126 else (if i < 128 then b 127 else b 128)))) else (if i < 135 then (if i < 132 then (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)) else (if i < 133 then b 132 else (if i < 134 then b 133 else b 134))) else (if i < 138 then (if i < 136 then b 135 else (if i < 137 then b 136 else b 137)) else (if i < 139 then b 138 else (if i < 140 then b 139 else b 140)))))) else (if i < 164 then (if i < 152 then (if i < 146 then (if i < 143 then (if i < 142 then b 141 else b 142) else (if i < 144 then b 143 else (if i < 145 then b 144 else b 145))) else (if i < 149 then (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)) else (if i < 150 then b 149 else (if i < 151 then b 150 else b 151)))) else (if i < 158 then (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 156 then b 155 else (if i < 157 then b 156 else b 157))) else (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 162 then b 161 else (if i < 163 then b 162 else b 163))))) else (if i < 176 then (if i < 170 then (if i < 167 then (if i < 165 then b 164 else (if i < 166 then b 165 else b 166)) else (if i < 168 then b 167 else (if i < 169 then b 168 else b 169))) else (if i < 173 then (if i < 171 then b 170 else (if i < 172 then b 171 else b 172)) else (if i < 174 then b 173 else (if i < 175 then b 174 else b 175)))) else (if i < 182 then (if i < 179 then (if i < 177 then b 176 else (if i < 178 then b 177 else b 178)) else (if i < 180 then b 179 else (if i < 181 then b 180 else b 181))) else (if i < 185 then (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)) else (if i < 186 then b 185 else (if i < 187 then b 186 else b 187)))))))) else (if i < 282 then (if i < 235 then (if i < 211 then (if i < 199 then (if i < 193 then (if i < 190 then (if i < 189 then b 188 else b 189) else (if i < 191 then b 190 else (if i < 192 then b 191 else b 192))) else (if i < 196 then (if i < 194 then b 193 else (if i < 195 then b 194 else b 195)) else (if i < 197 then b 196 else (if i < 198 then b 197 else b 198)))) else (if i < 205 then (if i < 202 then (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)) else (if i < 203 then b 202 else (if i < 204 then b 203 else b 204))) else (if i < 208 then (if i < 206 then b 205 else (if i < 207 then b 206 else b 207)) else (if i < 209 then b 208 else (if i < 210 then b 209 else b 210))))) else (if i < 223 then (if i < 217 then (if i < 214 then (if i < 212 then b 211 else (if i < 213 then b 212 else b 213)) else (if i < 215 then b 214 else (if i < 216 then decide (1 ≤ count215 b) else decide (2 ≤ count215 b)))) else (if i < 220 then (if i < 218 then decide (1 ≤ count217 b) else (if i < 219 then decide (2 ≤ count217 b) else decide (1 ≤ count219 b))) else (if i < 221 then decide (2 ≤ count219 b) else (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b))))) else (if i < 229 then (if i < 226 then (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b))) else (if i < 227 then decide (2 ≤ count225 b) else (if i < 228 then decide (1 ≤ count227 b) else decide (2 ≤ count227 b)))) else (if i < 232 then (if i < 230 then decide (1 ≤ count229 b) else (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b))) else (if i < 233 then decide (2 ≤ count231 b) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b))))))) else (if i < 258 then (if i < 246 then (if i < 240 then (if i < 237 then (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b)) else (if i < 238 then decide (1 ≤ count237 b) else (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b)))) else (if i < 243 then (if i < 241 then decide (2 ≤ count239 b) else (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b))) else (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b))))) else (if i < 252 then (if i < 249 then (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b))) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)))) else (if i < 255 then (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))) else (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b)))))) else (if i < 270 then (if i < 264 then (if i < 261 then (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)))) else (if i < 267 then (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))) else (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))))) else (if i < 276 then (if i < 273 then (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b))) else (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)))) else (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b)))))))) else (if i < 329 then (if i < 305 then (if i < 293 then (if i < 287 then (if i < 284 then (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b)) else (if i < 285 then decide (2 ≤ count283 b) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))) else (if i < 290 then (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))) else (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))))) else (if i < 299 then (if i < 296 then (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))) else (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))) else (if i < 302 then (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))) else (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b)))))) else (if i < 317 then (if i < 311 then (if i < 308 then (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))) else (if i < 309 then decide (2 ≤ count307 b) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)))) else (if i < 314 then (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b))) else (if i < 315 then decide (2 ≤ count313 b) else (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b))))) else (if i < 323 then (if i < 320 then (if i < 318 then decide (1 ≤ count317 b) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b))) else (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)))) else (if i < 326 then (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))) else (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))))))) else (if i < 353 then (if i < 341 then (if i < 335 then (if i < 332 then (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))) else (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b)))) else (if i < 338 then (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b))) else (if i < 339 then decide (2 ≤ count337 b) else (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b))))) else (if i < 347 then (if i < 344 then (if i < 342 then decide (1 ≤ count341 b) else (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b))) else (if i < 345 then decide (2 ≤ count343 b) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)))) else (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b)))))) else (if i < 365 then (if i < 359 then (if i < 356 then (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b))) else (if i < 357 then decide (2 ≤ count355 b) else (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)))) else (if i < 362 then (if i < 360 then decide (1 ≤ count359 b) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b))) else (if i < 363 then decide (2 ≤ count361 b) else (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b))))) else (if i < 371 then (if i < 368 then (if i < 366 then decide (1 ≤ count365 b) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))) else (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)))))))))) else (if i < 566 then (if i < 471 then (if i < 424 then (if i < 400 then (if i < 388 then (if i < 382 then (if i < 379 then (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)) else (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b)))) else (if i < 385 then (if i < 383 then decide (2 ≤ count381 b) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b))))) else (if i < 394 then (if i < 391 then (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b))) else (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b)))) else (if i < 397 then (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))) else (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))))) else (if i < 412 then (if i < 406 then (if i < 403 then (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))) else (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b)))) else (if i < 409 then (if i < 407 then decide (2 ≤ count405 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))) else (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b))))) else (if i < 418 then (if i < 415 then (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))) else (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)))) else (if i < 421 then (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))) else (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b))))))) else (if i < 447 then (if i < 435 then (if i < 429 then (if i < 426 then (if i < 425 then decide (2 ≤ count423 b) else decide (1 ≤ count425 b)) else (if i < 427 then decide (2 ≤ count425 b) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)))) else (if i < 432 then (if i < 430 then decide (3 ≤ count427 b) else (if i < 431 then decide (1 ≤ count430 b) else decide (2 ≤ count430 b))) else (if i < 433 then decide (1 ≤ count432 b) else (if i < 434 then decide (2 ≤ count432 b) else decide (3 ≤ count432 b))))) else (if i < 441 then (if i < 438 then (if i < 436 then decide (1 ≤ count435 b) else (if i < 437 then decide (2 ≤ count435 b) else decide (3 ≤ count435 b))) else (if i < 439 then decide (4 ≤ count435 b) else (if i < 440 then decide (5 ≤ count435 b) else decide (6 ≤ count435 b)))) else (if i < 444 then (if i < 442 then decide (1 ≤ count441 b) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b))) else (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (3 ≤ count443 b) else decide (1 ≤ count446 b)))))) else (if i < 459 then (if i < 453 then (if i < 450 then (if i < 448 then decide (2 ≤ count446 b) else (if i < 449 then decide (1 ≤ count448 b) else decide (2 ≤ count448 b))) else (if i < 451 then decide (1 ≤ count450 b) else (if i < 452 then decide (2 ≤ count450 b) else decide (3 ≤ count450 b)))) else (if i < 456 then (if i < 454 then decide (4 ≤ count450 b) else (if i < 455 then decide (1 ≤ count454 b) else decide (2 ≤ count454 b))) else (if i < 457 then decide (3 ≤ count454 b) else (if i < 458 then decide (4 ≤ count454 b) else decide (5 ≤ count454 b))))) else (if i < 465 then (if i < 462 then (if i < 460 then decide (6 ≤ count454 b) else (if i < 461 then decide (7 ≤ count454 b) else decide (1 ≤ count461 b))) else (if i < 463 then decide (2 ≤ count461 b) else (if i < 464 then decide (3 ≤ count461 b) else decide (4 ≤ count461 b)))) else (if i < 468 then (if i < 466 then decide (5 ≤ count461 b) else (if i < 467 then decide (6 ≤ count461 b) else decide (7 ≤ count461 b))) else (if i < 469 then decide (8 ≤ count461 b) else (if i < 470 then decide (9 ≤ count461 b) else decide (10 ≤ count461 b)))))))) else (if i < 518 then (if i < 494 then (if i < 482 then (if i < 476 then (if i < 473 then (if i < 472 then decide (11 ≤ count461 b) else decide (12 ≤ count461 b)) else (if i < 474 then decide (13 ≤ count461 b) else (if i < 475 then decide (1 ≤ count474 b) else decide (2 ≤ count474 b)))) else (if i < 479 then (if i < 477 then decide (1 ≤ count476 b) else (if i < 478 then decide (2 ≤ count476 b) else decide (3 ≤ count476 b))) else (if i < 480 then decide (1 ≤ count479 b) else (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b))))) else (if i < 488 then (if i < 485 then (if i < 483 then decide (2 ≤ count481 b) else (if i < 484 then decide (1 ≤ count483 b) else decide (2 ≤ count483 b))) else (if i < 486 then decide (3 ≤ count483 b) else (if i < 487 then decide (4 ≤ count483 b) else decide (1 ≤ count487 b)))) else (if i < 491 then (if i < 489 then decide (2 ≤ count487 b) else (if i < 490 then decide (3 ≤ count487 b) else decide (4 ≤ count487 b))) else (if i < 492 then decide (5 ≤ count487 b) else (if i < 493 then decide (6 ≤ count487 b) else decide (7 ≤ count487 b)))))) else (if i < 506 then (if i < 500 then (if i < 497 then (if i < 495 then decide (1 ≤ count494 b) else (if i < 496 then decide (2 ≤ count494 b) else decide (1 ≤ count496 b))) else (if i < 498 then decide (2 ≤ count496 b) else (if i < 499 then decide (3 ≤ count496 b) else decide (1 ≤ count499 b)))) else (if i < 503 then (if i < 501 then decide (2 ≤ count499 b) else (if i < 502 then decide (1 ≤ count501 b) else decide (2 ≤ count501 b))) else (if i < 504 then decide (1 ≤ count503 b) else (if i < 505 then decide (2 ≤ count503 b) else decide (3 ≤ count503 b))))) else (if i < 512 then (if i < 509 then (if i < 507 then decide (4 ≤ count503 b) else (if i < 508 then decide (1 ≤ count507 b) else decide (2 ≤ count507 b))) else (if i < 510 then decide (3 ≤ count507 b) else (if i < 511 then decide (4 ≤ count507 b) else decide (5 ≤ count507 b)))) else (if i < 515 then (if i < 513 then decide (6 ≤ count507 b) else (if i < 514 then decide (7 ≤ count507 b) else decide (1 ≤ count514 b))) else (if i < 516 then decide (2 ≤ count514 b) else (if i < 517 then decide (3 ≤ count514 b) else decide (4 ≤ count514 b))))))) else (if i < 542 then (if i < 530 then (if i < 524 then (if i < 521 then (if i < 519 then decide (5 ≤ count514 b) else (if i < 520 then decide (6 ≤ count514 b) else decide (7 ≤ count514 b))) else (if i < 522 then decide (8 ≤ count514 b) else (if i < 523 then decide (9 ≤ count514 b) else decide (10 ≤ count514 b)))) else (if i < 527 then (if i < 525 then decide (11 ≤ count514 b) else (if i < 526 then decide (12 ≤ count514 b) else decide (13 ≤ count514 b))) else (if i < 528 then decide (14 ≤ count514 b) else (if i < 529 then decide (1 ≤ count528 b) else decide (2 ≤ count528 b))))) else (if i < 536 then (if i < 533 then (if i < 531 then decide (3 ≤ count528 b) else (if i < 532 then decide (4 ≤ count528 b) else decide (5 ≤ count528 b))) else (if i < 534 then decide (6 ≤ count528 b) else (if i < 535 then decide (7 ≤ count528 b) else decide (8 ≤ count528 b)))) else (if i < 539 then (if i < 537 then decide (9 ≤ count528 b) else (if i < 538 then decide (10 ≤ count528 b) else decide (11 ≤ count528 b))) else (if i < 540 then decide (12 ≤ count528 b) else (if i < 541 then decide (13 ≤ count528 b) else decide (14 ≤ count528 b)))))) else (if i < 554 then (if i < 548 then (if i < 545 then (if i < 543 then decide (15 ≤ count528 b) else (if i < 544 then decide (16 ≤ count528 b) else decide (17 ≤ count528 b))) else (if i < 546 then decide (18 ≤ count528 b) else (if i < 547 then decide (19 ≤ count528 b) else decide (20 ≤ count528 b)))) else (if i < 551 then (if i < 549 then decide (21 ≤ count528 b) else (if i < 550 then decide (22 ≤ count528 b) else decide (23 ≤ count528 b))) else (if i < 552 then decide (24 ≤ count528 b) else (if i < 553 then decide (25 ≤ count528 b) else decide (26 ≤ count528 b))))) else (if i < 560 then (if i < 557 then (if i < 555 then decide (27 ≤ count528 b) else (if i < 556 then decide (1 ≤ count555 b) else decide (2 ≤ count555 b))) else (if i < 558 then decide (1 ≤ count557 b) else (if i < 559 then decide (2 ≤ count557 b) else decide (3 ≤ count557 b)))) else (if i < 563 then (if i < 561 then decide (1 ≤ count560 b) else (if i < 562 then decide (2 ≤ count560 b) else decide (1 ≤ count562 b))) else (if i < 564 then decide (2 ≤ count562 b) else (if i < 565 then decide (3 ≤ count562 b) else decide (1 ≤ count565 b))))))))) else (if i < 660 then (if i < 613 then (if i < 589 then (if i < 577 then (if i < 571 then (if i < 568 then (if i < 567 then decide (2 ≤ count565 b) else decide (3 ≤ count565 b)) else (if i < 569 then decide (4 ≤ count565 b) else (if i < 570 then decide (5 ≤ count565 b) else decide (6 ≤ count565 b)))) else (if i < 574 then (if i < 572 then decide (1 ≤ count571 b) else (if i < 573 then decide (2 ≤ count571 b) else decide (1 ≤ count573 b))) else (if i < 575 then decide (2 ≤ count573 b) else (if i < 576 then decide (3 ≤ count573 b) else decide (1 ≤ count576 b))))) else (if i < 583 then (if i < 580 then (if i < 578 then decide (2 ≤ count576 b) else (if i < 579 then decide (1 ≤ count578 b) else decide (2 ≤ count578 b))) else (if i < 581 then decide (1 ≤ count580 b) else (if i < 582 then decide (2 ≤ count580 b) else decide (3 ≤ count580 b)))) else (if i < 586 then (if i < 584 then decide (4 ≤ count580 b) else (if i < 585 then decide (1 ≤ count584 b) else decide (2 ≤ count584 b))) else (if i < 587 then decide (3 ≤ count584 b) else (if i < 588 then decide (4 ≤ count584 b) else decide (5 ≤ count584 b)))))) else (if i < 601 then (if i < 595 then (if i < 592 then (if i < 590 then decide (6 ≤ count584 b) else (if i < 591 then decide (7 ≤ count584 b) else decide (1 ≤ count591 b))) else (if i < 593 then decide (2 ≤ count591 b) else (if i < 594 then decide (3 ≤ count591 b) else decide (4 ≤ count591 b)))) else (if i < 598 then (if i < 596 then decide (5 ≤ count591 b) else (if i < 597 then decide (6 ≤ count591 b) else decide (7 ≤ count591 b))) else (if i < 599 then decide (8 ≤ count591 b) else (if i < 600 then decide (9 ≤ count591 b) else decide (10 ≤ count591 b))))) else (if i < 607 then (if i < 604 then (if i < 602 then decide (11 ≤ count591 b) else (if i < 603 then decide (12 ≤ count591 b) else decide (13 ≤ count591 b))) else (if i < 605 then decide (1 ≤ count604 b) else (if i < 606 then decide (2 ≤ count604 b) else decide (1 ≤ count606 b)))) else (if i < 610 then (if i < 608 then decide (2 ≤ count606 b) else (if i < 609 then decide (3 ≤ count606 b) else decide (1 ≤ count609 b))) else (if i < 611 then decide (2 ≤ count609 b) else (if i < 612 then decide (1 ≤ count611 b) else decide (2 ≤ count611 b))))))) else (if i < 636 then (if i < 624 then (if i < 618 then (if i < 615 then (if i < 614 then decide (1 ≤ count613 b) else decide (2 ≤ count613 b)) else (if i < 616 then decide (3 ≤ count613 b) else (if i < 617 then decide (4 ≤ count613 b) else decide (1 ≤ count617 b)))) else (if i < 621 then (if i < 619 then decide (2 ≤ count617 b) else (if i < 620 then decide (3 ≤ count617 b) else decide (4 ≤ count617 b))) else (if i < 622 then decide (5 ≤ count617 b) else (if i < 623 then decide (6 ≤ count617 b) else decide (7 ≤ count617 b))))) else (if i < 630 then (if i < 627 then (if i < 625 then decide (1 ≤ count624 b) else (if i < 626 then decide (2 ≤ count624 b) else decide (1 ≤ count626 b))) else (if i < 628 then decide (2 ≤ count626 b) else (if i < 629 then decide (3 ≤ count626 b) else decide (1 ≤ count629 b)))) else (if i < 633 then (if i < 631 then decide (2 ≤ count629 b) else (if i < 632 then decide (1 ≤ count631 b) else decide (2 ≤ count631 b))) else (if i < 634 then decide (1 ≤ count633 b) else (if i < 635 then decide (2 ≤ count633 b) else decide (3 ≤ count633 b)))))) else (if i < 648 then (if i < 642 then (if i < 639 then (if i < 637 then decide (4 ≤ count633 b) else (if i < 638 then decide (1 ≤ count637 b) else decide (2 ≤ count637 b))) else (if i < 640 then decide (3 ≤ count637 b) else (if i < 641 then decide (4 ≤ count637 b) else decide (5 ≤ count637 b)))) else (if i < 645 then (if i < 643 then decide (6 ≤ count637 b) else (if i < 644 then decide (7 ≤ count637 b) else decide (1 ≤ count644 b))) else (if i < 646 then decide (2 ≤ count644 b) else (if i < 647 then decide (3 ≤ count644 b) else decide (4 ≤ count644 b))))) else (if i < 654 then (if i < 651 then (if i < 649 then decide (5 ≤ count644 b) else (if i < 650 then decide (6 ≤ count644 b) else decide (7 ≤ count644 b))) else (if i < 652 then decide (8 ≤ count644 b) else (if i < 653 then decide (9 ≤ count644 b) else decide (10 ≤ count644 b)))) else (if i < 657 then (if i < 655 then decide (11 ≤ count644 b) else (if i < 656 then decide (12 ≤ count644 b) else decide (13 ≤ count644 b))) else (if i < 658 then decide (14 ≤ count644 b) else (if i < 659 then decide (1 ≤ count658 b) else decide (2 ≤ count658 b)))))))) else (if i < 707 then (if i < 683 then (if i < 671 then (if i < 665 then (if i < 662 then (if i < 661 then decide (3 ≤ count658 b) else decide (4 ≤ count658 b)) else (if i < 663 then decide (5 ≤ count658 b) else (if i < 664 then decide (6 ≤ count658 b) else decide (7 ≤ count658 b)))) else (if i < 668 then (if i < 666 then decide (8 ≤ count658 b) else (if i < 667 then decide (9 ≤ count658 b) else decide (10 ≤ count658 b))) else (if i < 669 then decide (11 ≤ count658 b) else (if i < 670 then decide (12 ≤ count658 b) else decide (13 ≤ count658 b))))) else (if i < 677 then (if i < 674 then (if i < 672 then decide (14 ≤ count658 b) else (if i < 673 then decide (15 ≤ count658 b) else decide (16 ≤ count658 b))) else (if i < 675 then decide (17 ≤ count658 b) else (if i < 676 then decide (18 ≤ count658 b) else decide (19 ≤ count658 b)))) else (if i < 680 then (if i < 678 then decide (20 ≤ count658 b) else (if i < 679 then decide (21 ≤ count658 b) else decide (22 ≤ count658 b))) else (if i < 681 then decide (23 ≤ count658 b) else (if i < 682 then decide (24 ≤ count658 b) else decide (25 ≤ count658 b)))))) else (if i < 695 then (if i < 689 then (if i < 686 then (if i < 684 then decide (26 ≤ count658 b) else (if i < 685 then decide (27 ≤ count658 b) else decide (1 ≤ count685 b))) else (if i < 687 then decide (2 ≤ count685 b) else (if i < 688 then decide (3 ≤ count685 b) else decide (4 ≤ count685 b)))) else (if i < 692 then (if i < 690 then decide (5 ≤ count685 b) else (if i < 691 then decide (6 ≤ count685 b) else decide (7 ≤ count685 b))) else (if i < 693 then decide (8 ≤ count685 b) else (if i < 694 then decide (9 ≤ count685 b) else decide (10 ≤ count685 b))))) else (if i < 701 then (if i < 698 then (if i < 696 then decide (11 ≤ count685 b) else (if i < 697 then decide (12 ≤ count685 b) else decide (13 ≤ count685 b))) else (if i < 699 then decide (14 ≤ count685 b) else (if i < 700 then decide (15 ≤ count685 b) else decide (16 ≤ count685 b)))) else (if i < 704 then (if i < 702 then decide (17 ≤ count685 b) else (if i < 703 then decide (18 ≤ count685 b) else decide (19 ≤ count685 b))) else (if i < 705 then decide (20 ≤ count685 b) else (if i < 706 then decide (21 ≤ count685 b) else decide (22 ≤ count685 b))))))) else (if i < 731 then (if i < 719 then (if i < 713 then (if i < 710 then (if i < 708 then decide (23 ≤ count685 b) else (if i < 709 then decide (24 ≤ count685 b) else decide (25 ≤ count685 b))) else (if i < 711 then decide (26 ≤ count685 b) else (if i < 712 then decide (27 ≤ count685 b) else decide (28 ≤ count685 b)))) else (if i < 716 then (if i < 714 then decide (29 ≤ count685 b) else (if i < 715 then decide (30 ≤ count685 b) else decide (31 ≤ count685 b))) else (if i < 717 then decide (32 ≤ count685 b) else (if i < 718 then decide (33 ≤ count685 b) else decide (34 ≤ count685 b))))) else (if i < 725 then (if i < 722 then (if i < 720 then decide (35 ≤ count685 b) else (if i < 721 then decide (36 ≤ count685 b) else decide (37 ≤ count685 b))) else (if i < 723 then decide (38 ≤ count685 b) else (if i < 724 then decide (39 ≤ count685 b) else decide (40 ≤ count685 b)))) else (if i < 728 then (if i < 726 then decide (41 ≤ count685 b) else (if i < 727 then decide (42 ≤ count685 b) else decide (1 ≤ count727 b))) else (if i < 729 then decide (2 ≤ count727 b) else (if i < 730 then decide (1 ≤ count729 b) else decide (2 ≤ count729 b)))))) else (if i < 743 then (if i < 737 then (if i < 734 then (if i < 732 then decide (3 ≤ count729 b) else (if i < 733 then decide (1 ≤ count732 b) else decide (2 ≤ count732 b))) else (if i < 735 then decide (1 ≤ count734 b) else (if i < 736 then decide (2 ≤ count734 b) else decide (3 ≤ count734 b)))) else (if i < 740 then (if i < 738 then decide (1 ≤ count737 b) else (if i < 739 then decide (2 ≤ count737 b) else decide (3 ≤ count737 b))) else (if i < 741 then decide (4 ≤ count737 b) else (if i < 742 then decide (5 ≤ count737 b) else decide (6 ≤ count737 b))))) else (if i < 749 then (if i < 746 then (if i < 744 then decide (1 ≤ count743 b) else (if i < 745 then decide (2 ≤ count743 b) else decide (1 ≤ count745 b))) else (if i < 747 then decide (2 ≤ count745 b) else (if i < 748 then decide (3 ≤ count745 b) else decide (1 ≤ count748 b)))) else (if i < 752 then (if i < 750 then decide (2 ≤ count748 b) else (if i < 751 then decide (1 ≤ count750 b) else decide (2 ≤ count750 b))) else (if i < 753 then decide (1 ≤ count752 b) else (if i < 754 then decide (2 ≤ count752 b) else decide (3 ≤ count752 b))))))))))) else (if i < 1132 then (if i < 943 then (if i < 849 then (if i < 802 then (if i < 778 then (if i < 766 then (if i < 760 then (if i < 757 then (if i < 756 then decide (4 ≤ count752 b) else decide (1 ≤ count756 b)) else (if i < 758 then decide (2 ≤ count756 b) else (if i < 759 then decide (3 ≤ count756 b) else decide (4 ≤ count756 b)))) else (if i < 763 then (if i < 761 then decide (5 ≤ count756 b) else (if i < 762 then decide (6 ≤ count756 b) else decide (7 ≤ count756 b))) else (if i < 764 then decide (1 ≤ count763 b) else (if i < 765 then decide (2 ≤ count763 b) else decide (3 ≤ count763 b))))) else (if i < 772 then (if i < 769 then (if i < 767 then decide (4 ≤ count763 b) else (if i < 768 then decide (5 ≤ count763 b) else decide (6 ≤ count763 b))) else (if i < 770 then decide (7 ≤ count763 b) else (if i < 771 then decide (8 ≤ count763 b) else decide (9 ≤ count763 b)))) else (if i < 775 then (if i < 773 then decide (10 ≤ count763 b) else (if i < 774 then decide (11 ≤ count763 b) else decide (12 ≤ count763 b))) else (if i < 776 then decide (13 ≤ count763 b) else (if i < 777 then decide (1 ≤ count776 b) else decide (2 ≤ count776 b)))))) else (if i < 790 then (if i < 784 then (if i < 781 then (if i < 779 then decide (1 ≤ count778 b) else (if i < 780 then decide (2 ≤ count778 b) else decide (3 ≤ count778 b))) else (if i < 782 then decide (1 ≤ count781 b) else (if i < 783 then decide (2 ≤ count781 b) else decide (1 ≤ count783 b)))) else (if i < 787 then (if i < 785 then decide (2 ≤ count783 b) else (if i < 786 then decide (1 ≤ count785 b) else decide (2 ≤ count785 b))) else (if i < 788 then decide (3 ≤ count785 b) else (if i < 789 then decide (4 ≤ count785 b) else decide (1 ≤ count789 b))))) else (if i < 796 then (if i < 793 then (if i < 791 then decide (2 ≤ count789 b) else (if i < 792 then decide (3 ≤ count789 b) else decide (4 ≤ count789 b))) else (if i < 794 then decide (5 ≤ count789 b) else (if i < 795 then decide (6 ≤ count789 b) else decide (7 ≤ count789 b)))) else (if i < 799 then (if i < 797 then decide (1 ≤ count796 b) else (if i < 798 then decide (2 ≤ count796 b) else decide (1 ≤ count798 b))) else (if i < 800 then decide (2 ≤ count798 b) else (if i < 801 then decide (3 ≤ count798 b) else decide (1 ≤ count801 b))))))) else (if i < 825 then (if i < 813 then (if i < 807 then (if i < 804 then (if i < 803 then decide (2 ≤ count801 b) else decide (1 ≤ count803 b)) else (if i < 805 then decide (2 ≤ count803 b) else (if i < 806 then decide (1 ≤ count805 b) else decide (2 ≤ count805 b)))) else (if i < 810 then (if i < 808 then decide (3 ≤ count805 b) else (if i < 809 then decide (4 ≤ count805 b) else decide (1 ≤ count809 b))) else (if i < 811 then decide (2 ≤ count809 b) else (if i < 812 then decide (3 ≤ count809 b) else decide (4 ≤ count809 b))))) else (if i < 819 then (if i < 816 then (if i < 814 then decide (5 ≤ count809 b) else (if i < 815 then decide (6 ≤ count809 b) else decide (7 ≤ count809 b))) else (if i < 817 then decide (1 ≤ count816 b) else (if i < 818 then decide (2 ≤ count816 b) else decide (3 ≤ count816 b)))) else (if i < 822 then (if i < 820 then decide (4 ≤ count816 b) else (if i < 821 then decide (5 ≤ count816 b) else decide (6 ≤ count816 b))) else (if i < 823 then decide (7 ≤ count816 b) else (if i < 824 then decide (8 ≤ count816 b) else decide (9 ≤ count816 b)))))) else (if i < 837 then (if i < 831 then (if i < 828 then (if i < 826 then decide (10 ≤ count816 b) else (if i < 827 then decide (11 ≤ count816 b) else decide (12 ≤ count816 b))) else (if i < 829 then decide (13 ≤ count816 b) else (if i < 830 then decide (14 ≤ count816 b) else decide (1 ≤ count830 b)))) else (if i < 834 then (if i < 832 then decide (2 ≤ count830 b) else (if i < 833 then decide (3 ≤ count830 b) else decide (4 ≤ count830 b))) else (if i < 835 then decide (5 ≤ count830 b) else (if i < 836 then decide (6 ≤ count830 b) else decide (7 ≤ count830 b))))) else (if i < 843 then (if i < 840 then (if i < 838 then decide (8 ≤ count830 b) else (if i < 839 then decide (9 ≤ count830 b) else decide (10 ≤ count830 b))) else (if i < 841 then decide (11 ≤ count830 b) else (if i < 842 then decide (12 ≤ count830 b) else decide (13 ≤ count830 b)))) else (if i < 846 then (if i < 844 then decide (14 ≤ count830 b) else (if i < 845 then decide (1 ≤ count844 b) else decide (2 ≤ count844 b))) else (if i < 847 then decide (1 ≤ count846 b) else (if i < 848 then decide (2 ≤ count846 b) else decide (3 ≤ count846 b)))))))) else (if i < 896 then (if i < 872 then (if i < 860 then (if i < 854 then (if i < 851 then (if i < 850 then decide (1 ≤ count849 b) else decide (2 ≤ count849 b)) else (if i < 852 then decide (1 ≤ count851 b) else (if i < 853 then decide (2 ≤ count851 b) else decide (3 ≤ count851 b)))) else (if i < 857 then (if i < 855 then decide (1 ≤ count854 b) else (if i < 856 then decide (2 ≤ count854 b) else decide (3 ≤ count854 b))) else (if i < 858 then decide (4 ≤ count854 b) else (if i < 859 then decide (5 ≤ count854 b) else decide (6 ≤ count854 b))))) else (if i < 866 then (if i < 863 then (if i < 861 then decide (1 ≤ count860 b) else (if i < 862 then decide (2 ≤ count860 b) else decide (1 ≤ count862 b))) else (if i < 864 then decide (2 ≤ count862 b) else (if i < 865 then decide (3 ≤ count862 b) else decide (1 ≤ count865 b)))) else (if i < 869 then (if i < 867 then decide (2 ≤ count865 b) else (if i < 868 then decide (1 ≤ count867 b) else decide (2 ≤ count867 b))) else (if i < 870 then decide (1 ≤ count869 b) else (if i < 871 then decide (2 ≤ count869 b) else decide (3 ≤ count869 b)))))) else (if i < 884 then (if i < 878 then (if i < 875 then (if i < 873 then decide (4 ≤ count869 b) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b))) else (if i < 876 then decide (3 ≤ count873 b) else (if i < 877 then decide (4 ≤ count873 b) else decide (5 ≤ count873 b)))) else (if i < 881 then (if i < 879 then decide (6 ≤ count873 b) else (if i < 880 then decide (7 ≤ count873 b) else decide (1 ≤ count880 b))) else (if i < 882 then decide (2 ≤ count880 b) else (if i < 883 then decide (3 ≤ count880 b) else decide (4 ≤ count880 b))))) else (if i < 890 then (if i < 887 then (if i < 885 then decide (5 ≤ count880 b) else (if i < 886 then decide (6 ≤ count880 b) else decide (7 ≤ count880 b))) else (if i < 888 then decide (8 ≤ count880 b) else (if i < 889 then decide (9 ≤ count880 b) else decide (10 ≤ count880 b)))) else (if i < 893 then (if i < 891 then decide (11 ≤ count880 b) else (if i < 892 then decide (12 ≤ count880 b) else decide (13 ≤ count880 b))) else (if i < 894 then decide (1 ≤ count893 b) else (if i < 895 then decide (2 ≤ count893 b) else decide (1 ≤ count895 b))))))) else (if i < 919 then (if i < 907 then (if i < 901 then (if i < 898 then (if i < 897 then decide (2 ≤ count895 b) else decide (3 ≤ count895 b)) else (if i < 899 then decide (1 ≤ count898 b) else (if i < 900 then decide (2 ≤ count898 b) else decide (1 ≤ count900 b)))) else (if i < 904 then (if i < 902 then decide (2 ≤ count900 b) else (if i < 903 then decide (1 ≤ count902 b) else decide (2 ≤ count902 b))) else (if i < 905 then decide (3 ≤ count902 b) else (if i < 906 then decide (4 ≤ count902 b) else decide (1 ≤ count906 b))))) else (if i < 913 then (if i < 910 then (if i < 908 then decide (2 ≤ count906 b) else (if i < 909 then decide (3 ≤ count906 b) else decide (4 ≤ count906 b))) else (if i < 911 then decide (5 ≤ count906 b) else (if i < 912 then decide (6 ≤ count906 b) else decide (7 ≤ count906 b)))) else (if i < 916 then (if i < 914 then decide (1 ≤ count913 b) else (if i < 915 then decide (2 ≤ count913 b) else decide (1 ≤ count915 b))) else (if i < 917 then decide (2 ≤ count915 b) else (if i < 918 then decide (3 ≤ count915 b) else decide (1 ≤ count918 b)))))) else (if i < 931 then (if i < 925 then (if i < 922 then (if i < 920 then decide (2 ≤ count918 b) else (if i < 921 then decide (1 ≤ count920 b) else decide (2 ≤ count920 b))) else (if i < 923 then decide (1 ≤ count922 b) else (if i < 924 then decide (2 ≤ count922 b) else decide (3 ≤ count922 b)))) else (if i < 928 then (if i < 926 then decide (4 ≤ count922 b) else (if i < 927 then decide (1 ≤ count926 b) else decide (2 ≤ count926 b))) else (if i < 929 then decide (3 ≤ count926 b) else (if i < 930 then decide (4 ≤ count926 b) else decide (5 ≤ count926 b))))) else (if i < 937 then (if i < 934 then (if i < 932 then decide (6 ≤ count926 b) else (if i < 933 then decide (7 ≤ count926 b) else decide (1 ≤ count933 b))) else (if i < 935 then decide (2 ≤ count933 b) else (if i < 936 then decide (3 ≤ count933 b) else decide (4 ≤ count933 b)))) else (if i < 940 then (if i < 938 then decide (5 ≤ count933 b) else (if i < 939 then decide (6 ≤ count933 b) else decide (7 ≤ count933 b))) else (if i < 941 then decide (8 ≤ count933 b) else (if i < 942 then decide (9 ≤ count933 b) else decide (10 ≤ count933 b))))))))) else (if i < 1037 then (if i < 990 then (if i < 966 then (if i < 954 then (if i < 948 then (if i < 945 then (if i < 944 then decide (11 ≤ count933 b) else decide (12 ≤ count933 b)) else (if i < 946 then decide (13 ≤ count933 b) else (if i < 947 then decide (14 ≤ count933 b) else decide (1 ≤ count947 b)))) else (if i < 951 then (if i < 949 then decide (2 ≤ count947 b) else (if i < 950 then decide (3 ≤ count947 b) else decide (4 ≤ count947 b))) else (if i < 952 then decide (5 ≤ count947 b) else (if i < 953 then decide (6 ≤ count947 b) else decide (7 ≤ count947 b))))) else (if i < 960 then (if i < 957 then (if i < 955 then decide (8 ≤ count947 b) else (if i < 956 then decide (9 ≤ count947 b) else decide (10 ≤ count947 b))) else (if i < 958 then decide (11 ≤ count947 b) else (if i < 959 then decide (12 ≤ count947 b) else decide (13 ≤ count947 b)))) else (if i < 963 then (if i < 961 then decide (14 ≤ count947 b) else (if i < 962 then decide (1 ≤ count961 b) else decide (2 ≤ count961 b))) else (if i < 964 then decide (3 ≤ count961 b) else (if i < 965 then decide (4 ≤ count961 b) else decide (5 ≤ count961 b)))))) else (if i < 978 then (if i < 972 then (if i < 969 then (if i < 967 then decide (6 ≤ count961 b) else (if i < 968 then decide (7 ≤ count961 b) else decide (8 ≤ count961 b))) else (if i < 970 then decide (9 ≤ count961 b) else (if i < 971 then decide (10 ≤ count961 b) else decide (11 ≤ count961 b)))) else (if i < 975 then (if i < 973 then decide (12 ≤ count961 b) else (if i < 974 then decide (13 ≤ count961 b) else decide (14 ≤ count961 b))) else (if i < 976 then decide (1 ≤ count975 b) else (if i < 977 then decide (2 ≤ count975 b) else decide (1 ≤ count977 b))))) else (if i < 984 then (if i < 981 then (if i < 979 then decide (2 ≤ count977 b) else (if i < 980 then decide (3 ≤ count977 b) else decide (1 ≤ count980 b))) else (if i < 982 then decide (2 ≤ count980 b) else (if i < 983 then decide (1 ≤ count982 b) else decide (2 ≤ count982 b)))) else (if i < 987 then (if i < 985 then decide (3 ≤ count982 b) else (if i < 986 then decide (1 ≤ count985 b) else decide (2 ≤ count985 b))) else (if i < 988 then decide (3 ≤ count985 b) else (if i < 989 then decide (4 ≤ count985 b) else decide (5 ≤ count985 b))))))) else (if i < 1013 then (if i < 1001 then (if i < 995 then (if i < 992 then (if i < 991 then decide (6 ≤ count985 b) else decide (1 ≤ count991 b)) else (if i < 993 then decide (2 ≤ count991 b) else (if i < 994 then decide (1 ≤ count993 b) else decide (2 ≤ count993 b)))) else (if i < 998 then (if i < 996 then decide (3 ≤ count993 b) else (if i < 997 then decide (1 ≤ count996 b) else decide (2 ≤ count996 b))) else (if i < 999 then decide (1 ≤ count998 b) else (if i < 1000 then decide (2 ≤ count998 b) else decide (1 ≤ count1000 b))))) else (if i < 1007 then (if i < 1004 then (if i < 1002 then decide (2 ≤ count1000 b) else (if i < 1003 then decide (3 ≤ count1000 b) else decide (4 ≤ count1000 b))) else (if i < 1005 then decide (1 ≤ count1004 b) else (if i < 1006 then decide (2 ≤ count1004 b) else decide (3 ≤ count1004 b)))) else (if i < 1010 then (if i < 1008 then decide (4 ≤ count1004 b) else (if i < 1009 then decide (5 ≤ count1004 b) else decide (6 ≤ count1004 b))) else (if i < 1011 then decide (7 ≤ count1004 b) else (if i < 1012 then decide (1 ≤ count1011 b) else decide (2 ≤ count1011 b)))))) else (if i < 1025 then (if i < 1019 then (if i < 1016 then (if i < 1014 then decide (3 ≤ count1011 b) else (if i < 1015 then decide (4 ≤ count1011 b) else decide (5 ≤ count1011 b))) else (if i < 1017 then decide (6 ≤ count1011 b) else (if i < 1018 then decide (7 ≤ count1011 b) else decide (8 ≤ count1011 b)))) else (if i < 1022 then (if i < 1020 then decide (9 ≤ count1011 b) else (if i < 1021 then decide (10 ≤ count1011 b) else decide (11 ≤ count1011 b))) else (if i < 1023 then decide (12 ≤ count1011 b) else (if i < 1024 then decide (13 ≤ count1011 b) else decide (1 ≤ count1024 b))))) else (if i < 1031 then (if i < 1028 then (if i < 1026 then decide (2 ≤ count1024 b) else (if i < 1027 then decide (1 ≤ count1026 b) else decide (2 ≤ count1026 b))) else (if i < 1029 then decide (3 ≤ count1026 b) else (if i < 1030 then decide (1 ≤ count1029 b) else decide (2 ≤ count1029 b)))) else (if i < 1034 then (if i < 1032 then decide (1 ≤ count1031 b) else (if i < 1033 then decide (2 ≤ count1031 b) else decide (3 ≤ count1031 b))) else (if i < 1035 then decide (1 ≤ count1034 b) else (if i < 1036 then decide (2 ≤ count1034 b) else decide (3 ≤ count1034 b)))))))) else (if i < 1084 then (if i < 1060 then (if i < 1048 then (if i < 1042 then (if i < 1039 then (if i < 1038 then decide (4 ≤ count1034 b) else decide (5 ≤ count1034 b)) else (if i < 1040 then decide (6 ≤ count1034 b) else (if i < 1041 then decide (1 ≤ count1040 b) else decide (2 ≤ count1040 b)))) else (if i < 1045 then (if i < 1043 then decide (1 ≤ count1042 b) else (if i < 1044 then decide (2 ≤ count1042 b) else decide (3 ≤ count1042 b))) else (if i < 1046 then decide (1 ≤ count1045 b) else (if i < 1047 then decide (2 ≤ count1045 b) else decide (1 ≤ count1047 b))))) else (if i < 1054 then (if i < 1051 then (if i < 1049 then decide (2 ≤ count1047 b) else (if i < 1050 then decide (1 ≤ count1049 b) else decide (2 ≤ count1049 b))) else (if i < 1052 then decide (3 ≤ count1049 b) else (if i < 1053 then decide (4 ≤ count1049 b) else decide (1 ≤ count1053 b)))) else (if i < 1057 then (if i < 1055 then decide (2 ≤ count1053 b) else (if i < 1056 then decide (3 ≤ count1053 b) else decide (4 ≤ count1053 b))) else (if i < 1058 then decide (5 ≤ count1053 b) else (if i < 1059 then decide (6 ≤ count1053 b) else decide (7 ≤ count1053 b)))))) else (if i < 1072 then (if i < 1066 then (if i < 1063 then (if i < 1061 then decide (1 ≤ count1060 b) else (if i < 1062 then decide (2 ≤ count1060 b) else decide (3 ≤ count1060 b))) else (if i < 1064 then decide (4 ≤ count1060 b) else (if i < 1065 then decide (5 ≤ count1060 b) else decide (6 ≤ count1060 b)))) else (if i < 1069 then (if i < 1067 then decide (7 ≤ count1060 b) else (if i < 1068 then decide (8 ≤ count1060 b) else decide (9 ≤ count1060 b))) else (if i < 1070 then decide (10 ≤ count1060 b) else (if i < 1071 then decide (11 ≤ count1060 b) else decide (12 ≤ count1060 b))))) else (if i < 1078 then (if i < 1075 then (if i < 1073 then decide (13 ≤ count1060 b) else (if i < 1074 then decide (1 ≤ count1073 b) else decide (2 ≤ count1073 b))) else (if i < 1076 then decide (3 ≤ count1073 b) else (if i < 1077 then decide (4 ≤ count1073 b) else decide (5 ≤ count1073 b)))) else (if i < 1081 then (if i < 1079 then decide (6 ≤ count1073 b) else (if i < 1080 then decide (7 ≤ count1073 b) else decide (8 ≤ count1073 b))) else (if i < 1082 then decide (9 ≤ count1073 b) else (if i < 1083 then decide (10 ≤ count1073 b) else decide (11 ≤ count1073 b))))))) else (if i < 1108 then (if i < 1096 then (if i < 1090 then (if i < 1087 then (if i < 1085 then decide (12 ≤ count1073 b) else (if i < 1086 then decide (13 ≤ count1073 b) else decide (14 ≤ count1073 b))) else (if i < 1088 then decide (15 ≤ count1073 b) else (if i < 1089 then decide (16 ≤ count1073 b) else decide (17 ≤ count1073 b)))) else (if i < 1093 then (if i < 1091 then decide (18 ≤ count1073 b) else (if i < 1092 then decide (19 ≤ count1073 b) else decide (20 ≤ count1073 b))) else (if i < 1094 then decide (21 ≤ count1073 b) else (if i < 1095 then decide (22 ≤ count1073 b) else decide (23 ≤ count1073 b))))) else (if i < 1102 then (if i < 1099 then (if i < 1097 then decide (24 ≤ count1073 b) else (if i < 1098 then decide (25 ≤ count1073 b) else decide (26 ≤ count1073 b))) else (if i < 1100 then decide (1 ≤ count1099 b) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (1 ≤ count1101 b)))) else (if i < 1105 then (if i < 1103 then decide (2 ≤ count1101 b) else (if i < 1104 then decide (3 ≤ count1101 b) else decide (1 ≤ count1104 b))) else (if i < 1106 then decide (2 ≤ count1104 b) else (if i < 1107 then decide (1 ≤ count1106 b) else decide (2 ≤ count1106 b)))))) else (if i < 1120 then (if i < 1114 then (if i < 1111 then (if i < 1109 then decide (3 ≤ count1106 b) else (if i < 1110 then decide (1 ≤ count1109 b) else decide (2 ≤ count1109 b))) else (if i < 1112 then decide (3 ≤ count1109 b) else (if i < 1113 then decide (4 ≤ count1109 b) else decide (5 ≤ count1109 b)))) else (if i < 1117 then (if i < 1115 then decide (6 ≤ count1109 b) else (if i < 1116 then decide (1 ≤ count1115 b) else decide (2 ≤ count1115 b))) else (if i < 1118 then decide (1 ≤ count1117 b) else (if i < 1119 then decide (2 ≤ count1117 b) else decide (3 ≤ count1117 b))))) else (if i < 1126 then (if i < 1123 then (if i < 1121 then decide (1 ≤ count1120 b) else (if i < 1122 then decide (2 ≤ count1120 b) else decide (1 ≤ count1122 b))) else (if i < 1124 then decide (2 ≤ count1122 b) else (if i < 1125 then decide (1 ≤ count1124 b) else decide (2 ≤ count1124 b)))) else (if i < 1129 then (if i < 1127 then decide (3 ≤ count1124 b) else (if i < 1128 then decide (4 ≤ count1124 b) else decide (1 ≤ count1128 b))) else (if i < 1130 then decide (2 ≤ count1128 b) else (if i < 1131 then decide (3 ≤ count1128 b) else decide (4 ≤ count1128 b)))))))))) else (if i < 1321 then (if i < 1226 then (if i < 1179 then (if i < 1155 then (if i < 1143 then (if i < 1137 then (if i < 1134 then (if i < 1133 then decide (5 ≤ count1128 b) else decide (6 ≤ count1128 b)) else (if i < 1135 then decide (7 ≤ count1128 b) else (if i < 1136 then decide (1 ≤ count1135 b) else decide (2 ≤ count1135 b)))) else (if i < 1140 then (if i < 1138 then decide (3 ≤ count1135 b) else (if i < 1139 then decide (4 ≤ count1135 b) else decide (5 ≤ count1135 b))) else (if i < 1141 then decide (6 ≤ count1135 b) else (if i < 1142 then decide (7 ≤ count1135 b) else decide (8 ≤ count1135 b))))) else (if i < 1149 then (if i < 1146 then (if i < 1144 then decide (9 ≤ count1135 b) else (if i < 1145 then decide (10 ≤ count1135 b) else decide (11 ≤ count1135 b))) else (if i < 1147 then decide (12 ≤ count1135 b) else (if i < 1148 then decide (13 ≤ count1135 b) else decide (1 ≤ count1148 b)))) else (if i < 1152 then (if i < 1150 then decide (2 ≤ count1148 b) else (if i < 1151 then decide (1 ≤ count1150 b) else decide (2 ≤ count1150 b))) else (if i < 1153 then decide (3 ≤ count1150 b) else (if i < 1154 then decide (1 ≤ count1153 b) else decide (2 ≤ count1153 b)))))) else (if i < 1167 then (if i < 1161 then (if i < 1158 then (if i < 1156 then decide (1 ≤ count1155 b) else (if i < 1157 then decide (2 ≤ count1155 b) else decide (1 ≤ count1157 b))) else (if i < 1159 then decide (2 ≤ count1157 b) else (if i < 1160 then decide (3 ≤ count1157 b) else decide (4 ≤ count1157 b)))) else (if i < 1164 then (if i < 1162 then decide (1 ≤ count1161 b) else (if i < 1163 then decide (2 ≤ count1161 b) else decide (3 ≤ count1161 b))) else (if i < 1165 then decide (4 ≤ count1161 b) else (if i < 1166 then decide (5 ≤ count1161 b) else decide (6 ≤ count1161 b))))) else (if i < 1173 then (if i < 1170 then (if i < 1168 then decide (7 ≤ count1161 b) else (if i < 1169 then decide (1 ≤ count1168 b) else decide (2 ≤ count1168 b))) else (if i < 1171 then decide (1 ≤ count1170 b) else (if i < 1172 then decide (2 ≤ count1170 b) else decide (3 ≤ count1170 b)))) else (if i < 1176 then (if i < 1174 then decide (1 ≤ count1173 b) else (if i < 1175 then decide (2 ≤ count1173 b) else decide (1 ≤ count1175 b))) else (if i < 1177 then decide (2 ≤ count1175 b) else (if i < 1178 then decide (1 ≤ count1177 b) else decide (2 ≤ count1177 b))))))) else (if i < 1202 then (if i < 1190 then (if i < 1184 then (if i < 1181 then (if i < 1180 then decide (3 ≤ count1177 b) else decide (4 ≤ count1177 b)) else (if i < 1182 then decide (1 ≤ count1181 b) else (if i < 1183 then decide (2 ≤ count1181 b) else decide (3 ≤ count1181 b)))) else (if i < 1187 then (if i < 1185 then decide (4 ≤ count1181 b) else (if i < 1186 then decide (5 ≤ count1181 b) else decide (6 ≤ count1181 b))) else (if i < 1188 then decide (7 ≤ count1181 b) else (if i < 1189 then decide (1 ≤ count1188 b) else decide (2 ≤ count1188 b))))) else (if i < 1196 then (if i < 1193 then (if i < 1191 then decide (3 ≤ count1188 b) else (if i < 1192 then decide (4 ≤ count1188 b) else decide (5 ≤ count1188 b))) else (if i < 1194 then decide (6 ≤ count1188 b) else (if i < 1195 then decide (7 ≤ count1188 b) else decide (8 ≤ count1188 b)))) else (if i < 1199 then (if i < 1197 then decide (9 ≤ count1188 b) else (if i < 1198 then decide (10 ≤ count1188 b) else decide (11 ≤ count1188 b))) else (if i < 1200 then decide (12 ≤ count1188 b) else (if i < 1201 then decide (13 ≤ count1188 b) else decide (14 ≤ count1188 b)))))) else (if i < 1214 then (if i < 1208 then (if i < 1205 then (if i < 1203 then decide (1 ≤ count1202 b) else (if i < 1204 then decide (2 ≤ count1202 b) else decide (3 ≤ count1202 b))) else (if i < 1206 then decide (4 ≤ count1202 b) else (if i < 1207 then decide (5 ≤ count1202 b) else decide (6 ≤ count1202 b)))) else (if i < 1211 then (if i < 1209 then decide (7 ≤ count1202 b) else (if i < 1210 then decide (8 ≤ count1202 b) else decide (9 ≤ count1202 b))) else (if i < 1212 then decide (10 ≤ count1202 b) else (if i < 1213 then decide (11 ≤ count1202 b) else decide (12 ≤ count1202 b))))) else (if i < 1220 then (if i < 1217 then (if i < 1215 then decide (13 ≤ count1202 b) else (if i < 1216 then decide (14 ≤ count1202 b) else decide (15 ≤ count1202 b))) else (if i < 1218 then decide (16 ≤ count1202 b) else (if i < 1219 then decide (17 ≤ count1202 b) else decide (18 ≤ count1202 b)))) else (if i < 1223 then (if i < 1221 then decide (19 ≤ count1202 b) else (if i < 1222 then decide (20 ≤ count1202 b) else decide (21 ≤ count1202 b))) else (if i < 1224 then decide (22 ≤ count1202 b) else (if i < 1225 then decide (23 ≤ count1202 b) else decide (24 ≤ count1202 b)))))))) else (if i < 1273 then (if i < 1249 then (if i < 1237 then (if i < 1231 then (if i < 1228 then (if i < 1227 then decide (25 ≤ count1202 b) else decide (26 ≤ count1202 b)) else (if i < 1229 then decide (27 ≤ count1202 b) else (if i < 1230 then decide (1 ≤ count1229 b) else decide (2 ≤ count1229 b)))) else (if i < 1234 then (if i < 1232 then decide (3 ≤ count1229 b) else (if i < 1233 then decide (4 ≤ count1229 b) else decide (5 ≤ count1229 b))) else (if i < 1235 then decide (6 ≤ count1229 b) else (if i < 1236 then decide (7 ≤ count1229 b) else decide (8 ≤ count1229 b))))) else (if i < 1243 then (if i < 1240 then (if i < 1238 then decide (9 ≤ count1229 b) else (if i < 1239 then decide (10 ≤ count1229 b) else decide (11 ≤ count1229 b))) else (if i < 1241 then decide (12 ≤ count1229 b) else (if i < 1242 then decide (13 ≤ count1229 b) else decide (14 ≤ count1229 b)))) else (if i < 1246 then (if i < 1244 then decide (15 ≤ count1229 b) else (if i < 1245 then decide (16 ≤ count1229 b) else decide (17 ≤ count1229 b))) else (if i < 1247 then decide (18 ≤ count1229 b) else (if i < 1248 then decide (19 ≤ count1229 b) else decide (20 ≤ count1229 b)))))) else (if i < 1261 then (if i < 1255 then (if i < 1252 then (if i < 1250 then decide (21 ≤ count1229 b) else (if i < 1251 then decide (22 ≤ count1229 b) else decide (23 ≤ count1229 b))) else (if i < 1253 then decide (24 ≤ count1229 b) else (if i < 1254 then decide (25 ≤ count1229 b) else decide (26 ≤ count1229 b)))) else (if i < 1258 then (if i < 1256 then decide (27 ≤ count1229 b) else (if i < 1257 then decide (28 ≤ count1229 b) else decide (29 ≤ count1229 b))) else (if i < 1259 then decide (30 ≤ count1229 b) else (if i < 1260 then decide (31 ≤ count1229 b) else decide (32 ≤ count1229 b))))) else (if i < 1267 then (if i < 1264 then (if i < 1262 then decide (33 ≤ count1229 b) else (if i < 1263 then decide (34 ≤ count1229 b) else decide (35 ≤ count1229 b))) else (if i < 1265 then decide (36 ≤ count1229 b) else (if i < 1266 then decide (37 ≤ count1229 b) else decide (38 ≤ count1229 b)))) else (if i < 1270 then (if i < 1268 then decide (39 ≤ count1229 b) else (if i < 1269 then decide (40 ≤ count1229 b) else decide (41 ≤ count1229 b))) else (if i < 1271 then decide (42 ≤ count1229 b) else (if i < 1272 then decide (1 ≤ count1271 b) else decide (2 ≤ count1271 b))))))) else (if i < 1297 then (if i < 1285 then (if i < 1279 then (if i < 1276 then (if i < 1274 then decide (1 ≤ count1273 b) else (if i < 1275 then decide (2 ≤ count1273 b) else decide (3 ≤ count1273 b))) else (if i < 1277 then decide (1 ≤ count1276 b) else (if i < 1278 then decide (2 ≤ count1276 b) else decide (1 ≤ count1278 b)))) else (if i < 1282 then (if i < 1280 then decide (2 ≤ count1278 b) else (if i < 1281 then decide (3 ≤ count1278 b) else decide (1 ≤ count1281 b))) else (if i < 1283 then decide (2 ≤ count1281 b) else (if i < 1284 then decide (3 ≤ count1281 b) else decide (4 ≤ count1281 b))))) else (if i < 1291 then (if i < 1288 then (if i < 1286 then decide (5 ≤ count1281 b) else (if i < 1287 then decide (6 ≤ count1281 b) else decide (1 ≤ count1287 b))) else (if i < 1289 then decide (2 ≤ count1287 b) else (if i < 1290 then decide (1 ≤ count1289 b) else decide (2 ≤ count1289 b)))) else (if i < 1294 then (if i < 1292 then decide (3 ≤ count1289 b) else (if i < 1293 then decide (1 ≤ count1292 b) else decide (2 ≤ count1292 b))) else (if i < 1295 then decide (1 ≤ count1294 b) else (if i < 1296 then decide (2 ≤ count1294 b) else decide (1 ≤ count1296 b)))))) else (if i < 1309 then (if i < 1303 then (if i < 1300 then (if i < 1298 then decide (2 ≤ count1296 b) else (if i < 1299 then decide (3 ≤ count1296 b) else decide (4 ≤ count1296 b))) else (if i < 1301 then decide (1 ≤ count1300 b) else (if i < 1302 then decide (2 ≤ count1300 b) else decide (3 ≤ count1300 b)))) else (if i < 1306 then (if i < 1304 then decide (4 ≤ count1300 b) else (if i < 1305 then decide (5 ≤ count1300 b) else decide (6 ≤ count1300 b))) else (if i < 1307 then decide (7 ≤ count1300 b) else (if i < 1308 then decide (1 ≤ count1307 b) else decide (2 ≤ count1307 b))))) else (if i < 1315 then (if i < 1312 then (if i < 1310 then decide (3 ≤ count1307 b) else (if i < 1311 then decide (4 ≤ count1307 b) else decide (5 ≤ count1307 b))) else (if i < 1313 then decide (6 ≤ count1307 b) else (if i < 1314 then decide (7 ≤ count1307 b) else decide (8 ≤ count1307 b)))) else (if i < 1318 then (if i < 1316 then decide (9 ≤ count1307 b) else (if i < 1317 then decide (10 ≤ count1307 b) else decide (11 ≤ count1307 b))) else (if i < 1319 then decide (12 ≤ count1307 b) else (if i < 1320 then decide (13 ≤ count1307 b) else decide (1 ≤ count1320 b))))))))) else (if i < 1415 then (if i < 1368 then (if i < 1344 then (if i < 1332 then (if i < 1326 then (if i < 1323 then (if i < 1322 then decide (2 ≤ count1320 b) else decide (1 ≤ count1322 b)) else (if i < 1324 then decide (2 ≤ count1322 b) else (if i < 1325 then decide (3 ≤ count1322 b) else decide (1 ≤ count1325 b)))) else (if i < 1329 then (if i < 1327 then decide (2 ≤ count1325 b) else (if i < 1328 then decide (1 ≤ count1327 b) else decide (2 ≤ count1327 b))) else (if i < 1330 then decide (3 ≤ count1327 b) else (if i < 1331 then decide (1 ≤ count1330 b) else decide (2 ≤ count1330 b))))) else (if i < 1338 then (if i < 1335 then (if i < 1333 then decide (3 ≤ count1330 b) else (if i < 1334 then decide (4 ≤ count1330 b) else decide (5 ≤ count1330 b))) else (if i < 1336 then decide (6 ≤ count1330 b) else (if i < 1337 then decide (1 ≤ count1336 b) else decide (2 ≤ count1336 b)))) else (if i < 1341 then (if i < 1339 then decide (1 ≤ count1338 b) else (if i < 1340 then decide (2 ≤ count1338 b) else decide (3 ≤ count1338 b))) else (if i < 1342 then decide (1 ≤ count1341 b) else (if i < 1343 then decide (2 ≤ count1341 b) else decide (1 ≤ count1343 b)))))) else (if i < 1356 then (if i < 1350 then (if i < 1347 then (if i < 1345 then decide (2 ≤ count1343 b) else (if i < 1346 then decide (1 ≤ count1345 b) else decide (2 ≤ count1345 b))) else (if i < 1348 then decide (3 ≤ count1345 b) else (if i < 1349 then decide (4 ≤ count1345 b) else decide (1 ≤ count1349 b)))) else (if i < 1353 then (if i < 1351 then decide (2 ≤ count1349 b) else (if i < 1352 then decide (3 ≤ count1349 b) else decide (4 ≤ count1349 b))) else (if i < 1354 then decide (5 ≤ count1349 b) else (if i < 1355 then decide (6 ≤ count1349 b) else decide (7 ≤ count1349 b))))) else (if i < 1362 then (if i < 1359 then (if i < 1357 then decide (1 ≤ count1356 b) else (if i < 1358 then decide (2 ≤ count1356 b) else decide (3 ≤ count1356 b))) else (if i < 1360 then decide (4 ≤ count1356 b) else (if i < 1361 then decide (5 ≤ count1356 b) else decide (6 ≤ count1356 b)))) else (if i < 1365 then (if i < 1363 then decide (7 ≤ count1356 b) else (if i < 1364 then decide (8 ≤ count1356 b) else decide (9 ≤ count1356 b))) else (if i < 1366 then decide (10 ≤ count1356 b) else (if i < 1367 then decide (11 ≤ count1356 b) else decide (12 ≤ count1356 b))))))) else (if i < 1391 then (if i < 1379 then (if i < 1373 then (if i < 1370 then (if i < 1369 then decide (13 ≤ count1356 b) else decide (1 ≤ count1369 b)) else (if i < 1371 then decide (2 ≤ count1369 b) else (if i < 1372 then decide (3 ≤ count1369 b) else decide (4 ≤ count1369 b)))) else (if i < 1376 then (if i < 1374 then decide (5 ≤ count1369 b) else (if i < 1375 then decide (6 ≤ count1369 b) else decide (7 ≤ count1369 b))) else (if i < 1377 then decide (8 ≤ count1369 b) else (if i < 1378 then decide (9 ≤ count1369 b) else decide (10 ≤ count1369 b))))) else (if i < 1385 then (if i < 1382 then (if i < 1380 then decide (11 ≤ count1369 b) else (if i < 1381 then decide (12 ≤ count1369 b) else decide (13 ≤ count1369 b))) else (if i < 1383 then decide (1 ≤ count1382 b) else (if i < 1384 then decide (2 ≤ count1382 b) else decide (1 ≤ count1384 b)))) else (if i < 1388 then (if i < 1386 then decide (2 ≤ count1384 b) else (if i < 1387 then decide (3 ≤ count1384 b) else decide (1 ≤ count1387 b))) else (if i < 1389 then decide (2 ≤ count1387 b) else (if i < 1390 then decide (1 ≤ count1389 b) else decide (2 ≤ count1389 b)))))) else (if i < 1403 then (if i < 1397 then (if i < 1394 then (if i < 1392 then decide (3 ≤ count1389 b) else (if i < 1393 then decide (1 ≤ count1392 b) else decide (2 ≤ count1392 b))) else (if i < 1395 then decide (3 ≤ count1392 b) else (if i < 1396 then decide (4 ≤ count1392 b) else decide (5 ≤ count1392 b)))) else (if i < 1400 then (if i < 1398 then decide (6 ≤ count1392 b) else (if i < 1399 then decide (1 ≤ count1398 b) else decide (2 ≤ count1398 b))) else (if i < 1401 then decide (1 ≤ count1400 b) else (if i < 1402 then decide (2 ≤ count1400 b) else decide (3 ≤ count1400 b))))) else (if i < 1409 then (if i < 1406 then (if i < 1404 then decide (1 ≤ count1403 b) else (if i < 1405 then decide (2 ≤ count1403 b) else decide (1 ≤ count1405 b))) else (if i < 1407 then decide (2 ≤ count1405 b) else (if i < 1408 then decide (1 ≤ count1407 b) else decide (2 ≤ count1407 b)))) else (if i < 1412 then (if i < 1410 then decide (3 ≤ count1407 b) else (if i < 1411 then decide (4 ≤ count1407 b) else decide (1 ≤ count1411 b))) else (if i < 1413 then decide (2 ≤ count1411 b) else (if i < 1414 then decide (3 ≤ count1411 b) else decide (4 ≤ count1411 b)))))))) else (if i < 1462 then (if i < 1438 then (if i < 1426 then (if i < 1420 then (if i < 1417 then (if i < 1416 then decide (5 ≤ count1411 b) else decide (6 ≤ count1411 b)) else (if i < 1418 then decide (7 ≤ count1411 b) else (if i < 1419 then decide (1 ≤ count1418 b) else decide (2 ≤ count1418 b)))) else (if i < 1423 then (if i < 1421 then decide (3 ≤ count1418 b) else (if i < 1422 then decide (4 ≤ count1418 b) else decide (5 ≤ count1418 b))) else (if i < 1424 then decide (6 ≤ count1418 b) else (if i < 1425 then decide (7 ≤ count1418 b) else decide (8 ≤ count1418 b))))) else (if i < 1432 then (if i < 1429 then (if i < 1427 then decide (9 ≤ count1418 b) else (if i < 1428 then decide (10 ≤ count1418 b) else decide (11 ≤ count1418 b))) else (if i < 1430 then decide (12 ≤ count1418 b) else (if i < 1431 then decide (13 ≤ count1418 b) else decide (1 ≤ count1431 b)))) else (if i < 1435 then (if i < 1433 then decide (2 ≤ count1431 b) else (if i < 1434 then decide (1 ≤ count1433 b) else decide (2 ≤ count1433 b))) else (if i < 1436 then decide (3 ≤ count1433 b) else (if i < 1437 then decide (1 ≤ count1436 b) else decide (2 ≤ count1436 b)))))) else (if i < 1450 then (if i < 1444 then (if i < 1441 then (if i < 1439 then decide (1 ≤ count1438 b) else (if i < 1440 then decide (2 ≤ count1438 b) else decide (1 ≤ count1440 b))) else (if i < 1442 then decide (2 ≤ count1440 b) else (if i < 1443 then decide (3 ≤ count1440 b) else decide (4 ≤ count1440 b)))) else (if i < 1447 then (if i < 1445 then decide (1 ≤ count1444 b) else (if i < 1446 then decide (2 ≤ count1444 b) else decide (3 ≤ count1444 b))) else (if i < 1448 then decide (4 ≤ count1444 b) else (if i < 1449 then decide (5 ≤ count1444 b) else decide (6 ≤ count1444 b))))) else (if i < 1456 then (if i < 1453 then (if i < 1451 then decide (7 ≤ count1444 b) else (if i < 1452 then decide (1 ≤ count1451 b) else decide (2 ≤ count1451 b))) else (if i < 1454 then decide (1 ≤ count1453 b) else (if i < 1455 then decide (2 ≤ count1453 b) else decide (3 ≤ count1453 b)))) else (if i < 1459 then (if i < 1457 then decide (1 ≤ count1456 b) else (if i < 1458 then decide (2 ≤ count1456 b) else decide (1 ≤ count1458 b))) else (if i < 1460 then decide (2 ≤ count1458 b) else (if i < 1461 then decide (1 ≤ count1460 b) else decide (2 ≤ count1460 b))))))) else (if i < 1486 then (if i < 1474 then (if i < 1468 then (if i < 1465 then (if i < 1463 then decide (3 ≤ count1460 b) else (if i < 1464 then decide (4 ≤ count1460 b) else decide (1 ≤ count1464 b))) else (if i < 1466 then decide (2 ≤ count1464 b) else (if i < 1467 then decide (3 ≤ count1464 b) else decide (4 ≤ count1464 b)))) else (if i < 1471 then (if i < 1469 then decide (5 ≤ count1464 b) else (if i < 1470 then decide (6 ≤ count1464 b) else decide (7 ≤ count1464 b))) else (if i < 1472 then decide (1 ≤ count1471 b) else (if i < 1473 then decide (2 ≤ count1471 b) else decide (3 ≤ count1471 b))))) else (if i < 1480 then (if i < 1477 then (if i < 1475 then decide (4 ≤ count1471 b) else (if i < 1476 then decide (5 ≤ count1471 b) else decide (6 ≤ count1471 b))) else (if i < 1478 then decide (7 ≤ count1471 b) else (if i < 1479 then decide (8 ≤ count1471 b) else decide (9 ≤ count1471 b)))) else (if i < 1483 then (if i < 1481 then decide (10 ≤ count1471 b) else (if i < 1482 then decide (11 ≤ count1471 b) else decide (12 ≤ count1471 b))) else (if i < 1484 then decide (13 ≤ count1471 b) else (if i < 1485 then decide (1 ≤ count1484 b) else decide (2 ≤ count1484 b)))))) else (if i < 1498 then (if i < 1492 then (if i < 1489 then (if i < 1487 then decide (3 ≤ count1484 b) else (if i < 1488 then decide (4 ≤ count1484 b) else decide (5 ≤ count1484 b))) else (if i < 1490 then decide (6 ≤ count1484 b) else (if i < 1491 then decide (7 ≤ count1484 b) else decide (8 ≤ count1484 b)))) else (if i < 1495 then (if i < 1493 then decide (9 ≤ count1484 b) else (if i < 1494 then decide (10 ≤ count1484 b) else decide (11 ≤ count1484 b))) else (if i < 1496 then decide (12 ≤ count1484 b) else (if i < 1497 then decide (13 ≤ count1484 b) else decide (1 ≤ count1497 b))))) else (if i < 1504 then (if i < 1501 then (if i < 1499 then decide (2 ≤ count1497 b) else (if i < 1500 then decide (3 ≤ count1497 b) else decide (4 ≤ count1497 b))) else (if i < 1502 then decide (5 ≤ count1497 b) else (if i < 1503 then decide (6 ≤ count1497 b) else decide (7 ≤ count1497 b)))) else (if i < 1507 then (if i < 1505 then decide (8 ≤ count1497 b) else (if i < 1506 then decide (9 ≤ count1497 b) else decide (10 ≤ count1497 b))) else (if i < 1508 then decide (11 ≤ count1497 b) else (if i < 1509 then decide (12 ≤ count1497 b) else decide (13 ≤ count1497 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (2 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (18 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (26 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (58 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (115 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (119 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (122 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (123 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (160 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (161 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (162 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (166 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (172 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (173 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (174 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (178 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (179 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (181 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (183 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (186 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (187 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (188 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (189 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (192 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (193 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (194 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (198 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (201 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (204 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (205 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (210 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (211 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (218 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (219 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (221 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (257 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (260 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (261 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (262 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (263 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (264 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (265 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (266 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (267 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (274 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (276 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (278 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (280 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (281 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (282 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (283 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (284 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (320 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (321 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (322 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (326 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (329 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (332 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (333 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (334 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (338 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (339 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (341 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (343 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (346 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (347 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (348 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (349 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (417 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (420 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (421 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (422 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (423 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (424 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (425 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (426 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (427 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (431 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (434 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (436 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (438 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (440 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (441 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (442 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (443 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (444 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (456 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (457 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (458 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (473 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (474 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (480 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (482 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (486 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (489 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (492 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (493 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (494 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (498 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (506 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (508 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (2 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (58 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (123 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (172 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (181 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (183 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (187 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (198 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (201 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (219 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (257 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (260 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (263 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (274 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (278 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (284 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (341 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (343 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (347 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (420 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (423 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (424 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (431 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (438 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (441 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (456 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (473 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (474 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (489 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (492 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (494 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (1 ≤ count215 (baseVal q)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (1 ≤ count217 (baseVal q)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (2 ≤ count223 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (2 ≤ count237 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value264 (q : Snake 81) : valuation q 264 = decide (2 ≤ count263 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value420 (q : Snake 81) : valuation q 420 = decide (2 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value422 (q : Snake 81) : valuation q 422 = decide (2 ≤ count421 (baseVal q)) := rfl
theorem value424 (q : Snake 81) : valuation q 424 = decide (2 ≤ count423 (baseVal q)) := rfl
theorem value727 (q : Snake 81) : valuation q 727 = decide (1 ≤ count727 (baseVal q)) := rfl
theorem value728 (q : Snake 81) : valuation q 728 = decide (2 ≤ count727 (baseVal q)) := rfl
theorem value729 (q : Snake 81) : valuation q 729 = decide (1 ≤ count729 (baseVal q)) := rfl
theorem value730 (q : Snake 81) : valuation q 730 = decide (2 ≤ count729 (baseVal q)) := rfl
theorem value731 (q : Snake 81) : valuation q 731 = decide (3 ≤ count729 (baseVal q)) := rfl
theorem value732 (q : Snake 81) : valuation q 732 = decide (1 ≤ count732 (baseVal q)) := rfl
theorem value734 (q : Snake 81) : valuation q 734 = decide (1 ≤ count734 (baseVal q)) := rfl
theorem value737 (q : Snake 81) : valuation q 737 = decide (1 ≤ count737 (baseVal q)) := rfl
theorem value738 (q : Snake 81) : valuation q 738 = decide (2 ≤ count737 (baseVal q)) := rfl
theorem value739 (q : Snake 81) : valuation q 739 = decide (3 ≤ count737 (baseVal q)) := rfl
theorem value743 (q : Snake 81) : valuation q 743 = decide (1 ≤ count743 (baseVal q)) := rfl
theorem value744 (q : Snake 81) : valuation q 744 = decide (2 ≤ count743 (baseVal q)) := rfl
theorem value745 (q : Snake 81) : valuation q 745 = decide (1 ≤ count745 (baseVal q)) := rfl
theorem value746 (q : Snake 81) : valuation q 746 = decide (2 ≤ count745 (baseVal q)) := rfl
theorem value748 (q : Snake 81) : valuation q 748 = decide (1 ≤ count748 (baseVal q)) := rfl
theorem value749 (q : Snake 81) : valuation q 749 = decide (2 ≤ count748 (baseVal q)) := rfl
theorem value750 (q : Snake 81) : valuation q 750 = decide (1 ≤ count750 (baseVal q)) := rfl
theorem value752 (q : Snake 81) : valuation q 752 = decide (1 ≤ count752 (baseVal q)) := rfl
theorem value753 (q : Snake 81) : valuation q 753 = decide (2 ≤ count752 (baseVal q)) := rfl
theorem value754 (q : Snake 81) : valuation q 754 = decide (3 ≤ count752 (baseVal q)) := rfl
theorem value756 (q : Snake 81) : valuation q 756 = decide (1 ≤ count756 (baseVal q)) := rfl
theorem value757 (q : Snake 81) : valuation q 757 = decide (2 ≤ count756 (baseVal q)) := rfl
theorem value758 (q : Snake 81) : valuation q 758 = decide (3 ≤ count756 (baseVal q)) := rfl
theorem value759 (q : Snake 81) : valuation q 759 = decide (4 ≤ count756 (baseVal q)) := rfl
theorem value764 (q : Snake 81) : valuation q 764 = decide (2 ≤ count763 (baseVal q)) := rfl
theorem value765 (q : Snake 81) : valuation q 765 = decide (3 ≤ count763 (baseVal q)) := rfl
theorem value766 (q : Snake 81) : valuation q 766 = decide (4 ≤ count763 (baseVal q)) := rfl
theorem value767 (q : Snake 81) : valuation q 767 = decide (5 ≤ count763 (baseVal q)) := rfl
theorem value776 (q : Snake 81) : valuation q 776 = decide (1 ≤ count776 (baseVal q)) := rfl
theorem value778 (q : Snake 81) : valuation q 778 = decide (1 ≤ count778 (baseVal q)) := rfl
theorem value779 (q : Snake 81) : valuation q 779 = decide (2 ≤ count778 (baseVal q)) := rfl
theorem value781 (q : Snake 81) : valuation q 781 = decide (1 ≤ count781 (baseVal q)) := rfl
theorem value783 (q : Snake 81) : valuation q 783 = decide (1 ≤ count783 (baseVal q)) := rfl
theorem value785 (q : Snake 81) : valuation q 785 = decide (1 ≤ count785 (baseVal q)) := rfl
theorem value786 (q : Snake 81) : valuation q 786 = decide (2 ≤ count785 (baseVal q)) := rfl
theorem value789 (q : Snake 81) : valuation q 789 = decide (1 ≤ count789 (baseVal q)) := rfl
theorem value790 (q : Snake 81) : valuation q 790 = decide (2 ≤ count789 (baseVal q)) := rfl
theorem value791 (q : Snake 81) : valuation q 791 = decide (3 ≤ count789 (baseVal q)) := rfl
theorem value796 (q : Snake 81) : valuation q 796 = decide (1 ≤ count796 (baseVal q)) := rfl
theorem value797 (q : Snake 81) : valuation q 797 = decide (2 ≤ count796 (baseVal q)) := rfl
theorem value798 (q : Snake 81) : valuation q 798 = decide (1 ≤ count798 (baseVal q)) := rfl
theorem value799 (q : Snake 81) : valuation q 799 = decide (2 ≤ count798 (baseVal q)) := rfl
theorem value801 (q : Snake 81) : valuation q 801 = decide (1 ≤ count801 (baseVal q)) := rfl
theorem value802 (q : Snake 81) : valuation q 802 = decide (2 ≤ count801 (baseVal q)) := rfl
theorem value803 (q : Snake 81) : valuation q 803 = decide (1 ≤ count803 (baseVal q)) := rfl
theorem value804 (q : Snake 81) : valuation q 804 = decide (2 ≤ count803 (baseVal q)) := rfl
theorem value805 (q : Snake 81) : valuation q 805 = decide (1 ≤ count805 (baseVal q)) := rfl
theorem value806 (q : Snake 81) : valuation q 806 = decide (2 ≤ count805 (baseVal q)) := rfl
theorem value809 (q : Snake 81) : valuation q 809 = decide (1 ≤ count809 (baseVal q)) := rfl
theorem value810 (q : Snake 81) : valuation q 810 = decide (2 ≤ count809 (baseVal q)) := rfl
theorem value816 (q : Snake 81) : valuation q 816 = decide (1 ≤ count816 (baseVal q)) := rfl
theorem value817 (q : Snake 81) : valuation q 817 = decide (2 ≤ count816 (baseVal q)) := rfl
theorem value818 (q : Snake 81) : valuation q 818 = decide (3 ≤ count816 (baseVal q)) := rfl
theorem value819 (q : Snake 81) : valuation q 819 = decide (4 ≤ count816 (baseVal q)) := rfl
theorem value833 (q : Snake 81) : valuation q 833 = decide (4 ≤ count830 (baseVal q)) := rfl
theorem value834 (q : Snake 81) : valuation q 834 = decide (5 ≤ count830 (baseVal q)) := rfl
theorem value835 (q : Snake 81) : valuation q 835 = decide (6 ≤ count830 (baseVal q)) := rfl
theorem value836 (q : Snake 81) : valuation q 836 = decide (7 ≤ count830 (baseVal q)) := rfl
theorem value837 (q : Snake 81) : valuation q 837 = decide (8 ≤ count830 (baseVal q)) := rfl
theorem value844 (q : Snake 81) : valuation q 844 = decide (1 ≤ count844 (baseVal q)) := rfl
theorem value846 (q : Snake 81) : valuation q 846 = decide (1 ≤ count846 (baseVal q)) := rfl
theorem value847 (q : Snake 81) : valuation q 847 = decide (2 ≤ count846 (baseVal q)) := rfl
theorem value849 (q : Snake 81) : valuation q 849 = decide (1 ≤ count849 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (2 ≤ count849 (baseVal q)) := rfl
theorem value851 (q : Snake 81) : valuation q 851 = decide (1 ≤ count851 (baseVal q)) := rfl
theorem value852 (q : Snake 81) : valuation q 852 = decide (2 ≤ count851 (baseVal q)) := rfl
theorem value854 (q : Snake 81) : valuation q 854 = decide (1 ≤ count854 (baseVal q)) := rfl
theorem value855 (q : Snake 81) : valuation q 855 = decide (2 ≤ count854 (baseVal q)) := rfl
theorem value856 (q : Snake 81) : valuation q 856 = decide (3 ≤ count854 (baseVal q)) := rfl
theorem value860 (q : Snake 81) : valuation q 860 = decide (1 ≤ count860 (baseVal q)) := rfl
theorem value862 (q : Snake 81) : valuation q 862 = decide (1 ≤ count862 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (2 ≤ count862 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (1 ≤ count865 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (2 ≤ count865 (baseVal q)) := rfl
theorem value867 (q : Snake 81) : valuation q 867 = decide (1 ≤ count867 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (2 ≤ count867 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (1 ≤ count869 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (2 ≤ count869 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (3 ≤ count869 (baseVal q)) := rfl
theorem value873 (q : Snake 81) : valuation q 873 = decide (1 ≤ count873 (baseVal q)) := rfl
theorem value874 (q : Snake 81) : valuation q 874 = decide (2 ≤ count873 (baseVal q)) := rfl
theorem value875 (q : Snake 81) : valuation q 875 = decide (3 ≤ count873 (baseVal q)) := rfl
theorem value876 (q : Snake 81) : valuation q 876 = decide (4 ≤ count873 (baseVal q)) := rfl
theorem value880 (q : Snake 81) : valuation q 880 = decide (1 ≤ count880 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (2 ≤ count880 (baseVal q)) := rfl
theorem value882 (q : Snake 81) : valuation q 882 = decide (3 ≤ count880 (baseVal q)) := rfl
theorem value883 (q : Snake 81) : valuation q 883 = decide (4 ≤ count880 (baseVal q)) := rfl
theorem value884 (q : Snake 81) : valuation q 884 = decide (5 ≤ count880 (baseVal q)) := rfl
theorem value885 (q : Snake 81) : valuation q 885 = decide (6 ≤ count880 (baseVal q)) := rfl
theorem value893 (q : Snake 81) : valuation q 893 = decide (1 ≤ count893 (baseVal q)) := rfl
theorem value894 (q : Snake 81) : valuation q 894 = decide (2 ≤ count893 (baseVal q)) := rfl
theorem value895 (q : Snake 81) : valuation q 895 = decide (1 ≤ count895 (baseVal q)) := rfl
theorem value896 (q : Snake 81) : valuation q 896 = decide (2 ≤ count895 (baseVal q)) := rfl
theorem value897 (q : Snake 81) : valuation q 897 = decide (3 ≤ count895 (baseVal q)) := rfl
theorem value898 (q : Snake 81) : valuation q 898 = decide (1 ≤ count898 (baseVal q)) := rfl
theorem value899 (q : Snake 81) : valuation q 899 = decide (2 ≤ count898 (baseVal q)) := rfl
theorem value900 (q : Snake 81) : valuation q 900 = decide (1 ≤ count900 (baseVal q)) := rfl
theorem value901 (q : Snake 81) : valuation q 901 = decide (2 ≤ count900 (baseVal q)) := rfl
theorem value902 (q : Snake 81) : valuation q 902 = decide (1 ≤ count902 (baseVal q)) := rfl
theorem value903 (q : Snake 81) : valuation q 903 = decide (2 ≤ count902 (baseVal q)) := rfl
theorem value904 (q : Snake 81) : valuation q 904 = decide (3 ≤ count902 (baseVal q)) := rfl
theorem value906 (q : Snake 81) : valuation q 906 = decide (1 ≤ count906 (baseVal q)) := rfl
theorem value907 (q : Snake 81) : valuation q 907 = decide (2 ≤ count906 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (3 ≤ count906 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (4 ≤ count906 (baseVal q)) := rfl
theorem value910 (q : Snake 81) : valuation q 910 = decide (5 ≤ count906 (baseVal q)) := rfl
theorem value913 (q : Snake 81) : valuation q 913 = decide (1 ≤ count913 (baseVal q)) := rfl
theorem value914 (q : Snake 81) : valuation q 914 = decide (2 ≤ count913 (baseVal q)) := rfl
theorem value916 (q : Snake 81) : valuation q 916 = decide (2 ≤ count915 (baseVal q)) := rfl
theorem value917 (q : Snake 81) : valuation q 917 = decide (3 ≤ count915 (baseVal q)) := rfl
theorem value918 (q : Snake 81) : valuation q 918 = decide (1 ≤ count918 (baseVal q)) := rfl
theorem value919 (q : Snake 81) : valuation q 919 = decide (2 ≤ count918 (baseVal q)) := rfl
theorem value920 (q : Snake 81) : valuation q 920 = decide (1 ≤ count920 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (2 ≤ count920 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (1 ≤ count922 (baseVal q)) := rfl
theorem value923 (q : Snake 81) : valuation q 923 = decide (2 ≤ count922 (baseVal q)) := rfl
theorem value924 (q : Snake 81) : valuation q 924 = decide (3 ≤ count922 (baseVal q)) := rfl
theorem value925 (q : Snake 81) : valuation q 925 = decide (4 ≤ count922 (baseVal q)) := rfl
theorem value927 (q : Snake 81) : valuation q 927 = decide (2 ≤ count926 (baseVal q)) := rfl
theorem value928 (q : Snake 81) : valuation q 928 = decide (3 ≤ count926 (baseVal q)) := rfl
theorem value929 (q : Snake 81) : valuation q 929 = decide (4 ≤ count926 (baseVal q)) := rfl
theorem value930 (q : Snake 81) : valuation q 930 = decide (5 ≤ count926 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (6 ≤ count926 (baseVal q)) := rfl
theorem value936 (q : Snake 81) : valuation q 936 = decide (4 ≤ count933 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (5 ≤ count933 (baseVal q)) := rfl
theorem value938 (q : Snake 81) : valuation q 938 = decide (6 ≤ count933 (baseVal q)) := rfl
theorem value939 (q : Snake 81) : valuation q 939 = decide (7 ≤ count933 (baseVal q)) := rfl
theorem value940 (q : Snake 81) : valuation q 940 = decide (8 ≤ count933 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (9 ≤ count933 (baseVal q)) := rfl
theorem value952 (q : Snake 81) : valuation q 952 = decide (6 ≤ count947 (baseVal q)) := rfl
theorem value953 (q : Snake 81) : valuation q 953 = decide (7 ≤ count947 (baseVal q)) := rfl
theorem value954 (q : Snake 81) : valuation q 954 = decide (8 ≤ count947 (baseVal q)) := rfl
theorem value955 (q : Snake 81) : valuation q 955 = decide (9 ≤ count947 (baseVal q)) := rfl
theorem value956 (q : Snake 81) : valuation q 956 = decide (10 ≤ count947 (baseVal q)) := rfl
theorem value974 (q : Snake 81) : valuation q 974 = decide (14 ≤ count961 (baseVal q)) := rfl
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
theorem meaningNeg101 (b : Nat → Bool) : literal (valuationOf b) (-101) = decide (1 ≤ countLit b [-101]) := by
  change literal b (-101) = decide (1 ≤ countLit b [-101])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-101) <;> decide
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
theorem meaningNeg93 (b : Nat → Bool) : literal (valuationOf b) (-93) = decide (1 ≤ countLit b [-93]) := by
  change literal b (-93) = decide (1 ≤ countLit b [-93])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-93) <;> decide
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
theorem meaningNeg83 (b : Nat → Bool) : literal (valuationOf b) (-83) = decide (1 ≤ countLit b [-83]) := by
  change literal b (-83) = decide (1 ≤ countLit b [-83])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-83) <;> decide
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
theorem meaningNeg76 (b : Nat → Bool) : literal (valuationOf b) (-76) = decide (1 ≤ countLit b [-76]) := by
  change literal b (-76) = decide (1 ≤ countLit b [-76])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-76) <;> decide
theorem meaningNeg75 (b : Nat → Bool) : literal (valuationOf b) (-75) = decide (1 ≤ countLit b [-75]) := by
  change literal b (-75) = decide (1 ≤ countLit b [-75])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-75) <;> decide
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
theorem meaningNeg56 (b : Nat → Bool) : literal (valuationOf b) (-56) = decide (1 ≤ countLit b [-56]) := by
  change literal b (-56) = decide (1 ≤ countLit b [-56])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-56) <;> decide
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
theorem meaningNeg38 (b : Nat → Bool) : literal (valuationOf b) (-38) = decide (1 ≤ countLit b [-38]) := by
  change literal b (-38) = decide (1 ≤ countLit b [-38])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-38) <;> decide
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
theorem meaningNeg29 (b : Nat → Bool) : literal (valuationOf b) (-29) = decide (1 ≤ countLit b [-29]) := by
  change literal b (-29) = decide (1 ≤ countLit b [-29])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-29) <;> decide
theorem meaningNeg28 (b : Nat → Bool) : literal (valuationOf b) (-28) = decide (1 ≤ countLit b [-28]) := by
  change literal b (-28) = decide (1 ≤ countLit b [-28])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-28) <;> decide
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
theorem meaningNeg5 (b : Nat → Bool) : literal (valuationOf b) (-5) = decide (1 ≤ countLit b [-5]) := by
  change literal b (-5) = decide (1 ≤ countLit b [-5])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-5) <;> decide
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
theorem meaning115 (b : Nat → Bool) : literal (valuationOf b) (115) = decide (1 ≤ countLit b [115]) := by
  change literal b (115) = decide (1 ≤ countLit b [115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (115) <;> decide
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
theorem meaning125 (b : Nat → Bool) : literal (valuationOf b) (125) = decide (1 ≤ countLit b [125]) := by
  change literal b (125) = decide (1 ≤ countLit b [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (125) <;> decide
theorem meaning126 (b : Nat → Bool) : literal (valuationOf b) (126) = decide (1 ≤ countLit b [126]) := by
  change literal b (126) = decide (1 ≤ countLit b [126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (126) <;> decide
theorem meaning128 (b : Nat → Bool) : literal (valuationOf b) (128) = decide (1 ≤ countLit b [128]) := by
  change literal b (128) = decide (1 ≤ countLit b [128])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (128) <;> decide
theorem meaning133 (b : Nat → Bool) : literal (valuationOf b) (133) = decide (1 ≤ countLit b [133]) := by
  change literal b (133) = decide (1 ≤ countLit b [133])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (133) <;> decide
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
theorem meaning167 (b : Nat → Bool) : literal (valuationOf b) (167) = decide (1 ≤ countLit b [167]) := by
  change literal b (167) = decide (1 ≤ countLit b [167])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (167) <;> decide
theorem meaning176 (b : Nat → Bool) : literal (valuationOf b) (176) = decide (1 ≤ countLit b [176]) := by
  change literal b (176) = decide (1 ≤ countLit b [176])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (176) <;> decide
theorem meaning178 (b : Nat → Bool) : literal (valuationOf b) (178) = decide (1 ≤ countLit b [178]) := by
  change literal b (178) = decide (1 ≤ countLit b [178])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (178) <;> decide
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
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
theorem meaning202 (b : Nat → Bool) : literal (valuationOf b) (202) = decide (1 ≤ countLit b [202]) := by
  change literal b (202) = decide (1 ≤ countLit b [202])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (202) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning210 (b : Nat → Bool) : literal (valuationOf b) (210) = decide (1 ≤ countLit b [210]) := by
  change literal b (210) = decide (1 ≤ countLit b [210])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (210) <;> decide
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) (211) = decide (1 ≤ countLit b [211]) := by
  change literal b (211) = decide (1 ≤ countLit b [211])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (211) <;> decide
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) 215 = decide (1 ≤ count215 b) := rfl
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) 217 = decide (1 ≤ count217 b) := rfl
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning224 (b : Nat → Bool) : literal (valuationOf b) 224 = decide (2 ≤ count223 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) 238 = decide (2 ≤ count237 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning264 (b : Nat → Bool) : literal (valuationOf b) 264 = decide (2 ≤ count263 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning420 (b : Nat → Bool) : literal (valuationOf b) 420 = decide (2 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning422 (b : Nat → Bool) : literal (valuationOf b) 422 = decide (2 ≤ count421 b) := rfl
theorem meaning424 (b : Nat → Bool) : literal (valuationOf b) 424 = decide (2 ≤ count423 b) := rfl
theorem meaning727 (b : Nat → Bool) : literal (valuationOf b) 727 = decide (1 ≤ count727 b) := rfl
theorem meaning728 (b : Nat → Bool) : literal (valuationOf b) 728 = decide (2 ≤ count727 b) := rfl
theorem meaning729 (b : Nat → Bool) : literal (valuationOf b) 729 = decide (1 ≤ count729 b) := rfl
theorem meaning730 (b : Nat → Bool) : literal (valuationOf b) 730 = decide (2 ≤ count729 b) := rfl
theorem meaning731 (b : Nat → Bool) : literal (valuationOf b) 731 = decide (3 ≤ count729 b) := rfl
theorem meaning732 (b : Nat → Bool) : literal (valuationOf b) 732 = decide (1 ≤ count732 b) := rfl
theorem meaning734 (b : Nat → Bool) : literal (valuationOf b) 734 = decide (1 ≤ count734 b) := rfl
theorem meaning737 (b : Nat → Bool) : literal (valuationOf b) 737 = decide (1 ≤ count737 b) := rfl
theorem meaning738 (b : Nat → Bool) : literal (valuationOf b) 738 = decide (2 ≤ count737 b) := rfl
theorem meaning739 (b : Nat → Bool) : literal (valuationOf b) 739 = decide (3 ≤ count737 b) := rfl
theorem meaning743 (b : Nat → Bool) : literal (valuationOf b) 743 = decide (1 ≤ count743 b) := rfl
theorem meaning744 (b : Nat → Bool) : literal (valuationOf b) 744 = decide (2 ≤ count743 b) := rfl
theorem meaning745 (b : Nat → Bool) : literal (valuationOf b) 745 = decide (1 ≤ count745 b) := rfl
theorem meaning746 (b : Nat → Bool) : literal (valuationOf b) 746 = decide (2 ≤ count745 b) := rfl
theorem meaning748 (b : Nat → Bool) : literal (valuationOf b) 748 = decide (1 ≤ count748 b) := rfl
theorem meaning749 (b : Nat → Bool) : literal (valuationOf b) 749 = decide (2 ≤ count748 b) := rfl
theorem meaning750 (b : Nat → Bool) : literal (valuationOf b) 750 = decide (1 ≤ count750 b) := rfl
theorem meaning752 (b : Nat → Bool) : literal (valuationOf b) 752 = decide (1 ≤ count752 b) := rfl
theorem meaning753 (b : Nat → Bool) : literal (valuationOf b) 753 = decide (2 ≤ count752 b) := rfl
theorem meaning754 (b : Nat → Bool) : literal (valuationOf b) 754 = decide (3 ≤ count752 b) := rfl
theorem meaning756 (b : Nat → Bool) : literal (valuationOf b) 756 = decide (1 ≤ count756 b) := rfl
theorem meaning757 (b : Nat → Bool) : literal (valuationOf b) 757 = decide (2 ≤ count756 b) := rfl
theorem meaning758 (b : Nat → Bool) : literal (valuationOf b) 758 = decide (3 ≤ count756 b) := rfl
theorem meaning759 (b : Nat → Bool) : literal (valuationOf b) 759 = decide (4 ≤ count756 b) := rfl
theorem meaning764 (b : Nat → Bool) : literal (valuationOf b) 764 = decide (2 ≤ count763 b) := rfl
theorem meaning765 (b : Nat → Bool) : literal (valuationOf b) 765 = decide (3 ≤ count763 b) := rfl
theorem meaning766 (b : Nat → Bool) : literal (valuationOf b) 766 = decide (4 ≤ count763 b) := rfl
theorem meaning767 (b : Nat → Bool) : literal (valuationOf b) 767 = decide (5 ≤ count763 b) := rfl
theorem meaning776 (b : Nat → Bool) : literal (valuationOf b) 776 = decide (1 ≤ count776 b) := rfl
theorem meaning778 (b : Nat → Bool) : literal (valuationOf b) 778 = decide (1 ≤ count778 b) := rfl
theorem meaning779 (b : Nat → Bool) : literal (valuationOf b) 779 = decide (2 ≤ count778 b) := rfl
theorem meaning781 (b : Nat → Bool) : literal (valuationOf b) 781 = decide (1 ≤ count781 b) := rfl
theorem meaning783 (b : Nat → Bool) : literal (valuationOf b) 783 = decide (1 ≤ count783 b) := rfl
theorem meaning785 (b : Nat → Bool) : literal (valuationOf b) 785 = decide (1 ≤ count785 b) := rfl
theorem meaning786 (b : Nat → Bool) : literal (valuationOf b) 786 = decide (2 ≤ count785 b) := rfl
theorem meaning789 (b : Nat → Bool) : literal (valuationOf b) 789 = decide (1 ≤ count789 b) := rfl
theorem meaning790 (b : Nat → Bool) : literal (valuationOf b) 790 = decide (2 ≤ count789 b) := rfl
theorem meaning791 (b : Nat → Bool) : literal (valuationOf b) 791 = decide (3 ≤ count789 b) := rfl
theorem meaning796 (b : Nat → Bool) : literal (valuationOf b) 796 = decide (1 ≤ count796 b) := rfl
theorem meaning797 (b : Nat → Bool) : literal (valuationOf b) 797 = decide (2 ≤ count796 b) := rfl
theorem meaning798 (b : Nat → Bool) : literal (valuationOf b) 798 = decide (1 ≤ count798 b) := rfl
theorem meaning799 (b : Nat → Bool) : literal (valuationOf b) 799 = decide (2 ≤ count798 b) := rfl
theorem meaning801 (b : Nat → Bool) : literal (valuationOf b) 801 = decide (1 ≤ count801 b) := rfl
theorem meaning802 (b : Nat → Bool) : literal (valuationOf b) 802 = decide (2 ≤ count801 b) := rfl
theorem meaning803 (b : Nat → Bool) : literal (valuationOf b) 803 = decide (1 ≤ count803 b) := rfl
theorem meaning804 (b : Nat → Bool) : literal (valuationOf b) 804 = decide (2 ≤ count803 b) := rfl
theorem meaning805 (b : Nat → Bool) : literal (valuationOf b) 805 = decide (1 ≤ count805 b) := rfl
theorem meaning806 (b : Nat → Bool) : literal (valuationOf b) 806 = decide (2 ≤ count805 b) := rfl
theorem meaning809 (b : Nat → Bool) : literal (valuationOf b) 809 = decide (1 ≤ count809 b) := rfl
theorem meaning810 (b : Nat → Bool) : literal (valuationOf b) 810 = decide (2 ≤ count809 b) := rfl
theorem meaning816 (b : Nat → Bool) : literal (valuationOf b) 816 = decide (1 ≤ count816 b) := rfl
theorem meaning817 (b : Nat → Bool) : literal (valuationOf b) 817 = decide (2 ≤ count816 b) := rfl
theorem meaning818 (b : Nat → Bool) : literal (valuationOf b) 818 = decide (3 ≤ count816 b) := rfl
theorem meaning819 (b : Nat → Bool) : literal (valuationOf b) 819 = decide (4 ≤ count816 b) := rfl
theorem meaning833 (b : Nat → Bool) : literal (valuationOf b) 833 = decide (4 ≤ count830 b) := rfl
theorem meaning834 (b : Nat → Bool) : literal (valuationOf b) 834 = decide (5 ≤ count830 b) := rfl
theorem meaning835 (b : Nat → Bool) : literal (valuationOf b) 835 = decide (6 ≤ count830 b) := rfl
theorem meaning836 (b : Nat → Bool) : literal (valuationOf b) 836 = decide (7 ≤ count830 b) := rfl
theorem meaning837 (b : Nat → Bool) : literal (valuationOf b) 837 = decide (8 ≤ count830 b) := rfl
theorem meaning844 (b : Nat → Bool) : literal (valuationOf b) 844 = decide (1 ≤ count844 b) := rfl
theorem meaning846 (b : Nat → Bool) : literal (valuationOf b) 846 = decide (1 ≤ count846 b) := rfl
theorem meaning847 (b : Nat → Bool) : literal (valuationOf b) 847 = decide (2 ≤ count846 b) := rfl
theorem meaning849 (b : Nat → Bool) : literal (valuationOf b) 849 = decide (1 ≤ count849 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (2 ≤ count849 b) := rfl
theorem meaning851 (b : Nat → Bool) : literal (valuationOf b) 851 = decide (1 ≤ count851 b) := rfl
theorem meaning852 (b : Nat → Bool) : literal (valuationOf b) 852 = decide (2 ≤ count851 b) := rfl
theorem meaning854 (b : Nat → Bool) : literal (valuationOf b) 854 = decide (1 ≤ count854 b) := rfl
theorem meaning855 (b : Nat → Bool) : literal (valuationOf b) 855 = decide (2 ≤ count854 b) := rfl
theorem meaning856 (b : Nat → Bool) : literal (valuationOf b) 856 = decide (3 ≤ count854 b) := rfl
theorem meaning860 (b : Nat → Bool) : literal (valuationOf b) 860 = decide (1 ≤ count860 b) := rfl
theorem meaning862 (b : Nat → Bool) : literal (valuationOf b) 862 = decide (1 ≤ count862 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (2 ≤ count862 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (1 ≤ count865 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (2 ≤ count865 b) := rfl
theorem meaning867 (b : Nat → Bool) : literal (valuationOf b) 867 = decide (1 ≤ count867 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (2 ≤ count867 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (1 ≤ count869 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (2 ≤ count869 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (3 ≤ count869 b) := rfl
theorem meaning873 (b : Nat → Bool) : literal (valuationOf b) 873 = decide (1 ≤ count873 b) := rfl
theorem meaning874 (b : Nat → Bool) : literal (valuationOf b) 874 = decide (2 ≤ count873 b) := rfl
theorem meaning875 (b : Nat → Bool) : literal (valuationOf b) 875 = decide (3 ≤ count873 b) := rfl
theorem meaning876 (b : Nat → Bool) : literal (valuationOf b) 876 = decide (4 ≤ count873 b) := rfl
theorem meaning880 (b : Nat → Bool) : literal (valuationOf b) 880 = decide (1 ≤ count880 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (2 ≤ count880 b) := rfl
theorem meaning882 (b : Nat → Bool) : literal (valuationOf b) 882 = decide (3 ≤ count880 b) := rfl
theorem meaning883 (b : Nat → Bool) : literal (valuationOf b) 883 = decide (4 ≤ count880 b) := rfl
theorem meaning884 (b : Nat → Bool) : literal (valuationOf b) 884 = decide (5 ≤ count880 b) := rfl
theorem meaning885 (b : Nat → Bool) : literal (valuationOf b) 885 = decide (6 ≤ count880 b) := rfl
theorem meaning893 (b : Nat → Bool) : literal (valuationOf b) 893 = decide (1 ≤ count893 b) := rfl
theorem meaning894 (b : Nat → Bool) : literal (valuationOf b) 894 = decide (2 ≤ count893 b) := rfl
theorem meaning895 (b : Nat → Bool) : literal (valuationOf b) 895 = decide (1 ≤ count895 b) := rfl
theorem meaning896 (b : Nat → Bool) : literal (valuationOf b) 896 = decide (2 ≤ count895 b) := rfl
theorem meaning897 (b : Nat → Bool) : literal (valuationOf b) 897 = decide (3 ≤ count895 b) := rfl
theorem meaning898 (b : Nat → Bool) : literal (valuationOf b) 898 = decide (1 ≤ count898 b) := rfl
theorem meaning899 (b : Nat → Bool) : literal (valuationOf b) 899 = decide (2 ≤ count898 b) := rfl
theorem meaning900 (b : Nat → Bool) : literal (valuationOf b) 900 = decide (1 ≤ count900 b) := rfl
theorem meaning901 (b : Nat → Bool) : literal (valuationOf b) 901 = decide (2 ≤ count900 b) := rfl
theorem meaning902 (b : Nat → Bool) : literal (valuationOf b) 902 = decide (1 ≤ count902 b) := rfl
theorem meaning903 (b : Nat → Bool) : literal (valuationOf b) 903 = decide (2 ≤ count902 b) := rfl
theorem meaning904 (b : Nat → Bool) : literal (valuationOf b) 904 = decide (3 ≤ count902 b) := rfl
theorem meaning906 (b : Nat → Bool) : literal (valuationOf b) 906 = decide (1 ≤ count906 b) := rfl
theorem meaning907 (b : Nat → Bool) : literal (valuationOf b) 907 = decide (2 ≤ count906 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (3 ≤ count906 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (4 ≤ count906 b) := rfl
theorem meaning910 (b : Nat → Bool) : literal (valuationOf b) 910 = decide (5 ≤ count906 b) := rfl
theorem meaning913 (b : Nat → Bool) : literal (valuationOf b) 913 = decide (1 ≤ count913 b) := rfl
theorem meaning914 (b : Nat → Bool) : literal (valuationOf b) 914 = decide (2 ≤ count913 b) := rfl
theorem meaning916 (b : Nat → Bool) : literal (valuationOf b) 916 = decide (2 ≤ count915 b) := rfl
theorem meaning917 (b : Nat → Bool) : literal (valuationOf b) 917 = decide (3 ≤ count915 b) := rfl
theorem meaning918 (b : Nat → Bool) : literal (valuationOf b) 918 = decide (1 ≤ count918 b) := rfl
theorem meaning919 (b : Nat → Bool) : literal (valuationOf b) 919 = decide (2 ≤ count918 b) := rfl
theorem meaning920 (b : Nat → Bool) : literal (valuationOf b) 920 = decide (1 ≤ count920 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (2 ≤ count920 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (1 ≤ count922 b) := rfl
theorem meaning923 (b : Nat → Bool) : literal (valuationOf b) 923 = decide (2 ≤ count922 b) := rfl
theorem meaning924 (b : Nat → Bool) : literal (valuationOf b) 924 = decide (3 ≤ count922 b) := rfl
theorem meaning925 (b : Nat → Bool) : literal (valuationOf b) 925 = decide (4 ≤ count922 b) := rfl
theorem meaning927 (b : Nat → Bool) : literal (valuationOf b) 927 = decide (2 ≤ count926 b) := rfl
theorem meaning928 (b : Nat → Bool) : literal (valuationOf b) 928 = decide (3 ≤ count926 b) := rfl
theorem meaning929 (b : Nat → Bool) : literal (valuationOf b) 929 = decide (4 ≤ count926 b) := rfl
theorem meaning930 (b : Nat → Bool) : literal (valuationOf b) 930 = decide (5 ≤ count926 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (6 ≤ count926 b) := rfl
theorem meaning936 (b : Nat → Bool) : literal (valuationOf b) 936 = decide (4 ≤ count933 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (5 ≤ count933 b) := rfl
theorem meaning938 (b : Nat → Bool) : literal (valuationOf b) 938 = decide (6 ≤ count933 b) := rfl
theorem meaning939 (b : Nat → Bool) : literal (valuationOf b) 939 = decide (7 ≤ count933 b) := rfl
theorem meaning940 (b : Nat → Bool) : literal (valuationOf b) 940 = decide (8 ≤ count933 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (9 ≤ count933 b) := rfl
theorem meaning952 (b : Nat → Bool) : literal (valuationOf b) 952 = decide (6 ≤ count947 b) := rfl
theorem meaning953 (b : Nat → Bool) : literal (valuationOf b) 953 = decide (7 ≤ count947 b) := rfl
theorem meaning954 (b : Nat → Bool) : literal (valuationOf b) 954 = decide (8 ≤ count947 b) := rfl
theorem meaning955 (b : Nat → Bool) : literal (valuationOf b) 955 = decide (9 ≤ count947 b) := rfl
theorem meaning956 (b : Nat → Bool) : literal (valuationOf b) 956 = decide (10 ≤ count947 b) := rfl
theorem meaning974 (b : Nat → Bool) : literal (valuationOf b) 974 = decide (14 ≤ count961 b) := rfl
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
end Snake9.Regrowth.E112151
