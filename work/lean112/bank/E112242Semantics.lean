import E112242Data
namespace Snake9.Regrowth.E112242
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 104 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (34 : Vertex)) else decide (InPath q (36 : Vertex)))) else (if i < 4 then decide (InPath q (37 : Vertex)) else (if i < 5 then decide (InPath q (38 : Vertex)) else decide (InPath q (41 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (42 : Vertex)) else (if i < 8 then decide (InPath q (43 : Vertex)) else decide (InPath q (46 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (48 : Vertex)) else decide (InPath q (49 : Vertex))) else (if i < 12 then decide (InPath q (53 : Vertex)) else decide (InPath q (55 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (56 : Vertex)) else (if i < 15 then decide (InPath q (57 : Vertex)) else decide (InPath q (62 : Vertex)))) else (if i < 17 then decide (InPath q (63 : Vertex)) else (if i < 18 then decide (InPath q (97 : Vertex)) else decide (InPath q (98 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (99 : Vertex)) else (if i < 21 then decide (InPath q (103 : Vertex)) else decide (InPath q (108 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (109 : Vertex)) else decide (InPath q (111 : Vertex))) else (if i < 25 then decide (InPath q (113 : Vertex)) else decide (InPath q (114 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (116 : Vertex)) else (if i < 28 then decide (InPath q (118 : Vertex)) else decide (InPath q (122 : Vertex)))) else (if i < 30 then decide (InPath q (124 : Vertex)) else (if i < 31 then decide (InPath q (126 : Vertex)) else decide (InPath q (127 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (130 : Vertex)) else (if i < 34 then decide (InPath q (132 : Vertex)) else decide (InPath q (133 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (134 : Vertex)) else decide (InPath q (142 : Vertex))) else (if i < 38 then decide (InPath q (144 : Vertex)) else decide (InPath q (145 : Vertex)))))) else (if i < 45 then (if i < 42 then (if i < 40 then decide (InPath q (149 : Vertex)) else (if i < 41 then decide (InPath q (151 : Vertex)) else decide (InPath q (158 : Vertex)))) else (if i < 43 then decide (InPath q (176 : Vertex)) else (if i < 44 then decide (InPath q (180 : Vertex)) else decide (InPath q (182 : Vertex))))) else (if i < 48 then (if i < 46 then decide (InPath q (186 : Vertex)) else (if i < 47 then decide (InPath q (190 : Vertex)) else decide (InPath q (193 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (194 : Vertex)) else decide (InPath q (195 : Vertex))) else (if i < 51 then decide (InPath q (199 : Vertex)) else decide (InPath q (204 : Vertex)))))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then decide (InPath q (205 : Vertex)) else (if i < 54 then decide (InPath q (207 : Vertex)) else decide (InPath q (209 : Vertex)))) else (if i < 56 then decide (InPath q (210 : Vertex)) else (if i < 57 then decide (InPath q (212 : Vertex)) else decide (InPath q (214 : Vertex))))) else (if i < 61 then (if i < 59 then decide (InPath q (218 : Vertex)) else (if i < 60 then decide (InPath q (220 : Vertex)) else decide (InPath q (222 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (223 : Vertex)) else decide (InPath q (258 : Vertex))) else (if i < 64 then decide (InPath q (260 : Vertex)) else decide (InPath q (261 : Vertex)))))) else (if i < 71 then (if i < 68 then (if i < 66 then decide (InPath q (262 : Vertex)) else (if i < 67 then decide (InPath q (265 : Vertex)) else decide (InPath q (266 : Vertex)))) else (if i < 69 then decide (InPath q (267 : Vertex)) else (if i < 70 then decide (InPath q (270 : Vertex)) else decide (InPath q (273 : Vertex))))) else (if i < 74 then (if i < 72 then decide (InPath q (277 : Vertex)) else (if i < 73 then decide (InPath q (279 : Vertex)) else decide (InPath q (280 : Vertex)))) else (if i < 76 then (if i < 75 then decide (InPath q (281 : Vertex)) else decide (InPath q (286 : Vertex))) else (if i < 77 then decide (InPath q (287 : Vertex)) else decide (InPath q (342 : Vertex))))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then decide (InPath q (346 : Vertex)) else (if i < 80 then decide (InPath q (350 : Vertex)) else decide (InPath q (354 : Vertex)))) else (if i < 82 then decide (InPath q (356 : Vertex)) else (if i < 83 then decide (InPath q (357 : Vertex)) else decide (InPath q (358 : Vertex))))) else (if i < 87 then (if i < 85 then decide (InPath q (366 : Vertex)) else (if i < 86 then decide (InPath q (369 : Vertex)) else decide (InPath q (373 : Vertex)))) else (if i < 89 then (if i < 88 then decide (InPath q (375 : Vertex)) else decide (InPath q (382 : Vertex))) else (if i < 90 then decide (InPath q (418 : Vertex)) else decide (InPath q (420 : Vertex)))))) else (if i < 97 then (if i < 94 then (if i < 92 then decide (InPath q (421 : Vertex)) else (if i < 93 then decide (InPath q (422 : Vertex)) else decide (InPath q (425 : Vertex)))) else (if i < 95 then decide (InPath q (426 : Vertex)) else (if i < 96 then decide (InPath q (427 : Vertex)) else decide (InPath q (430 : Vertex))))) else (if i < 100 then (if i < 98 then decide (InPath q (432 : Vertex)) else (if i < 99 then decide (InPath q (433 : Vertex)) else decide (InPath q (437 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (439 : Vertex)) else decide (InPath q (440 : Vertex))) else (if i < 103 then decide (InPath q (441 : Vertex)) else decide (InPath q (446 : Vertex))))))))) else (if i < 156 then (if i < 130 then (if i < 117 then (if i < 110 then (if i < 107 then (if i < 105 then decide (InPath q (447 : Vertex)) else (if i < 106 then decide (BallClauseLogic.Endpoint q (34 : Vertex)) else decide (BallClauseLogic.Endpoint q (36 : Vertex)))) else (if i < 108 then decide (BallClauseLogic.Endpoint q (37 : Vertex)) else (if i < 109 then decide (BallClauseLogic.Endpoint q (38 : Vertex)) else decide (BallClauseLogic.Endpoint q (41 : Vertex))))) else (if i < 113 then (if i < 111 then decide (BallClauseLogic.Endpoint q (42 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (43 : Vertex)) else decide (BallClauseLogic.Endpoint q (46 : Vertex)))) else (if i < 115 then (if i < 114 then decide (BallClauseLogic.Endpoint q (48 : Vertex)) else decide (BallClauseLogic.Endpoint q (49 : Vertex))) else (if i < 116 then decide (BallClauseLogic.Endpoint q (53 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex)))))) else (if i < 123 then (if i < 120 then (if i < 118 then decide (BallClauseLogic.Endpoint q (56 : Vertex)) else (if i < 119 then decide (BallClauseLogic.Endpoint q (57 : Vertex)) else decide (BallClauseLogic.Endpoint q (62 : Vertex)))) else (if i < 121 then decide (BallClauseLogic.Endpoint q (63 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (97 : Vertex)) else decide (BallClauseLogic.Endpoint q (98 : Vertex))))) else (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (99 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (103 : Vertex)) else decide (BallClauseLogic.Endpoint q (108 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (109 : Vertex)) else decide (BallClauseLogic.Endpoint q (111 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (113 : Vertex)) else decide (BallClauseLogic.Endpoint q (114 : Vertex))))))) else (if i < 143 then (if i < 136 then (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (116 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (118 : Vertex)) else decide (BallClauseLogic.Endpoint q (122 : Vertex)))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (124 : Vertex)) else (if i < 135 then decide (BallClauseLogic.Endpoint q (126 : Vertex)) else decide (BallClauseLogic.Endpoint q (127 : Vertex))))) else (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (130 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else decide (BallClauseLogic.Endpoint q (133 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (134 : Vertex)) else decide (BallClauseLogic.Endpoint q (142 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (145 : Vertex)))))) else (if i < 149 then (if i < 146 then (if i < 144 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (158 : Vertex)))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (176 : Vertex)) else (if i < 148 then decide (BallClauseLogic.Endpoint q (180 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex))))) else (if i < 152 then (if i < 150 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else (if i < 151 then decide (BallClauseLogic.Endpoint q (190 : Vertex)) else decide (BallClauseLogic.Endpoint q (193 : Vertex)))) else (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (194 : Vertex)) else decide (BallClauseLogic.Endpoint q (195 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else decide (BallClauseLogic.Endpoint q (204 : Vertex)))))))) else (if i < 182 then (if i < 169 then (if i < 162 then (if i < 159 then (if i < 157 then decide (BallClauseLogic.Endpoint q (205 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else decide (BallClauseLogic.Endpoint q (209 : Vertex)))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (210 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (212 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex))))) else (if i < 165 then (if i < 163 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (220 : Vertex)) else decide (BallClauseLogic.Endpoint q (222 : Vertex)))) else (if i < 167 then (if i < 166 then decide (BallClauseLogic.Endpoint q (223 : Vertex)) else decide (BallClauseLogic.Endpoint q (258 : Vertex))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (260 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex)))))) else (if i < 175 then (if i < 172 then (if i < 170 then decide (BallClauseLogic.Endpoint q (262 : Vertex)) else (if i < 171 then decide (BallClauseLogic.Endpoint q (265 : Vertex)) else decide (BallClauseLogic.Endpoint q (266 : Vertex)))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (267 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (270 : Vertex)) else decide (BallClauseLogic.Endpoint q (273 : Vertex))))) else (if i < 178 then (if i < 176 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else (if i < 177 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else decide (BallClauseLogic.Endpoint q (280 : Vertex)))) else (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else decide (BallClauseLogic.Endpoint q (286 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (342 : Vertex))))))) else (if i < 195 then (if i < 188 then (if i < 185 then (if i < 183 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (350 : Vertex)) else decide (BallClauseLogic.Endpoint q (354 : Vertex)))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (356 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else decide (BallClauseLogic.Endpoint q (358 : Vertex))))) else (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (366 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (369 : Vertex)) else decide (BallClauseLogic.Endpoint q (373 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (375 : Vertex)) else decide (BallClauseLogic.Endpoint q (382 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (420 : Vertex)))))) else (if i < 202 then (if i < 198 then (if i < 196 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (422 : Vertex)) else decide (BallClauseLogic.Endpoint q (425 : Vertex)))) else (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (432 : Vertex))))) else (if i < 205 then (if i < 203 then decide (BallClauseLogic.Endpoint q (433 : Vertex)) else (if i < 204 then decide (BallClauseLogic.Endpoint q (437 : Vertex)) else decide (BallClauseLogic.Endpoint q (439 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else decide (BallClauseLogic.Endpoint q (441 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (446 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count209 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count211 (b : Nat → Bool) : Nat := countLit b [105, 106, 107]
def count213 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count215 (b : Nat → Bool) : Nat := countLit b [108, 109, 110]
def count217 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110]
def count219 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count221 (b : Nat → Bool) : Nat := countLit b [111, 112, 113]
def count223 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count225 (b : Nat → Bool) : Nat := countLit b [114, 115, 116]
def count227 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116]
def count229 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
def count231 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count233 (b : Nat → Bool) : Nat := countLit b [117, 118, 119]
def count235 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count237 (b : Nat → Bool) : Nat := countLit b [120, 121, 122]
def count239 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122]
def count241 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count243 (b : Nat → Bool) : Nat := countLit b [123, 124, 125]
def count245 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count247 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count249 (b : Nat → Bool) : Nat := countLit b [126, 127, 128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
def count257 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [130, 131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [133, 134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count275 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count287 (b : Nat → Bool) : Nat := countLit b [146, 147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count307 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count309 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [156, 157, 158]
def count313 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [159, 160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169]
def count329 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 166, 167, 168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169]
def count333 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count335 (b : Nat → Bool) : Nat := countLit b [170, 171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [173, 174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count349 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count365 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count375 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count377 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195]
def count379 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192, 193, 194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [196, 197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200, 201]
def count391 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count395 (b : Nat → Bool) : Nat := countLit b [202, 203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count399 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count401 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208]
def count403 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205, 206, 207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count409 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count411 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count413 (b : Nat → Bool) : Nat := countLit b [2, 7]
def count415 (b : Nat → Bool) : Nat := countLit b [1, 2, 7]
def count418 (b : Nat → Bool) : Nat := countLit b [9, 11]
def count420 (b : Nat → Bool) : Nat := countLit b [8, 9, 11]
def count423 (b : Nat → Bool) : Nat := countLit b [1, 2, 7, 8, 9, 11]
def count429 (b : Nat → Bool) : Nat := countLit b [16, 19]
def count431 (b : Nat → Bool) : Nat := countLit b [14, 16, 19]
def count434 (b : Nat → Bool) : Nat := countLit b [23, 24]
def count436 (b : Nat → Bool) : Nat := countLit b [21, 23, 24]
def count439 (b : Nat → Bool) : Nat := countLit b [14, 16, 19, 21, 23, 24]
def count445 (b : Nat → Bool) : Nat := countLit b [1, 2, 7, 8, 9, 11, 14, 16, 19, 21, 23, 24]
def count457 (b : Nat → Bool) : Nat := countLit b [26, 30]
def count459 (b : Nat → Bool) : Nat := countLit b [25, 26, 30]
def count462 (b : Nat → Bool) : Nat := countLit b [33, 36]
def count464 (b : Nat → Bool) : Nat := countLit b [32, 33, 36]
def count467 (b : Nat → Bool) : Nat := countLit b [25, 26, 30, 32, 33, 36]
def count473 (b : Nat → Bool) : Nat := countLit b [39, 43]
def count475 (b : Nat → Bool) : Nat := countLit b [37, 39, 43]
def count478 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count480 (b : Nat → Bool) : Nat := countLit b [46, 49, 51]
def count483 (b : Nat → Bool) : Nat := countLit b [37, 39, 43, 46, 49, 51]
def count489 (b : Nat → Bool) : Nat := countLit b [25, 26, 30, 32, 33, 36, 37, 39, 43, 46, 49, 51]
def count501 (b : Nat → Bool) : Nat := countLit b [1, 2, 7, 8, 9, 11, 14, 16, 19, 21, 23, 24, 25, 26, 30, 32, 33, 36, 37, 39, 43, 46, 49, 51]
def count525 (b : Nat → Bool) : Nat := countLit b [54, 55]
def count527 (b : Nat → Bool) : Nat := countLit b [53, 54, 55]
def count530 (b : Nat → Bool) : Nat := countLit b [60, 62]
def count532 (b : Nat → Bool) : Nat := countLit b [56, 60, 62]
def count535 (b : Nat → Bool) : Nat := countLit b [53, 54, 55, 56, 60, 62]
def count541 (b : Nat → Bool) : Nat := countLit b [68, 69]
def count543 (b : Nat → Bool) : Nat := countLit b [63, 68, 69]
def count546 (b : Nat → Bool) : Nat := countLit b [74, 76]
def count548 (b : Nat → Bool) : Nat := countLit b [71, 74, 76]
def count551 (b : Nat → Bool) : Nat := countLit b [63, 68, 69, 71, 74, 76]
def count557 (b : Nat → Bool) : Nat := countLit b [53, 54, 55, 56, 60, 62, 63, 68, 69, 71, 74, 76]
def count569 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count571 (b : Nat → Bool) : Nat := countLit b [79, 80, 81]
def count574 (b : Nat → Bool) : Nat := countLit b [86, 89]
def count576 (b : Nat → Bool) : Nat := countLit b [84, 86, 89]
def count579 (b : Nat → Bool) : Nat := countLit b [79, 80, 81, 84, 86, 89]
def count585 (b : Nat → Bool) : Nat := countLit b [95, 96]
def count587 (b : Nat → Bool) : Nat := countLit b [90, 95, 96]
def count590 (b : Nat → Bool) : Nat := countLit b [97, 99]
def count592 (b : Nat → Bool) : Nat := countLit b [102, 104]
def count594 (b : Nat → Bool) : Nat := countLit b [97, 99, 102, 104]
def count598 (b : Nat → Bool) : Nat := countLit b [90, 95, 96, 97, 99, 102, 104]
def count605 (b : Nat → Bool) : Nat := countLit b [79, 80, 81, 84, 86, 89, 90, 95, 96, 97, 99, 102, 104]
def count618 (b : Nat → Bool) : Nat := countLit b [53, 54, 55, 56, 60, 62, 63, 68, 69, 71, 74, 76, 79, 80, 81, 84, 86, 89, 90, 95, 96, 97, 99, 102, 104]
def count643 (b : Nat → Bool) : Nat := countLit b [1, 2, 7, 8, 9, 11, 14, 16, 19, 21, 23, 24, 25, 26, 30, 32, 33, 36, 37, 39, 43, 46, 49, 51, 53, 54, 55, 56, 60, 62, 63, 68, 69, 71, 74, 76, 79, 80, 81, 84, 86, 89, 90, 95, 96, 97, 99, 102, 104]
def count685 (b : Nat → Bool) : Nat := countLit b [-2, -7]
def count687 (b : Nat → Bool) : Nat := countLit b [-1, -2, -7]
def count690 (b : Nat → Bool) : Nat := countLit b [-9, -11]
def count692 (b : Nat → Bool) : Nat := countLit b [-8, -9, -11]
def count695 (b : Nat → Bool) : Nat := countLit b [-1, -2, -7, -8, -9, -11]
def count701 (b : Nat → Bool) : Nat := countLit b [-16, -19]
def count703 (b : Nat → Bool) : Nat := countLit b [-14, -16, -19]
def count706 (b : Nat → Bool) : Nat := countLit b [-23, -24]
def count708 (b : Nat → Bool) : Nat := countLit b [-21, -23, -24]
def count711 (b : Nat → Bool) : Nat := countLit b [-14, -16, -19, -21, -23, -24]
def count717 (b : Nat → Bool) : Nat := countLit b [-1, -2, -7, -8, -9, -11, -14, -16, -19, -21, -23, -24]
def count726 (b : Nat → Bool) : Nat := countLit b [-26, -30]
def count728 (b : Nat → Bool) : Nat := countLit b [-25, -26, -30]
def count731 (b : Nat → Bool) : Nat := countLit b [-33, -36]
def count733 (b : Nat → Bool) : Nat := countLit b [-32, -33, -36]
def count736 (b : Nat → Bool) : Nat := countLit b [-25, -26, -30, -32, -33, -36]
def count742 (b : Nat → Bool) : Nat := countLit b [-39, -43]
def count744 (b : Nat → Bool) : Nat := countLit b [-37, -39, -43]
def count747 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count749 (b : Nat → Bool) : Nat := countLit b [-46, -49, -51]
def count752 (b : Nat → Bool) : Nat := countLit b [-37, -39, -43, -46, -49, -51]
def count758 (b : Nat → Bool) : Nat := countLit b [-25, -26, -30, -32, -33, -36, -37, -39, -43, -46, -49, -51]
def count767 (b : Nat → Bool) : Nat := countLit b [-1, -2, -7, -8, -9, -11, -14, -16, -19, -21, -23, -24, -25, -26, -30, -32, -33, -36, -37, -39, -43, -46, -49, -51]
def count776 (b : Nat → Bool) : Nat := countLit b [-54, -55]
def count778 (b : Nat → Bool) : Nat := countLit b [-53, -54, -55]
def count781 (b : Nat → Bool) : Nat := countLit b [-60, -62]
def count783 (b : Nat → Bool) : Nat := countLit b [-56, -60, -62]
def count786 (b : Nat → Bool) : Nat := countLit b [-53, -54, -55, -56, -60, -62]
def count792 (b : Nat → Bool) : Nat := countLit b [-68, -69]
def count794 (b : Nat → Bool) : Nat := countLit b [-63, -68, -69]
def count797 (b : Nat → Bool) : Nat := countLit b [-74, -76]
def count799 (b : Nat → Bool) : Nat := countLit b [-71, -74, -76]
def count802 (b : Nat → Bool) : Nat := countLit b [-63, -68, -69, -71, -74, -76]
def count808 (b : Nat → Bool) : Nat := countLit b [-53, -54, -55, -56, -60, -62, -63, -68, -69, -71, -74, -76]
def count817 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count819 (b : Nat → Bool) : Nat := countLit b [-79, -80, -81]
def count822 (b : Nat → Bool) : Nat := countLit b [-86, -89]
def count824 (b : Nat → Bool) : Nat := countLit b [-84, -86, -89]
def count827 (b : Nat → Bool) : Nat := countLit b [-79, -80, -81, -84, -86, -89]
def count833 (b : Nat → Bool) : Nat := countLit b [-95, -96]
def count835 (b : Nat → Bool) : Nat := countLit b [-90, -95, -96]
def count838 (b : Nat → Bool) : Nat := countLit b [-97, -99]
def count840 (b : Nat → Bool) : Nat := countLit b [-102, -104]
def count842 (b : Nat → Bool) : Nat := countLit b [-97, -99, -102, -104]
def count846 (b : Nat → Bool) : Nat := countLit b [-90, -95, -96, -97, -99, -102, -104]
def count853 (b : Nat → Bool) : Nat := countLit b [-79, -80, -81, -84, -86, -89, -90, -95, -96, -97, -99, -102, -104]
def count862 (b : Nat → Bool) : Nat := countLit b [-53, -54, -55, -56, -60, -62, -63, -68, -69, -71, -74, -76, -79, -80, -81, -84, -86, -89, -90, -95, -96, -97, -99, -102, -104]
def count871 (b : Nat → Bool) : Nat := countLit b [-1, -2, -7, -8, -9, -11, -14, -16, -19, -21, -23, -24, -25, -26, -30, -32, -33, -36, -37, -39, -43, -46, -49, -51, -53, -54, -55, -56, -60, -62, -63, -68, -69, -71, -74, -76, -79, -80, -81, -84, -86, -89, -90, -95, -96, -97, -99, -102, -104]
def count880 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count882 (b : Nat → Bool) : Nat := countLit b [3, 4, 5]
def count885 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count887 (b : Nat → Bool) : Nat := countLit b [6, 10, 12]
def count890 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 6, 10, 12]
def count896 (b : Nat → Bool) : Nat := countLit b [15, 17]
def count898 (b : Nat → Bool) : Nat := countLit b [13, 15, 17]
def count901 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count903 (b : Nat → Bool) : Nat := countLit b [22, 27]
def count905 (b : Nat → Bool) : Nat := countLit b [18, 20, 22, 27]
def count909 (b : Nat → Bool) : Nat := countLit b [13, 15, 17, 18, 20, 22, 27]
def count916 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 6, 10, 12, 13, 15, 17, 18, 20, 22, 27]
def count929 (b : Nat → Bool) : Nat := countLit b [29, 31]
def count931 (b : Nat → Bool) : Nat := countLit b [28, 29, 31]
def count934 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count936 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count938 (b : Nat → Bool) : Nat := countLit b [34, 35, 38, 40]
def count942 (b : Nat → Bool) : Nat := countLit b [28, 29, 31, 34, 35, 38, 40]
def count949 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count951 (b : Nat → Bool) : Nat := countLit b [41, 42, 44]
def count954 (b : Nat → Bool) : Nat := countLit b [45, 47]
def count956 (b : Nat → Bool) : Nat := countLit b [48, 50]
def count958 (b : Nat → Bool) : Nat := countLit b [45, 47, 48, 50]
def count962 (b : Nat → Bool) : Nat := countLit b [41, 42, 44, 45, 47, 48, 50]
def count969 (b : Nat → Bool) : Nat := countLit b [28, 29, 31, 34, 35, 38, 40, 41, 42, 44, 45, 47, 48, 50]
def count983 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 6, 10, 12, 13, 15, 17, 18, 20, 22, 27, 28, 29, 31, 34, 35, 38, 40, 41, 42, 44, 45, 47, 48, 50]
def count1010 (b : Nat → Bool) : Nat := countLit b [57, 58]
def count1012 (b : Nat → Bool) : Nat := countLit b [52, 57, 58]
def count1015 (b : Nat → Bool) : Nat := countLit b [59, 61]
def count1017 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count1019 (b : Nat → Bool) : Nat := countLit b [59, 61, 64, 65]
def count1023 (b : Nat → Bool) : Nat := countLit b [52, 57, 58, 59, 61, 64, 65]
def count1030 (b : Nat → Bool) : Nat := countLit b [67, 70]
def count1032 (b : Nat → Bool) : Nat := countLit b [66, 67, 70]
def count1035 (b : Nat → Bool) : Nat := countLit b [72, 73]
def count1037 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count1039 (b : Nat → Bool) : Nat := countLit b [72, 73, 75, 77]
def count1043 (b : Nat → Bool) : Nat := countLit b [66, 67, 70, 72, 73, 75, 77]
def count1050 (b : Nat → Bool) : Nat := countLit b [52, 57, 58, 59, 61, 64, 65, 66, 67, 70, 72, 73, 75, 77]
def count1064 (b : Nat → Bool) : Nat := countLit b [82, 83]
def count1066 (b : Nat → Bool) : Nat := countLit b [78, 82, 83]
def count1069 (b : Nat → Bool) : Nat := countLit b [85, 87]
def count1071 (b : Nat → Bool) : Nat := countLit b [88, 91]
def count1073 (b : Nat → Bool) : Nat := countLit b [85, 87, 88, 91]
def count1077 (b : Nat → Bool) : Nat := countLit b [78, 82, 83, 85, 87, 88, 91]
def count1084 (b : Nat → Bool) : Nat := countLit b [93, 94]
def count1086 (b : Nat → Bool) : Nat := countLit b [92, 93, 94]
def count1089 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count1091 (b : Nat → Bool) : Nat := countLit b [101, 103]
def count1093 (b : Nat → Bool) : Nat := countLit b [98, 100, 101, 103]
def count1097 (b : Nat → Bool) : Nat := countLit b [92, 93, 94, 98, 100, 101, 103]
def count1104 (b : Nat → Bool) : Nat := countLit b [78, 82, 83, 85, 87, 88, 91, 92, 93, 94, 98, 100, 101, 103]
def count1118 (b : Nat → Bool) : Nat := countLit b [52, 57, 58, 59, 61, 64, 65, 66, 67, 70, 72, 73, 75, 77, 78, 82, 83, 85, 87, 88, 91, 92, 93, 94, 98, 100, 101, 103]
def count1146 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 6, 10, 12, 13, 15, 17, 18, 20, 22, 27, 28, 29, 31, 34, 35, 38, 40, 41, 42, 44, 45, 47, 48, 50, 52, 57, 58, 59, 61, 64, 65, 66, 67, 70, 72, 73, 75, 77, 78, 82, 83, 85, 87, 88, 91, 92, 93, 94, 98, 100, 101, 103]
def count1188 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1190 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5]
def count1193 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count1195 (b : Nat → Bool) : Nat := countLit b [-6, -10, -12]
def count1198 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -6, -10, -12]
def count1204 (b : Nat → Bool) : Nat := countLit b [-15, -17]
def count1206 (b : Nat → Bool) : Nat := countLit b [-13, -15, -17]
def count1209 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count1211 (b : Nat → Bool) : Nat := countLit b [-22, -27]
def count1213 (b : Nat → Bool) : Nat := countLit b [-18, -20, -22, -27]
def count1217 (b : Nat → Bool) : Nat := countLit b [-13, -15, -17, -18, -20, -22, -27]
def count1224 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]
def count1237 (b : Nat → Bool) : Nat := countLit b [-29, -31]
def count1239 (b : Nat → Bool) : Nat := countLit b [-28, -29, -31]
def count1242 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count1244 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1246 (b : Nat → Bool) : Nat := countLit b [-34, -35, -38, -40]
def count1250 (b : Nat → Bool) : Nat := countLit b [-28, -29, -31, -34, -35, -38, -40]
def count1257 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count1259 (b : Nat → Bool) : Nat := countLit b [-41, -42, -44]
def count1262 (b : Nat → Bool) : Nat := countLit b [-45, -47]
def count1264 (b : Nat → Bool) : Nat := countLit b [-48, -50]
def count1266 (b : Nat → Bool) : Nat := countLit b [-45, -47, -48, -50]
def count1270 (b : Nat → Bool) : Nat := countLit b [-41, -42, -44, -45, -47, -48, -50]
def count1277 (b : Nat → Bool) : Nat := countLit b [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]
def count1291 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]
def count1306 (b : Nat → Bool) : Nat := countLit b [-57, -58]
def count1308 (b : Nat → Bool) : Nat := countLit b [-52, -57, -58]
def count1311 (b : Nat → Bool) : Nat := countLit b [-59, -61]
def count1313 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count1315 (b : Nat → Bool) : Nat := countLit b [-59, -61, -64, -65]
def count1319 (b : Nat → Bool) : Nat := countLit b [-52, -57, -58, -59, -61, -64, -65]
def count1326 (b : Nat → Bool) : Nat := countLit b [-67, -70]
def count1328 (b : Nat → Bool) : Nat := countLit b [-66, -67, -70]
def count1331 (b : Nat → Bool) : Nat := countLit b [-72, -73]
def count1333 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count1335 (b : Nat → Bool) : Nat := countLit b [-72, -73, -75, -77]
def count1339 (b : Nat → Bool) : Nat := countLit b [-66, -67, -70, -72, -73, -75, -77]
def count1346 (b : Nat → Bool) : Nat := countLit b [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77]
def count1360 (b : Nat → Bool) : Nat := countLit b [-82, -83]
def count1362 (b : Nat → Bool) : Nat := countLit b [-78, -82, -83]
def count1365 (b : Nat → Bool) : Nat := countLit b [-85, -87]
def count1367 (b : Nat → Bool) : Nat := countLit b [-88, -91]
def count1369 (b : Nat → Bool) : Nat := countLit b [-85, -87, -88, -91]
def count1373 (b : Nat → Bool) : Nat := countLit b [-78, -82, -83, -85, -87, -88, -91]
def count1380 (b : Nat → Bool) : Nat := countLit b [-93, -94]
def count1382 (b : Nat → Bool) : Nat := countLit b [-92, -93, -94]
def count1385 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count1387 (b : Nat → Bool) : Nat := countLit b [-101, -103]
def count1389 (b : Nat → Bool) : Nat := countLit b [-98, -100, -101, -103]
def count1393 (b : Nat → Bool) : Nat := countLit b [-92, -93, -94, -98, -100, -101, -103]
def count1400 (b : Nat → Bool) : Nat := countLit b [-78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]
def count1414 (b : Nat → Bool) : Nat := countLit b [-52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]
def count1429 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27, -28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50, -52, -57, -58, -59, -61, -64, -65, -66, -67, -70, -72, -73, -75, -77, -78, -82, -83, -85, -87, -88, -91, -92, -93, -94, -98, -100, -101, -103]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 722 then (if i < 361 then (if i < 180 then (if i < 90 then (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 16 then (if i < 13 then (if i < 12 then b 11 else b 12) else (if i < 14 then b 13 else (if i < 15 then b 14 else b 15))) else (if i < 19 then (if i < 17 then b 16 else (if i < 18 then b 17 else b 18)) else (if i < 20 then b 19 else (if i < 21 then b 20 else b 21))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else (if i < 26 then b 25 else b 26))) else (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)))) else (if i < 39 then (if i < 36 then (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)) else (if i < 37 then b 36 else (if i < 38 then b 37 else b 38))) else (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)))))) else (if i < 67 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else (if i < 49 then b 48 else b 49))) else (if i < 53 then (if i < 51 then b 50 else (if i < 52 then b 51 else b 52)) else (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)))) else (if i < 61 then (if i < 58 then (if i < 57 then b 56 else b 57) else (if i < 59 then b 58 else (if i < 60 then b 59 else b 60))) else (if i < 64 then (if i < 62 then b 61 else (if i < 63 then b 62 else b 63)) else (if i < 65 then b 64 else (if i < 66 then b 65 else b 66))))) else (if i < 78 then (if i < 72 then (if i < 69 then (if i < 68 then b 67 else b 68) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))) else (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77)))) else (if i < 84 then (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))) else (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))))))) else (if i < 135 then (if i < 112 then (if i < 101 then (if i < 95 then (if i < 92 then (if i < 91 then b 90 else b 91) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94))) else (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)))) else (if i < 106 then (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else (if i < 105 then b 104 else b 105))) else (if i < 109 then (if i < 107 then b 106 else (if i < 108 then b 107 else b 108)) else (if i < 110 then b 109 else (if i < 111 then b 110 else b 111))))) else (if i < 123 then (if i < 117 then (if i < 114 then (if i < 113 then b 112 else b 113) else (if i < 115 then b 114 else (if i < 116 then b 115 else b 116))) else (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)))) else (if i < 129 then (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 127 then b 126 else (if i < 128 then b 127 else b 128))) else (if i < 132 then (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)) else (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)))))) else (if i < 157 then (if i < 146 then (if i < 140 then (if i < 137 then (if i < 136 then b 135 else b 136) else (if i < 138 then b 137 else (if i < 139 then b 138 else b 139))) else (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)))) else (if i < 151 then (if i < 148 then (if i < 147 then b 146 else b 147) else (if i < 149 then b 148 else (if i < 150 then b 149 else b 150))) else (if i < 154 then (if i < 152 then b 151 else (if i < 153 then b 152 else b 153)) else (if i < 155 then b 154 else (if i < 156 then b 155 else b 156))))) else (if i < 168 then (if i < 162 then (if i < 159 then (if i < 158 then b 157 else b 158) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)))) else (if i < 174 then (if i < 171 then (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)) else (if i < 172 then b 171 else (if i < 173 then b 172 else b 173))) else (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)))))))) else (if i < 270 then (if i < 225 then (if i < 202 then (if i < 191 then (if i < 185 then (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else (if i < 184 then b 183 else b 184))) else (if i < 188 then (if i < 186 then b 185 else (if i < 187 then b 186 else b 187)) else (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)))) else (if i < 196 then (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else (if i < 195 then b 194 else b 195))) else (if i < 199 then (if i < 197 then b 196 else (if i < 198 then b 197 else b 198)) else (if i < 200 then b 199 else (if i < 201 then b 200 else b 201))))) else (if i < 213 then (if i < 207 then (if i < 204 then (if i < 203 then b 202 else b 203) else (if i < 205 then b 204 else (if i < 206 then b 205 else b 206))) else (if i < 210 then (if i < 208 then b 207 else (if i < 209 then b 208 else decide (1 ≤ count209 b))) else (if i < 211 then decide (2 ≤ count209 b) else (if i < 212 then decide (1 ≤ count211 b) else decide (2 ≤ count211 b))))) else (if i < 219 then (if i < 216 then (if i < 214 then decide (1 ≤ count213 b) else (if i < 215 then decide (2 ≤ count213 b) else decide (1 ≤ count215 b))) else (if i < 217 then decide (2 ≤ count215 b) else (if i < 218 then decide (1 ≤ count217 b) else decide (2 ≤ count217 b)))) else (if i < 222 then (if i < 220 then decide (1 ≤ count219 b) else (if i < 221 then decide (2 ≤ count219 b) else decide (1 ≤ count221 b))) else (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b))))))) else (if i < 247 then (if i < 236 then (if i < 230 then (if i < 227 then (if i < 226 then decide (1 ≤ count225 b) else decide (2 ≤ count225 b)) else (if i < 228 then decide (1 ≤ count227 b) else (if i < 229 then decide (2 ≤ count227 b) else decide (1 ≤ count229 b)))) else (if i < 233 then (if i < 231 then decide (2 ≤ count229 b) else (if i < 232 then decide (1 ≤ count231 b) else decide (2 ≤ count231 b))) else (if i < 234 then decide (1 ≤ count233 b) else (if i < 235 then decide (2 ≤ count233 b) else decide (1 ≤ count235 b))))) else (if i < 241 then (if i < 238 then (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b)) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b)))) else (if i < 244 then (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))) else (if i < 245 then decide (2 ≤ count243 b) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b)))))) else (if i < 258 then (if i < 252 then (if i < 249 then (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b)) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)))) else (if i < 255 then (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))) else (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))))) else (if i < 264 then (if i < 261 then (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)))) else (if i < 267 then (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))) else (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)))))))) else (if i < 315 then (if i < 292 then (if i < 281 then (if i < 275 then (if i < 272 then (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)) else (if i < 273 then decide (2 ≤ count271 b) else (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b)))) else (if i < 278 then (if i < 276 then decide (1 ≤ count275 b) else (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b))) else (if i < 279 then decide (2 ≤ count277 b) else (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b))))) else (if i < 286 then (if i < 283 then (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)) else (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)))) else (if i < 289 then (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b))) else (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b)))))) else (if i < 303 then (if i < 297 then (if i < 294 then (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b)) else (if i < 295 then decide (2 ≤ count293 b) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b)))) else (if i < 300 then (if i < 298 then decide (1 ≤ count297 b) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))) else (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b))))) else (if i < 309 then (if i < 306 then (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b))) else (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)))) else (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b))))))) else (if i < 338 then (if i < 326 then (if i < 320 then (if i < 317 then (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b)) else (if i < 318 then decide (1 ≤ count317 b) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))) else (if i < 323 then (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))) else (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))))) else (if i < 332 then (if i < 329 then (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))) else (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)))) else (if i < 335 then (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)))))) else (if i < 349 then (if i < 343 then (if i < 340 then (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)) else (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)))) else (if i < 346 then (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 347 then decide (2 ≤ count345 b) else (if i < 348 then decide (1 ≤ count347 b) else decide (2 ≤ count347 b))))) else (if i < 355 then (if i < 352 then (if i < 350 then decide (1 ≤ count349 b) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b))) else (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)))) else (if i < 358 then (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b))) else (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))))))))) else (if i < 541 then (if i < 451 then (if i < 406 then (if i < 383 then (if i < 372 then (if i < 366 then (if i < 363 then (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)) else (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))) else (if i < 369 then (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b))))) else (if i < 377 then (if i < 374 then (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)))) else (if i < 380 then (if i < 378 then decide (1 ≤ count377 b) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b))) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))))) else (if i < 394 then (if i < 388 then (if i < 385 then (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b)) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)))) else (if i < 391 then (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b))) else (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))))) else (if i < 400 then (if i < 397 then (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))) else (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))) else (if i < 403 then (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))) else (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))))))) else (if i < 428 then (if i < 417 then (if i < 411 then (if i < 408 then (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b)) else (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)))) else (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 415 then decide (2 ≤ count413 b) else (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b))))) else (if i < 422 then (if i < 419 then (if i < 418 then decide (3 ≤ count415 b) else decide (1 ≤ count418 b)) else (if i < 420 then decide (2 ≤ count418 b) else (if i < 421 then decide (1 ≤ count420 b) else decide (2 ≤ count420 b)))) else (if i < 425 then (if i < 423 then decide (3 ≤ count420 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 426 then decide (3 ≤ count423 b) else (if i < 427 then decide (4 ≤ count423 b) else decide (5 ≤ count423 b)))))) else (if i < 439 then (if i < 433 then (if i < 430 then (if i < 429 then decide (6 ≤ count423 b) else decide (1 ≤ count429 b)) else (if i < 431 then decide (2 ≤ count429 b) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)))) else (if i < 436 then (if i < 434 then decide (3 ≤ count431 b) else (if i < 435 then decide (1 ≤ count434 b) else decide (2 ≤ count434 b))) else (if i < 437 then decide (1 ≤ count436 b) else (if i < 438 then decide (2 ≤ count436 b) else decide (3 ≤ count436 b))))) else (if i < 445 then (if i < 442 then (if i < 440 then decide (1 ≤ count439 b) else (if i < 441 then decide (2 ≤ count439 b) else decide (3 ≤ count439 b))) else (if i < 443 then decide (4 ≤ count439 b) else (if i < 444 then decide (5 ≤ count439 b) else decide (6 ≤ count439 b)))) else (if i < 448 then (if i < 446 then decide (1 ≤ count445 b) else (if i < 447 then decide (2 ≤ count445 b) else decide (3 ≤ count445 b))) else (if i < 449 then decide (4 ≤ count445 b) else (if i < 450 then decide (5 ≤ count445 b) else decide (6 ≤ count445 b)))))))) else (if i < 496 then (if i < 473 then (if i < 462 then (if i < 456 then (if i < 453 then (if i < 452 then decide (7 ≤ count445 b) else decide (8 ≤ count445 b)) else (if i < 454 then decide (9 ≤ count445 b) else (if i < 455 then decide (10 ≤ count445 b) else decide (11 ≤ count445 b)))) else (if i < 459 then (if i < 457 then decide (12 ≤ count445 b) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b))) else (if i < 460 then decide (1 ≤ count459 b) else (if i < 461 then decide (2 ≤ count459 b) else decide (3 ≤ count459 b))))) else (if i < 467 then (if i < 464 then (if i < 463 then decide (1 ≤ count462 b) else decide (2 ≤ count462 b)) else (if i < 465 then decide (1 ≤ count464 b) else (if i < 466 then decide (2 ≤ count464 b) else decide (3 ≤ count464 b)))) else (if i < 470 then (if i < 468 then decide (1 ≤ count467 b) else (if i < 469 then decide (2 ≤ count467 b) else decide (3 ≤ count467 b))) else (if i < 471 then decide (4 ≤ count467 b) else (if i < 472 then decide (5 ≤ count467 b) else decide (6 ≤ count467 b)))))) else (if i < 484 then (if i < 478 then (if i < 475 then (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)) else (if i < 476 then decide (1 ≤ count475 b) else (if i < 477 then decide (2 ≤ count475 b) else decide (3 ≤ count475 b)))) else (if i < 481 then (if i < 479 then decide (1 ≤ count478 b) else (if i < 480 then decide (2 ≤ count478 b) else decide (1 ≤ count480 b))) else (if i < 482 then decide (2 ≤ count480 b) else (if i < 483 then decide (3 ≤ count480 b) else decide (1 ≤ count483 b))))) else (if i < 490 then (if i < 487 then (if i < 485 then decide (2 ≤ count483 b) else (if i < 486 then decide (3 ≤ count483 b) else decide (4 ≤ count483 b))) else (if i < 488 then decide (5 ≤ count483 b) else (if i < 489 then decide (6 ≤ count483 b) else decide (1 ≤ count489 b)))) else (if i < 493 then (if i < 491 then decide (2 ≤ count489 b) else (if i < 492 then decide (3 ≤ count489 b) else decide (4 ≤ count489 b))) else (if i < 494 then decide (5 ≤ count489 b) else (if i < 495 then decide (6 ≤ count489 b) else decide (7 ≤ count489 b))))))) else (if i < 518 then (if i < 507 then (if i < 501 then (if i < 498 then (if i < 497 then decide (8 ≤ count489 b) else decide (9 ≤ count489 b)) else (if i < 499 then decide (10 ≤ count489 b) else (if i < 500 then decide (11 ≤ count489 b) else decide (12 ≤ count489 b)))) else (if i < 504 then (if i < 502 then decide (1 ≤ count501 b) else (if i < 503 then decide (2 ≤ count501 b) else decide (3 ≤ count501 b))) else (if i < 505 then decide (4 ≤ count501 b) else (if i < 506 then decide (5 ≤ count501 b) else decide (6 ≤ count501 b))))) else (if i < 512 then (if i < 509 then (if i < 508 then decide (7 ≤ count501 b) else decide (8 ≤ count501 b)) else (if i < 510 then decide (9 ≤ count501 b) else (if i < 511 then decide (10 ≤ count501 b) else decide (11 ≤ count501 b)))) else (if i < 515 then (if i < 513 then decide (12 ≤ count501 b) else (if i < 514 then decide (13 ≤ count501 b) else decide (14 ≤ count501 b))) else (if i < 516 then decide (15 ≤ count501 b) else (if i < 517 then decide (16 ≤ count501 b) else decide (17 ≤ count501 b)))))) else (if i < 529 then (if i < 523 then (if i < 520 then (if i < 519 then decide (18 ≤ count501 b) else decide (19 ≤ count501 b)) else (if i < 521 then decide (20 ≤ count501 b) else (if i < 522 then decide (21 ≤ count501 b) else decide (22 ≤ count501 b)))) else (if i < 526 then (if i < 524 then decide (23 ≤ count501 b) else (if i < 525 then decide (24 ≤ count501 b) else decide (1 ≤ count525 b))) else (if i < 527 then decide (2 ≤ count525 b) else (if i < 528 then decide (1 ≤ count527 b) else decide (2 ≤ count527 b))))) else (if i < 535 then (if i < 532 then (if i < 530 then decide (3 ≤ count527 b) else (if i < 531 then decide (1 ≤ count530 b) else decide (2 ≤ count530 b))) else (if i < 533 then decide (1 ≤ count532 b) else (if i < 534 then decide (2 ≤ count532 b) else decide (3 ≤ count532 b)))) else (if i < 538 then (if i < 536 then decide (1 ≤ count535 b) else (if i < 537 then decide (2 ≤ count535 b) else decide (3 ≤ count535 b))) else (if i < 539 then decide (4 ≤ count535 b) else (if i < 540 then decide (5 ≤ count535 b) else decide (6 ≤ count535 b))))))))) else (if i < 631 then (if i < 586 then (if i < 563 then (if i < 552 then (if i < 546 then (if i < 543 then (if i < 542 then decide (1 ≤ count541 b) else decide (2 ≤ count541 b)) else (if i < 544 then decide (1 ≤ count543 b) else (if i < 545 then decide (2 ≤ count543 b) else decide (3 ≤ count543 b)))) else (if i < 549 then (if i < 547 then decide (1 ≤ count546 b) else (if i < 548 then decide (2 ≤ count546 b) else decide (1 ≤ count548 b))) else (if i < 550 then decide (2 ≤ count548 b) else (if i < 551 then decide (3 ≤ count548 b) else decide (1 ≤ count551 b))))) else (if i < 557 then (if i < 554 then (if i < 553 then decide (2 ≤ count551 b) else decide (3 ≤ count551 b)) else (if i < 555 then decide (4 ≤ count551 b) else (if i < 556 then decide (5 ≤ count551 b) else decide (6 ≤ count551 b)))) else (if i < 560 then (if i < 558 then decide (1 ≤ count557 b) else (if i < 559 then decide (2 ≤ count557 b) else decide (3 ≤ count557 b))) else (if i < 561 then decide (4 ≤ count557 b) else (if i < 562 then decide (5 ≤ count557 b) else decide (6 ≤ count557 b)))))) else (if i < 574 then (if i < 568 then (if i < 565 then (if i < 564 then decide (7 ≤ count557 b) else decide (8 ≤ count557 b)) else (if i < 566 then decide (9 ≤ count557 b) else (if i < 567 then decide (10 ≤ count557 b) else decide (11 ≤ count557 b)))) else (if i < 571 then (if i < 569 then decide (12 ≤ count557 b) else (if i < 570 then decide (1 ≤ count569 b) else decide (2 ≤ count569 b))) else (if i < 572 then decide (1 ≤ count571 b) else (if i < 573 then decide (2 ≤ count571 b) else decide (3 ≤ count571 b))))) else (if i < 580 then (if i < 577 then (if i < 575 then decide (1 ≤ count574 b) else (if i < 576 then decide (2 ≤ count574 b) else decide (1 ≤ count576 b))) else (if i < 578 then decide (2 ≤ count576 b) else (if i < 579 then decide (3 ≤ count576 b) else decide (1 ≤ count579 b)))) else (if i < 583 then (if i < 581 then decide (2 ≤ count579 b) else (if i < 582 then decide (3 ≤ count579 b) else decide (4 ≤ count579 b))) else (if i < 584 then decide (5 ≤ count579 b) else (if i < 585 then decide (6 ≤ count579 b) else decide (1 ≤ count585 b))))))) else (if i < 608 then (if i < 597 then (if i < 591 then (if i < 588 then (if i < 587 then decide (2 ≤ count585 b) else decide (1 ≤ count587 b)) else (if i < 589 then decide (2 ≤ count587 b) else (if i < 590 then decide (3 ≤ count587 b) else decide (1 ≤ count590 b)))) else (if i < 594 then (if i < 592 then decide (2 ≤ count590 b) else (if i < 593 then decide (1 ≤ count592 b) else decide (2 ≤ count592 b))) else (if i < 595 then decide (1 ≤ count594 b) else (if i < 596 then decide (2 ≤ count594 b) else decide (3 ≤ count594 b))))) else (if i < 602 then (if i < 599 then (if i < 598 then decide (4 ≤ count594 b) else decide (1 ≤ count598 b)) else (if i < 600 then decide (2 ≤ count598 b) else (if i < 601 then decide (3 ≤ count598 b) else decide (4 ≤ count598 b)))) else (if i < 605 then (if i < 603 then decide (5 ≤ count598 b) else (if i < 604 then decide (6 ≤ count598 b) else decide (7 ≤ count598 b))) else (if i < 606 then decide (1 ≤ count605 b) else (if i < 607 then decide (2 ≤ count605 b) else decide (3 ≤ count605 b)))))) else (if i < 619 then (if i < 613 then (if i < 610 then (if i < 609 then decide (4 ≤ count605 b) else decide (5 ≤ count605 b)) else (if i < 611 then decide (6 ≤ count605 b) else (if i < 612 then decide (7 ≤ count605 b) else decide (8 ≤ count605 b)))) else (if i < 616 then (if i < 614 then decide (9 ≤ count605 b) else (if i < 615 then decide (10 ≤ count605 b) else decide (11 ≤ count605 b))) else (if i < 617 then decide (12 ≤ count605 b) else (if i < 618 then decide (13 ≤ count605 b) else decide (1 ≤ count618 b))))) else (if i < 625 then (if i < 622 then (if i < 620 then decide (2 ≤ count618 b) else (if i < 621 then decide (3 ≤ count618 b) else decide (4 ≤ count618 b))) else (if i < 623 then decide (5 ≤ count618 b) else (if i < 624 then decide (6 ≤ count618 b) else decide (7 ≤ count618 b)))) else (if i < 628 then (if i < 626 then decide (8 ≤ count618 b) else (if i < 627 then decide (9 ≤ count618 b) else decide (10 ≤ count618 b))) else (if i < 629 then decide (11 ≤ count618 b) else (if i < 630 then decide (12 ≤ count618 b) else decide (13 ≤ count618 b)))))))) else (if i < 676 then (if i < 653 then (if i < 642 then (if i < 636 then (if i < 633 then (if i < 632 then decide (14 ≤ count618 b) else decide (15 ≤ count618 b)) else (if i < 634 then decide (16 ≤ count618 b) else (if i < 635 then decide (17 ≤ count618 b) else decide (18 ≤ count618 b)))) else (if i < 639 then (if i < 637 then decide (19 ≤ count618 b) else (if i < 638 then decide (20 ≤ count618 b) else decide (21 ≤ count618 b))) else (if i < 640 then decide (22 ≤ count618 b) else (if i < 641 then decide (23 ≤ count618 b) else decide (24 ≤ count618 b))))) else (if i < 647 then (if i < 644 then (if i < 643 then decide (25 ≤ count618 b) else decide (1 ≤ count643 b)) else (if i < 645 then decide (2 ≤ count643 b) else (if i < 646 then decide (3 ≤ count643 b) else decide (4 ≤ count643 b)))) else (if i < 650 then (if i < 648 then decide (5 ≤ count643 b) else (if i < 649 then decide (6 ≤ count643 b) else decide (7 ≤ count643 b))) else (if i < 651 then decide (8 ≤ count643 b) else (if i < 652 then decide (9 ≤ count643 b) else decide (10 ≤ count643 b)))))) else (if i < 664 then (if i < 658 then (if i < 655 then (if i < 654 then decide (11 ≤ count643 b) else decide (12 ≤ count643 b)) else (if i < 656 then decide (13 ≤ count643 b) else (if i < 657 then decide (14 ≤ count643 b) else decide (15 ≤ count643 b)))) else (if i < 661 then (if i < 659 then decide (16 ≤ count643 b) else (if i < 660 then decide (17 ≤ count643 b) else decide (18 ≤ count643 b))) else (if i < 662 then decide (19 ≤ count643 b) else (if i < 663 then decide (20 ≤ count643 b) else decide (21 ≤ count643 b))))) else (if i < 670 then (if i < 667 then (if i < 665 then decide (22 ≤ count643 b) else (if i < 666 then decide (23 ≤ count643 b) else decide (24 ≤ count643 b))) else (if i < 668 then decide (25 ≤ count643 b) else (if i < 669 then decide (26 ≤ count643 b) else decide (27 ≤ count643 b)))) else (if i < 673 then (if i < 671 then decide (28 ≤ count643 b) else (if i < 672 then decide (29 ≤ count643 b) else decide (30 ≤ count643 b))) else (if i < 674 then decide (31 ≤ count643 b) else (if i < 675 then decide (32 ≤ count643 b) else decide (33 ≤ count643 b))))))) else (if i < 699 then (if i < 687 then (if i < 681 then (if i < 678 then (if i < 677 then decide (34 ≤ count643 b) else decide (35 ≤ count643 b)) else (if i < 679 then decide (36 ≤ count643 b) else (if i < 680 then decide (37 ≤ count643 b) else decide (38 ≤ count643 b)))) else (if i < 684 then (if i < 682 then decide (39 ≤ count643 b) else (if i < 683 then decide (40 ≤ count643 b) else decide (41 ≤ count643 b))) else (if i < 685 then decide (42 ≤ count643 b) else (if i < 686 then decide (1 ≤ count685 b) else decide (2 ≤ count685 b))))) else (if i < 693 then (if i < 690 then (if i < 688 then decide (1 ≤ count687 b) else (if i < 689 then decide (2 ≤ count687 b) else decide (3 ≤ count687 b))) else (if i < 691 then decide (1 ≤ count690 b) else (if i < 692 then decide (2 ≤ count690 b) else decide (1 ≤ count692 b)))) else (if i < 696 then (if i < 694 then decide (2 ≤ count692 b) else (if i < 695 then decide (3 ≤ count692 b) else decide (1 ≤ count695 b))) else (if i < 697 then decide (2 ≤ count695 b) else (if i < 698 then decide (3 ≤ count695 b) else decide (4 ≤ count695 b)))))) else (if i < 710 then (if i < 704 then (if i < 701 then (if i < 700 then decide (5 ≤ count695 b) else decide (6 ≤ count695 b)) else (if i < 702 then decide (1 ≤ count701 b) else (if i < 703 then decide (2 ≤ count701 b) else decide (1 ≤ count703 b)))) else (if i < 707 then (if i < 705 then decide (2 ≤ count703 b) else (if i < 706 then decide (3 ≤ count703 b) else decide (1 ≤ count706 b))) else (if i < 708 then decide (2 ≤ count706 b) else (if i < 709 then decide (1 ≤ count708 b) else decide (2 ≤ count708 b))))) else (if i < 716 then (if i < 713 then (if i < 711 then decide (3 ≤ count708 b) else (if i < 712 then decide (1 ≤ count711 b) else decide (2 ≤ count711 b))) else (if i < 714 then decide (3 ≤ count711 b) else (if i < 715 then decide (4 ≤ count711 b) else decide (5 ≤ count711 b)))) else (if i < 719 then (if i < 717 then decide (6 ≤ count711 b) else (if i < 718 then decide (1 ≤ count717 b) else decide (2 ≤ count717 b))) else (if i < 720 then decide (3 ≤ count717 b) else (if i < 721 then decide (4 ≤ count717 b) else decide (5 ≤ count717 b))))))))))) else (if i < 1083 then (if i < 902 then (if i < 812 then (if i < 767 then (if i < 744 then (if i < 733 then (if i < 727 then (if i < 724 then (if i < 723 then decide (6 ≤ count717 b) else decide (7 ≤ count717 b)) else (if i < 725 then decide (8 ≤ count717 b) else (if i < 726 then decide (9 ≤ count717 b) else decide (1 ≤ count726 b)))) else (if i < 730 then (if i < 728 then decide (2 ≤ count726 b) else (if i < 729 then decide (1 ≤ count728 b) else decide (2 ≤ count728 b))) else (if i < 731 then decide (3 ≤ count728 b) else (if i < 732 then decide (1 ≤ count731 b) else decide (2 ≤ count731 b))))) else (if i < 738 then (if i < 735 then (if i < 734 then decide (1 ≤ count733 b) else decide (2 ≤ count733 b)) else (if i < 736 then decide (3 ≤ count733 b) else (if i < 737 then decide (1 ≤ count736 b) else decide (2 ≤ count736 b)))) else (if i < 741 then (if i < 739 then decide (3 ≤ count736 b) else (if i < 740 then decide (4 ≤ count736 b) else decide (5 ≤ count736 b))) else (if i < 742 then decide (6 ≤ count736 b) else (if i < 743 then decide (1 ≤ count742 b) else decide (2 ≤ count742 b)))))) else (if i < 755 then (if i < 749 then (if i < 746 then (if i < 745 then decide (1 ≤ count744 b) else decide (2 ≤ count744 b)) else (if i < 747 then decide (3 ≤ count744 b) else (if i < 748 then decide (1 ≤ count747 b) else decide (2 ≤ count747 b)))) else (if i < 752 then (if i < 750 then decide (1 ≤ count749 b) else (if i < 751 then decide (2 ≤ count749 b) else decide (3 ≤ count749 b))) else (if i < 753 then decide (1 ≤ count752 b) else (if i < 754 then decide (2 ≤ count752 b) else decide (3 ≤ count752 b))))) else (if i < 761 then (if i < 758 then (if i < 756 then decide (4 ≤ count752 b) else (if i < 757 then decide (5 ≤ count752 b) else decide (6 ≤ count752 b))) else (if i < 759 then decide (1 ≤ count758 b) else (if i < 760 then decide (2 ≤ count758 b) else decide (3 ≤ count758 b)))) else (if i < 764 then (if i < 762 then decide (4 ≤ count758 b) else (if i < 763 then decide (5 ≤ count758 b) else decide (6 ≤ count758 b))) else (if i < 765 then decide (7 ≤ count758 b) else (if i < 766 then decide (8 ≤ count758 b) else decide (9 ≤ count758 b))))))) else (if i < 789 then (if i < 778 then (if i < 772 then (if i < 769 then (if i < 768 then decide (1 ≤ count767 b) else decide (2 ≤ count767 b)) else (if i < 770 then decide (3 ≤ count767 b) else (if i < 771 then decide (4 ≤ count767 b) else decide (5 ≤ count767 b)))) else (if i < 775 then (if i < 773 then decide (6 ≤ count767 b) else (if i < 774 then decide (7 ≤ count767 b) else decide (8 ≤ count767 b))) else (if i < 776 then decide (9 ≤ count767 b) else (if i < 777 then decide (1 ≤ count776 b) else decide (2 ≤ count776 b))))) else (if i < 783 then (if i < 780 then (if i < 779 then decide (1 ≤ count778 b) else decide (2 ≤ count778 b)) else (if i < 781 then decide (3 ≤ count778 b) else (if i < 782 then decide (1 ≤ count781 b) else decide (2 ≤ count781 b)))) else (if i < 786 then (if i < 784 then decide (1 ≤ count783 b) else (if i < 785 then decide (2 ≤ count783 b) else decide (3 ≤ count783 b))) else (if i < 787 then decide (1 ≤ count786 b) else (if i < 788 then decide (2 ≤ count786 b) else decide (3 ≤ count786 b)))))) else (if i < 800 then (if i < 794 then (if i < 791 then (if i < 790 then decide (4 ≤ count786 b) else decide (5 ≤ count786 b)) else (if i < 792 then decide (6 ≤ count786 b) else (if i < 793 then decide (1 ≤ count792 b) else decide (2 ≤ count792 b)))) else (if i < 797 then (if i < 795 then decide (1 ≤ count794 b) else (if i < 796 then decide (2 ≤ count794 b) else decide (3 ≤ count794 b))) else (if i < 798 then decide (1 ≤ count797 b) else (if i < 799 then decide (2 ≤ count797 b) else decide (1 ≤ count799 b))))) else (if i < 806 then (if i < 803 then (if i < 801 then decide (2 ≤ count799 b) else (if i < 802 then decide (3 ≤ count799 b) else decide (1 ≤ count802 b))) else (if i < 804 then decide (2 ≤ count802 b) else (if i < 805 then decide (3 ≤ count802 b) else decide (4 ≤ count802 b)))) else (if i < 809 then (if i < 807 then decide (5 ≤ count802 b) else (if i < 808 then decide (6 ≤ count802 b) else decide (1 ≤ count808 b))) else (if i < 810 then decide (2 ≤ count808 b) else (if i < 811 then decide (3 ≤ count808 b) else decide (4 ≤ count808 b)))))))) else (if i < 857 then (if i < 834 then (if i < 823 then (if i < 817 then (if i < 814 then (if i < 813 then decide (5 ≤ count808 b) else decide (6 ≤ count808 b)) else (if i < 815 then decide (7 ≤ count808 b) else (if i < 816 then decide (8 ≤ count808 b) else decide (9 ≤ count808 b)))) else (if i < 820 then (if i < 818 then decide (1 ≤ count817 b) else (if i < 819 then decide (2 ≤ count817 b) else decide (1 ≤ count819 b))) else (if i < 821 then decide (2 ≤ count819 b) else (if i < 822 then decide (3 ≤ count819 b) else decide (1 ≤ count822 b))))) else (if i < 828 then (if i < 825 then (if i < 824 then decide (2 ≤ count822 b) else decide (1 ≤ count824 b)) else (if i < 826 then decide (2 ≤ count824 b) else (if i < 827 then decide (3 ≤ count824 b) else decide (1 ≤ count827 b)))) else (if i < 831 then (if i < 829 then decide (2 ≤ count827 b) else (if i < 830 then decide (3 ≤ count827 b) else decide (4 ≤ count827 b))) else (if i < 832 then decide (5 ≤ count827 b) else (if i < 833 then decide (6 ≤ count827 b) else decide (1 ≤ count833 b)))))) else (if i < 845 then (if i < 839 then (if i < 836 then (if i < 835 then decide (2 ≤ count833 b) else decide (1 ≤ count835 b)) else (if i < 837 then decide (2 ≤ count835 b) else (if i < 838 then decide (3 ≤ count835 b) else decide (1 ≤ count838 b)))) else (if i < 842 then (if i < 840 then decide (2 ≤ count838 b) else (if i < 841 then decide (1 ≤ count840 b) else decide (2 ≤ count840 b))) else (if i < 843 then decide (1 ≤ count842 b) else (if i < 844 then decide (2 ≤ count842 b) else decide (3 ≤ count842 b))))) else (if i < 851 then (if i < 848 then (if i < 846 then decide (4 ≤ count842 b) else (if i < 847 then decide (1 ≤ count846 b) else decide (2 ≤ count846 b))) else (if i < 849 then decide (3 ≤ count846 b) else (if i < 850 then decide (4 ≤ count846 b) else decide (5 ≤ count846 b)))) else (if i < 854 then (if i < 852 then decide (6 ≤ count846 b) else (if i < 853 then decide (7 ≤ count846 b) else decide (1 ≤ count853 b))) else (if i < 855 then decide (2 ≤ count853 b) else (if i < 856 then decide (3 ≤ count853 b) else decide (4 ≤ count853 b))))))) else (if i < 879 then (if i < 868 then (if i < 862 then (if i < 859 then (if i < 858 then decide (5 ≤ count853 b) else decide (6 ≤ count853 b)) else (if i < 860 then decide (7 ≤ count853 b) else (if i < 861 then decide (8 ≤ count853 b) else decide (9 ≤ count853 b)))) else (if i < 865 then (if i < 863 then decide (1 ≤ count862 b) else (if i < 864 then decide (2 ≤ count862 b) else decide (3 ≤ count862 b))) else (if i < 866 then decide (4 ≤ count862 b) else (if i < 867 then decide (5 ≤ count862 b) else decide (6 ≤ count862 b))))) else (if i < 873 then (if i < 870 then (if i < 869 then decide (7 ≤ count862 b) else decide (8 ≤ count862 b)) else (if i < 871 then decide (9 ≤ count862 b) else (if i < 872 then decide (1 ≤ count871 b) else decide (2 ≤ count871 b)))) else (if i < 876 then (if i < 874 then decide (3 ≤ count871 b) else (if i < 875 then decide (4 ≤ count871 b) else decide (5 ≤ count871 b))) else (if i < 877 then decide (6 ≤ count871 b) else (if i < 878 then decide (7 ≤ count871 b) else decide (8 ≤ count871 b)))))) else (if i < 890 then (if i < 884 then (if i < 881 then (if i < 880 then decide (9 ≤ count871 b) else decide (1 ≤ count880 b)) else (if i < 882 then decide (2 ≤ count880 b) else (if i < 883 then decide (1 ≤ count882 b) else decide (2 ≤ count882 b)))) else (if i < 887 then (if i < 885 then decide (3 ≤ count882 b) else (if i < 886 then decide (1 ≤ count885 b) else decide (2 ≤ count885 b))) else (if i < 888 then decide (1 ≤ count887 b) else (if i < 889 then decide (2 ≤ count887 b) else decide (3 ≤ count887 b))))) else (if i < 896 then (if i < 893 then (if i < 891 then decide (1 ≤ count890 b) else (if i < 892 then decide (2 ≤ count890 b) else decide (3 ≤ count890 b))) else (if i < 894 then decide (4 ≤ count890 b) else (if i < 895 then decide (5 ≤ count890 b) else decide (6 ≤ count890 b)))) else (if i < 899 then (if i < 897 then decide (1 ≤ count896 b) else (if i < 898 then decide (2 ≤ count896 b) else decide (1 ≤ count898 b))) else (if i < 900 then decide (2 ≤ count898 b) else (if i < 901 then decide (3 ≤ count898 b) else decide (1 ≤ count901 b))))))))) else (if i < 992 then (if i < 947 then (if i < 924 then (if i < 913 then (if i < 907 then (if i < 904 then (if i < 903 then decide (2 ≤ count901 b) else decide (1 ≤ count903 b)) else (if i < 905 then decide (2 ≤ count903 b) else (if i < 906 then decide (1 ≤ count905 b) else decide (2 ≤ count905 b)))) else (if i < 910 then (if i < 908 then decide (3 ≤ count905 b) else (if i < 909 then decide (4 ≤ count905 b) else decide (1 ≤ count909 b))) else (if i < 911 then decide (2 ≤ count909 b) else (if i < 912 then decide (3 ≤ count909 b) else decide (4 ≤ count909 b))))) else (if i < 918 then (if i < 915 then (if i < 914 then decide (5 ≤ count909 b) else decide (6 ≤ count909 b)) else (if i < 916 then decide (7 ≤ count909 b) else (if i < 917 then decide (1 ≤ count916 b) else decide (2 ≤ count916 b)))) else (if i < 921 then (if i < 919 then decide (3 ≤ count916 b) else (if i < 920 then decide (4 ≤ count916 b) else decide (5 ≤ count916 b))) else (if i < 922 then decide (6 ≤ count916 b) else (if i < 923 then decide (7 ≤ count916 b) else decide (8 ≤ count916 b)))))) else (if i < 935 then (if i < 929 then (if i < 926 then (if i < 925 then decide (9 ≤ count916 b) else decide (10 ≤ count916 b)) else (if i < 927 then decide (11 ≤ count916 b) else (if i < 928 then decide (12 ≤ count916 b) else decide (13 ≤ count916 b)))) else (if i < 932 then (if i < 930 then decide (1 ≤ count929 b) else (if i < 931 then decide (2 ≤ count929 b) else decide (1 ≤ count931 b))) else (if i < 933 then decide (2 ≤ count931 b) else (if i < 934 then decide (3 ≤ count931 b) else decide (1 ≤ count934 b))))) else (if i < 941 then (if i < 938 then (if i < 936 then decide (2 ≤ count934 b) else (if i < 937 then decide (1 ≤ count936 b) else decide (2 ≤ count936 b))) else (if i < 939 then decide (1 ≤ count938 b) else (if i < 940 then decide (2 ≤ count938 b) else decide (3 ≤ count938 b)))) else (if i < 944 then (if i < 942 then decide (4 ≤ count938 b) else (if i < 943 then decide (1 ≤ count942 b) else decide (2 ≤ count942 b))) else (if i < 945 then decide (3 ≤ count942 b) else (if i < 946 then decide (4 ≤ count942 b) else decide (5 ≤ count942 b))))))) else (if i < 969 then (if i < 958 then (if i < 952 then (if i < 949 then (if i < 948 then decide (6 ≤ count942 b) else decide (7 ≤ count942 b)) else (if i < 950 then decide (1 ≤ count949 b) else (if i < 951 then decide (2 ≤ count949 b) else decide (1 ≤ count951 b)))) else (if i < 955 then (if i < 953 then decide (2 ≤ count951 b) else (if i < 954 then decide (3 ≤ count951 b) else decide (1 ≤ count954 b))) else (if i < 956 then decide (2 ≤ count954 b) else (if i < 957 then decide (1 ≤ count956 b) else decide (2 ≤ count956 b))))) else (if i < 963 then (if i < 960 then (if i < 959 then decide (1 ≤ count958 b) else decide (2 ≤ count958 b)) else (if i < 961 then decide (3 ≤ count958 b) else (if i < 962 then decide (4 ≤ count958 b) else decide (1 ≤ count962 b)))) else (if i < 966 then (if i < 964 then decide (2 ≤ count962 b) else (if i < 965 then decide (3 ≤ count962 b) else decide (4 ≤ count962 b))) else (if i < 967 then decide (5 ≤ count962 b) else (if i < 968 then decide (6 ≤ count962 b) else decide (7 ≤ count962 b)))))) else (if i < 980 then (if i < 974 then (if i < 971 then (if i < 970 then decide (1 ≤ count969 b) else decide (2 ≤ count969 b)) else (if i < 972 then decide (3 ≤ count969 b) else (if i < 973 then decide (4 ≤ count969 b) else decide (5 ≤ count969 b)))) else (if i < 977 then (if i < 975 then decide (6 ≤ count969 b) else (if i < 976 then decide (7 ≤ count969 b) else decide (8 ≤ count969 b))) else (if i < 978 then decide (9 ≤ count969 b) else (if i < 979 then decide (10 ≤ count969 b) else decide (11 ≤ count969 b))))) else (if i < 986 then (if i < 983 then (if i < 981 then decide (12 ≤ count969 b) else (if i < 982 then decide (13 ≤ count969 b) else decide (14 ≤ count969 b))) else (if i < 984 then decide (1 ≤ count983 b) else (if i < 985 then decide (2 ≤ count983 b) else decide (3 ≤ count983 b)))) else (if i < 989 then (if i < 987 then decide (4 ≤ count983 b) else (if i < 988 then decide (5 ≤ count983 b) else decide (6 ≤ count983 b))) else (if i < 990 then decide (7 ≤ count983 b) else (if i < 991 then decide (8 ≤ count983 b) else decide (9 ≤ count983 b)))))))) else (if i < 1037 then (if i < 1014 then (if i < 1003 then (if i < 997 then (if i < 994 then (if i < 993 then decide (10 ≤ count983 b) else decide (11 ≤ count983 b)) else (if i < 995 then decide (12 ≤ count983 b) else (if i < 996 then decide (13 ≤ count983 b) else decide (14 ≤ count983 b)))) else (if i < 1000 then (if i < 998 then decide (15 ≤ count983 b) else (if i < 999 then decide (16 ≤ count983 b) else decide (17 ≤ count983 b))) else (if i < 1001 then decide (18 ≤ count983 b) else (if i < 1002 then decide (19 ≤ count983 b) else decide (20 ≤ count983 b))))) else (if i < 1008 then (if i < 1005 then (if i < 1004 then decide (21 ≤ count983 b) else decide (22 ≤ count983 b)) else (if i < 1006 then decide (23 ≤ count983 b) else (if i < 1007 then decide (24 ≤ count983 b) else decide (25 ≤ count983 b)))) else (if i < 1011 then (if i < 1009 then decide (26 ≤ count983 b) else (if i < 1010 then decide (27 ≤ count983 b) else decide (1 ≤ count1010 b))) else (if i < 1012 then decide (2 ≤ count1010 b) else (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b)))))) else (if i < 1025 then (if i < 1019 then (if i < 1016 then (if i < 1015 then decide (3 ≤ count1012 b) else decide (1 ≤ count1015 b)) else (if i < 1017 then decide (2 ≤ count1015 b) else (if i < 1018 then decide (1 ≤ count1017 b) else decide (2 ≤ count1017 b)))) else (if i < 1022 then (if i < 1020 then decide (1 ≤ count1019 b) else (if i < 1021 then decide (2 ≤ count1019 b) else decide (3 ≤ count1019 b))) else (if i < 1023 then decide (4 ≤ count1019 b) else (if i < 1024 then decide (1 ≤ count1023 b) else decide (2 ≤ count1023 b))))) else (if i < 1031 then (if i < 1028 then (if i < 1026 then decide (3 ≤ count1023 b) else (if i < 1027 then decide (4 ≤ count1023 b) else decide (5 ≤ count1023 b))) else (if i < 1029 then decide (6 ≤ count1023 b) else (if i < 1030 then decide (7 ≤ count1023 b) else decide (1 ≤ count1030 b)))) else (if i < 1034 then (if i < 1032 then decide (2 ≤ count1030 b) else (if i < 1033 then decide (1 ≤ count1032 b) else decide (2 ≤ count1032 b))) else (if i < 1035 then decide (3 ≤ count1032 b) else (if i < 1036 then decide (1 ≤ count1035 b) else decide (2 ≤ count1035 b))))))) else (if i < 1060 then (if i < 1048 then (if i < 1042 then (if i < 1039 then (if i < 1038 then decide (1 ≤ count1037 b) else decide (2 ≤ count1037 b)) else (if i < 1040 then decide (1 ≤ count1039 b) else (if i < 1041 then decide (2 ≤ count1039 b) else decide (3 ≤ count1039 b)))) else (if i < 1045 then (if i < 1043 then decide (4 ≤ count1039 b) else (if i < 1044 then decide (1 ≤ count1043 b) else decide (2 ≤ count1043 b))) else (if i < 1046 then decide (3 ≤ count1043 b) else (if i < 1047 then decide (4 ≤ count1043 b) else decide (5 ≤ count1043 b))))) else (if i < 1054 then (if i < 1051 then (if i < 1049 then decide (6 ≤ count1043 b) else (if i < 1050 then decide (7 ≤ count1043 b) else decide (1 ≤ count1050 b))) else (if i < 1052 then decide (2 ≤ count1050 b) else (if i < 1053 then decide (3 ≤ count1050 b) else decide (4 ≤ count1050 b)))) else (if i < 1057 then (if i < 1055 then decide (5 ≤ count1050 b) else (if i < 1056 then decide (6 ≤ count1050 b) else decide (7 ≤ count1050 b))) else (if i < 1058 then decide (8 ≤ count1050 b) else (if i < 1059 then decide (9 ≤ count1050 b) else decide (10 ≤ count1050 b)))))) else (if i < 1071 then (if i < 1065 then (if i < 1062 then (if i < 1061 then decide (11 ≤ count1050 b) else decide (12 ≤ count1050 b)) else (if i < 1063 then decide (13 ≤ count1050 b) else (if i < 1064 then decide (14 ≤ count1050 b) else decide (1 ≤ count1064 b)))) else (if i < 1068 then (if i < 1066 then decide (2 ≤ count1064 b) else (if i < 1067 then decide (1 ≤ count1066 b) else decide (2 ≤ count1066 b))) else (if i < 1069 then decide (3 ≤ count1066 b) else (if i < 1070 then decide (1 ≤ count1069 b) else decide (2 ≤ count1069 b))))) else (if i < 1077 then (if i < 1074 then (if i < 1072 then decide (1 ≤ count1071 b) else (if i < 1073 then decide (2 ≤ count1071 b) else decide (1 ≤ count1073 b))) else (if i < 1075 then decide (2 ≤ count1073 b) else (if i < 1076 then decide (3 ≤ count1073 b) else decide (4 ≤ count1073 b)))) else (if i < 1080 then (if i < 1078 then decide (1 ≤ count1077 b) else (if i < 1079 then decide (2 ≤ count1077 b) else decide (3 ≤ count1077 b))) else (if i < 1081 then decide (4 ≤ count1077 b) else (if i < 1082 then decide (5 ≤ count1077 b) else decide (6 ≤ count1077 b)))))))))) else (if i < 1263 then (if i < 1173 then (if i < 1128 then (if i < 1105 then (if i < 1094 then (if i < 1088 then (if i < 1085 then (if i < 1084 then decide (7 ≤ count1077 b) else decide (1 ≤ count1084 b)) else (if i < 1086 then decide (2 ≤ count1084 b) else (if i < 1087 then decide (1 ≤ count1086 b) else decide (2 ≤ count1086 b)))) else (if i < 1091 then (if i < 1089 then decide (3 ≤ count1086 b) else (if i < 1090 then decide (1 ≤ count1089 b) else decide (2 ≤ count1089 b))) else (if i < 1092 then decide (1 ≤ count1091 b) else (if i < 1093 then decide (2 ≤ count1091 b) else decide (1 ≤ count1093 b))))) else (if i < 1099 then (if i < 1096 then (if i < 1095 then decide (2 ≤ count1093 b) else decide (3 ≤ count1093 b)) else (if i < 1097 then decide (4 ≤ count1093 b) else (if i < 1098 then decide (1 ≤ count1097 b) else decide (2 ≤ count1097 b)))) else (if i < 1102 then (if i < 1100 then decide (3 ≤ count1097 b) else (if i < 1101 then decide (4 ≤ count1097 b) else decide (5 ≤ count1097 b))) else (if i < 1103 then decide (6 ≤ count1097 b) else (if i < 1104 then decide (7 ≤ count1097 b) else decide (1 ≤ count1104 b)))))) else (if i < 1116 then (if i < 1110 then (if i < 1107 then (if i < 1106 then decide (2 ≤ count1104 b) else decide (3 ≤ count1104 b)) else (if i < 1108 then decide (4 ≤ count1104 b) else (if i < 1109 then decide (5 ≤ count1104 b) else decide (6 ≤ count1104 b)))) else (if i < 1113 then (if i < 1111 then decide (7 ≤ count1104 b) else (if i < 1112 then decide (8 ≤ count1104 b) else decide (9 ≤ count1104 b))) else (if i < 1114 then decide (10 ≤ count1104 b) else (if i < 1115 then decide (11 ≤ count1104 b) else decide (12 ≤ count1104 b))))) else (if i < 1122 then (if i < 1119 then (if i < 1117 then decide (13 ≤ count1104 b) else (if i < 1118 then decide (14 ≤ count1104 b) else decide (1 ≤ count1118 b))) else (if i < 1120 then decide (2 ≤ count1118 b) else (if i < 1121 then decide (3 ≤ count1118 b) else decide (4 ≤ count1118 b)))) else (if i < 1125 then (if i < 1123 then decide (5 ≤ count1118 b) else (if i < 1124 then decide (6 ≤ count1118 b) else decide (7 ≤ count1118 b))) else (if i < 1126 then decide (8 ≤ count1118 b) else (if i < 1127 then decide (9 ≤ count1118 b) else decide (10 ≤ count1118 b))))))) else (if i < 1150 then (if i < 1139 then (if i < 1133 then (if i < 1130 then (if i < 1129 then decide (11 ≤ count1118 b) else decide (12 ≤ count1118 b)) else (if i < 1131 then decide (13 ≤ count1118 b) else (if i < 1132 then decide (14 ≤ count1118 b) else decide (15 ≤ count1118 b)))) else (if i < 1136 then (if i < 1134 then decide (16 ≤ count1118 b) else (if i < 1135 then decide (17 ≤ count1118 b) else decide (18 ≤ count1118 b))) else (if i < 1137 then decide (19 ≤ count1118 b) else (if i < 1138 then decide (20 ≤ count1118 b) else decide (21 ≤ count1118 b))))) else (if i < 1144 then (if i < 1141 then (if i < 1140 then decide (22 ≤ count1118 b) else decide (23 ≤ count1118 b)) else (if i < 1142 then decide (24 ≤ count1118 b) else (if i < 1143 then decide (25 ≤ count1118 b) else decide (26 ≤ count1118 b)))) else (if i < 1147 then (if i < 1145 then decide (27 ≤ count1118 b) else (if i < 1146 then decide (28 ≤ count1118 b) else decide (1 ≤ count1146 b))) else (if i < 1148 then decide (2 ≤ count1146 b) else (if i < 1149 then decide (3 ≤ count1146 b) else decide (4 ≤ count1146 b)))))) else (if i < 1161 then (if i < 1155 then (if i < 1152 then (if i < 1151 then decide (5 ≤ count1146 b) else decide (6 ≤ count1146 b)) else (if i < 1153 then decide (7 ≤ count1146 b) else (if i < 1154 then decide (8 ≤ count1146 b) else decide (9 ≤ count1146 b)))) else (if i < 1158 then (if i < 1156 then decide (10 ≤ count1146 b) else (if i < 1157 then decide (11 ≤ count1146 b) else decide (12 ≤ count1146 b))) else (if i < 1159 then decide (13 ≤ count1146 b) else (if i < 1160 then decide (14 ≤ count1146 b) else decide (15 ≤ count1146 b))))) else (if i < 1167 then (if i < 1164 then (if i < 1162 then decide (16 ≤ count1146 b) else (if i < 1163 then decide (17 ≤ count1146 b) else decide (18 ≤ count1146 b))) else (if i < 1165 then decide (19 ≤ count1146 b) else (if i < 1166 then decide (20 ≤ count1146 b) else decide (21 ≤ count1146 b)))) else (if i < 1170 then (if i < 1168 then decide (22 ≤ count1146 b) else (if i < 1169 then decide (23 ≤ count1146 b) else decide (24 ≤ count1146 b))) else (if i < 1171 then decide (25 ≤ count1146 b) else (if i < 1172 then decide (26 ≤ count1146 b) else decide (27 ≤ count1146 b)))))))) else (if i < 1218 then (if i < 1195 then (if i < 1184 then (if i < 1178 then (if i < 1175 then (if i < 1174 then decide (28 ≤ count1146 b) else decide (29 ≤ count1146 b)) else (if i < 1176 then decide (30 ≤ count1146 b) else (if i < 1177 then decide (31 ≤ count1146 b) else decide (32 ≤ count1146 b)))) else (if i < 1181 then (if i < 1179 then decide (33 ≤ count1146 b) else (if i < 1180 then decide (34 ≤ count1146 b) else decide (35 ≤ count1146 b))) else (if i < 1182 then decide (36 ≤ count1146 b) else (if i < 1183 then decide (37 ≤ count1146 b) else decide (38 ≤ count1146 b))))) else (if i < 1189 then (if i < 1186 then (if i < 1185 then decide (39 ≤ count1146 b) else decide (40 ≤ count1146 b)) else (if i < 1187 then decide (41 ≤ count1146 b) else (if i < 1188 then decide (42 ≤ count1146 b) else decide (1 ≤ count1188 b)))) else (if i < 1192 then (if i < 1190 then decide (2 ≤ count1188 b) else (if i < 1191 then decide (1 ≤ count1190 b) else decide (2 ≤ count1190 b))) else (if i < 1193 then decide (3 ≤ count1190 b) else (if i < 1194 then decide (1 ≤ count1193 b) else decide (2 ≤ count1193 b)))))) else (if i < 1206 then (if i < 1200 then (if i < 1197 then (if i < 1196 then decide (1 ≤ count1195 b) else decide (2 ≤ count1195 b)) else (if i < 1198 then decide (3 ≤ count1195 b) else (if i < 1199 then decide (1 ≤ count1198 b) else decide (2 ≤ count1198 b)))) else (if i < 1203 then (if i < 1201 then decide (3 ≤ count1198 b) else (if i < 1202 then decide (4 ≤ count1198 b) else decide (5 ≤ count1198 b))) else (if i < 1204 then decide (6 ≤ count1198 b) else (if i < 1205 then decide (1 ≤ count1204 b) else decide (2 ≤ count1204 b))))) else (if i < 1212 then (if i < 1209 then (if i < 1207 then decide (1 ≤ count1206 b) else (if i < 1208 then decide (2 ≤ count1206 b) else decide (3 ≤ count1206 b))) else (if i < 1210 then decide (1 ≤ count1209 b) else (if i < 1211 then decide (2 ≤ count1209 b) else decide (1 ≤ count1211 b)))) else (if i < 1215 then (if i < 1213 then decide (2 ≤ count1211 b) else (if i < 1214 then decide (1 ≤ count1213 b) else decide (2 ≤ count1213 b))) else (if i < 1216 then decide (3 ≤ count1213 b) else (if i < 1217 then decide (4 ≤ count1213 b) else decide (1 ≤ count1217 b))))))) else (if i < 1240 then (if i < 1229 then (if i < 1223 then (if i < 1220 then (if i < 1219 then decide (2 ≤ count1217 b) else decide (3 ≤ count1217 b)) else (if i < 1221 then decide (4 ≤ count1217 b) else (if i < 1222 then decide (5 ≤ count1217 b) else decide (6 ≤ count1217 b)))) else (if i < 1226 then (if i < 1224 then decide (7 ≤ count1217 b) else (if i < 1225 then decide (1 ≤ count1224 b) else decide (2 ≤ count1224 b))) else (if i < 1227 then decide (3 ≤ count1224 b) else (if i < 1228 then decide (4 ≤ count1224 b) else decide (5 ≤ count1224 b))))) else (if i < 1234 then (if i < 1231 then (if i < 1230 then decide (6 ≤ count1224 b) else decide (7 ≤ count1224 b)) else (if i < 1232 then decide (8 ≤ count1224 b) else (if i < 1233 then decide (9 ≤ count1224 b) else decide (10 ≤ count1224 b)))) else (if i < 1237 then (if i < 1235 then decide (11 ≤ count1224 b) else (if i < 1236 then decide (12 ≤ count1224 b) else decide (13 ≤ count1224 b))) else (if i < 1238 then decide (1 ≤ count1237 b) else (if i < 1239 then decide (2 ≤ count1237 b) else decide (1 ≤ count1239 b)))))) else (if i < 1251 then (if i < 1245 then (if i < 1242 then (if i < 1241 then decide (2 ≤ count1239 b) else decide (3 ≤ count1239 b)) else (if i < 1243 then decide (1 ≤ count1242 b) else (if i < 1244 then decide (2 ≤ count1242 b) else decide (1 ≤ count1244 b)))) else (if i < 1248 then (if i < 1246 then decide (2 ≤ count1244 b) else (if i < 1247 then decide (1 ≤ count1246 b) else decide (2 ≤ count1246 b))) else (if i < 1249 then decide (3 ≤ count1246 b) else (if i < 1250 then decide (4 ≤ count1246 b) else decide (1 ≤ count1250 b))))) else (if i < 1257 then (if i < 1254 then (if i < 1252 then decide (2 ≤ count1250 b) else (if i < 1253 then decide (3 ≤ count1250 b) else decide (4 ≤ count1250 b))) else (if i < 1255 then decide (5 ≤ count1250 b) else (if i < 1256 then decide (6 ≤ count1250 b) else decide (7 ≤ count1250 b)))) else (if i < 1260 then (if i < 1258 then decide (1 ≤ count1257 b) else (if i < 1259 then decide (2 ≤ count1257 b) else decide (1 ≤ count1259 b))) else (if i < 1261 then decide (2 ≤ count1259 b) else (if i < 1262 then decide (3 ≤ count1259 b) else decide (1 ≤ count1262 b))))))))) else (if i < 1353 then (if i < 1308 then (if i < 1285 then (if i < 1274 then (if i < 1268 then (if i < 1265 then (if i < 1264 then decide (2 ≤ count1262 b) else decide (1 ≤ count1264 b)) else (if i < 1266 then decide (2 ≤ count1264 b) else (if i < 1267 then decide (1 ≤ count1266 b) else decide (2 ≤ count1266 b)))) else (if i < 1271 then (if i < 1269 then decide (3 ≤ count1266 b) else (if i < 1270 then decide (4 ≤ count1266 b) else decide (1 ≤ count1270 b))) else (if i < 1272 then decide (2 ≤ count1270 b) else (if i < 1273 then decide (3 ≤ count1270 b) else decide (4 ≤ count1270 b))))) else (if i < 1279 then (if i < 1276 then (if i < 1275 then decide (5 ≤ count1270 b) else decide (6 ≤ count1270 b)) else (if i < 1277 then decide (7 ≤ count1270 b) else (if i < 1278 then decide (1 ≤ count1277 b) else decide (2 ≤ count1277 b)))) else (if i < 1282 then (if i < 1280 then decide (3 ≤ count1277 b) else (if i < 1281 then decide (4 ≤ count1277 b) else decide (5 ≤ count1277 b))) else (if i < 1283 then decide (6 ≤ count1277 b) else (if i < 1284 then decide (7 ≤ count1277 b) else decide (8 ≤ count1277 b)))))) else (if i < 1296 then (if i < 1290 then (if i < 1287 then (if i < 1286 then decide (9 ≤ count1277 b) else decide (10 ≤ count1277 b)) else (if i < 1288 then decide (11 ≤ count1277 b) else (if i < 1289 then decide (12 ≤ count1277 b) else decide (13 ≤ count1277 b)))) else (if i < 1293 then (if i < 1291 then decide (14 ≤ count1277 b) else (if i < 1292 then decide (1 ≤ count1291 b) else decide (2 ≤ count1291 b))) else (if i < 1294 then decide (3 ≤ count1291 b) else (if i < 1295 then decide (4 ≤ count1291 b) else decide (5 ≤ count1291 b))))) else (if i < 1302 then (if i < 1299 then (if i < 1297 then decide (6 ≤ count1291 b) else (if i < 1298 then decide (7 ≤ count1291 b) else decide (8 ≤ count1291 b))) else (if i < 1300 then decide (9 ≤ count1291 b) else (if i < 1301 then decide (10 ≤ count1291 b) else decide (11 ≤ count1291 b)))) else (if i < 1305 then (if i < 1303 then decide (12 ≤ count1291 b) else (if i < 1304 then decide (13 ≤ count1291 b) else decide (14 ≤ count1291 b))) else (if i < 1306 then decide (15 ≤ count1291 b) else (if i < 1307 then decide (1 ≤ count1306 b) else decide (2 ≤ count1306 b))))))) else (if i < 1330 then (if i < 1319 then (if i < 1313 then (if i < 1310 then (if i < 1309 then decide (1 ≤ count1308 b) else decide (2 ≤ count1308 b)) else (if i < 1311 then decide (3 ≤ count1308 b) else (if i < 1312 then decide (1 ≤ count1311 b) else decide (2 ≤ count1311 b)))) else (if i < 1316 then (if i < 1314 then decide (1 ≤ count1313 b) else (if i < 1315 then decide (2 ≤ count1313 b) else decide (1 ≤ count1315 b))) else (if i < 1317 then decide (2 ≤ count1315 b) else (if i < 1318 then decide (3 ≤ count1315 b) else decide (4 ≤ count1315 b))))) else (if i < 1324 then (if i < 1321 then (if i < 1320 then decide (1 ≤ count1319 b) else decide (2 ≤ count1319 b)) else (if i < 1322 then decide (3 ≤ count1319 b) else (if i < 1323 then decide (4 ≤ count1319 b) else decide (5 ≤ count1319 b)))) else (if i < 1327 then (if i < 1325 then decide (6 ≤ count1319 b) else (if i < 1326 then decide (7 ≤ count1319 b) else decide (1 ≤ count1326 b))) else (if i < 1328 then decide (2 ≤ count1326 b) else (if i < 1329 then decide (1 ≤ count1328 b) else decide (2 ≤ count1328 b)))))) else (if i < 1341 then (if i < 1335 then (if i < 1332 then (if i < 1331 then decide (3 ≤ count1328 b) else decide (1 ≤ count1331 b)) else (if i < 1333 then decide (2 ≤ count1331 b) else (if i < 1334 then decide (1 ≤ count1333 b) else decide (2 ≤ count1333 b)))) else (if i < 1338 then (if i < 1336 then decide (1 ≤ count1335 b) else (if i < 1337 then decide (2 ≤ count1335 b) else decide (3 ≤ count1335 b))) else (if i < 1339 then decide (4 ≤ count1335 b) else (if i < 1340 then decide (1 ≤ count1339 b) else decide (2 ≤ count1339 b))))) else (if i < 1347 then (if i < 1344 then (if i < 1342 then decide (3 ≤ count1339 b) else (if i < 1343 then decide (4 ≤ count1339 b) else decide (5 ≤ count1339 b))) else (if i < 1345 then decide (6 ≤ count1339 b) else (if i < 1346 then decide (7 ≤ count1339 b) else decide (1 ≤ count1346 b)))) else (if i < 1350 then (if i < 1348 then decide (2 ≤ count1346 b) else (if i < 1349 then decide (3 ≤ count1346 b) else decide (4 ≤ count1346 b))) else (if i < 1351 then decide (5 ≤ count1346 b) else (if i < 1352 then decide (6 ≤ count1346 b) else decide (7 ≤ count1346 b)))))))) else (if i < 1398 then (if i < 1375 then (if i < 1364 then (if i < 1358 then (if i < 1355 then (if i < 1354 then decide (8 ≤ count1346 b) else decide (9 ≤ count1346 b)) else (if i < 1356 then decide (10 ≤ count1346 b) else (if i < 1357 then decide (11 ≤ count1346 b) else decide (12 ≤ count1346 b)))) else (if i < 1361 then (if i < 1359 then decide (13 ≤ count1346 b) else (if i < 1360 then decide (14 ≤ count1346 b) else decide (1 ≤ count1360 b))) else (if i < 1362 then decide (2 ≤ count1360 b) else (if i < 1363 then decide (1 ≤ count1362 b) else decide (2 ≤ count1362 b))))) else (if i < 1369 then (if i < 1366 then (if i < 1365 then decide (3 ≤ count1362 b) else decide (1 ≤ count1365 b)) else (if i < 1367 then decide (2 ≤ count1365 b) else (if i < 1368 then decide (1 ≤ count1367 b) else decide (2 ≤ count1367 b)))) else (if i < 1372 then (if i < 1370 then decide (1 ≤ count1369 b) else (if i < 1371 then decide (2 ≤ count1369 b) else decide (3 ≤ count1369 b))) else (if i < 1373 then decide (4 ≤ count1369 b) else (if i < 1374 then decide (1 ≤ count1373 b) else decide (2 ≤ count1373 b)))))) else (if i < 1386 then (if i < 1380 then (if i < 1377 then (if i < 1376 then decide (3 ≤ count1373 b) else decide (4 ≤ count1373 b)) else (if i < 1378 then decide (5 ≤ count1373 b) else (if i < 1379 then decide (6 ≤ count1373 b) else decide (7 ≤ count1373 b)))) else (if i < 1383 then (if i < 1381 then decide (1 ≤ count1380 b) else (if i < 1382 then decide (2 ≤ count1380 b) else decide (1 ≤ count1382 b))) else (if i < 1384 then decide (2 ≤ count1382 b) else (if i < 1385 then decide (3 ≤ count1382 b) else decide (1 ≤ count1385 b))))) else (if i < 1392 then (if i < 1389 then (if i < 1387 then decide (2 ≤ count1385 b) else (if i < 1388 then decide (1 ≤ count1387 b) else decide (2 ≤ count1387 b))) else (if i < 1390 then decide (1 ≤ count1389 b) else (if i < 1391 then decide (2 ≤ count1389 b) else decide (3 ≤ count1389 b)))) else (if i < 1395 then (if i < 1393 then decide (4 ≤ count1389 b) else (if i < 1394 then decide (1 ≤ count1393 b) else decide (2 ≤ count1393 b))) else (if i < 1396 then decide (3 ≤ count1393 b) else (if i < 1397 then decide (4 ≤ count1393 b) else decide (5 ≤ count1393 b))))))) else (if i < 1421 then (if i < 1409 then (if i < 1403 then (if i < 1400 then (if i < 1399 then decide (6 ≤ count1393 b) else decide (7 ≤ count1393 b)) else (if i < 1401 then decide (1 ≤ count1400 b) else (if i < 1402 then decide (2 ≤ count1400 b) else decide (3 ≤ count1400 b)))) else (if i < 1406 then (if i < 1404 then decide (4 ≤ count1400 b) else (if i < 1405 then decide (5 ≤ count1400 b) else decide (6 ≤ count1400 b))) else (if i < 1407 then decide (7 ≤ count1400 b) else (if i < 1408 then decide (8 ≤ count1400 b) else decide (9 ≤ count1400 b))))) else (if i < 1415 then (if i < 1412 then (if i < 1410 then decide (10 ≤ count1400 b) else (if i < 1411 then decide (11 ≤ count1400 b) else decide (12 ≤ count1400 b))) else (if i < 1413 then decide (13 ≤ count1400 b) else (if i < 1414 then decide (14 ≤ count1400 b) else decide (1 ≤ count1414 b)))) else (if i < 1418 then (if i < 1416 then decide (2 ≤ count1414 b) else (if i < 1417 then decide (3 ≤ count1414 b) else decide (4 ≤ count1414 b))) else (if i < 1419 then decide (5 ≤ count1414 b) else (if i < 1420 then decide (6 ≤ count1414 b) else decide (7 ≤ count1414 b)))))) else (if i < 1432 then (if i < 1426 then (if i < 1423 then (if i < 1422 then decide (8 ≤ count1414 b) else decide (9 ≤ count1414 b)) else (if i < 1424 then decide (10 ≤ count1414 b) else (if i < 1425 then decide (11 ≤ count1414 b) else decide (12 ≤ count1414 b)))) else (if i < 1429 then (if i < 1427 then decide (13 ≤ count1414 b) else (if i < 1428 then decide (14 ≤ count1414 b) else decide (15 ≤ count1414 b))) else (if i < 1430 then decide (1 ≤ count1429 b) else (if i < 1431 then decide (2 ≤ count1429 b) else decide (3 ≤ count1429 b))))) else (if i < 1438 then (if i < 1435 then (if i < 1433 then decide (4 ≤ count1429 b) else (if i < 1434 then decide (5 ≤ count1429 b) else decide (6 ≤ count1429 b))) else (if i < 1436 then decide (7 ≤ count1429 b) else (if i < 1437 then decide (8 ≤ count1429 b) else decide (9 ≤ count1429 b)))) else (if i < 1441 then (if i < 1439 then decide (10 ≤ count1429 b) else (if i < 1440 then decide (11 ≤ count1429 b) else decide (12 ≤ count1429 b))) else (if i < 1442 then decide (13 ≤ count1429 b) else (if i < 1443 then decide (14 ≤ count1429 b) else decide (15 ≤ count1429 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (37 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (48 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (49 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (53 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (55 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (56 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (62 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (97 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (98 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (99 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (103 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (122 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (124 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (126 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (127 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (151 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (158 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (176 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (180 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (182 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (186 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (190 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (193 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (194 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (195 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (199 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (205 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (207 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (214 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (218 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (220 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (222 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (223 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (261 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (273 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (277 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (279 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (280 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (342 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (346 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (375 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (421 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (422 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (425 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (426 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (430 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (432 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (433 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (437 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (439 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (440 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (441 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (446 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (447 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (37 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (56 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (97 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (103 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (158 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (223 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (375 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (441 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (446 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value402 (q : Snake 81) : valuation q 402 = decide (2 ≤ count401 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value408 (q : Snake 81) : valuation q 408 = decide (2 ≤ count407 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value1190 (q : Snake 81) : valuation q 1190 = decide (1 ≤ count1190 (baseVal q)) := rfl
theorem value1193 (q : Snake 81) : valuation q 1193 = decide (1 ≤ count1193 (baseVal q)) := rfl
theorem value1195 (q : Snake 81) : valuation q 1195 = decide (1 ≤ count1195 (baseVal q)) := rfl
theorem value1198 (q : Snake 81) : valuation q 1198 = decide (1 ≤ count1198 (baseVal q)) := rfl
theorem value1204 (q : Snake 81) : valuation q 1204 = decide (1 ≤ count1204 (baseVal q)) := rfl
theorem value1205 (q : Snake 81) : valuation q 1205 = decide (2 ≤ count1204 (baseVal q)) := rfl
theorem value1206 (q : Snake 81) : valuation q 1206 = decide (1 ≤ count1206 (baseVal q)) := rfl
theorem value1207 (q : Snake 81) : valuation q 1207 = decide (2 ≤ count1206 (baseVal q)) := rfl
theorem value1209 (q : Snake 81) : valuation q 1209 = decide (1 ≤ count1209 (baseVal q)) := rfl
theorem value1213 (q : Snake 81) : valuation q 1213 = decide (1 ≤ count1213 (baseVal q)) := rfl
theorem value1217 (q : Snake 81) : valuation q 1217 = decide (1 ≤ count1217 (baseVal q)) := rfl
theorem value1218 (q : Snake 81) : valuation q 1218 = decide (2 ≤ count1217 (baseVal q)) := rfl
theorem value1225 (q : Snake 81) : valuation q 1225 = decide (2 ≤ count1224 (baseVal q)) := rfl
theorem value1226 (q : Snake 81) : valuation q 1226 = decide (3 ≤ count1224 (baseVal q)) := rfl
theorem value1237 (q : Snake 81) : valuation q 1237 = decide (1 ≤ count1237 (baseVal q)) := rfl
theorem value1239 (q : Snake 81) : valuation q 1239 = decide (1 ≤ count1239 (baseVal q)) := rfl
theorem value1244 (q : Snake 81) : valuation q 1244 = decide (1 ≤ count1244 (baseVal q)) := rfl
theorem value1246 (q : Snake 81) : valuation q 1246 = decide (1 ≤ count1246 (baseVal q)) := rfl
theorem value1251 (q : Snake 81) : valuation q 1251 = decide (2 ≤ count1250 (baseVal q)) := rfl
theorem value1257 (q : Snake 81) : valuation q 1257 = decide (1 ≤ count1257 (baseVal q)) := rfl
theorem value1259 (q : Snake 81) : valuation q 1259 = decide (1 ≤ count1259 (baseVal q)) := rfl
theorem value1260 (q : Snake 81) : valuation q 1260 = decide (2 ≤ count1259 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (1 ≤ count1262 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (2 ≤ count1262 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (1 ≤ count1264 (baseVal q)) := rfl
theorem value1267 (q : Snake 81) : valuation q 1267 = decide (2 ≤ count1266 (baseVal q)) := rfl
theorem value1271 (q : Snake 81) : valuation q 1271 = decide (2 ≤ count1270 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (3 ≤ count1270 (baseVal q)) := rfl
theorem value1273 (q : Snake 81) : valuation q 1273 = decide (4 ≤ count1270 (baseVal q)) := rfl
theorem value1280 (q : Snake 81) : valuation q 1280 = decide (4 ≤ count1277 (baseVal q)) := rfl
theorem value1281 (q : Snake 81) : valuation q 1281 = decide (5 ≤ count1277 (baseVal q)) := rfl
theorem value1282 (q : Snake 81) : valuation q 1282 = decide (6 ≤ count1277 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (6 ≤ count1291 (baseVal q)) := rfl
theorem value1297 (q : Snake 81) : valuation q 1297 = decide (7 ≤ count1291 (baseVal q)) := rfl
theorem value1298 (q : Snake 81) : valuation q 1298 = decide (8 ≤ count1291 (baseVal q)) := rfl
theorem value1306 (q : Snake 81) : valuation q 1306 = decide (1 ≤ count1306 (baseVal q)) := rfl
theorem value1308 (q : Snake 81) : valuation q 1308 = decide (1 ≤ count1308 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (2 ≤ count1308 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (1 ≤ count1311 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (1 ≤ count1313 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (1 ≤ count1315 (baseVal q)) := rfl
theorem value1316 (q : Snake 81) : valuation q 1316 = decide (2 ≤ count1315 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (1 ≤ count1319 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (2 ≤ count1319 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (3 ≤ count1319 (baseVal q)) := rfl
theorem value1326 (q : Snake 81) : valuation q 1326 = decide (1 ≤ count1326 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (1 ≤ count1328 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (1 ≤ count1331 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (2 ≤ count1331 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (1 ≤ count1333 (baseVal q)) := rfl
theorem value1336 (q : Snake 81) : valuation q 1336 = decide (2 ≤ count1335 (baseVal q)) := rfl
theorem value1337 (q : Snake 81) : valuation q 1337 = decide (3 ≤ count1335 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (2 ≤ count1339 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (3 ≤ count1339 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (4 ≤ count1346 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (5 ≤ count1346 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (1 ≤ count1362 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (1 ≤ count1365 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (1 ≤ count1367 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (1 ≤ count1369 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (2 ≤ count1369 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (2 ≤ count1373 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (3 ≤ count1373 (baseVal q)) := rfl
theorem value1380 (q : Snake 81) : valuation q 1380 = decide (1 ≤ count1380 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (1 ≤ count1382 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (1 ≤ count1385 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (2 ≤ count1385 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (1 ≤ count1387 (baseVal q)) := rfl
theorem value1388 (q : Snake 81) : valuation q 1388 = decide (2 ≤ count1387 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (1 ≤ count1389 (baseVal q)) := rfl
theorem value1390 (q : Snake 81) : valuation q 1390 = decide (2 ≤ count1389 (baseVal q)) := rfl
theorem value1391 (q : Snake 81) : valuation q 1391 = decide (3 ≤ count1389 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (1 ≤ count1393 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (2 ≤ count1393 (baseVal q)) := rfl
theorem value1395 (q : Snake 81) : valuation q 1395 = decide (3 ≤ count1393 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (3 ≤ count1400 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (4 ≤ count1400 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (5 ≤ count1400 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (7 ≤ count1414 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (8 ≤ count1414 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (9 ≤ count1414 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (15 ≤ count1429 (baseVal q)) := rfl
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
theorem meaningNeg92 (b : Nat → Bool) : literal (valuationOf b) (-92) = decide (1 ≤ countLit b [-92]) := by
  change literal b (-92) = decide (1 ≤ countLit b [-92])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-92) <;> decide
theorem meaningNeg91 (b : Nat → Bool) : literal (valuationOf b) (-91) = decide (1 ≤ countLit b [-91]) := by
  change literal b (-91) = decide (1 ≤ countLit b [-91])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-91) <;> decide
theorem meaningNeg87 (b : Nat → Bool) : literal (valuationOf b) (-87) = decide (1 ≤ countLit b [-87]) := by
  change literal b (-87) = decide (1 ≤ countLit b [-87])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-87) <;> decide
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
theorem meaningNeg73 (b : Nat → Bool) : literal (valuationOf b) (-73) = decide (1 ≤ countLit b [-73]) := by
  change literal b (-73) = decide (1 ≤ countLit b [-73])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-73) <;> decide
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
theorem meaningNeg64 (b : Nat → Bool) : literal (valuationOf b) (-64) = decide (1 ≤ countLit b [-64]) := by
  change literal b (-64) = decide (1 ≤ countLit b [-64])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-64) <;> decide
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
theorem meaningNeg31 (b : Nat → Bool) : literal (valuationOf b) (-31) = decide (1 ≤ countLit b [-31]) := by
  change literal b (-31) = decide (1 ≤ countLit b [-31])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-31) <;> decide
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
theorem meaningNeg10 (b : Nat → Bool) : literal (valuationOf b) (-10) = decide (1 ≤ countLit b [-10]) := by
  change literal b (-10) = decide (1 ≤ countLit b [-10])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-10) <;> decide
theorem meaningNeg3 (b : Nat → Bool) : literal (valuationOf b) (-3) = decide (1 ≤ countLit b [-3]) := by
  change literal b (-3) = decide (1 ≤ countLit b [-3])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-3) <;> decide
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
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning402 (b : Nat → Bool) : literal (valuationOf b) 402 = decide (2 ≤ count401 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning408 (b : Nat → Bool) : literal (valuationOf b) 408 = decide (2 ≤ count407 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning1190 (b : Nat → Bool) : literal (valuationOf b) 1190 = decide (1 ≤ count1190 b) := rfl
theorem meaning1193 (b : Nat → Bool) : literal (valuationOf b) 1193 = decide (1 ≤ count1193 b) := rfl
theorem meaning1195 (b : Nat → Bool) : literal (valuationOf b) 1195 = decide (1 ≤ count1195 b) := rfl
theorem meaning1198 (b : Nat → Bool) : literal (valuationOf b) 1198 = decide (1 ≤ count1198 b) := rfl
theorem meaning1204 (b : Nat → Bool) : literal (valuationOf b) 1204 = decide (1 ≤ count1204 b) := rfl
theorem meaning1205 (b : Nat → Bool) : literal (valuationOf b) 1205 = decide (2 ≤ count1204 b) := rfl
theorem meaning1206 (b : Nat → Bool) : literal (valuationOf b) 1206 = decide (1 ≤ count1206 b) := rfl
theorem meaning1207 (b : Nat → Bool) : literal (valuationOf b) 1207 = decide (2 ≤ count1206 b) := rfl
theorem meaning1209 (b : Nat → Bool) : literal (valuationOf b) 1209 = decide (1 ≤ count1209 b) := rfl
theorem meaning1213 (b : Nat → Bool) : literal (valuationOf b) 1213 = decide (1 ≤ count1213 b) := rfl
theorem meaning1217 (b : Nat → Bool) : literal (valuationOf b) 1217 = decide (1 ≤ count1217 b) := rfl
theorem meaning1218 (b : Nat → Bool) : literal (valuationOf b) 1218 = decide (2 ≤ count1217 b) := rfl
theorem meaning1225 (b : Nat → Bool) : literal (valuationOf b) 1225 = decide (2 ≤ count1224 b) := rfl
theorem meaning1226 (b : Nat → Bool) : literal (valuationOf b) 1226 = decide (3 ≤ count1224 b) := rfl
theorem meaning1237 (b : Nat → Bool) : literal (valuationOf b) 1237 = decide (1 ≤ count1237 b) := rfl
theorem meaning1239 (b : Nat → Bool) : literal (valuationOf b) 1239 = decide (1 ≤ count1239 b) := rfl
theorem meaning1244 (b : Nat → Bool) : literal (valuationOf b) 1244 = decide (1 ≤ count1244 b) := rfl
theorem meaning1246 (b : Nat → Bool) : literal (valuationOf b) 1246 = decide (1 ≤ count1246 b) := rfl
theorem meaning1251 (b : Nat → Bool) : literal (valuationOf b) 1251 = decide (2 ≤ count1250 b) := rfl
theorem meaning1257 (b : Nat → Bool) : literal (valuationOf b) 1257 = decide (1 ≤ count1257 b) := rfl
theorem meaning1259 (b : Nat → Bool) : literal (valuationOf b) 1259 = decide (1 ≤ count1259 b) := rfl
theorem meaning1260 (b : Nat → Bool) : literal (valuationOf b) 1260 = decide (2 ≤ count1259 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (1 ≤ count1262 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (2 ≤ count1262 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (1 ≤ count1264 b) := rfl
theorem meaning1267 (b : Nat → Bool) : literal (valuationOf b) 1267 = decide (2 ≤ count1266 b) := rfl
theorem meaning1271 (b : Nat → Bool) : literal (valuationOf b) 1271 = decide (2 ≤ count1270 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (3 ≤ count1270 b) := rfl
theorem meaning1273 (b : Nat → Bool) : literal (valuationOf b) 1273 = decide (4 ≤ count1270 b) := rfl
theorem meaning1280 (b : Nat → Bool) : literal (valuationOf b) 1280 = decide (4 ≤ count1277 b) := rfl
theorem meaning1281 (b : Nat → Bool) : literal (valuationOf b) 1281 = decide (5 ≤ count1277 b) := rfl
theorem meaning1282 (b : Nat → Bool) : literal (valuationOf b) 1282 = decide (6 ≤ count1277 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (6 ≤ count1291 b) := rfl
theorem meaning1297 (b : Nat → Bool) : literal (valuationOf b) 1297 = decide (7 ≤ count1291 b) := rfl
theorem meaning1298 (b : Nat → Bool) : literal (valuationOf b) 1298 = decide (8 ≤ count1291 b) := rfl
theorem meaning1306 (b : Nat → Bool) : literal (valuationOf b) 1306 = decide (1 ≤ count1306 b) := rfl
theorem meaning1308 (b : Nat → Bool) : literal (valuationOf b) 1308 = decide (1 ≤ count1308 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (2 ≤ count1308 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (1 ≤ count1311 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (1 ≤ count1313 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (1 ≤ count1315 b) := rfl
theorem meaning1316 (b : Nat → Bool) : literal (valuationOf b) 1316 = decide (2 ≤ count1315 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (1 ≤ count1319 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (2 ≤ count1319 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (3 ≤ count1319 b) := rfl
theorem meaning1326 (b : Nat → Bool) : literal (valuationOf b) 1326 = decide (1 ≤ count1326 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (1 ≤ count1328 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (1 ≤ count1331 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (2 ≤ count1331 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (1 ≤ count1333 b) := rfl
theorem meaning1336 (b : Nat → Bool) : literal (valuationOf b) 1336 = decide (2 ≤ count1335 b) := rfl
theorem meaning1337 (b : Nat → Bool) : literal (valuationOf b) 1337 = decide (3 ≤ count1335 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (2 ≤ count1339 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (3 ≤ count1339 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (4 ≤ count1346 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (5 ≤ count1346 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (1 ≤ count1362 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (1 ≤ count1365 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (1 ≤ count1367 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (1 ≤ count1369 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (2 ≤ count1369 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (2 ≤ count1373 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (3 ≤ count1373 b) := rfl
theorem meaning1380 (b : Nat → Bool) : literal (valuationOf b) 1380 = decide (1 ≤ count1380 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (1 ≤ count1382 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (1 ≤ count1385 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (2 ≤ count1385 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (1 ≤ count1387 b) := rfl
theorem meaning1388 (b : Nat → Bool) : literal (valuationOf b) 1388 = decide (2 ≤ count1387 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (1 ≤ count1389 b) := rfl
theorem meaning1390 (b : Nat → Bool) : literal (valuationOf b) 1390 = decide (2 ≤ count1389 b) := rfl
theorem meaning1391 (b : Nat → Bool) : literal (valuationOf b) 1391 = decide (3 ≤ count1389 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (1 ≤ count1393 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (2 ≤ count1393 b) := rfl
theorem meaning1395 (b : Nat → Bool) : literal (valuationOf b) 1395 = decide (3 ≤ count1393 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (3 ≤ count1400 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (4 ≤ count1400 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (5 ≤ count1400 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (7 ≤ count1414 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (8 ≤ count1414 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (9 ≤ count1414 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (15 ≤ count1429 b) := rfl
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
end Snake9.Regrowth.E112242
