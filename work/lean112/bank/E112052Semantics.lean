import E112052Data
namespace Snake9.Regrowth.E112052
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 127 then (if i < 63 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (55 : Vertex)) else decide (InPath q (66 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (76 : Vertex)) else decide (InPath q (80 : Vertex))) else (if i < 6 then decide (InPath q (82 : Vertex)) else decide (InPath q (83 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (87 : Vertex)) else decide (InPath q (88 : Vertex))) else (if i < 10 then decide (InPath q (92 : Vertex)) else decide (InPath q (94 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (103 : Vertex)) else decide (InPath q (118 : Vertex))) else (if i < 14 then decide (InPath q (119 : Vertex)) else decide (InPath q (130 : Vertex)))))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then decide (InPath q (131 : Vertex)) else decide (InPath q (132 : Vertex))) else (if i < 18 then decide (InPath q (133 : Vertex)) else decide (InPath q (137 : Vertex)))) else (if i < 21 then (if i < 20 then decide (InPath q (139 : Vertex)) else decide (InPath q (140 : Vertex))) else (if i < 22 then decide (InPath q (141 : Vertex)) else decide (InPath q (142 : Vertex))))) else (if i < 27 then (if i < 25 then (if i < 24 then decide (InPath q (144 : Vertex)) else decide (InPath q (145 : Vertex))) else (if i < 26 then decide (InPath q (146 : Vertex)) else decide (InPath q (147 : Vertex)))) else (if i < 29 then (if i < 28 then decide (InPath q (151 : Vertex)) else decide (InPath q (152 : Vertex))) else (if i < 30 then decide (InPath q (156 : Vertex)) else decide (InPath q (158 : Vertex))))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then decide (InPath q (159 : Vertex)) else decide (InPath q (192 : Vertex))) else (if i < 34 then decide (InPath q (194 : Vertex)) else decide (InPath q (198 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (199 : Vertex)) else decide (InPath q (200 : Vertex))) else (if i < 38 then decide (InPath q (202 : Vertex)) else decide (InPath q (204 : Vertex))))) else (if i < 43 then (if i < 41 then (if i < 40 then decide (InPath q (206 : Vertex)) else decide (InPath q (209 : Vertex))) else (if i < 42 then decide (InPath q (212 : Vertex)) else decide (InPath q (213 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (214 : Vertex)) else decide (InPath q (215 : Vertex))) else (if i < 46 then decide (InPath q (217 : Vertex)) else decide (InPath q (218 : Vertex)))))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then decide (InPath q (219 : Vertex)) else decide (InPath q (221 : Vertex))) else (if i < 50 then decide (InPath q (257 : Vertex)) else decide (InPath q (258 : Vertex)))) else (if i < 53 then (if i < 52 then decide (InPath q (259 : Vertex)) else decide (InPath q (260 : Vertex))) else (if i < 54 then decide (InPath q (261 : Vertex)) else decide (InPath q (265 : Vertex))))) else (if i < 59 then (if i < 57 then (if i < 56 then decide (InPath q (267 : Vertex)) else decide (InPath q (268 : Vertex))) else (if i < 58 then decide (InPath q (269 : Vertex)) else decide (InPath q (270 : Vertex)))) else (if i < 61 then (if i < 60 then decide (InPath q (272 : Vertex)) else decide (InPath q (274 : Vertex))) else (if i < 62 then decide (InPath q (275 : Vertex)) else decide (InPath q (279 : Vertex)))))))) else (if i < 95 then (if i < 79 then (if i < 71 then (if i < 67 then (if i < 65 then (if i < 64 then decide (InPath q (280 : Vertex)) else decide (InPath q (284 : Vertex))) else (if i < 66 then decide (InPath q (286 : Vertex)) else decide (InPath q (287 : Vertex)))) else (if i < 69 then (if i < 68 then decide (InPath q (322 : Vertex)) else decide (InPath q (324 : Vertex))) else (if i < 70 then decide (InPath q (325 : Vertex)) else decide (InPath q (326 : Vertex))))) else (if i < 75 then (if i < 73 then (if i < 72 then decide (InPath q (327 : Vertex)) else decide (InPath q (328 : Vertex))) else (if i < 74 then decide (InPath q (330 : Vertex)) else decide (InPath q (332 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (337 : Vertex)) else decide (InPath q (340 : Vertex))) else (if i < 78 then decide (InPath q (341 : Vertex)) else decide (InPath q (342 : Vertex)))))) else (if i < 87 then (if i < 83 then (if i < 81 then (if i < 80 then decide (InPath q (343 : Vertex)) else decide (InPath q (344 : Vertex))) else (if i < 82 then decide (InPath q (345 : Vertex)) else decide (InPath q (346 : Vertex)))) else (if i < 85 then (if i < 84 then decide (InPath q (347 : Vertex)) else decide (InPath q (351 : Vertex))) else (if i < 86 then decide (InPath q (384 : Vertex)) else decide (InPath q (386 : Vertex))))) else (if i < 91 then (if i < 89 then (if i < 88 then decide (InPath q (388 : Vertex)) else decide (InPath q (389 : Vertex))) else (if i < 90 then decide (InPath q (390 : Vertex)) else decide (InPath q (391 : Vertex)))) else (if i < 93 then (if i < 92 then decide (InPath q (392 : Vertex)) else decide (InPath q (393 : Vertex))) else (if i < 94 then decide (InPath q (394 : Vertex)) else decide (InPath q (395 : Vertex))))))) else (if i < 111 then (if i < 103 then (if i < 99 then (if i < 97 then (if i < 96 then decide (InPath q (397 : Vertex)) else decide (InPath q (398 : Vertex))) else (if i < 98 then decide (InPath q (401 : Vertex)) else decide (InPath q (404 : Vertex)))) else (if i < 101 then (if i < 100 then decide (InPath q (405 : Vertex)) else decide (InPath q (406 : Vertex))) else (if i < 102 then decide (InPath q (407 : Vertex)) else decide (InPath q (409 : Vertex))))) else (if i < 107 then (if i < 105 then (if i < 104 then decide (InPath q (410 : Vertex)) else decide (InPath q (411 : Vertex))) else (if i < 106 then decide (InPath q (413 : Vertex)) else decide (InPath q (414 : Vertex)))) else (if i < 109 then (if i < 108 then decide (InPath q (415 : Vertex)) else decide (InPath q (448 : Vertex))) else (if i < 110 then decide (InPath q (449 : Vertex)) else decide (InPath q (451 : Vertex)))))) else (if i < 119 then (if i < 115 then (if i < 113 then (if i < 112 then decide (InPath q (452 : Vertex)) else decide (InPath q (453 : Vertex))) else (if i < 114 then decide (InPath q (455 : Vertex)) else decide (InPath q (457 : Vertex)))) else (if i < 117 then (if i < 116 then decide (InPath q (459 : Vertex)) else decide (InPath q (461 : Vertex))) else (if i < 118 then decide (InPath q (462 : Vertex)) else decide (InPath q (463 : Vertex))))) else (if i < 123 then (if i < 121 then (if i < 120 then decide (InPath q (464 : Vertex)) else decide (InPath q (466 : Vertex))) else (if i < 122 then decide (InPath q (467 : Vertex)) else decide (InPath q (471 : Vertex)))) else (if i < 125 then (if i < 124 then decide (InPath q (472 : Vertex)) else decide (InPath q (474 : Vertex))) else (if i < 126 then decide (InPath q (476 : Vertex)) else decide (InPath q (477 : Vertex))))))))) else (if i < 191 then (if i < 159 then (if i < 143 then (if i < 135 then (if i < 131 then (if i < 129 then (if i < 128 then decide (InPath q (478 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (66 : Vertex)) else decide (BallClauseLogic.Endpoint q (76 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else decide (BallClauseLogic.Endpoint q (82 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (83 : Vertex)) else decide (BallClauseLogic.Endpoint q (87 : Vertex))))) else (if i < 139 then (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (88 : Vertex)) else decide (BallClauseLogic.Endpoint q (92 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (94 : Vertex)) else decide (BallClauseLogic.Endpoint q (103 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (118 : Vertex)) else decide (BallClauseLogic.Endpoint q (119 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (130 : Vertex)) else decide (BallClauseLogic.Endpoint q (131 : Vertex)))))) else (if i < 151 then (if i < 147 then (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else decide (BallClauseLogic.Endpoint q (133 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex)))) else (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else decide (BallClauseLogic.Endpoint q (141 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else decide (BallClauseLogic.Endpoint q (144 : Vertex))))) else (if i < 155 then (if i < 153 then (if i < 152 then decide (BallClauseLogic.Endpoint q (145 : Vertex)) else decide (BallClauseLogic.Endpoint q (146 : Vertex))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (147 : Vertex)) else decide (BallClauseLogic.Endpoint q (151 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (152 : Vertex)) else decide (BallClauseLogic.Endpoint q (156 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (158 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex))))))) else (if i < 175 then (if i < 167 then (if i < 163 then (if i < 161 then (if i < 160 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else decide (BallClauseLogic.Endpoint q (194 : Vertex))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else decide (BallClauseLogic.Endpoint q (199 : Vertex)))) else (if i < 165 then (if i < 164 then decide (BallClauseLogic.Endpoint q (200 : Vertex)) else decide (BallClauseLogic.Endpoint q (202 : Vertex))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (204 : Vertex)) else decide (BallClauseLogic.Endpoint q (206 : Vertex))))) else (if i < 171 then (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else decide (BallClauseLogic.Endpoint q (212 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (213 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex)))) else (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (215 : Vertex)) else decide (BallClauseLogic.Endpoint q (217 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (219 : Vertex)))))) else (if i < 183 then (if i < 179 then (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else decide (BallClauseLogic.Endpoint q (257 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else decide (BallClauseLogic.Endpoint q (259 : Vertex)))) else (if i < 181 then (if i < 180 then decide (BallClauseLogic.Endpoint q (260 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex))) else (if i < 182 then decide (BallClauseLogic.Endpoint q (265 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex))))) else (if i < 187 then (if i < 185 then (if i < 184 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else decide (BallClauseLogic.Endpoint q (269 : Vertex))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (270 : Vertex)) else decide (BallClauseLogic.Endpoint q (272 : Vertex)))) else (if i < 189 then (if i < 188 then decide (BallClauseLogic.Endpoint q (274 : Vertex)) else decide (BallClauseLogic.Endpoint q (275 : Vertex))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else decide (BallClauseLogic.Endpoint q (280 : Vertex)))))))) else (if i < 223 then (if i < 207 then (if i < 199 then (if i < 195 then (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (284 : Vertex)) else decide (BallClauseLogic.Endpoint q (286 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (322 : Vertex)))) else (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (324 : Vertex)) else decide (BallClauseLogic.Endpoint q (325 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (326 : Vertex)) else decide (BallClauseLogic.Endpoint q (327 : Vertex))))) else (if i < 203 then (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (328 : Vertex)) else decide (BallClauseLogic.Endpoint q (330 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (332 : Vertex)) else decide (BallClauseLogic.Endpoint q (337 : Vertex)))) else (if i < 205 then (if i < 204 then decide (BallClauseLogic.Endpoint q (340 : Vertex)) else decide (BallClauseLogic.Endpoint q (341 : Vertex))) else (if i < 206 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (343 : Vertex)))))) else (if i < 215 then (if i < 211 then (if i < 209 then (if i < 208 then decide (BallClauseLogic.Endpoint q (344 : Vertex)) else decide (BallClauseLogic.Endpoint q (345 : Vertex))) else (if i < 210 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else decide (BallClauseLogic.Endpoint q (347 : Vertex)))) else (if i < 213 then (if i < 212 then decide (BallClauseLogic.Endpoint q (351 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 214 then decide (BallClauseLogic.Endpoint q (386 : Vertex)) else decide (BallClauseLogic.Endpoint q (388 : Vertex))))) else (if i < 219 then (if i < 217 then (if i < 216 then decide (BallClauseLogic.Endpoint q (389 : Vertex)) else decide (BallClauseLogic.Endpoint q (390 : Vertex))) else (if i < 218 then decide (BallClauseLogic.Endpoint q (391 : Vertex)) else decide (BallClauseLogic.Endpoint q (392 : Vertex)))) else (if i < 221 then (if i < 220 then decide (BallClauseLogic.Endpoint q (393 : Vertex)) else decide (BallClauseLogic.Endpoint q (394 : Vertex))) else (if i < 222 then decide (BallClauseLogic.Endpoint q (395 : Vertex)) else decide (BallClauseLogic.Endpoint q (397 : Vertex))))))) else (if i < 239 then (if i < 231 then (if i < 227 then (if i < 225 then (if i < 224 then decide (BallClauseLogic.Endpoint q (398 : Vertex)) else decide (BallClauseLogic.Endpoint q (401 : Vertex))) else (if i < 226 then decide (BallClauseLogic.Endpoint q (404 : Vertex)) else decide (BallClauseLogic.Endpoint q (405 : Vertex)))) else (if i < 229 then (if i < 228 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else decide (BallClauseLogic.Endpoint q (407 : Vertex))) else (if i < 230 then decide (BallClauseLogic.Endpoint q (409 : Vertex)) else decide (BallClauseLogic.Endpoint q (410 : Vertex))))) else (if i < 235 then (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (411 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (414 : Vertex)) else decide (BallClauseLogic.Endpoint q (415 : Vertex)))) else (if i < 237 then (if i < 236 then decide (BallClauseLogic.Endpoint q (448 : Vertex)) else decide (BallClauseLogic.Endpoint q (449 : Vertex))) else (if i < 238 then decide (BallClauseLogic.Endpoint q (451 : Vertex)) else decide (BallClauseLogic.Endpoint q (452 : Vertex)))))) else (if i < 247 then (if i < 243 then (if i < 241 then (if i < 240 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else decide (BallClauseLogic.Endpoint q (455 : Vertex))) else (if i < 242 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else decide (BallClauseLogic.Endpoint q (459 : Vertex)))) else (if i < 245 then (if i < 244 then decide (BallClauseLogic.Endpoint q (461 : Vertex)) else decide (BallClauseLogic.Endpoint q (462 : Vertex))) else (if i < 246 then decide (BallClauseLogic.Endpoint q (463 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))))) else (if i < 251 then (if i < 249 then (if i < 248 then decide (BallClauseLogic.Endpoint q (466 : Vertex)) else decide (BallClauseLogic.Endpoint q (467 : Vertex))) else (if i < 250 then decide (BallClauseLogic.Endpoint q (471 : Vertex)) else decide (BallClauseLogic.Endpoint q (472 : Vertex)))) else (if i < 253 then (if i < 252 then decide (BallClauseLogic.Endpoint q (474 : Vertex)) else decide (BallClauseLogic.Endpoint q (476 : Vertex))) else (if i < 254 then decide (BallClauseLogic.Endpoint q (477 : Vertex)) else decide (BallClauseLogic.Endpoint q (478 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count255 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [129, 130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count271 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count277 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]
def count283 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149, 150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count299 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count305 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count307 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171, 172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]
def count345 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count349 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179]
def count351 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183]
def count359 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count363 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count367 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count377 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count379 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [192, 193, 194]
def count383 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198]
def count391 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202]
def count397 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count401 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202, 203, 204, 205, 206]
def count405 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]
def count407 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count409 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count411 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210]
def count413 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count417 (b : Nat → Bool) : Nat := countLit b [211, 212, 213, 214]
def count419 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210, 211, 212, 213, 214]
def count421 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count425 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count429 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count431 (b : Nat → Bool) : Nat := countLit b [219, 220, 221, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218, 219, 220, 221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count437 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count439 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count441 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count443 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226]
def count445 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [227, 228, 229, 230]
def count451 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229, 230]
def count453 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count463 (b : Nat → Bool) : Nat := countLit b [235, 236, 237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234, 235, 236, 237, 238]
def count467 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]
def count469 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count471 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count473 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242]
def count475 (b : Nat → Bool) : Nat := countLit b [243, 244]
def count477 (b : Nat → Bool) : Nat := countLit b [245, 246]
def count479 (b : Nat → Bool) : Nat := countLit b [243, 244, 245, 246]
def count481 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242, 243, 244, 245, 246]
def count483 (b : Nat → Bool) : Nat := countLit b [247, 248]
def count485 (b : Nat → Bool) : Nat := countLit b [249, 250]
def count487 (b : Nat → Bool) : Nat := countLit b [247, 248, 249, 250]
def count489 (b : Nat → Bool) : Nat := countLit b [251, 252]
def count491 (b : Nat → Bool) : Nat := countLit b [253, 254]
def count493 (b : Nat → Bool) : Nat := countLit b [251, 252, 253, 254]
def count495 (b : Nat → Bool) : Nat := countLit b [247, 248, 249, 250, 251, 252, 253, 254]
def count497 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]
def count499 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]
def count501 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]
def count503 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]
def count505 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count507 (b : Nat → Bool) : Nat := countLit b [2, 4, 6]
def count510 (b : Nat → Bool) : Nat := countLit b [9, 13]
def count512 (b : Nat → Bool) : Nat := countLit b [14, 16]
def count514 (b : Nat → Bool) : Nat := countLit b [9, 13, 14, 16]
def count518 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 9, 13, 14, 16]
def count525 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count527 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count529 (b : Nat → Bool) : Nat := countLit b [19, 21, 22, 23]
def count533 (b : Nat → Bool) : Nat := countLit b [26, 29]
def count535 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count537 (b : Nat → Bool) : Nat := countLit b [26, 29, 31, 32]
def count541 (b : Nat → Bool) : Nat := countLit b [19, 21, 22, 23, 26, 29, 31, 32]
def count549 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 9, 13, 14, 16, 19, 21, 22, 23, 26, 29, 31, 32]
def count564 (b : Nat → Bool) : Nat := countLit b [34, 37]
def count566 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count568 (b : Nat → Bool) : Nat := countLit b [34, 37, 38, 40]
def count572 (b : Nat → Bool) : Nat := countLit b [41, 44]
def count574 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count576 (b : Nat → Bool) : Nat := countLit b [41, 44, 47, 48]
def count580 (b : Nat → Bool) : Nat := countLit b [34, 37, 38, 40, 41, 44, 47, 48]
def count588 (b : Nat → Bool) : Nat := countLit b [49, 50]
def count590 (b : Nat → Bool) : Nat := countLit b [52, 55]
def count592 (b : Nat → Bool) : Nat := countLit b [49, 50, 52, 55]
def count596 (b : Nat → Bool) : Nat := countLit b [57, 58]
def count598 (b : Nat → Bool) : Nat := countLit b [59, 61]
def count600 (b : Nat → Bool) : Nat := countLit b [57, 58, 59, 61]
def count604 (b : Nat → Bool) : Nat := countLit b [49, 50, 52, 55, 57, 58, 59, 61]
def count612 (b : Nat → Bool) : Nat := countLit b [34, 37, 38, 40, 41, 44, 47, 48, 49, 50, 52, 55, 57, 58, 59, 61]
def count628 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 9, 13, 14, 16, 19, 21, 22, 23, 26, 29, 31, 32, 34, 37, 38, 40, 41, 44, 47, 48, 49, 50, 52, 55, 57, 58, 59, 61]
def count659 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count661 (b : Nat → Bool) : Nat := countLit b [69, 70]
def count663 (b : Nat → Bool) : Nat := countLit b [64, 66, 69, 70]
def count667 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count669 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count671 (b : Nat → Bool) : Nat := countLit b [73, 74, 75, 76]
def count675 (b : Nat → Bool) : Nat := countLit b [64, 66, 69, 70, 73, 74, 75, 76]
def count683 (b : Nat → Bool) : Nat := countLit b [79, 80]
def count685 (b : Nat → Bool) : Nat := countLit b [83, 85]
def count687 (b : Nat → Bool) : Nat := countLit b [79, 80, 83, 85]
def count691 (b : Nat → Bool) : Nat := countLit b [88, 89]
def count693 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count695 (b : Nat → Bool) : Nat := countLit b [88, 89, 92, 93]
def count699 (b : Nat → Bool) : Nat := countLit b [79, 80, 83, 85, 88, 89, 92, 93]
def count707 (b : Nat → Bool) : Nat := countLit b [64, 66, 69, 70, 73, 74, 75, 76, 79, 80, 83, 85, 88, 89, 92, 93]
def count723 (b : Nat → Bool) : Nat := countLit b [97, 98]
def count725 (b : Nat → Bool) : Nat := countLit b [101, 104]
def count727 (b : Nat → Bool) : Nat := countLit b [97, 98, 101, 104]
def count731 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count733 (b : Nat → Bool) : Nat := countLit b [109, 111]
def count735 (b : Nat → Bool) : Nat := countLit b [105, 106, 109, 111]
def count739 (b : Nat → Bool) : Nat := countLit b [97, 98, 101, 104, 105, 106, 109, 111]
def count747 (b : Nat → Bool) : Nat := countLit b [113, 115]
def count749 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count751 (b : Nat → Bool) : Nat := countLit b [113, 115, 116, 117]
def count755 (b : Nat → Bool) : Nat := countLit b [119, 121]
def count757 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count759 (b : Nat → Bool) : Nat := countLit b [119, 121, 124, 125]
def count763 (b : Nat → Bool) : Nat := countLit b [113, 115, 116, 117, 119, 121, 124, 125]
def count771 (b : Nat → Bool) : Nat := countLit b [97, 98, 101, 104, 105, 106, 109, 111, 113, 115, 116, 117, 119, 121, 124, 125]
def count787 (b : Nat → Bool) : Nat := countLit b [64, 66, 69, 70, 73, 74, 75, 76, 79, 80, 83, 85, 88, 89, 92, 93, 97, 98, 101, 104, 105, 106, 109, 111, 113, 115, 116, 117, 119, 121, 124, 125]
def count819 (b : Nat → Bool) : Nat := countLit b [2, 4, 6, 9, 13, 14, 16, 19, 21, 22, 23, 26, 29, 31, 32, 34, 37, 38, 40, 41, 44, 47, 48, 49, 50, 52, 55, 57, 58, 59, 61, 64, 66, 69, 70, 73, 74, 75, 76, 79, 80, 83, 85, 88, 89, 92, 93, 97, 98, 101, 104, 105, 106, 109, 111, 113, 115, 116, 117, 119, 121, 124, 125]
def count861 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count863 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6]
def count866 (b : Nat → Bool) : Nat := countLit b [-9, -13]
def count868 (b : Nat → Bool) : Nat := countLit b [-14, -16]
def count870 (b : Nat → Bool) : Nat := countLit b [-9, -13, -14, -16]
def count874 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -9, -13, -14, -16]
def count881 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count883 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count885 (b : Nat → Bool) : Nat := countLit b [-19, -21, -22, -23]
def count889 (b : Nat → Bool) : Nat := countLit b [-26, -29]
def count891 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count893 (b : Nat → Bool) : Nat := countLit b [-26, -29, -31, -32]
def count897 (b : Nat → Bool) : Nat := countLit b [-19, -21, -22, -23, -26, -29, -31, -32]
def count905 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -9, -13, -14, -16, -19, -21, -22, -23, -26, -29, -31, -32]
def count920 (b : Nat → Bool) : Nat := countLit b [-34, -37]
def count922 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count924 (b : Nat → Bool) : Nat := countLit b [-34, -37, -38, -40]
def count928 (b : Nat → Bool) : Nat := countLit b [-41, -44]
def count930 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count932 (b : Nat → Bool) : Nat := countLit b [-41, -44, -47, -48]
def count936 (b : Nat → Bool) : Nat := countLit b [-34, -37, -38, -40, -41, -44, -47, -48]
def count944 (b : Nat → Bool) : Nat := countLit b [-49, -50]
def count946 (b : Nat → Bool) : Nat := countLit b [-52, -55]
def count948 (b : Nat → Bool) : Nat := countLit b [-49, -50, -52, -55]
def count952 (b : Nat → Bool) : Nat := countLit b [-57, -58]
def count954 (b : Nat → Bool) : Nat := countLit b [-59, -61]
def count956 (b : Nat → Bool) : Nat := countLit b [-57, -58, -59, -61]
def count960 (b : Nat → Bool) : Nat := countLit b [-49, -50, -52, -55, -57, -58, -59, -61]
def count968 (b : Nat → Bool) : Nat := countLit b [-34, -37, -38, -40, -41, -44, -47, -48, -49, -50, -52, -55, -57, -58, -59, -61]
def count984 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -9, -13, -14, -16, -19, -21, -22, -23, -26, -29, -31, -32, -34, -37, -38, -40, -41, -44, -47, -48, -49, -50, -52, -55, -57, -58, -59, -61]
def count1007 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count1009 (b : Nat → Bool) : Nat := countLit b [-69, -70]
def count1011 (b : Nat → Bool) : Nat := countLit b [-64, -66, -69, -70]
def count1015 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count1017 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count1019 (b : Nat → Bool) : Nat := countLit b [-73, -74, -75, -76]
def count1023 (b : Nat → Bool) : Nat := countLit b [-64, -66, -69, -70, -73, -74, -75, -76]
def count1031 (b : Nat → Bool) : Nat := countLit b [-79, -80]
def count1033 (b : Nat → Bool) : Nat := countLit b [-83, -85]
def count1035 (b : Nat → Bool) : Nat := countLit b [-79, -80, -83, -85]
def count1039 (b : Nat → Bool) : Nat := countLit b [-88, -89]
def count1041 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1043 (b : Nat → Bool) : Nat := countLit b [-88, -89, -92, -93]
def count1047 (b : Nat → Bool) : Nat := countLit b [-79, -80, -83, -85, -88, -89, -92, -93]
def count1055 (b : Nat → Bool) : Nat := countLit b [-64, -66, -69, -70, -73, -74, -75, -76, -79, -80, -83, -85, -88, -89, -92, -93]
def count1071 (b : Nat → Bool) : Nat := countLit b [-97, -98]
def count1073 (b : Nat → Bool) : Nat := countLit b [-101, -104]
def count1075 (b : Nat → Bool) : Nat := countLit b [-97, -98, -101, -104]
def count1079 (b : Nat → Bool) : Nat := countLit b [-105, -106]
def count1081 (b : Nat → Bool) : Nat := countLit b [-109, -111]
def count1083 (b : Nat → Bool) : Nat := countLit b [-105, -106, -109, -111]
def count1087 (b : Nat → Bool) : Nat := countLit b [-97, -98, -101, -104, -105, -106, -109, -111]
def count1095 (b : Nat → Bool) : Nat := countLit b [-113, -115]
def count1097 (b : Nat → Bool) : Nat := countLit b [-116, -117]
def count1099 (b : Nat → Bool) : Nat := countLit b [-113, -115, -116, -117]
def count1103 (b : Nat → Bool) : Nat := countLit b [-119, -121]
def count1105 (b : Nat → Bool) : Nat := countLit b [-124, -125]
def count1107 (b : Nat → Bool) : Nat := countLit b [-119, -121, -124, -125]
def count1111 (b : Nat → Bool) : Nat := countLit b [-113, -115, -116, -117, -119, -121, -124, -125]
def count1119 (b : Nat → Bool) : Nat := countLit b [-97, -98, -101, -104, -105, -106, -109, -111, -113, -115, -116, -117, -119, -121, -124, -125]
def count1135 (b : Nat → Bool) : Nat := countLit b [-64, -66, -69, -70, -73, -74, -75, -76, -79, -80, -83, -85, -88, -89, -92, -93, -97, -98, -101, -104, -105, -106, -109, -111, -113, -115, -116, -117, -119, -121, -124, -125]
def count1158 (b : Nat → Bool) : Nat := countLit b [-2, -4, -6, -9, -13, -14, -16, -19, -21, -22, -23, -26, -29, -31, -32, -34, -37, -38, -40, -41, -44, -47, -48, -49, -50, -52, -55, -57, -58, -59, -61, -64, -66, -69, -70, -73, -74, -75, -76, -79, -80, -83, -85, -88, -89, -92, -93, -97, -98, -101, -104, -105, -106, -109, -111, -113, -115, -116, -117, -119, -121, -124, -125]
def count1181 (b : Nat → Bool) : Nat := countLit b [1, 3]
def count1183 (b : Nat → Bool) : Nat := countLit b [5, 7]
def count1185 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7]
def count1189 (b : Nat → Bool) : Nat := countLit b [8, 10]
def count1191 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count1193 (b : Nat → Bool) : Nat := countLit b [8, 10, 11, 12]
def count1197 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 8, 10, 11, 12]
def count1205 (b : Nat → Bool) : Nat := countLit b [15, 17]
def count1207 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count1209 (b : Nat → Bool) : Nat := countLit b [15, 17, 18, 20]
def count1213 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count1215 (b : Nat → Bool) : Nat := countLit b [27, 28]
def count1217 (b : Nat → Bool) : Nat := countLit b [24, 25, 27, 28]
def count1221 (b : Nat → Bool) : Nat := countLit b [15, 17, 18, 20, 24, 25, 27, 28]
def count1229 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 8, 10, 11, 12, 15, 17, 18, 20, 24, 25, 27, 28]
def count1245 (b : Nat → Bool) : Nat := countLit b [30, 33]
def count1247 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count1249 (b : Nat → Bool) : Nat := countLit b [30, 33, 35, 36]
def count1253 (b : Nat → Bool) : Nat := countLit b [39, 42]
def count1255 (b : Nat → Bool) : Nat := countLit b [43, 45]
def count1257 (b : Nat → Bool) : Nat := countLit b [39, 42, 43, 45]
def count1261 (b : Nat → Bool) : Nat := countLit b [30, 33, 35, 36, 39, 42, 43, 45]
def count1269 (b : Nat → Bool) : Nat := countLit b [46, 51]
def count1271 (b : Nat → Bool) : Nat := countLit b [53, 54]
def count1273 (b : Nat → Bool) : Nat := countLit b [46, 51, 53, 54]
def count1277 (b : Nat → Bool) : Nat := countLit b [56, 60]
def count1279 (b : Nat → Bool) : Nat := countLit b [62, 63]
def count1281 (b : Nat → Bool) : Nat := countLit b [56, 60, 62, 63]
def count1285 (b : Nat → Bool) : Nat := countLit b [46, 51, 53, 54, 56, 60, 62, 63]
def count1293 (b : Nat → Bool) : Nat := countLit b [30, 33, 35, 36, 39, 42, 43, 45, 46, 51, 53, 54, 56, 60, 62, 63]
def count1309 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 8, 10, 11, 12, 15, 17, 18, 20, 24, 25, 27, 28, 30, 33, 35, 36, 39, 42, 43, 45, 46, 51, 53, 54, 56, 60, 62, 63]
def count1341 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count1343 (b : Nat → Bool) : Nat := countLit b [68, 71]
def count1345 (b : Nat → Bool) : Nat := countLit b [65, 67, 68, 71]
def count1349 (b : Nat → Bool) : Nat := countLit b [72, 77]
def count1351 (b : Nat → Bool) : Nat := countLit b [78, 81]
def count1353 (b : Nat → Bool) : Nat := countLit b [72, 77, 78, 81]
def count1357 (b : Nat → Bool) : Nat := countLit b [65, 67, 68, 71, 72, 77, 78, 81]
def count1365 (b : Nat → Bool) : Nat := countLit b [82, 84]
def count1367 (b : Nat → Bool) : Nat := countLit b [86, 87]
def count1369 (b : Nat → Bool) : Nat := countLit b [82, 84, 86, 87]
def count1373 (b : Nat → Bool) : Nat := countLit b [90, 91]
def count1375 (b : Nat → Bool) : Nat := countLit b [94, 95]
def count1377 (b : Nat → Bool) : Nat := countLit b [90, 91, 94, 95]
def count1381 (b : Nat → Bool) : Nat := countLit b [82, 84, 86, 87, 90, 91, 94, 95]
def count1389 (b : Nat → Bool) : Nat := countLit b [65, 67, 68, 71, 72, 77, 78, 81, 82, 84, 86, 87, 90, 91, 94, 95]
def count1405 (b : Nat → Bool) : Nat := countLit b [96, 99]
def count1407 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count1409 (b : Nat → Bool) : Nat := countLit b [96, 99, 100, 102]
def count1413 (b : Nat → Bool) : Nat := countLit b [103, 107]
def count1415 (b : Nat → Bool) : Nat := countLit b [108, 110]
def count1417 (b : Nat → Bool) : Nat := countLit b [103, 107, 108, 110]
def count1421 (b : Nat → Bool) : Nat := countLit b [96, 99, 100, 102, 103, 107, 108, 110]
def count1429 (b : Nat → Bool) : Nat := countLit b [112, 114]
def count1431 (b : Nat → Bool) : Nat := countLit b [118, 120]
def count1433 (b : Nat → Bool) : Nat := countLit b [112, 114, 118, 120]
def count1437 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count1439 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count1441 (b : Nat → Bool) : Nat := countLit b [122, 123, 126, 127]
def count1445 (b : Nat → Bool) : Nat := countLit b [112, 114, 118, 120, 122, 123, 126, 127]
def count1453 (b : Nat → Bool) : Nat := countLit b [96, 99, 100, 102, 103, 107, 108, 110, 112, 114, 118, 120, 122, 123, 126, 127]
def count1469 (b : Nat → Bool) : Nat := countLit b [65, 67, 68, 71, 72, 77, 78, 81, 82, 84, 86, 87, 90, 91, 94, 95, 96, 99, 100, 102, 103, 107, 108, 110, 112, 114, 118, 120, 122, 123, 126, 127]
def count1501 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 7, 8, 10, 11, 12, 15, 17, 18, 20, 24, 25, 27, 28, 30, 33, 35, 36, 39, 42, 43, 45, 46, 51, 53, 54, 56, 60, 62, 63, 65, 67, 68, 71, 72, 77, 78, 81, 82, 84, 86, 87, 90, 91, 94, 95, 96, 99, 100, 102, 103, 107, 108, 110, 112, 114, 118, 120, 122, 123, 126, 127]
def count1543 (b : Nat → Bool) : Nat := countLit b [-1, -3]
def count1545 (b : Nat → Bool) : Nat := countLit b [-5, -7]
def count1547 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7]
def count1551 (b : Nat → Bool) : Nat := countLit b [-8, -10]
def count1553 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count1555 (b : Nat → Bool) : Nat := countLit b [-8, -10, -11, -12]
def count1559 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -8, -10, -11, -12]
def count1567 (b : Nat → Bool) : Nat := countLit b [-15, -17]
def count1569 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count1571 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18, -20]
def count1575 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count1577 (b : Nat → Bool) : Nat := countLit b [-27, -28]
def count1579 (b : Nat → Bool) : Nat := countLit b [-24, -25, -27, -28]
def count1583 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18, -20, -24, -25, -27, -28]
def count1591 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]
def count1607 (b : Nat → Bool) : Nat := countLit b [-30, -33]
def count1609 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count1611 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35, -36]
def count1615 (b : Nat → Bool) : Nat := countLit b [-39, -42]
def count1617 (b : Nat → Bool) : Nat := countLit b [-43, -45]
def count1619 (b : Nat → Bool) : Nat := countLit b [-39, -42, -43, -45]
def count1623 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35, -36, -39, -42, -43, -45]
def count1631 (b : Nat → Bool) : Nat := countLit b [-46, -51]
def count1633 (b : Nat → Bool) : Nat := countLit b [-53, -54]
def count1635 (b : Nat → Bool) : Nat := countLit b [-46, -51, -53, -54]
def count1639 (b : Nat → Bool) : Nat := countLit b [-56, -60]
def count1641 (b : Nat → Bool) : Nat := countLit b [-62, -63]
def count1643 (b : Nat → Bool) : Nat := countLit b [-56, -60, -62, -63]
def count1647 (b : Nat → Bool) : Nat := countLit b [-46, -51, -53, -54, -56, -60, -62, -63]
def count1655 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]
def count1671 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]
def count1695 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count1697 (b : Nat → Bool) : Nat := countLit b [-68, -71]
def count1699 (b : Nat → Bool) : Nat := countLit b [-65, -67, -68, -71]
def count1703 (b : Nat → Bool) : Nat := countLit b [-72, -77]
def count1705 (b : Nat → Bool) : Nat := countLit b [-78, -81]
def count1707 (b : Nat → Bool) : Nat := countLit b [-72, -77, -78, -81]
def count1711 (b : Nat → Bool) : Nat := countLit b [-65, -67, -68, -71, -72, -77, -78, -81]
def count1719 (b : Nat → Bool) : Nat := countLit b [-82, -84]
def count1721 (b : Nat → Bool) : Nat := countLit b [-86, -87]
def count1723 (b : Nat → Bool) : Nat := countLit b [-82, -84, -86, -87]
def count1727 (b : Nat → Bool) : Nat := countLit b [-90, -91]
def count1729 (b : Nat → Bool) : Nat := countLit b [-94, -95]
def count1731 (b : Nat → Bool) : Nat := countLit b [-90, -91, -94, -95]
def count1735 (b : Nat → Bool) : Nat := countLit b [-82, -84, -86, -87, -90, -91, -94, -95]
def count1743 (b : Nat → Bool) : Nat := countLit b [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]
def count1759 (b : Nat → Bool) : Nat := countLit b [-96, -99]
def count1761 (b : Nat → Bool) : Nat := countLit b [-100, -102]
def count1763 (b : Nat → Bool) : Nat := countLit b [-96, -99, -100, -102]
def count1767 (b : Nat → Bool) : Nat := countLit b [-103, -107]
def count1769 (b : Nat → Bool) : Nat := countLit b [-108, -110]
def count1771 (b : Nat → Bool) : Nat := countLit b [-103, -107, -108, -110]
def count1775 (b : Nat → Bool) : Nat := countLit b [-96, -99, -100, -102, -103, -107, -108, -110]
def count1783 (b : Nat → Bool) : Nat := countLit b [-112, -114]
def count1785 (b : Nat → Bool) : Nat := countLit b [-118, -120]
def count1787 (b : Nat → Bool) : Nat := countLit b [-112, -114, -118, -120]
def count1791 (b : Nat → Bool) : Nat := countLit b [-122, -123]
def count1793 (b : Nat → Bool) : Nat := countLit b [-126, -127]
def count1795 (b : Nat → Bool) : Nat := countLit b [-122, -123, -126, -127]
def count1799 (b : Nat → Bool) : Nat := countLit b [-112, -114, -118, -120, -122, -123, -126, -127]
def count1807 (b : Nat → Bool) : Nat := countLit b [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]
def count1823 (b : Nat → Bool) : Nat := countLit b [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]
def count1847 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63, -65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 935 then (if i < 467 then (if i < 233 then (if i < 116 then (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 25 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else b 24)) else (if i < 27 then (if i < 26 then b 25 else b 26) else (if i < 28 then b 27 else b 28))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)) else (if i < 34 then (if i < 33 then b 32 else b 33) else (if i < 35 then b 34 else b 35))) else (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 41 then (if i < 40 then b 39 else b 40) else (if i < 42 then b 41 else b 42)))) else (if i < 50 then (if i < 46 then (if i < 44 then b 43 else (if i < 45 then b 44 else b 45)) else (if i < 48 then (if i < 47 then b 46 else b 47) else (if i < 49 then b 48 else b 49))) else (if i < 54 then (if i < 52 then (if i < 51 then b 50 else b 51) else (if i < 53 then b 52 else b 53)) else (if i < 56 then (if i < 55 then b 54 else b 55) else (if i < 57 then b 56 else b 57)))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 63 then (if i < 62 then b 61 else b 62) else (if i < 64 then b 63 else b 64))) else (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 70 then (if i < 69 then b 68 else b 69) else (if i < 71 then b 70 else b 71)))) else (if i < 79 then (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 77 then (if i < 76 then b 75 else b 76) else (if i < 78 then b 77 else b 78))) else (if i < 83 then (if i < 81 then (if i < 80 then b 79 else b 80) else (if i < 82 then b 81 else b 82)) else (if i < 85 then (if i < 84 then b 83 else b 84) else (if i < 86 then b 85 else b 86))))) else (if i < 101 then (if i < 94 then (if i < 90 then (if i < 88 then b 87 else (if i < 89 then b 88 else b 89)) else (if i < 92 then (if i < 91 then b 90 else b 91) else (if i < 93 then b 92 else b 93))) else (if i < 97 then (if i < 95 then b 94 else (if i < 96 then b 95 else b 96)) else (if i < 99 then (if i < 98 then b 97 else b 98) else (if i < 100 then b 99 else b 100)))) else (if i < 108 then (if i < 104 then (if i < 102 then b 101 else (if i < 103 then b 102 else b 103)) else (if i < 106 then (if i < 105 then b 104 else b 105) else (if i < 107 then b 106 else b 107))) else (if i < 112 then (if i < 110 then (if i < 109 then b 108 else b 109) else (if i < 111 then b 110 else b 111)) else (if i < 114 then (if i < 113 then b 112 else b 113) else (if i < 115 then b 114 else b 115))))))) else (if i < 174 then (if i < 145 then (if i < 130 then (if i < 123 then (if i < 119 then (if i < 117 then b 116 else (if i < 118 then b 117 else b 118)) else (if i < 121 then (if i < 120 then b 119 else b 120) else (if i < 122 then b 121 else b 122))) else (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 128 then (if i < 127 then b 126 else b 127) else (if i < 129 then b 128 else b 129)))) else (if i < 137 then (if i < 133 then (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)) else (if i < 135 then (if i < 134 then b 133 else b 134) else (if i < 136 then b 135 else b 136))) else (if i < 141 then (if i < 139 then (if i < 138 then b 137 else b 138) else (if i < 140 then b 139 else b 140)) else (if i < 143 then (if i < 142 then b 141 else b 142) else (if i < 144 then b 143 else b 144))))) else (if i < 159 then (if i < 152 then (if i < 148 then (if i < 146 then b 145 else (if i < 147 then b 146 else b 147)) else (if i < 150 then (if i < 149 then b 148 else b 149) else (if i < 151 then b 150 else b 151))) else (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 157 then (if i < 156 then b 155 else b 156) else (if i < 158 then b 157 else b 158)))) else (if i < 166 then (if i < 162 then (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)) else (if i < 164 then (if i < 163 then b 162 else b 163) else (if i < 165 then b 164 else b 165))) else (if i < 170 then (if i < 168 then (if i < 167 then b 166 else b 167) else (if i < 169 then b 168 else b 169)) else (if i < 172 then (if i < 171 then b 170 else b 171) else (if i < 173 then b 172 else b 173)))))) else (if i < 203 then (if i < 188 then (if i < 181 then (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 179 then (if i < 178 then b 177 else b 178) else (if i < 180 then b 179 else b 180))) else (if i < 184 then (if i < 182 then b 181 else (if i < 183 then b 182 else b 183)) else (if i < 186 then (if i < 185 then b 184 else b 185) else (if i < 187 then b 186 else b 187)))) else (if i < 195 then (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else b 194))) else (if i < 199 then (if i < 197 then (if i < 196 then b 195 else b 196) else (if i < 198 then b 197 else b 198)) else (if i < 201 then (if i < 200 then b 199 else b 200) else (if i < 202 then b 201 else b 202))))) else (if i < 218 then (if i < 210 then (if i < 206 then (if i < 204 then b 203 else (if i < 205 then b 204 else b 205)) else (if i < 208 then (if i < 207 then b 206 else b 207) else (if i < 209 then b 208 else b 209))) else (if i < 214 then (if i < 212 then (if i < 211 then b 210 else b 211) else (if i < 213 then b 212 else b 213)) else (if i < 216 then (if i < 215 then b 214 else b 215) else (if i < 217 then b 216 else b 217)))) else (if i < 225 then (if i < 221 then (if i < 219 then b 218 else (if i < 220 then b 219 else b 220)) else (if i < 223 then (if i < 222 then b 221 else b 222) else (if i < 224 then b 223 else b 224))) else (if i < 229 then (if i < 227 then (if i < 226 then b 225 else b 226) else (if i < 228 then b 227 else b 228)) else (if i < 231 then (if i < 230 then b 229 else b 230) else (if i < 232 then b 231 else b 232)))))))) else (if i < 350 then (if i < 291 then (if i < 262 then (if i < 247 then (if i < 240 then (if i < 236 then (if i < 234 then b 233 else (if i < 235 then b 234 else b 235)) else (if i < 238 then (if i < 237 then b 236 else b 237) else (if i < 239 then b 238 else b 239))) else (if i < 243 then (if i < 241 then b 240 else (if i < 242 then b 241 else b 242)) else (if i < 245 then (if i < 244 then b 243 else b 244) else (if i < 246 then b 245 else b 246)))) else (if i < 254 then (if i < 250 then (if i < 248 then b 247 else (if i < 249 then b 248 else b 249)) else (if i < 252 then (if i < 251 then b 250 else b 251) else (if i < 253 then b 252 else b 253))) else (if i < 258 then (if i < 256 then (if i < 255 then b 254 else decide (1 ≤ count255 b)) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 260 then (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b)) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))))) else (if i < 276 then (if i < 269 then (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 267 then (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b)))) else (if i < 272 then (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))) else (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))))) else (if i < 283 then (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 281 then (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)))) else (if i < 287 then (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b))) else (if i < 289 then (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))))))) else (if i < 320 then (if i < 305 then (if i < 298 then (if i < 294 then (if i < 292 then decide (1 ≤ count291 b) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b))) else (if i < 296 then (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)))) else (if i < 301 then (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))) else (if i < 303 then (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b)) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))))) else (if i < 312 then (if i < 308 then (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))) else (if i < 310 then (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)))) else (if i < 316 then (if i < 314 then (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))))) else (if i < 335 then (if i < 327 then (if i < 323 then (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))) else (if i < 325 then (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b)) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)))) else (if i < 331 then (if i < 329 then (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b))) else (if i < 333 then (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))))) else (if i < 342 then (if i < 338 then (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b))) else (if i < 340 then (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)))) else (if i < 346 then (if i < 344 then (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b)) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)))))))) else (if i < 408 then (if i < 379 then (if i < 364 then (if i < 357 then (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 355 then (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)))) else (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 362 then (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))))) else (if i < 371 then (if i < 367 then (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))) else (if i < 369 then (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b)) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 375 then (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b))) else (if i < 377 then (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)))))) else (if i < 393 then (if i < 386 then (if i < 382 then (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))) else (if i < 384 then (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)))) else (if i < 389 then (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b))) else (if i < 391 then (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))))) else (if i < 400 then (if i < 396 then (if i < 394 then decide (1 ≤ count393 b) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b))) else (if i < 398 then (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b)) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))) else (if i < 404 then (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))) else (if i < 406 then (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b)) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b))))))) else (if i < 437 then (if i < 422 then (if i < 415 then (if i < 411 then (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))) else (if i < 413 then (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b)) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))) else (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 420 then (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))))) else (if i < 429 then (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 427 then (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)))) else (if i < 433 then (if i < 431 then (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b)) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b))) else (if i < 435 then (if i < 434 then decide (1 ≤ count433 b) else decide (2 ≤ count433 b)) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)))))) else (if i < 452 then (if i < 444 then (if i < 440 then (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b))) else (if i < 442 then (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)))) else (if i < 448 then (if i < 446 then (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)) else (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b))) else (if i < 450 then (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b)) else (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b))))) else (if i < 459 then (if i < 455 then (if i < 453 then decide (2 ≤ count451 b) else (if i < 454 then decide (1 ≤ count453 b) else decide (2 ≤ count453 b))) else (if i < 457 then (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b)) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)))) else (if i < 463 then (if i < 461 then (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b))) else (if i < 465 then (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b)) else (if i < 466 then decide (1 ≤ count465 b) else decide (2 ≤ count465 b)))))))))) else (if i < 701 then (if i < 584 then (if i < 525 then (if i < 496 then (if i < 481 then (if i < 474 then (if i < 470 then (if i < 468 then decide (1 ≤ count467 b) else (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b))) else (if i < 472 then (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b)) else (if i < 473 then decide (2 ≤ count471 b) else decide (1 ≤ count473 b)))) else (if i < 477 then (if i < 475 then decide (2 ≤ count473 b) else (if i < 476 then decide (1 ≤ count475 b) else decide (2 ≤ count475 b))) else (if i < 479 then (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b)) else (if i < 480 then decide (1 ≤ count479 b) else decide (2 ≤ count479 b))))) else (if i < 488 then (if i < 484 then (if i < 482 then decide (1 ≤ count481 b) else (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b))) else (if i < 486 then (if i < 485 then decide (2 ≤ count483 b) else decide (1 ≤ count485 b)) else (if i < 487 then decide (2 ≤ count485 b) else decide (1 ≤ count487 b)))) else (if i < 492 then (if i < 490 then (if i < 489 then decide (2 ≤ count487 b) else decide (1 ≤ count489 b)) else (if i < 491 then decide (2 ≤ count489 b) else decide (1 ≤ count491 b))) else (if i < 494 then (if i < 493 then decide (2 ≤ count491 b) else decide (1 ≤ count493 b)) else (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b)))))) else (if i < 510 then (if i < 503 then (if i < 499 then (if i < 497 then decide (2 ≤ count495 b) else (if i < 498 then decide (1 ≤ count497 b) else decide (2 ≤ count497 b))) else (if i < 501 then (if i < 500 then decide (1 ≤ count499 b) else decide (2 ≤ count499 b)) else (if i < 502 then decide (1 ≤ count501 b) else decide (2 ≤ count501 b)))) else (if i < 506 then (if i < 504 then decide (1 ≤ count503 b) else (if i < 505 then decide (2 ≤ count503 b) else decide (1 ≤ count505 b))) else (if i < 508 then (if i < 507 then decide (2 ≤ count505 b) else decide (1 ≤ count507 b)) else (if i < 509 then decide (2 ≤ count507 b) else decide (3 ≤ count507 b))))) else (if i < 517 then (if i < 513 then (if i < 511 then decide (1 ≤ count510 b) else (if i < 512 then decide (2 ≤ count510 b) else decide (1 ≤ count512 b))) else (if i < 515 then (if i < 514 then decide (2 ≤ count512 b) else decide (1 ≤ count514 b)) else (if i < 516 then decide (2 ≤ count514 b) else decide (3 ≤ count514 b)))) else (if i < 521 then (if i < 519 then (if i < 518 then decide (4 ≤ count514 b) else decide (1 ≤ count518 b)) else (if i < 520 then decide (2 ≤ count518 b) else decide (3 ≤ count518 b))) else (if i < 523 then (if i < 522 then decide (4 ≤ count518 b) else decide (5 ≤ count518 b)) else (if i < 524 then decide (6 ≤ count518 b) else decide (7 ≤ count518 b))))))) else (if i < 554 then (if i < 539 then (if i < 532 then (if i < 528 then (if i < 526 then decide (1 ≤ count525 b) else (if i < 527 then decide (2 ≤ count525 b) else decide (1 ≤ count527 b))) else (if i < 530 then (if i < 529 then decide (2 ≤ count527 b) else decide (1 ≤ count529 b)) else (if i < 531 then decide (2 ≤ count529 b) else decide (3 ≤ count529 b)))) else (if i < 535 then (if i < 533 then decide (4 ≤ count529 b) else (if i < 534 then decide (1 ≤ count533 b) else decide (2 ≤ count533 b))) else (if i < 537 then (if i < 536 then decide (1 ≤ count535 b) else decide (2 ≤ count535 b)) else (if i < 538 then decide (1 ≤ count537 b) else decide (2 ≤ count537 b))))) else (if i < 546 then (if i < 542 then (if i < 540 then decide (3 ≤ count537 b) else (if i < 541 then decide (4 ≤ count537 b) else decide (1 ≤ count541 b))) else (if i < 544 then (if i < 543 then decide (2 ≤ count541 b) else decide (3 ≤ count541 b)) else (if i < 545 then decide (4 ≤ count541 b) else decide (5 ≤ count541 b)))) else (if i < 550 then (if i < 548 then (if i < 547 then decide (6 ≤ count541 b) else decide (7 ≤ count541 b)) else (if i < 549 then decide (8 ≤ count541 b) else decide (1 ≤ count549 b))) else (if i < 552 then (if i < 551 then decide (2 ≤ count549 b) else decide (3 ≤ count549 b)) else (if i < 553 then decide (4 ≤ count549 b) else decide (5 ≤ count549 b)))))) else (if i < 569 then (if i < 561 then (if i < 557 then (if i < 555 then decide (6 ≤ count549 b) else (if i < 556 then decide (7 ≤ count549 b) else decide (8 ≤ count549 b))) else (if i < 559 then (if i < 558 then decide (9 ≤ count549 b) else decide (10 ≤ count549 b)) else (if i < 560 then decide (11 ≤ count549 b) else decide (12 ≤ count549 b)))) else (if i < 565 then (if i < 563 then (if i < 562 then decide (13 ≤ count549 b) else decide (14 ≤ count549 b)) else (if i < 564 then decide (15 ≤ count549 b) else decide (1 ≤ count564 b))) else (if i < 567 then (if i < 566 then decide (2 ≤ count564 b) else decide (1 ≤ count566 b)) else (if i < 568 then decide (2 ≤ count566 b) else decide (1 ≤ count568 b))))) else (if i < 576 then (if i < 572 then (if i < 570 then decide (2 ≤ count568 b) else (if i < 571 then decide (3 ≤ count568 b) else decide (4 ≤ count568 b))) else (if i < 574 then (if i < 573 then decide (1 ≤ count572 b) else decide (2 ≤ count572 b)) else (if i < 575 then decide (1 ≤ count574 b) else decide (2 ≤ count574 b)))) else (if i < 580 then (if i < 578 then (if i < 577 then decide (1 ≤ count576 b) else decide (2 ≤ count576 b)) else (if i < 579 then decide (3 ≤ count576 b) else decide (4 ≤ count576 b))) else (if i < 582 then (if i < 581 then decide (1 ≤ count580 b) else decide (2 ≤ count580 b)) else (if i < 583 then decide (3 ≤ count580 b) else decide (4 ≤ count580 b)))))))) else (if i < 642 then (if i < 613 then (if i < 598 then (if i < 591 then (if i < 587 then (if i < 585 then decide (5 ≤ count580 b) else (if i < 586 then decide (6 ≤ count580 b) else decide (7 ≤ count580 b))) else (if i < 589 then (if i < 588 then decide (8 ≤ count580 b) else decide (1 ≤ count588 b)) else (if i < 590 then decide (2 ≤ count588 b) else decide (1 ≤ count590 b)))) else (if i < 594 then (if i < 592 then decide (2 ≤ count590 b) else (if i < 593 then decide (1 ≤ count592 b) else decide (2 ≤ count592 b))) else (if i < 596 then (if i < 595 then decide (3 ≤ count592 b) else decide (4 ≤ count592 b)) else (if i < 597 then decide (1 ≤ count596 b) else decide (2 ≤ count596 b))))) else (if i < 605 then (if i < 601 then (if i < 599 then decide (1 ≤ count598 b) else (if i < 600 then decide (2 ≤ count598 b) else decide (1 ≤ count600 b))) else (if i < 603 then (if i < 602 then decide (2 ≤ count600 b) else decide (3 ≤ count600 b)) else (if i < 604 then decide (4 ≤ count600 b) else decide (1 ≤ count604 b)))) else (if i < 609 then (if i < 607 then (if i < 606 then decide (2 ≤ count604 b) else decide (3 ≤ count604 b)) else (if i < 608 then decide (4 ≤ count604 b) else decide (5 ≤ count604 b))) else (if i < 611 then (if i < 610 then decide (6 ≤ count604 b) else decide (7 ≤ count604 b)) else (if i < 612 then decide (8 ≤ count604 b) else decide (1 ≤ count612 b)))))) else (if i < 627 then (if i < 620 then (if i < 616 then (if i < 614 then decide (2 ≤ count612 b) else (if i < 615 then decide (3 ≤ count612 b) else decide (4 ≤ count612 b))) else (if i < 618 then (if i < 617 then decide (5 ≤ count612 b) else decide (6 ≤ count612 b)) else (if i < 619 then decide (7 ≤ count612 b) else decide (8 ≤ count612 b)))) else (if i < 623 then (if i < 621 then decide (9 ≤ count612 b) else (if i < 622 then decide (10 ≤ count612 b) else decide (11 ≤ count612 b))) else (if i < 625 then (if i < 624 then decide (12 ≤ count612 b) else decide (13 ≤ count612 b)) else (if i < 626 then decide (14 ≤ count612 b) else decide (15 ≤ count612 b))))) else (if i < 634 then (if i < 630 then (if i < 628 then decide (16 ≤ count612 b) else (if i < 629 then decide (1 ≤ count628 b) else decide (2 ≤ count628 b))) else (if i < 632 then (if i < 631 then decide (3 ≤ count628 b) else decide (4 ≤ count628 b)) else (if i < 633 then decide (5 ≤ count628 b) else decide (6 ≤ count628 b)))) else (if i < 638 then (if i < 636 then (if i < 635 then decide (7 ≤ count628 b) else decide (8 ≤ count628 b)) else (if i < 637 then decide (9 ≤ count628 b) else decide (10 ≤ count628 b))) else (if i < 640 then (if i < 639 then decide (11 ≤ count628 b) else decide (12 ≤ count628 b)) else (if i < 641 then decide (13 ≤ count628 b) else decide (14 ≤ count628 b))))))) else (if i < 671 then (if i < 656 then (if i < 649 then (if i < 645 then (if i < 643 then decide (15 ≤ count628 b) else (if i < 644 then decide (16 ≤ count628 b) else decide (17 ≤ count628 b))) else (if i < 647 then (if i < 646 then decide (18 ≤ count628 b) else decide (19 ≤ count628 b)) else (if i < 648 then decide (20 ≤ count628 b) else decide (21 ≤ count628 b)))) else (if i < 652 then (if i < 650 then decide (22 ≤ count628 b) else (if i < 651 then decide (23 ≤ count628 b) else decide (24 ≤ count628 b))) else (if i < 654 then (if i < 653 then decide (25 ≤ count628 b) else decide (26 ≤ count628 b)) else (if i < 655 then decide (27 ≤ count628 b) else decide (28 ≤ count628 b))))) else (if i < 663 then (if i < 659 then (if i < 657 then decide (29 ≤ count628 b) else (if i < 658 then decide (30 ≤ count628 b) else decide (31 ≤ count628 b))) else (if i < 661 then (if i < 660 then decide (1 ≤ count659 b) else decide (2 ≤ count659 b)) else (if i < 662 then decide (1 ≤ count661 b) else decide (2 ≤ count661 b)))) else (if i < 667 then (if i < 665 then (if i < 664 then decide (1 ≤ count663 b) else decide (2 ≤ count663 b)) else (if i < 666 then decide (3 ≤ count663 b) else decide (4 ≤ count663 b))) else (if i < 669 then (if i < 668 then decide (1 ≤ count667 b) else decide (2 ≤ count667 b)) else (if i < 670 then decide (1 ≤ count669 b) else decide (2 ≤ count669 b)))))) else (if i < 686 then (if i < 678 then (if i < 674 then (if i < 672 then decide (1 ≤ count671 b) else (if i < 673 then decide (2 ≤ count671 b) else decide (3 ≤ count671 b))) else (if i < 676 then (if i < 675 then decide (4 ≤ count671 b) else decide (1 ≤ count675 b)) else (if i < 677 then decide (2 ≤ count675 b) else decide (3 ≤ count675 b)))) else (if i < 682 then (if i < 680 then (if i < 679 then decide (4 ≤ count675 b) else decide (5 ≤ count675 b)) else (if i < 681 then decide (6 ≤ count675 b) else decide (7 ≤ count675 b))) else (if i < 684 then (if i < 683 then decide (8 ≤ count675 b) else decide (1 ≤ count683 b)) else (if i < 685 then decide (2 ≤ count683 b) else decide (1 ≤ count685 b))))) else (if i < 693 then (if i < 689 then (if i < 687 then decide (2 ≤ count685 b) else (if i < 688 then decide (1 ≤ count687 b) else decide (2 ≤ count687 b))) else (if i < 691 then (if i < 690 then decide (3 ≤ count687 b) else decide (4 ≤ count687 b)) else (if i < 692 then decide (1 ≤ count691 b) else decide (2 ≤ count691 b)))) else (if i < 697 then (if i < 695 then (if i < 694 then decide (1 ≤ count693 b) else decide (2 ≤ count693 b)) else (if i < 696 then decide (1 ≤ count695 b) else decide (2 ≤ count695 b))) else (if i < 699 then (if i < 698 then decide (3 ≤ count695 b) else decide (4 ≤ count695 b)) else (if i < 700 then decide (1 ≤ count699 b) else decide (2 ≤ count699 b))))))))) else (if i < 818 then (if i < 759 then (if i < 730 then (if i < 715 then (if i < 708 then (if i < 704 then (if i < 702 then decide (3 ≤ count699 b) else (if i < 703 then decide (4 ≤ count699 b) else decide (5 ≤ count699 b))) else (if i < 706 then (if i < 705 then decide (6 ≤ count699 b) else decide (7 ≤ count699 b)) else (if i < 707 then decide (8 ≤ count699 b) else decide (1 ≤ count707 b)))) else (if i < 711 then (if i < 709 then decide (2 ≤ count707 b) else (if i < 710 then decide (3 ≤ count707 b) else decide (4 ≤ count707 b))) else (if i < 713 then (if i < 712 then decide (5 ≤ count707 b) else decide (6 ≤ count707 b)) else (if i < 714 then decide (7 ≤ count707 b) else decide (8 ≤ count707 b))))) else (if i < 722 then (if i < 718 then (if i < 716 then decide (9 ≤ count707 b) else (if i < 717 then decide (10 ≤ count707 b) else decide (11 ≤ count707 b))) else (if i < 720 then (if i < 719 then decide (12 ≤ count707 b) else decide (13 ≤ count707 b)) else (if i < 721 then decide (14 ≤ count707 b) else decide (15 ≤ count707 b)))) else (if i < 726 then (if i < 724 then (if i < 723 then decide (16 ≤ count707 b) else decide (1 ≤ count723 b)) else (if i < 725 then decide (2 ≤ count723 b) else decide (1 ≤ count725 b))) else (if i < 728 then (if i < 727 then decide (2 ≤ count725 b) else decide (1 ≤ count727 b)) else (if i < 729 then decide (2 ≤ count727 b) else decide (3 ≤ count727 b)))))) else (if i < 744 then (if i < 737 then (if i < 733 then (if i < 731 then decide (4 ≤ count727 b) else (if i < 732 then decide (1 ≤ count731 b) else decide (2 ≤ count731 b))) else (if i < 735 then (if i < 734 then decide (1 ≤ count733 b) else decide (2 ≤ count733 b)) else (if i < 736 then decide (1 ≤ count735 b) else decide (2 ≤ count735 b)))) else (if i < 740 then (if i < 738 then decide (3 ≤ count735 b) else (if i < 739 then decide (4 ≤ count735 b) else decide (1 ≤ count739 b))) else (if i < 742 then (if i < 741 then decide (2 ≤ count739 b) else decide (3 ≤ count739 b)) else (if i < 743 then decide (4 ≤ count739 b) else decide (5 ≤ count739 b))))) else (if i < 751 then (if i < 747 then (if i < 745 then decide (6 ≤ count739 b) else (if i < 746 then decide (7 ≤ count739 b) else decide (8 ≤ count739 b))) else (if i < 749 then (if i < 748 then decide (1 ≤ count747 b) else decide (2 ≤ count747 b)) else (if i < 750 then decide (1 ≤ count749 b) else decide (2 ≤ count749 b)))) else (if i < 755 then (if i < 753 then (if i < 752 then decide (1 ≤ count751 b) else decide (2 ≤ count751 b)) else (if i < 754 then decide (3 ≤ count751 b) else decide (4 ≤ count751 b))) else (if i < 757 then (if i < 756 then decide (1 ≤ count755 b) else decide (2 ≤ count755 b)) else (if i < 758 then decide (1 ≤ count757 b) else decide (2 ≤ count757 b))))))) else (if i < 788 then (if i < 773 then (if i < 766 then (if i < 762 then (if i < 760 then decide (1 ≤ count759 b) else (if i < 761 then decide (2 ≤ count759 b) else decide (3 ≤ count759 b))) else (if i < 764 then (if i < 763 then decide (4 ≤ count759 b) else decide (1 ≤ count763 b)) else (if i < 765 then decide (2 ≤ count763 b) else decide (3 ≤ count763 b)))) else (if i < 769 then (if i < 767 then decide (4 ≤ count763 b) else (if i < 768 then decide (5 ≤ count763 b) else decide (6 ≤ count763 b))) else (if i < 771 then (if i < 770 then decide (7 ≤ count763 b) else decide (8 ≤ count763 b)) else (if i < 772 then decide (1 ≤ count771 b) else decide (2 ≤ count771 b))))) else (if i < 780 then (if i < 776 then (if i < 774 then decide (3 ≤ count771 b) else (if i < 775 then decide (4 ≤ count771 b) else decide (5 ≤ count771 b))) else (if i < 778 then (if i < 777 then decide (6 ≤ count771 b) else decide (7 ≤ count771 b)) else (if i < 779 then decide (8 ≤ count771 b) else decide (9 ≤ count771 b)))) else (if i < 784 then (if i < 782 then (if i < 781 then decide (10 ≤ count771 b) else decide (11 ≤ count771 b)) else (if i < 783 then decide (12 ≤ count771 b) else decide (13 ≤ count771 b))) else (if i < 786 then (if i < 785 then decide (14 ≤ count771 b) else decide (15 ≤ count771 b)) else (if i < 787 then decide (16 ≤ count771 b) else decide (1 ≤ count787 b)))))) else (if i < 803 then (if i < 795 then (if i < 791 then (if i < 789 then decide (2 ≤ count787 b) else (if i < 790 then decide (3 ≤ count787 b) else decide (4 ≤ count787 b))) else (if i < 793 then (if i < 792 then decide (5 ≤ count787 b) else decide (6 ≤ count787 b)) else (if i < 794 then decide (7 ≤ count787 b) else decide (8 ≤ count787 b)))) else (if i < 799 then (if i < 797 then (if i < 796 then decide (9 ≤ count787 b) else decide (10 ≤ count787 b)) else (if i < 798 then decide (11 ≤ count787 b) else decide (12 ≤ count787 b))) else (if i < 801 then (if i < 800 then decide (13 ≤ count787 b) else decide (14 ≤ count787 b)) else (if i < 802 then decide (15 ≤ count787 b) else decide (16 ≤ count787 b))))) else (if i < 810 then (if i < 806 then (if i < 804 then decide (17 ≤ count787 b) else (if i < 805 then decide (18 ≤ count787 b) else decide (19 ≤ count787 b))) else (if i < 808 then (if i < 807 then decide (20 ≤ count787 b) else decide (21 ≤ count787 b)) else (if i < 809 then decide (22 ≤ count787 b) else decide (23 ≤ count787 b)))) else (if i < 814 then (if i < 812 then (if i < 811 then decide (24 ≤ count787 b) else decide (25 ≤ count787 b)) else (if i < 813 then decide (26 ≤ count787 b) else decide (27 ≤ count787 b))) else (if i < 816 then (if i < 815 then decide (28 ≤ count787 b) else decide (29 ≤ count787 b)) else (if i < 817 then decide (30 ≤ count787 b) else decide (31 ≤ count787 b)))))))) else (if i < 876 then (if i < 847 then (if i < 832 then (if i < 825 then (if i < 821 then (if i < 819 then decide (32 ≤ count787 b) else (if i < 820 then decide (1 ≤ count819 b) else decide (2 ≤ count819 b))) else (if i < 823 then (if i < 822 then decide (3 ≤ count819 b) else decide (4 ≤ count819 b)) else (if i < 824 then decide (5 ≤ count819 b) else decide (6 ≤ count819 b)))) else (if i < 828 then (if i < 826 then decide (7 ≤ count819 b) else (if i < 827 then decide (8 ≤ count819 b) else decide (9 ≤ count819 b))) else (if i < 830 then (if i < 829 then decide (10 ≤ count819 b) else decide (11 ≤ count819 b)) else (if i < 831 then decide (12 ≤ count819 b) else decide (13 ≤ count819 b))))) else (if i < 839 then (if i < 835 then (if i < 833 then decide (14 ≤ count819 b) else (if i < 834 then decide (15 ≤ count819 b) else decide (16 ≤ count819 b))) else (if i < 837 then (if i < 836 then decide (17 ≤ count819 b) else decide (18 ≤ count819 b)) else (if i < 838 then decide (19 ≤ count819 b) else decide (20 ≤ count819 b)))) else (if i < 843 then (if i < 841 then (if i < 840 then decide (21 ≤ count819 b) else decide (22 ≤ count819 b)) else (if i < 842 then decide (23 ≤ count819 b) else decide (24 ≤ count819 b))) else (if i < 845 then (if i < 844 then decide (25 ≤ count819 b) else decide (26 ≤ count819 b)) else (if i < 846 then decide (27 ≤ count819 b) else decide (28 ≤ count819 b)))))) else (if i < 861 then (if i < 854 then (if i < 850 then (if i < 848 then decide (29 ≤ count819 b) else (if i < 849 then decide (30 ≤ count819 b) else decide (31 ≤ count819 b))) else (if i < 852 then (if i < 851 then decide (32 ≤ count819 b) else decide (33 ≤ count819 b)) else (if i < 853 then decide (34 ≤ count819 b) else decide (35 ≤ count819 b)))) else (if i < 857 then (if i < 855 then decide (36 ≤ count819 b) else (if i < 856 then decide (37 ≤ count819 b) else decide (38 ≤ count819 b))) else (if i < 859 then (if i < 858 then decide (39 ≤ count819 b) else decide (40 ≤ count819 b)) else (if i < 860 then decide (41 ≤ count819 b) else decide (42 ≤ count819 b))))) else (if i < 868 then (if i < 864 then (if i < 862 then decide (1 ≤ count861 b) else (if i < 863 then decide (2 ≤ count861 b) else decide (1 ≤ count863 b))) else (if i < 866 then (if i < 865 then decide (2 ≤ count863 b) else decide (3 ≤ count863 b)) else (if i < 867 then decide (1 ≤ count866 b) else decide (2 ≤ count866 b)))) else (if i < 872 then (if i < 870 then (if i < 869 then decide (1 ≤ count868 b) else decide (2 ≤ count868 b)) else (if i < 871 then decide (1 ≤ count870 b) else decide (2 ≤ count870 b))) else (if i < 874 then (if i < 873 then decide (3 ≤ count870 b) else decide (4 ≤ count870 b)) else (if i < 875 then decide (1 ≤ count874 b) else decide (2 ≤ count874 b))))))) else (if i < 905 then (if i < 890 then (if i < 883 then (if i < 879 then (if i < 877 then decide (3 ≤ count874 b) else (if i < 878 then decide (4 ≤ count874 b) else decide (5 ≤ count874 b))) else (if i < 881 then (if i < 880 then decide (6 ≤ count874 b) else decide (7 ≤ count874 b)) else (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b)))) else (if i < 886 then (if i < 884 then decide (1 ≤ count883 b) else (if i < 885 then decide (2 ≤ count883 b) else decide (1 ≤ count885 b))) else (if i < 888 then (if i < 887 then decide (2 ≤ count885 b) else decide (3 ≤ count885 b)) else (if i < 889 then decide (4 ≤ count885 b) else decide (1 ≤ count889 b))))) else (if i < 897 then (if i < 893 then (if i < 891 then decide (2 ≤ count889 b) else (if i < 892 then decide (1 ≤ count891 b) else decide (2 ≤ count891 b))) else (if i < 895 then (if i < 894 then decide (1 ≤ count893 b) else decide (2 ≤ count893 b)) else (if i < 896 then decide (3 ≤ count893 b) else decide (4 ≤ count893 b)))) else (if i < 901 then (if i < 899 then (if i < 898 then decide (1 ≤ count897 b) else decide (2 ≤ count897 b)) else (if i < 900 then decide (3 ≤ count897 b) else decide (4 ≤ count897 b))) else (if i < 903 then (if i < 902 then decide (5 ≤ count897 b) else decide (6 ≤ count897 b)) else (if i < 904 then decide (7 ≤ count897 b) else decide (8 ≤ count897 b)))))) else (if i < 920 then (if i < 912 then (if i < 908 then (if i < 906 then decide (1 ≤ count905 b) else (if i < 907 then decide (2 ≤ count905 b) else decide (3 ≤ count905 b))) else (if i < 910 then (if i < 909 then decide (4 ≤ count905 b) else decide (5 ≤ count905 b)) else (if i < 911 then decide (6 ≤ count905 b) else decide (7 ≤ count905 b)))) else (if i < 916 then (if i < 914 then (if i < 913 then decide (8 ≤ count905 b) else decide (9 ≤ count905 b)) else (if i < 915 then decide (10 ≤ count905 b) else decide (11 ≤ count905 b))) else (if i < 918 then (if i < 917 then decide (12 ≤ count905 b) else decide (13 ≤ count905 b)) else (if i < 919 then decide (14 ≤ count905 b) else decide (15 ≤ count905 b))))) else (if i < 927 then (if i < 923 then (if i < 921 then decide (1 ≤ count920 b) else (if i < 922 then decide (2 ≤ count920 b) else decide (1 ≤ count922 b))) else (if i < 925 then (if i < 924 then decide (2 ≤ count922 b) else decide (1 ≤ count924 b)) else (if i < 926 then decide (2 ≤ count924 b) else decide (3 ≤ count924 b)))) else (if i < 931 then (if i < 929 then (if i < 928 then decide (4 ≤ count924 b) else decide (1 ≤ count928 b)) else (if i < 930 then decide (2 ≤ count928 b) else decide (1 ≤ count930 b))) else (if i < 933 then (if i < 932 then decide (2 ≤ count930 b) else decide (1 ≤ count932 b)) else (if i < 934 then decide (2 ≤ count932 b) else decide (3 ≤ count932 b))))))))))) else (if i < 1403 then (if i < 1169 then (if i < 1052 then (if i < 993 then (if i < 964 then (if i < 949 then (if i < 942 then (if i < 938 then (if i < 936 then decide (4 ≤ count932 b) else (if i < 937 then decide (1 ≤ count936 b) else decide (2 ≤ count936 b))) else (if i < 940 then (if i < 939 then decide (3 ≤ count936 b) else decide (4 ≤ count936 b)) else (if i < 941 then decide (5 ≤ count936 b) else decide (6 ≤ count936 b)))) else (if i < 945 then (if i < 943 then decide (7 ≤ count936 b) else (if i < 944 then decide (8 ≤ count936 b) else decide (1 ≤ count944 b))) else (if i < 947 then (if i < 946 then decide (2 ≤ count944 b) else decide (1 ≤ count946 b)) else (if i < 948 then decide (2 ≤ count946 b) else decide (1 ≤ count948 b))))) else (if i < 956 then (if i < 952 then (if i < 950 then decide (2 ≤ count948 b) else (if i < 951 then decide (3 ≤ count948 b) else decide (4 ≤ count948 b))) else (if i < 954 then (if i < 953 then decide (1 ≤ count952 b) else decide (2 ≤ count952 b)) else (if i < 955 then decide (1 ≤ count954 b) else decide (2 ≤ count954 b)))) else (if i < 960 then (if i < 958 then (if i < 957 then decide (1 ≤ count956 b) else decide (2 ≤ count956 b)) else (if i < 959 then decide (3 ≤ count956 b) else decide (4 ≤ count956 b))) else (if i < 962 then (if i < 961 then decide (1 ≤ count960 b) else decide (2 ≤ count960 b)) else (if i < 963 then decide (3 ≤ count960 b) else decide (4 ≤ count960 b)))))) else (if i < 978 then (if i < 971 then (if i < 967 then (if i < 965 then decide (5 ≤ count960 b) else (if i < 966 then decide (6 ≤ count960 b) else decide (7 ≤ count960 b))) else (if i < 969 then (if i < 968 then decide (8 ≤ count960 b) else decide (1 ≤ count968 b)) else (if i < 970 then decide (2 ≤ count968 b) else decide (3 ≤ count968 b)))) else (if i < 974 then (if i < 972 then decide (4 ≤ count968 b) else (if i < 973 then decide (5 ≤ count968 b) else decide (6 ≤ count968 b))) else (if i < 976 then (if i < 975 then decide (7 ≤ count968 b) else decide (8 ≤ count968 b)) else (if i < 977 then decide (9 ≤ count968 b) else decide (10 ≤ count968 b))))) else (if i < 985 then (if i < 981 then (if i < 979 then decide (11 ≤ count968 b) else (if i < 980 then decide (12 ≤ count968 b) else decide (13 ≤ count968 b))) else (if i < 983 then (if i < 982 then decide (14 ≤ count968 b) else decide (15 ≤ count968 b)) else (if i < 984 then decide (16 ≤ count968 b) else decide (1 ≤ count984 b)))) else (if i < 989 then (if i < 987 then (if i < 986 then decide (2 ≤ count984 b) else decide (3 ≤ count984 b)) else (if i < 988 then decide (4 ≤ count984 b) else decide (5 ≤ count984 b))) else (if i < 991 then (if i < 990 then decide (6 ≤ count984 b) else decide (7 ≤ count984 b)) else (if i < 992 then decide (8 ≤ count984 b) else decide (9 ≤ count984 b))))))) else (if i < 1022 then (if i < 1007 then (if i < 1000 then (if i < 996 then (if i < 994 then decide (10 ≤ count984 b) else (if i < 995 then decide (11 ≤ count984 b) else decide (12 ≤ count984 b))) else (if i < 998 then (if i < 997 then decide (13 ≤ count984 b) else decide (14 ≤ count984 b)) else (if i < 999 then decide (15 ≤ count984 b) else decide (16 ≤ count984 b)))) else (if i < 1003 then (if i < 1001 then decide (17 ≤ count984 b) else (if i < 1002 then decide (18 ≤ count984 b) else decide (19 ≤ count984 b))) else (if i < 1005 then (if i < 1004 then decide (20 ≤ count984 b) else decide (21 ≤ count984 b)) else (if i < 1006 then decide (22 ≤ count984 b) else decide (23 ≤ count984 b))))) else (if i < 1014 then (if i < 1010 then (if i < 1008 then decide (1 ≤ count1007 b) else (if i < 1009 then decide (2 ≤ count1007 b) else decide (1 ≤ count1009 b))) else (if i < 1012 then (if i < 1011 then decide (2 ≤ count1009 b) else decide (1 ≤ count1011 b)) else (if i < 1013 then decide (2 ≤ count1011 b) else decide (3 ≤ count1011 b)))) else (if i < 1018 then (if i < 1016 then (if i < 1015 then decide (4 ≤ count1011 b) else decide (1 ≤ count1015 b)) else (if i < 1017 then decide (2 ≤ count1015 b) else decide (1 ≤ count1017 b))) else (if i < 1020 then (if i < 1019 then decide (2 ≤ count1017 b) else decide (1 ≤ count1019 b)) else (if i < 1021 then decide (2 ≤ count1019 b) else decide (3 ≤ count1019 b)))))) else (if i < 1037 then (if i < 1029 then (if i < 1025 then (if i < 1023 then decide (4 ≤ count1019 b) else (if i < 1024 then decide (1 ≤ count1023 b) else decide (2 ≤ count1023 b))) else (if i < 1027 then (if i < 1026 then decide (3 ≤ count1023 b) else decide (4 ≤ count1023 b)) else (if i < 1028 then decide (5 ≤ count1023 b) else decide (6 ≤ count1023 b)))) else (if i < 1033 then (if i < 1031 then (if i < 1030 then decide (7 ≤ count1023 b) else decide (8 ≤ count1023 b)) else (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b))) else (if i < 1035 then (if i < 1034 then decide (1 ≤ count1033 b) else decide (2 ≤ count1033 b)) else (if i < 1036 then decide (1 ≤ count1035 b) else decide (2 ≤ count1035 b))))) else (if i < 1044 then (if i < 1040 then (if i < 1038 then decide (3 ≤ count1035 b) else (if i < 1039 then decide (4 ≤ count1035 b) else decide (1 ≤ count1039 b))) else (if i < 1042 then (if i < 1041 then decide (2 ≤ count1039 b) else decide (1 ≤ count1041 b)) else (if i < 1043 then decide (2 ≤ count1041 b) else decide (1 ≤ count1043 b)))) else (if i < 1048 then (if i < 1046 then (if i < 1045 then decide (2 ≤ count1043 b) else decide (3 ≤ count1043 b)) else (if i < 1047 then decide (4 ≤ count1043 b) else decide (1 ≤ count1047 b))) else (if i < 1050 then (if i < 1049 then decide (2 ≤ count1047 b) else decide (3 ≤ count1047 b)) else (if i < 1051 then decide (4 ≤ count1047 b) else decide (5 ≤ count1047 b)))))))) else (if i < 1110 then (if i < 1081 then (if i < 1066 then (if i < 1059 then (if i < 1055 then (if i < 1053 then decide (6 ≤ count1047 b) else (if i < 1054 then decide (7 ≤ count1047 b) else decide (8 ≤ count1047 b))) else (if i < 1057 then (if i < 1056 then decide (1 ≤ count1055 b) else decide (2 ≤ count1055 b)) else (if i < 1058 then decide (3 ≤ count1055 b) else decide (4 ≤ count1055 b)))) else (if i < 1062 then (if i < 1060 then decide (5 ≤ count1055 b) else (if i < 1061 then decide (6 ≤ count1055 b) else decide (7 ≤ count1055 b))) else (if i < 1064 then (if i < 1063 then decide (8 ≤ count1055 b) else decide (9 ≤ count1055 b)) else (if i < 1065 then decide (10 ≤ count1055 b) else decide (11 ≤ count1055 b))))) else (if i < 1073 then (if i < 1069 then (if i < 1067 then decide (12 ≤ count1055 b) else (if i < 1068 then decide (13 ≤ count1055 b) else decide (14 ≤ count1055 b))) else (if i < 1071 then (if i < 1070 then decide (15 ≤ count1055 b) else decide (16 ≤ count1055 b)) else (if i < 1072 then decide (1 ≤ count1071 b) else decide (2 ≤ count1071 b)))) else (if i < 1077 then (if i < 1075 then (if i < 1074 then decide (1 ≤ count1073 b) else decide (2 ≤ count1073 b)) else (if i < 1076 then decide (1 ≤ count1075 b) else decide (2 ≤ count1075 b))) else (if i < 1079 then (if i < 1078 then decide (3 ≤ count1075 b) else decide (4 ≤ count1075 b)) else (if i < 1080 then decide (1 ≤ count1079 b) else decide (2 ≤ count1079 b)))))) else (if i < 1095 then (if i < 1088 then (if i < 1084 then (if i < 1082 then decide (1 ≤ count1081 b) else (if i < 1083 then decide (2 ≤ count1081 b) else decide (1 ≤ count1083 b))) else (if i < 1086 then (if i < 1085 then decide (2 ≤ count1083 b) else decide (3 ≤ count1083 b)) else (if i < 1087 then decide (4 ≤ count1083 b) else decide (1 ≤ count1087 b)))) else (if i < 1091 then (if i < 1089 then decide (2 ≤ count1087 b) else (if i < 1090 then decide (3 ≤ count1087 b) else decide (4 ≤ count1087 b))) else (if i < 1093 then (if i < 1092 then decide (5 ≤ count1087 b) else decide (6 ≤ count1087 b)) else (if i < 1094 then decide (7 ≤ count1087 b) else decide (8 ≤ count1087 b))))) else (if i < 1102 then (if i < 1098 then (if i < 1096 then decide (1 ≤ count1095 b) else (if i < 1097 then decide (2 ≤ count1095 b) else decide (1 ≤ count1097 b))) else (if i < 1100 then (if i < 1099 then decide (2 ≤ count1097 b) else decide (1 ≤ count1099 b)) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (3 ≤ count1099 b)))) else (if i < 1106 then (if i < 1104 then (if i < 1103 then decide (4 ≤ count1099 b) else decide (1 ≤ count1103 b)) else (if i < 1105 then decide (2 ≤ count1103 b) else decide (1 ≤ count1105 b))) else (if i < 1108 then (if i < 1107 then decide (2 ≤ count1105 b) else decide (1 ≤ count1107 b)) else (if i < 1109 then decide (2 ≤ count1107 b) else decide (3 ≤ count1107 b))))))) else (if i < 1139 then (if i < 1124 then (if i < 1117 then (if i < 1113 then (if i < 1111 then decide (4 ≤ count1107 b) else (if i < 1112 then decide (1 ≤ count1111 b) else decide (2 ≤ count1111 b))) else (if i < 1115 then (if i < 1114 then decide (3 ≤ count1111 b) else decide (4 ≤ count1111 b)) else (if i < 1116 then decide (5 ≤ count1111 b) else decide (6 ≤ count1111 b)))) else (if i < 1120 then (if i < 1118 then decide (7 ≤ count1111 b) else (if i < 1119 then decide (8 ≤ count1111 b) else decide (1 ≤ count1119 b))) else (if i < 1122 then (if i < 1121 then decide (2 ≤ count1119 b) else decide (3 ≤ count1119 b)) else (if i < 1123 then decide (4 ≤ count1119 b) else decide (5 ≤ count1119 b))))) else (if i < 1131 then (if i < 1127 then (if i < 1125 then decide (6 ≤ count1119 b) else (if i < 1126 then decide (7 ≤ count1119 b) else decide (8 ≤ count1119 b))) else (if i < 1129 then (if i < 1128 then decide (9 ≤ count1119 b) else decide (10 ≤ count1119 b)) else (if i < 1130 then decide (11 ≤ count1119 b) else decide (12 ≤ count1119 b)))) else (if i < 1135 then (if i < 1133 then (if i < 1132 then decide (13 ≤ count1119 b) else decide (14 ≤ count1119 b)) else (if i < 1134 then decide (15 ≤ count1119 b) else decide (16 ≤ count1119 b))) else (if i < 1137 then (if i < 1136 then decide (1 ≤ count1135 b) else decide (2 ≤ count1135 b)) else (if i < 1138 then decide (3 ≤ count1135 b) else decide (4 ≤ count1135 b)))))) else (if i < 1154 then (if i < 1146 then (if i < 1142 then (if i < 1140 then decide (5 ≤ count1135 b) else (if i < 1141 then decide (6 ≤ count1135 b) else decide (7 ≤ count1135 b))) else (if i < 1144 then (if i < 1143 then decide (8 ≤ count1135 b) else decide (9 ≤ count1135 b)) else (if i < 1145 then decide (10 ≤ count1135 b) else decide (11 ≤ count1135 b)))) else (if i < 1150 then (if i < 1148 then (if i < 1147 then decide (12 ≤ count1135 b) else decide (13 ≤ count1135 b)) else (if i < 1149 then decide (14 ≤ count1135 b) else decide (15 ≤ count1135 b))) else (if i < 1152 then (if i < 1151 then decide (16 ≤ count1135 b) else decide (17 ≤ count1135 b)) else (if i < 1153 then decide (18 ≤ count1135 b) else decide (19 ≤ count1135 b))))) else (if i < 1161 then (if i < 1157 then (if i < 1155 then decide (20 ≤ count1135 b) else (if i < 1156 then decide (21 ≤ count1135 b) else decide (22 ≤ count1135 b))) else (if i < 1159 then (if i < 1158 then decide (23 ≤ count1135 b) else decide (1 ≤ count1158 b)) else (if i < 1160 then decide (2 ≤ count1158 b) else decide (3 ≤ count1158 b)))) else (if i < 1165 then (if i < 1163 then (if i < 1162 then decide (4 ≤ count1158 b) else decide (5 ≤ count1158 b)) else (if i < 1164 then decide (6 ≤ count1158 b) else decide (7 ≤ count1158 b))) else (if i < 1167 then (if i < 1166 then decide (8 ≤ count1158 b) else decide (9 ≤ count1158 b)) else (if i < 1168 then decide (10 ≤ count1158 b) else decide (11 ≤ count1158 b))))))))) else (if i < 1286 then (if i < 1227 then (if i < 1198 then (if i < 1183 then (if i < 1176 then (if i < 1172 then (if i < 1170 then decide (12 ≤ count1158 b) else (if i < 1171 then decide (13 ≤ count1158 b) else decide (14 ≤ count1158 b))) else (if i < 1174 then (if i < 1173 then decide (15 ≤ count1158 b) else decide (16 ≤ count1158 b)) else (if i < 1175 then decide (17 ≤ count1158 b) else decide (18 ≤ count1158 b)))) else (if i < 1179 then (if i < 1177 then decide (19 ≤ count1158 b) else (if i < 1178 then decide (20 ≤ count1158 b) else decide (21 ≤ count1158 b))) else (if i < 1181 then (if i < 1180 then decide (22 ≤ count1158 b) else decide (23 ≤ count1158 b)) else (if i < 1182 then decide (1 ≤ count1181 b) else decide (2 ≤ count1181 b))))) else (if i < 1190 then (if i < 1186 then (if i < 1184 then decide (1 ≤ count1183 b) else (if i < 1185 then decide (2 ≤ count1183 b) else decide (1 ≤ count1185 b))) else (if i < 1188 then (if i < 1187 then decide (2 ≤ count1185 b) else decide (3 ≤ count1185 b)) else (if i < 1189 then decide (4 ≤ count1185 b) else decide (1 ≤ count1189 b)))) else (if i < 1194 then (if i < 1192 then (if i < 1191 then decide (2 ≤ count1189 b) else decide (1 ≤ count1191 b)) else (if i < 1193 then decide (2 ≤ count1191 b) else decide (1 ≤ count1193 b))) else (if i < 1196 then (if i < 1195 then decide (2 ≤ count1193 b) else decide (3 ≤ count1193 b)) else (if i < 1197 then decide (4 ≤ count1193 b) else decide (1 ≤ count1197 b)))))) else (if i < 1212 then (if i < 1205 then (if i < 1201 then (if i < 1199 then decide (2 ≤ count1197 b) else (if i < 1200 then decide (3 ≤ count1197 b) else decide (4 ≤ count1197 b))) else (if i < 1203 then (if i < 1202 then decide (5 ≤ count1197 b) else decide (6 ≤ count1197 b)) else (if i < 1204 then decide (7 ≤ count1197 b) else decide (8 ≤ count1197 b)))) else (if i < 1208 then (if i < 1206 then decide (1 ≤ count1205 b) else (if i < 1207 then decide (2 ≤ count1205 b) else decide (1 ≤ count1207 b))) else (if i < 1210 then (if i < 1209 then decide (2 ≤ count1207 b) else decide (1 ≤ count1209 b)) else (if i < 1211 then decide (2 ≤ count1209 b) else decide (3 ≤ count1209 b))))) else (if i < 1219 then (if i < 1215 then (if i < 1213 then decide (4 ≤ count1209 b) else (if i < 1214 then decide (1 ≤ count1213 b) else decide (2 ≤ count1213 b))) else (if i < 1217 then (if i < 1216 then decide (1 ≤ count1215 b) else decide (2 ≤ count1215 b)) else (if i < 1218 then decide (1 ≤ count1217 b) else decide (2 ≤ count1217 b)))) else (if i < 1223 then (if i < 1221 then (if i < 1220 then decide (3 ≤ count1217 b) else decide (4 ≤ count1217 b)) else (if i < 1222 then decide (1 ≤ count1221 b) else decide (2 ≤ count1221 b))) else (if i < 1225 then (if i < 1224 then decide (3 ≤ count1221 b) else decide (4 ≤ count1221 b)) else (if i < 1226 then decide (5 ≤ count1221 b) else decide (6 ≤ count1221 b))))))) else (if i < 1256 then (if i < 1241 then (if i < 1234 then (if i < 1230 then (if i < 1228 then decide (7 ≤ count1221 b) else (if i < 1229 then decide (8 ≤ count1221 b) else decide (1 ≤ count1229 b))) else (if i < 1232 then (if i < 1231 then decide (2 ≤ count1229 b) else decide (3 ≤ count1229 b)) else (if i < 1233 then decide (4 ≤ count1229 b) else decide (5 ≤ count1229 b)))) else (if i < 1237 then (if i < 1235 then decide (6 ≤ count1229 b) else (if i < 1236 then decide (7 ≤ count1229 b) else decide (8 ≤ count1229 b))) else (if i < 1239 then (if i < 1238 then decide (9 ≤ count1229 b) else decide (10 ≤ count1229 b)) else (if i < 1240 then decide (11 ≤ count1229 b) else decide (12 ≤ count1229 b))))) else (if i < 1248 then (if i < 1244 then (if i < 1242 then decide (13 ≤ count1229 b) else (if i < 1243 then decide (14 ≤ count1229 b) else decide (15 ≤ count1229 b))) else (if i < 1246 then (if i < 1245 then decide (16 ≤ count1229 b) else decide (1 ≤ count1245 b)) else (if i < 1247 then decide (2 ≤ count1245 b) else decide (1 ≤ count1247 b)))) else (if i < 1252 then (if i < 1250 then (if i < 1249 then decide (2 ≤ count1247 b) else decide (1 ≤ count1249 b)) else (if i < 1251 then decide (2 ≤ count1249 b) else decide (3 ≤ count1249 b))) else (if i < 1254 then (if i < 1253 then decide (4 ≤ count1249 b) else decide (1 ≤ count1253 b)) else (if i < 1255 then decide (2 ≤ count1253 b) else decide (1 ≤ count1255 b)))))) else (if i < 1271 then (if i < 1263 then (if i < 1259 then (if i < 1257 then decide (2 ≤ count1255 b) else (if i < 1258 then decide (1 ≤ count1257 b) else decide (2 ≤ count1257 b))) else (if i < 1261 then (if i < 1260 then decide (3 ≤ count1257 b) else decide (4 ≤ count1257 b)) else (if i < 1262 then decide (1 ≤ count1261 b) else decide (2 ≤ count1261 b)))) else (if i < 1267 then (if i < 1265 then (if i < 1264 then decide (3 ≤ count1261 b) else decide (4 ≤ count1261 b)) else (if i < 1266 then decide (5 ≤ count1261 b) else decide (6 ≤ count1261 b))) else (if i < 1269 then (if i < 1268 then decide (7 ≤ count1261 b) else decide (8 ≤ count1261 b)) else (if i < 1270 then decide (1 ≤ count1269 b) else decide (2 ≤ count1269 b))))) else (if i < 1278 then (if i < 1274 then (if i < 1272 then decide (1 ≤ count1271 b) else (if i < 1273 then decide (2 ≤ count1271 b) else decide (1 ≤ count1273 b))) else (if i < 1276 then (if i < 1275 then decide (2 ≤ count1273 b) else decide (3 ≤ count1273 b)) else (if i < 1277 then decide (4 ≤ count1273 b) else decide (1 ≤ count1277 b)))) else (if i < 1282 then (if i < 1280 then (if i < 1279 then decide (2 ≤ count1277 b) else decide (1 ≤ count1279 b)) else (if i < 1281 then decide (2 ≤ count1279 b) else decide (1 ≤ count1281 b))) else (if i < 1284 then (if i < 1283 then decide (2 ≤ count1281 b) else decide (3 ≤ count1281 b)) else (if i < 1285 then decide (4 ≤ count1281 b) else decide (1 ≤ count1285 b)))))))) else (if i < 1344 then (if i < 1315 then (if i < 1300 then (if i < 1293 then (if i < 1289 then (if i < 1287 then decide (2 ≤ count1285 b) else (if i < 1288 then decide (3 ≤ count1285 b) else decide (4 ≤ count1285 b))) else (if i < 1291 then (if i < 1290 then decide (5 ≤ count1285 b) else decide (6 ≤ count1285 b)) else (if i < 1292 then decide (7 ≤ count1285 b) else decide (8 ≤ count1285 b)))) else (if i < 1296 then (if i < 1294 then decide (1 ≤ count1293 b) else (if i < 1295 then decide (2 ≤ count1293 b) else decide (3 ≤ count1293 b))) else (if i < 1298 then (if i < 1297 then decide (4 ≤ count1293 b) else decide (5 ≤ count1293 b)) else (if i < 1299 then decide (6 ≤ count1293 b) else decide (7 ≤ count1293 b))))) else (if i < 1307 then (if i < 1303 then (if i < 1301 then decide (8 ≤ count1293 b) else (if i < 1302 then decide (9 ≤ count1293 b) else decide (10 ≤ count1293 b))) else (if i < 1305 then (if i < 1304 then decide (11 ≤ count1293 b) else decide (12 ≤ count1293 b)) else (if i < 1306 then decide (13 ≤ count1293 b) else decide (14 ≤ count1293 b)))) else (if i < 1311 then (if i < 1309 then (if i < 1308 then decide (15 ≤ count1293 b) else decide (16 ≤ count1293 b)) else (if i < 1310 then decide (1 ≤ count1309 b) else decide (2 ≤ count1309 b))) else (if i < 1313 then (if i < 1312 then decide (3 ≤ count1309 b) else decide (4 ≤ count1309 b)) else (if i < 1314 then decide (5 ≤ count1309 b) else decide (6 ≤ count1309 b)))))) else (if i < 1329 then (if i < 1322 then (if i < 1318 then (if i < 1316 then decide (7 ≤ count1309 b) else (if i < 1317 then decide (8 ≤ count1309 b) else decide (9 ≤ count1309 b))) else (if i < 1320 then (if i < 1319 then decide (10 ≤ count1309 b) else decide (11 ≤ count1309 b)) else (if i < 1321 then decide (12 ≤ count1309 b) else decide (13 ≤ count1309 b)))) else (if i < 1325 then (if i < 1323 then decide (14 ≤ count1309 b) else (if i < 1324 then decide (15 ≤ count1309 b) else decide (16 ≤ count1309 b))) else (if i < 1327 then (if i < 1326 then decide (17 ≤ count1309 b) else decide (18 ≤ count1309 b)) else (if i < 1328 then decide (19 ≤ count1309 b) else decide (20 ≤ count1309 b))))) else (if i < 1336 then (if i < 1332 then (if i < 1330 then decide (21 ≤ count1309 b) else (if i < 1331 then decide (22 ≤ count1309 b) else decide (23 ≤ count1309 b))) else (if i < 1334 then (if i < 1333 then decide (24 ≤ count1309 b) else decide (25 ≤ count1309 b)) else (if i < 1335 then decide (26 ≤ count1309 b) else decide (27 ≤ count1309 b)))) else (if i < 1340 then (if i < 1338 then (if i < 1337 then decide (28 ≤ count1309 b) else decide (29 ≤ count1309 b)) else (if i < 1339 then decide (30 ≤ count1309 b) else decide (31 ≤ count1309 b))) else (if i < 1342 then (if i < 1341 then decide (32 ≤ count1309 b) else decide (1 ≤ count1341 b)) else (if i < 1343 then decide (2 ≤ count1341 b) else decide (1 ≤ count1343 b))))))) else (if i < 1373 then (if i < 1358 then (if i < 1351 then (if i < 1347 then (if i < 1345 then decide (2 ≤ count1343 b) else (if i < 1346 then decide (1 ≤ count1345 b) else decide (2 ≤ count1345 b))) else (if i < 1349 then (if i < 1348 then decide (3 ≤ count1345 b) else decide (4 ≤ count1345 b)) else (if i < 1350 then decide (1 ≤ count1349 b) else decide (2 ≤ count1349 b)))) else (if i < 1354 then (if i < 1352 then decide (1 ≤ count1351 b) else (if i < 1353 then decide (2 ≤ count1351 b) else decide (1 ≤ count1353 b))) else (if i < 1356 then (if i < 1355 then decide (2 ≤ count1353 b) else decide (3 ≤ count1353 b)) else (if i < 1357 then decide (4 ≤ count1353 b) else decide (1 ≤ count1357 b))))) else (if i < 1365 then (if i < 1361 then (if i < 1359 then decide (2 ≤ count1357 b) else (if i < 1360 then decide (3 ≤ count1357 b) else decide (4 ≤ count1357 b))) else (if i < 1363 then (if i < 1362 then decide (5 ≤ count1357 b) else decide (6 ≤ count1357 b)) else (if i < 1364 then decide (7 ≤ count1357 b) else decide (8 ≤ count1357 b)))) else (if i < 1369 then (if i < 1367 then (if i < 1366 then decide (1 ≤ count1365 b) else decide (2 ≤ count1365 b)) else (if i < 1368 then decide (1 ≤ count1367 b) else decide (2 ≤ count1367 b))) else (if i < 1371 then (if i < 1370 then decide (1 ≤ count1369 b) else decide (2 ≤ count1369 b)) else (if i < 1372 then decide (3 ≤ count1369 b) else decide (4 ≤ count1369 b)))))) else (if i < 1388 then (if i < 1380 then (if i < 1376 then (if i < 1374 then decide (1 ≤ count1373 b) else (if i < 1375 then decide (2 ≤ count1373 b) else decide (1 ≤ count1375 b))) else (if i < 1378 then (if i < 1377 then decide (2 ≤ count1375 b) else decide (1 ≤ count1377 b)) else (if i < 1379 then decide (2 ≤ count1377 b) else decide (3 ≤ count1377 b)))) else (if i < 1384 then (if i < 1382 then (if i < 1381 then decide (4 ≤ count1377 b) else decide (1 ≤ count1381 b)) else (if i < 1383 then decide (2 ≤ count1381 b) else decide (3 ≤ count1381 b))) else (if i < 1386 then (if i < 1385 then decide (4 ≤ count1381 b) else decide (5 ≤ count1381 b)) else (if i < 1387 then decide (6 ≤ count1381 b) else decide (7 ≤ count1381 b))))) else (if i < 1395 then (if i < 1391 then (if i < 1389 then decide (8 ≤ count1381 b) else (if i < 1390 then decide (1 ≤ count1389 b) else decide (2 ≤ count1389 b))) else (if i < 1393 then (if i < 1392 then decide (3 ≤ count1389 b) else decide (4 ≤ count1389 b)) else (if i < 1394 then decide (5 ≤ count1389 b) else decide (6 ≤ count1389 b)))) else (if i < 1399 then (if i < 1397 then (if i < 1396 then decide (7 ≤ count1389 b) else decide (8 ≤ count1389 b)) else (if i < 1398 then decide (9 ≤ count1389 b) else decide (10 ≤ count1389 b))) else (if i < 1401 then (if i < 1400 then decide (11 ≤ count1389 b) else decide (12 ≤ count1389 b)) else (if i < 1402 then decide (13 ≤ count1389 b) else decide (14 ≤ count1389 b)))))))))) else (if i < 1637 then (if i < 1520 then (if i < 1461 then (if i < 1432 then (if i < 1417 then (if i < 1410 then (if i < 1406 then (if i < 1404 then decide (15 ≤ count1389 b) else (if i < 1405 then decide (16 ≤ count1389 b) else decide (1 ≤ count1405 b))) else (if i < 1408 then (if i < 1407 then decide (2 ≤ count1405 b) else decide (1 ≤ count1407 b)) else (if i < 1409 then decide (2 ≤ count1407 b) else decide (1 ≤ count1409 b)))) else (if i < 1413 then (if i < 1411 then decide (2 ≤ count1409 b) else (if i < 1412 then decide (3 ≤ count1409 b) else decide (4 ≤ count1409 b))) else (if i < 1415 then (if i < 1414 then decide (1 ≤ count1413 b) else decide (2 ≤ count1413 b)) else (if i < 1416 then decide (1 ≤ count1415 b) else decide (2 ≤ count1415 b))))) else (if i < 1424 then (if i < 1420 then (if i < 1418 then decide (1 ≤ count1417 b) else (if i < 1419 then decide (2 ≤ count1417 b) else decide (3 ≤ count1417 b))) else (if i < 1422 then (if i < 1421 then decide (4 ≤ count1417 b) else decide (1 ≤ count1421 b)) else (if i < 1423 then decide (2 ≤ count1421 b) else decide (3 ≤ count1421 b)))) else (if i < 1428 then (if i < 1426 then (if i < 1425 then decide (4 ≤ count1421 b) else decide (5 ≤ count1421 b)) else (if i < 1427 then decide (6 ≤ count1421 b) else decide (7 ≤ count1421 b))) else (if i < 1430 then (if i < 1429 then decide (8 ≤ count1421 b) else decide (1 ≤ count1429 b)) else (if i < 1431 then decide (2 ≤ count1429 b) else decide (1 ≤ count1431 b)))))) else (if i < 1446 then (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (2 ≤ count1431 b) else (if i < 1434 then decide (1 ≤ count1433 b) else decide (2 ≤ count1433 b))) else (if i < 1437 then (if i < 1436 then decide (3 ≤ count1433 b) else decide (4 ≤ count1433 b)) else (if i < 1438 then decide (1 ≤ count1437 b) else decide (2 ≤ count1437 b)))) else (if i < 1442 then (if i < 1440 then decide (1 ≤ count1439 b) else (if i < 1441 then decide (2 ≤ count1439 b) else decide (1 ≤ count1441 b))) else (if i < 1444 then (if i < 1443 then decide (2 ≤ count1441 b) else decide (3 ≤ count1441 b)) else (if i < 1445 then decide (4 ≤ count1441 b) else decide (1 ≤ count1445 b))))) else (if i < 1453 then (if i < 1449 then (if i < 1447 then decide (2 ≤ count1445 b) else (if i < 1448 then decide (3 ≤ count1445 b) else decide (4 ≤ count1445 b))) else (if i < 1451 then (if i < 1450 then decide (5 ≤ count1445 b) else decide (6 ≤ count1445 b)) else (if i < 1452 then decide (7 ≤ count1445 b) else decide (8 ≤ count1445 b)))) else (if i < 1457 then (if i < 1455 then (if i < 1454 then decide (1 ≤ count1453 b) else decide (2 ≤ count1453 b)) else (if i < 1456 then decide (3 ≤ count1453 b) else decide (4 ≤ count1453 b))) else (if i < 1459 then (if i < 1458 then decide (5 ≤ count1453 b) else decide (6 ≤ count1453 b)) else (if i < 1460 then decide (7 ≤ count1453 b) else decide (8 ≤ count1453 b))))))) else (if i < 1490 then (if i < 1475 then (if i < 1468 then (if i < 1464 then (if i < 1462 then decide (9 ≤ count1453 b) else (if i < 1463 then decide (10 ≤ count1453 b) else decide (11 ≤ count1453 b))) else (if i < 1466 then (if i < 1465 then decide (12 ≤ count1453 b) else decide (13 ≤ count1453 b)) else (if i < 1467 then decide (14 ≤ count1453 b) else decide (15 ≤ count1453 b)))) else (if i < 1471 then (if i < 1469 then decide (16 ≤ count1453 b) else (if i < 1470 then decide (1 ≤ count1469 b) else decide (2 ≤ count1469 b))) else (if i < 1473 then (if i < 1472 then decide (3 ≤ count1469 b) else decide (4 ≤ count1469 b)) else (if i < 1474 then decide (5 ≤ count1469 b) else decide (6 ≤ count1469 b))))) else (if i < 1482 then (if i < 1478 then (if i < 1476 then decide (7 ≤ count1469 b) else (if i < 1477 then decide (8 ≤ count1469 b) else decide (9 ≤ count1469 b))) else (if i < 1480 then (if i < 1479 then decide (10 ≤ count1469 b) else decide (11 ≤ count1469 b)) else (if i < 1481 then decide (12 ≤ count1469 b) else decide (13 ≤ count1469 b)))) else (if i < 1486 then (if i < 1484 then (if i < 1483 then decide (14 ≤ count1469 b) else decide (15 ≤ count1469 b)) else (if i < 1485 then decide (16 ≤ count1469 b) else decide (17 ≤ count1469 b))) else (if i < 1488 then (if i < 1487 then decide (18 ≤ count1469 b) else decide (19 ≤ count1469 b)) else (if i < 1489 then decide (20 ≤ count1469 b) else decide (21 ≤ count1469 b)))))) else (if i < 1505 then (if i < 1497 then (if i < 1493 then (if i < 1491 then decide (22 ≤ count1469 b) else (if i < 1492 then decide (23 ≤ count1469 b) else decide (24 ≤ count1469 b))) else (if i < 1495 then (if i < 1494 then decide (25 ≤ count1469 b) else decide (26 ≤ count1469 b)) else (if i < 1496 then decide (27 ≤ count1469 b) else decide (28 ≤ count1469 b)))) else (if i < 1501 then (if i < 1499 then (if i < 1498 then decide (29 ≤ count1469 b) else decide (30 ≤ count1469 b)) else (if i < 1500 then decide (31 ≤ count1469 b) else decide (32 ≤ count1469 b))) else (if i < 1503 then (if i < 1502 then decide (1 ≤ count1501 b) else decide (2 ≤ count1501 b)) else (if i < 1504 then decide (3 ≤ count1501 b) else decide (4 ≤ count1501 b))))) else (if i < 1512 then (if i < 1508 then (if i < 1506 then decide (5 ≤ count1501 b) else (if i < 1507 then decide (6 ≤ count1501 b) else decide (7 ≤ count1501 b))) else (if i < 1510 then (if i < 1509 then decide (8 ≤ count1501 b) else decide (9 ≤ count1501 b)) else (if i < 1511 then decide (10 ≤ count1501 b) else decide (11 ≤ count1501 b)))) else (if i < 1516 then (if i < 1514 then (if i < 1513 then decide (12 ≤ count1501 b) else decide (13 ≤ count1501 b)) else (if i < 1515 then decide (14 ≤ count1501 b) else decide (15 ≤ count1501 b))) else (if i < 1518 then (if i < 1517 then decide (16 ≤ count1501 b) else decide (17 ≤ count1501 b)) else (if i < 1519 then decide (18 ≤ count1501 b) else decide (19 ≤ count1501 b)))))))) else (if i < 1578 then (if i < 1549 then (if i < 1534 then (if i < 1527 then (if i < 1523 then (if i < 1521 then decide (20 ≤ count1501 b) else (if i < 1522 then decide (21 ≤ count1501 b) else decide (22 ≤ count1501 b))) else (if i < 1525 then (if i < 1524 then decide (23 ≤ count1501 b) else decide (24 ≤ count1501 b)) else (if i < 1526 then decide (25 ≤ count1501 b) else decide (26 ≤ count1501 b)))) else (if i < 1530 then (if i < 1528 then decide (27 ≤ count1501 b) else (if i < 1529 then decide (28 ≤ count1501 b) else decide (29 ≤ count1501 b))) else (if i < 1532 then (if i < 1531 then decide (30 ≤ count1501 b) else decide (31 ≤ count1501 b)) else (if i < 1533 then decide (32 ≤ count1501 b) else decide (33 ≤ count1501 b))))) else (if i < 1541 then (if i < 1537 then (if i < 1535 then decide (34 ≤ count1501 b) else (if i < 1536 then decide (35 ≤ count1501 b) else decide (36 ≤ count1501 b))) else (if i < 1539 then (if i < 1538 then decide (37 ≤ count1501 b) else decide (38 ≤ count1501 b)) else (if i < 1540 then decide (39 ≤ count1501 b) else decide (40 ≤ count1501 b)))) else (if i < 1545 then (if i < 1543 then (if i < 1542 then decide (41 ≤ count1501 b) else decide (42 ≤ count1501 b)) else (if i < 1544 then decide (1 ≤ count1543 b) else decide (2 ≤ count1543 b))) else (if i < 1547 then (if i < 1546 then decide (1 ≤ count1545 b) else decide (2 ≤ count1545 b)) else (if i < 1548 then decide (1 ≤ count1547 b) else decide (2 ≤ count1547 b)))))) else (if i < 1563 then (if i < 1556 then (if i < 1552 then (if i < 1550 then decide (3 ≤ count1547 b) else (if i < 1551 then decide (4 ≤ count1547 b) else decide (1 ≤ count1551 b))) else (if i < 1554 then (if i < 1553 then decide (2 ≤ count1551 b) else decide (1 ≤ count1553 b)) else (if i < 1555 then decide (2 ≤ count1553 b) else decide (1 ≤ count1555 b)))) else (if i < 1559 then (if i < 1557 then decide (2 ≤ count1555 b) else (if i < 1558 then decide (3 ≤ count1555 b) else decide (4 ≤ count1555 b))) else (if i < 1561 then (if i < 1560 then decide (1 ≤ count1559 b) else decide (2 ≤ count1559 b)) else (if i < 1562 then decide (3 ≤ count1559 b) else decide (4 ≤ count1559 b))))) else (if i < 1570 then (if i < 1566 then (if i < 1564 then decide (5 ≤ count1559 b) else (if i < 1565 then decide (6 ≤ count1559 b) else decide (7 ≤ count1559 b))) else (if i < 1568 then (if i < 1567 then decide (8 ≤ count1559 b) else decide (1 ≤ count1567 b)) else (if i < 1569 then decide (2 ≤ count1567 b) else decide (1 ≤ count1569 b)))) else (if i < 1574 then (if i < 1572 then (if i < 1571 then decide (2 ≤ count1569 b) else decide (1 ≤ count1571 b)) else (if i < 1573 then decide (2 ≤ count1571 b) else decide (3 ≤ count1571 b))) else (if i < 1576 then (if i < 1575 then decide (4 ≤ count1571 b) else decide (1 ≤ count1575 b)) else (if i < 1577 then decide (2 ≤ count1575 b) else decide (1 ≤ count1577 b))))))) else (if i < 1607 then (if i < 1592 then (if i < 1585 then (if i < 1581 then (if i < 1579 then decide (2 ≤ count1577 b) else (if i < 1580 then decide (1 ≤ count1579 b) else decide (2 ≤ count1579 b))) else (if i < 1583 then (if i < 1582 then decide (3 ≤ count1579 b) else decide (4 ≤ count1579 b)) else (if i < 1584 then decide (1 ≤ count1583 b) else decide (2 ≤ count1583 b)))) else (if i < 1588 then (if i < 1586 then decide (3 ≤ count1583 b) else (if i < 1587 then decide (4 ≤ count1583 b) else decide (5 ≤ count1583 b))) else (if i < 1590 then (if i < 1589 then decide (6 ≤ count1583 b) else decide (7 ≤ count1583 b)) else (if i < 1591 then decide (8 ≤ count1583 b) else decide (1 ≤ count1591 b))))) else (if i < 1599 then (if i < 1595 then (if i < 1593 then decide (2 ≤ count1591 b) else (if i < 1594 then decide (3 ≤ count1591 b) else decide (4 ≤ count1591 b))) else (if i < 1597 then (if i < 1596 then decide (5 ≤ count1591 b) else decide (6 ≤ count1591 b)) else (if i < 1598 then decide (7 ≤ count1591 b) else decide (8 ≤ count1591 b)))) else (if i < 1603 then (if i < 1601 then (if i < 1600 then decide (9 ≤ count1591 b) else decide (10 ≤ count1591 b)) else (if i < 1602 then decide (11 ≤ count1591 b) else decide (12 ≤ count1591 b))) else (if i < 1605 then (if i < 1604 then decide (13 ≤ count1591 b) else decide (14 ≤ count1591 b)) else (if i < 1606 then decide (15 ≤ count1591 b) else decide (16 ≤ count1591 b)))))) else (if i < 1622 then (if i < 1614 then (if i < 1610 then (if i < 1608 then decide (1 ≤ count1607 b) else (if i < 1609 then decide (2 ≤ count1607 b) else decide (1 ≤ count1609 b))) else (if i < 1612 then (if i < 1611 then decide (2 ≤ count1609 b) else decide (1 ≤ count1611 b)) else (if i < 1613 then decide (2 ≤ count1611 b) else decide (3 ≤ count1611 b)))) else (if i < 1618 then (if i < 1616 then (if i < 1615 then decide (4 ≤ count1611 b) else decide (1 ≤ count1615 b)) else (if i < 1617 then decide (2 ≤ count1615 b) else decide (1 ≤ count1617 b))) else (if i < 1620 then (if i < 1619 then decide (2 ≤ count1617 b) else decide (1 ≤ count1619 b)) else (if i < 1621 then decide (2 ≤ count1619 b) else decide (3 ≤ count1619 b))))) else (if i < 1629 then (if i < 1625 then (if i < 1623 then decide (4 ≤ count1619 b) else (if i < 1624 then decide (1 ≤ count1623 b) else decide (2 ≤ count1623 b))) else (if i < 1627 then (if i < 1626 then decide (3 ≤ count1623 b) else decide (4 ≤ count1623 b)) else (if i < 1628 then decide (5 ≤ count1623 b) else decide (6 ≤ count1623 b)))) else (if i < 1633 then (if i < 1631 then (if i < 1630 then decide (7 ≤ count1623 b) else decide (8 ≤ count1623 b)) else (if i < 1632 then decide (1 ≤ count1631 b) else decide (2 ≤ count1631 b))) else (if i < 1635 then (if i < 1634 then decide (1 ≤ count1633 b) else decide (2 ≤ count1633 b)) else (if i < 1636 then decide (1 ≤ count1635 b) else decide (2 ≤ count1635 b))))))))) else (if i < 1754 then (if i < 1695 then (if i < 1666 then (if i < 1651 then (if i < 1644 then (if i < 1640 then (if i < 1638 then decide (3 ≤ count1635 b) else (if i < 1639 then decide (4 ≤ count1635 b) else decide (1 ≤ count1639 b))) else (if i < 1642 then (if i < 1641 then decide (2 ≤ count1639 b) else decide (1 ≤ count1641 b)) else (if i < 1643 then decide (2 ≤ count1641 b) else decide (1 ≤ count1643 b)))) else (if i < 1647 then (if i < 1645 then decide (2 ≤ count1643 b) else (if i < 1646 then decide (3 ≤ count1643 b) else decide (4 ≤ count1643 b))) else (if i < 1649 then (if i < 1648 then decide (1 ≤ count1647 b) else decide (2 ≤ count1647 b)) else (if i < 1650 then decide (3 ≤ count1647 b) else decide (4 ≤ count1647 b))))) else (if i < 1658 then (if i < 1654 then (if i < 1652 then decide (5 ≤ count1647 b) else (if i < 1653 then decide (6 ≤ count1647 b) else decide (7 ≤ count1647 b))) else (if i < 1656 then (if i < 1655 then decide (8 ≤ count1647 b) else decide (1 ≤ count1655 b)) else (if i < 1657 then decide (2 ≤ count1655 b) else decide (3 ≤ count1655 b)))) else (if i < 1662 then (if i < 1660 then (if i < 1659 then decide (4 ≤ count1655 b) else decide (5 ≤ count1655 b)) else (if i < 1661 then decide (6 ≤ count1655 b) else decide (7 ≤ count1655 b))) else (if i < 1664 then (if i < 1663 then decide (8 ≤ count1655 b) else decide (9 ≤ count1655 b)) else (if i < 1665 then decide (10 ≤ count1655 b) else decide (11 ≤ count1655 b)))))) else (if i < 1680 then (if i < 1673 then (if i < 1669 then (if i < 1667 then decide (12 ≤ count1655 b) else (if i < 1668 then decide (13 ≤ count1655 b) else decide (14 ≤ count1655 b))) else (if i < 1671 then (if i < 1670 then decide (15 ≤ count1655 b) else decide (16 ≤ count1655 b)) else (if i < 1672 then decide (1 ≤ count1671 b) else decide (2 ≤ count1671 b)))) else (if i < 1676 then (if i < 1674 then decide (3 ≤ count1671 b) else (if i < 1675 then decide (4 ≤ count1671 b) else decide (5 ≤ count1671 b))) else (if i < 1678 then (if i < 1677 then decide (6 ≤ count1671 b) else decide (7 ≤ count1671 b)) else (if i < 1679 then decide (8 ≤ count1671 b) else decide (9 ≤ count1671 b))))) else (if i < 1687 then (if i < 1683 then (if i < 1681 then decide (10 ≤ count1671 b) else (if i < 1682 then decide (11 ≤ count1671 b) else decide (12 ≤ count1671 b))) else (if i < 1685 then (if i < 1684 then decide (13 ≤ count1671 b) else decide (14 ≤ count1671 b)) else (if i < 1686 then decide (15 ≤ count1671 b) else decide (16 ≤ count1671 b)))) else (if i < 1691 then (if i < 1689 then (if i < 1688 then decide (17 ≤ count1671 b) else decide (18 ≤ count1671 b)) else (if i < 1690 then decide (19 ≤ count1671 b) else decide (20 ≤ count1671 b))) else (if i < 1693 then (if i < 1692 then decide (21 ≤ count1671 b) else decide (22 ≤ count1671 b)) else (if i < 1694 then decide (23 ≤ count1671 b) else decide (24 ≤ count1671 b))))))) else (if i < 1724 then (if i < 1709 then (if i < 1702 then (if i < 1698 then (if i < 1696 then decide (1 ≤ count1695 b) else (if i < 1697 then decide (2 ≤ count1695 b) else decide (1 ≤ count1697 b))) else (if i < 1700 then (if i < 1699 then decide (2 ≤ count1697 b) else decide (1 ≤ count1699 b)) else (if i < 1701 then decide (2 ≤ count1699 b) else decide (3 ≤ count1699 b)))) else (if i < 1705 then (if i < 1703 then decide (4 ≤ count1699 b) else (if i < 1704 then decide (1 ≤ count1703 b) else decide (2 ≤ count1703 b))) else (if i < 1707 then (if i < 1706 then decide (1 ≤ count1705 b) else decide (2 ≤ count1705 b)) else (if i < 1708 then decide (1 ≤ count1707 b) else decide (2 ≤ count1707 b))))) else (if i < 1716 then (if i < 1712 then (if i < 1710 then decide (3 ≤ count1707 b) else (if i < 1711 then decide (4 ≤ count1707 b) else decide (1 ≤ count1711 b))) else (if i < 1714 then (if i < 1713 then decide (2 ≤ count1711 b) else decide (3 ≤ count1711 b)) else (if i < 1715 then decide (4 ≤ count1711 b) else decide (5 ≤ count1711 b)))) else (if i < 1720 then (if i < 1718 then (if i < 1717 then decide (6 ≤ count1711 b) else decide (7 ≤ count1711 b)) else (if i < 1719 then decide (8 ≤ count1711 b) else decide (1 ≤ count1719 b))) else (if i < 1722 then (if i < 1721 then decide (2 ≤ count1719 b) else decide (1 ≤ count1721 b)) else (if i < 1723 then decide (2 ≤ count1721 b) else decide (1 ≤ count1723 b)))))) else (if i < 1739 then (if i < 1731 then (if i < 1727 then (if i < 1725 then decide (2 ≤ count1723 b) else (if i < 1726 then decide (3 ≤ count1723 b) else decide (4 ≤ count1723 b))) else (if i < 1729 then (if i < 1728 then decide (1 ≤ count1727 b) else decide (2 ≤ count1727 b)) else (if i < 1730 then decide (1 ≤ count1729 b) else decide (2 ≤ count1729 b)))) else (if i < 1735 then (if i < 1733 then (if i < 1732 then decide (1 ≤ count1731 b) else decide (2 ≤ count1731 b)) else (if i < 1734 then decide (3 ≤ count1731 b) else decide (4 ≤ count1731 b))) else (if i < 1737 then (if i < 1736 then decide (1 ≤ count1735 b) else decide (2 ≤ count1735 b)) else (if i < 1738 then decide (3 ≤ count1735 b) else decide (4 ≤ count1735 b))))) else (if i < 1746 then (if i < 1742 then (if i < 1740 then decide (5 ≤ count1735 b) else (if i < 1741 then decide (6 ≤ count1735 b) else decide (7 ≤ count1735 b))) else (if i < 1744 then (if i < 1743 then decide (8 ≤ count1735 b) else decide (1 ≤ count1743 b)) else (if i < 1745 then decide (2 ≤ count1743 b) else decide (3 ≤ count1743 b)))) else (if i < 1750 then (if i < 1748 then (if i < 1747 then decide (4 ≤ count1743 b) else decide (5 ≤ count1743 b)) else (if i < 1749 then decide (6 ≤ count1743 b) else decide (7 ≤ count1743 b))) else (if i < 1752 then (if i < 1751 then decide (8 ≤ count1743 b) else decide (9 ≤ count1743 b)) else (if i < 1753 then decide (10 ≤ count1743 b) else decide (11 ≤ count1743 b)))))))) else (if i < 1812 then (if i < 1783 then (if i < 1768 then (if i < 1761 then (if i < 1757 then (if i < 1755 then decide (12 ≤ count1743 b) else (if i < 1756 then decide (13 ≤ count1743 b) else decide (14 ≤ count1743 b))) else (if i < 1759 then (if i < 1758 then decide (15 ≤ count1743 b) else decide (16 ≤ count1743 b)) else (if i < 1760 then decide (1 ≤ count1759 b) else decide (2 ≤ count1759 b)))) else (if i < 1764 then (if i < 1762 then decide (1 ≤ count1761 b) else (if i < 1763 then decide (2 ≤ count1761 b) else decide (1 ≤ count1763 b))) else (if i < 1766 then (if i < 1765 then decide (2 ≤ count1763 b) else decide (3 ≤ count1763 b)) else (if i < 1767 then decide (4 ≤ count1763 b) else decide (1 ≤ count1767 b))))) else (if i < 1775 then (if i < 1771 then (if i < 1769 then decide (2 ≤ count1767 b) else (if i < 1770 then decide (1 ≤ count1769 b) else decide (2 ≤ count1769 b))) else (if i < 1773 then (if i < 1772 then decide (1 ≤ count1771 b) else decide (2 ≤ count1771 b)) else (if i < 1774 then decide (3 ≤ count1771 b) else decide (4 ≤ count1771 b)))) else (if i < 1779 then (if i < 1777 then (if i < 1776 then decide (1 ≤ count1775 b) else decide (2 ≤ count1775 b)) else (if i < 1778 then decide (3 ≤ count1775 b) else decide (4 ≤ count1775 b))) else (if i < 1781 then (if i < 1780 then decide (5 ≤ count1775 b) else decide (6 ≤ count1775 b)) else (if i < 1782 then decide (7 ≤ count1775 b) else decide (8 ≤ count1775 b)))))) else (if i < 1797 then (if i < 1790 then (if i < 1786 then (if i < 1784 then decide (1 ≤ count1783 b) else (if i < 1785 then decide (2 ≤ count1783 b) else decide (1 ≤ count1785 b))) else (if i < 1788 then (if i < 1787 then decide (2 ≤ count1785 b) else decide (1 ≤ count1787 b)) else (if i < 1789 then decide (2 ≤ count1787 b) else decide (3 ≤ count1787 b)))) else (if i < 1793 then (if i < 1791 then decide (4 ≤ count1787 b) else (if i < 1792 then decide (1 ≤ count1791 b) else decide (2 ≤ count1791 b))) else (if i < 1795 then (if i < 1794 then decide (1 ≤ count1793 b) else decide (2 ≤ count1793 b)) else (if i < 1796 then decide (1 ≤ count1795 b) else decide (2 ≤ count1795 b))))) else (if i < 1804 then (if i < 1800 then (if i < 1798 then decide (3 ≤ count1795 b) else (if i < 1799 then decide (4 ≤ count1795 b) else decide (1 ≤ count1799 b))) else (if i < 1802 then (if i < 1801 then decide (2 ≤ count1799 b) else decide (3 ≤ count1799 b)) else (if i < 1803 then decide (4 ≤ count1799 b) else decide (5 ≤ count1799 b)))) else (if i < 1808 then (if i < 1806 then (if i < 1805 then decide (6 ≤ count1799 b) else decide (7 ≤ count1799 b)) else (if i < 1807 then decide (8 ≤ count1799 b) else decide (1 ≤ count1807 b))) else (if i < 1810 then (if i < 1809 then decide (2 ≤ count1807 b) else decide (3 ≤ count1807 b)) else (if i < 1811 then decide (4 ≤ count1807 b) else decide (5 ≤ count1807 b))))))) else (if i < 1841 then (if i < 1826 then (if i < 1819 then (if i < 1815 then (if i < 1813 then decide (6 ≤ count1807 b) else (if i < 1814 then decide (7 ≤ count1807 b) else decide (8 ≤ count1807 b))) else (if i < 1817 then (if i < 1816 then decide (9 ≤ count1807 b) else decide (10 ≤ count1807 b)) else (if i < 1818 then decide (11 ≤ count1807 b) else decide (12 ≤ count1807 b)))) else (if i < 1822 then (if i < 1820 then decide (13 ≤ count1807 b) else (if i < 1821 then decide (14 ≤ count1807 b) else decide (15 ≤ count1807 b))) else (if i < 1824 then (if i < 1823 then decide (16 ≤ count1807 b) else decide (1 ≤ count1823 b)) else (if i < 1825 then decide (2 ≤ count1823 b) else decide (3 ≤ count1823 b))))) else (if i < 1833 then (if i < 1829 then (if i < 1827 then decide (4 ≤ count1823 b) else (if i < 1828 then decide (5 ≤ count1823 b) else decide (6 ≤ count1823 b))) else (if i < 1831 then (if i < 1830 then decide (7 ≤ count1823 b) else decide (8 ≤ count1823 b)) else (if i < 1832 then decide (9 ≤ count1823 b) else decide (10 ≤ count1823 b)))) else (if i < 1837 then (if i < 1835 then (if i < 1834 then decide (11 ≤ count1823 b) else decide (12 ≤ count1823 b)) else (if i < 1836 then decide (13 ≤ count1823 b) else decide (14 ≤ count1823 b))) else (if i < 1839 then (if i < 1838 then decide (15 ≤ count1823 b) else decide (16 ≤ count1823 b)) else (if i < 1840 then decide (17 ≤ count1823 b) else decide (18 ≤ count1823 b)))))) else (if i < 1856 then (if i < 1848 then (if i < 1844 then (if i < 1842 then decide (19 ≤ count1823 b) else (if i < 1843 then decide (20 ≤ count1823 b) else decide (21 ≤ count1823 b))) else (if i < 1846 then (if i < 1845 then decide (22 ≤ count1823 b) else decide (23 ≤ count1823 b)) else (if i < 1847 then decide (24 ≤ count1823 b) else decide (1 ≤ count1847 b)))) else (if i < 1852 then (if i < 1850 then (if i < 1849 then decide (2 ≤ count1847 b) else decide (3 ≤ count1847 b)) else (if i < 1851 then decide (4 ≤ count1847 b) else decide (5 ≤ count1847 b))) else (if i < 1854 then (if i < 1853 then decide (6 ≤ count1847 b) else decide (7 ≤ count1847 b)) else (if i < 1855 then decide (8 ≤ count1847 b) else decide (9 ≤ count1847 b))))) else (if i < 1863 then (if i < 1859 then (if i < 1857 then decide (10 ≤ count1847 b) else (if i < 1858 then decide (11 ≤ count1847 b) else decide (12 ≤ count1847 b))) else (if i < 1861 then (if i < 1860 then decide (13 ≤ count1847 b) else decide (14 ≤ count1847 b)) else (if i < 1862 then decide (15 ≤ count1847 b) else decide (16 ≤ count1847 b)))) else (if i < 1867 then (if i < 1865 then (if i < 1864 then decide (17 ≤ count1847 b) else decide (18 ≤ count1847 b)) else (if i < 1866 then decide (19 ≤ count1847 b) else decide (20 ≤ count1847 b))) else (if i < 1869 then (if i < 1868 then decide (21 ≤ count1847 b) else decide (22 ≤ count1847 b)) else (if i < 1870 then decide (23 ≤ count1847 b) else decide (24 ≤ count1847 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (55 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (66 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (76 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (80 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (82 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (83 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (87 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (88 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (92 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (94 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (103 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (118 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (119 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (130 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (131 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (132 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (133 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (137 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (139 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (140 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (141 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (142 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (144 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (145 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (146 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (147 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (151 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (152 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (156 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (158 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (159 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (192 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (194 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (198 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (199 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (200 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (202 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (204 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (206 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (209 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (212 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (213 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (214 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (215 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (217 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (218 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (219 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (221 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (257 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (258 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (259 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (260 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (261 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (265 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (267 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (268 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (269 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (270 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (272 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (274 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (275 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (279 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (280 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (284 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (286 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (287 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (322 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (324 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (325 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (326 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (327 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (328 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (330 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (332 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (337 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (340 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (341 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (342 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (343 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (344 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (345 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (346 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (347 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (351 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (384 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (386 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (388 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (389 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (390 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (391 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (392 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (393 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (394 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (395 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (397 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (398 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (401 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (404 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (405 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (406 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (407 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (409 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (410 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (411 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (413 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (414 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (415 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (448 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (449 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (451 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (452 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (453 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (455 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (457 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (459 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (461 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (462 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (463 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (464 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (466 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (467 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (471 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (472 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (474 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (InPath q (476 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (InPath q (477 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (InPath q (478 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (80 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (82 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (83 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (87 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (88 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (92 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (103 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (119 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (141 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (145 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (146 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (156 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (158 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (198 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (202 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (206 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (212 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (213 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (215 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (217 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (219 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (257 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (269 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (270 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (274 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (275 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (284 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (286 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (322 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (324 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (326 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (330 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (340 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (341 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (347 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (351 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (388 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (389 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (390 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (392 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (393 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (394 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (398 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (404 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (405 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (407 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (411 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (415 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (448 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (449 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (451 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (452 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (457 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (459 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (461 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (BallClauseLogic.Endpoint q (463 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (BallClauseLogic.Endpoint q (466 : Vertex)) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (BallClauseLogic.Endpoint q (467 : Vertex)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (BallClauseLogic.Endpoint q (471 : Vertex)) := rfl
theorem value250 (q : Snake 81) : valuation q 250 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (BallClauseLogic.Endpoint q (476 : Vertex)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (BallClauseLogic.Endpoint q (477 : Vertex)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (BallClauseLogic.Endpoint q (478 : Vertex)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value274 (q : Snake 81) : valuation q 274 = decide (2 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value278 (q : Snake 81) : valuation q 278 = decide (2 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value308 (q : Snake 81) : valuation q 308 = decide (2 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value310 (q : Snake 81) : valuation q 310 = decide (2 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value396 (q : Snake 81) : valuation q 396 = decide (2 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value434 (q : Snake 81) : valuation q 434 = decide (2 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value444 (q : Snake 81) : valuation q 444 = decide (2 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value452 (q : Snake 81) : valuation q 452 = decide (2 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value468 (q : Snake 81) : valuation q 468 = decide (2 ≤ count467 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value479 (q : Snake 81) : valuation q 479 = decide (1 ≤ count479 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value482 (q : Snake 81) : valuation q 482 = decide (2 ≤ count481 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value487 (q : Snake 81) : valuation q 487 = decide (1 ≤ count487 (baseVal q)) := rfl
theorem value489 (q : Snake 81) : valuation q 489 = decide (1 ≤ count489 (baseVal q)) := rfl
theorem value493 (q : Snake 81) : valuation q 493 = decide (1 ≤ count493 (baseVal q)) := rfl
theorem value495 (q : Snake 81) : valuation q 495 = decide (1 ≤ count495 (baseVal q)) := rfl
theorem value496 (q : Snake 81) : valuation q 496 = decide (2 ≤ count495 (baseVal q)) := rfl
theorem value497 (q : Snake 81) : valuation q 497 = decide (1 ≤ count497 (baseVal q)) := rfl
theorem value498 (q : Snake 81) : valuation q 498 = decide (2 ≤ count497 (baseVal q)) := rfl
theorem value499 (q : Snake 81) : valuation q 499 = decide (1 ≤ count499 (baseVal q)) := rfl
theorem value500 (q : Snake 81) : valuation q 500 = decide (2 ≤ count499 (baseVal q)) := rfl
theorem value501 (q : Snake 81) : valuation q 501 = decide (1 ≤ count501 (baseVal q)) := rfl
theorem value502 (q : Snake 81) : valuation q 502 = decide (2 ≤ count501 (baseVal q)) := rfl
theorem value504 (q : Snake 81) : valuation q 504 = decide (2 ≤ count503 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (1 ≤ count1543 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (1 ≤ count1545 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (2 ≤ count1545 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (1 ≤ count1547 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (2 ≤ count1547 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (3 ≤ count1547 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (1 ≤ count1551 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (2 ≤ count1551 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (2 ≤ count1553 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (2 ≤ count1555 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (3 ≤ count1555 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (4 ≤ count1555 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (2 ≤ count1559 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (3 ≤ count1559 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (4 ≤ count1559 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (5 ≤ count1559 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (6 ≤ count1559 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (7 ≤ count1559 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (1 ≤ count1567 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (2 ≤ count1567 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (1 ≤ count1569 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (2 ≤ count1569 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (1 ≤ count1571 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (2 ≤ count1571 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (3 ≤ count1571 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (4 ≤ count1571 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (1 ≤ count1575 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (2 ≤ count1575 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (1 ≤ count1577 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (2 ≤ count1577 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (1 ≤ count1579 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (2 ≤ count1579 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (3 ≤ count1579 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (4 ≤ count1579 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (1 ≤ count1583 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (2 ≤ count1583 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (3 ≤ count1583 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (4 ≤ count1583 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (5 ≤ count1583 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (3 ≤ count1591 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (4 ≤ count1591 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (5 ≤ count1591 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (6 ≤ count1591 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (7 ≤ count1591 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (8 ≤ count1591 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (9 ≤ count1591 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (10 ≤ count1591 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (11 ≤ count1591 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (1 ≤ count1607 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (2 ≤ count1607 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (1 ≤ count1609 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (2 ≤ count1609 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (1 ≤ count1611 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (2 ≤ count1611 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (3 ≤ count1611 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (4 ≤ count1611 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (1 ≤ count1615 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (2 ≤ count1615 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (1 ≤ count1617 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (2 ≤ count1617 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (1 ≤ count1619 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (2 ≤ count1619 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (3 ≤ count1619 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (1 ≤ count1623 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (2 ≤ count1623 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (3 ≤ count1623 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (4 ≤ count1623 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (5 ≤ count1623 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (6 ≤ count1623 (baseVal q)) := rfl
theorem value1631 (q : Snake 81) : valuation q 1631 = decide (1 ≤ count1631 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (2 ≤ count1631 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (1 ≤ count1633 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (2 ≤ count1633 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (1 ≤ count1635 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (2 ≤ count1635 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (3 ≤ count1635 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (4 ≤ count1635 (baseVal q)) := rfl
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
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (3 ≤ count1647 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (4 ≤ count1647 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (5 ≤ count1647 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (6 ≤ count1647 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (1 ≤ count1655 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (2 ≤ count1655 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (3 ≤ count1655 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (4 ≤ count1655 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (5 ≤ count1655 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (6 ≤ count1655 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (7 ≤ count1655 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (8 ≤ count1655 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (9 ≤ count1655 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (5 ≤ count1671 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (6 ≤ count1671 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (7 ≤ count1671 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (8 ≤ count1671 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (9 ≤ count1671 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (10 ≤ count1671 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (11 ≤ count1671 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (12 ≤ count1671 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (13 ≤ count1671 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (14 ≤ count1671 (baseVal q)) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (15 ≤ count1671 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (16 ≤ count1671 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (17 ≤ count1671 (baseVal q)) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (1 ≤ count1695 (baseVal q)) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (2 ≤ count1695 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (1 ≤ count1697 (baseVal q)) := rfl
theorem value1698 (q : Snake 81) : valuation q 1698 = decide (2 ≤ count1697 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (1 ≤ count1699 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (2 ≤ count1699 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (3 ≤ count1699 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (4 ≤ count1699 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (1 ≤ count1703 (baseVal q)) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (2 ≤ count1703 (baseVal q)) := rfl
theorem value1705 (q : Snake 81) : valuation q 1705 = decide (1 ≤ count1705 (baseVal q)) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (2 ≤ count1705 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (1 ≤ count1707 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (2 ≤ count1707 (baseVal q)) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (3 ≤ count1707 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (4 ≤ count1707 (baseVal q)) := rfl
theorem value1711 (q : Snake 81) : valuation q 1711 = decide (1 ≤ count1711 (baseVal q)) := rfl
theorem value1712 (q : Snake 81) : valuation q 1712 = decide (2 ≤ count1711 (baseVal q)) := rfl
theorem value1713 (q : Snake 81) : valuation q 1713 = decide (3 ≤ count1711 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (4 ≤ count1711 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (5 ≤ count1711 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (6 ≤ count1711 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (7 ≤ count1711 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (1 ≤ count1719 (baseVal q)) := rfl
theorem value1720 (q : Snake 81) : valuation q 1720 = decide (2 ≤ count1719 (baseVal q)) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (1 ≤ count1721 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (2 ≤ count1721 (baseVal q)) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (1 ≤ count1723 (baseVal q)) := rfl
theorem value1724 (q : Snake 81) : valuation q 1724 = decide (2 ≤ count1723 (baseVal q)) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (3 ≤ count1723 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (4 ≤ count1723 (baseVal q)) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (1 ≤ count1727 (baseVal q)) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (2 ≤ count1727 (baseVal q)) := rfl
theorem value1729 (q : Snake 81) : valuation q 1729 = decide (1 ≤ count1729 (baseVal q)) := rfl
theorem value1730 (q : Snake 81) : valuation q 1730 = decide (2 ≤ count1729 (baseVal q)) := rfl
theorem value1731 (q : Snake 81) : valuation q 1731 = decide (1 ≤ count1731 (baseVal q)) := rfl
theorem value1732 (q : Snake 81) : valuation q 1732 = decide (2 ≤ count1731 (baseVal q)) := rfl
theorem value1733 (q : Snake 81) : valuation q 1733 = decide (3 ≤ count1731 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (4 ≤ count1731 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (1 ≤ count1735 (baseVal q)) := rfl
theorem value1736 (q : Snake 81) : valuation q 1736 = decide (2 ≤ count1735 (baseVal q)) := rfl
theorem value1737 (q : Snake 81) : valuation q 1737 = decide (3 ≤ count1735 (baseVal q)) := rfl
theorem value1738 (q : Snake 81) : valuation q 1738 = decide (4 ≤ count1735 (baseVal q)) := rfl
theorem value1739 (q : Snake 81) : valuation q 1739 = decide (5 ≤ count1735 (baseVal q)) := rfl
theorem value1740 (q : Snake 81) : valuation q 1740 = decide (6 ≤ count1735 (baseVal q)) := rfl
theorem value1741 (q : Snake 81) : valuation q 1741 = decide (7 ≤ count1735 (baseVal q)) := rfl
theorem value1742 (q : Snake 81) : valuation q 1742 = decide (8 ≤ count1735 (baseVal q)) := rfl
theorem value1745 (q : Snake 81) : valuation q 1745 = decide (3 ≤ count1743 (baseVal q)) := rfl
theorem value1746 (q : Snake 81) : valuation q 1746 = decide (4 ≤ count1743 (baseVal q)) := rfl
theorem value1747 (q : Snake 81) : valuation q 1747 = decide (5 ≤ count1743 (baseVal q)) := rfl
theorem value1748 (q : Snake 81) : valuation q 1748 = decide (6 ≤ count1743 (baseVal q)) := rfl
theorem value1749 (q : Snake 81) : valuation q 1749 = decide (7 ≤ count1743 (baseVal q)) := rfl
theorem value1750 (q : Snake 81) : valuation q 1750 = decide (8 ≤ count1743 (baseVal q)) := rfl
theorem value1751 (q : Snake 81) : valuation q 1751 = decide (9 ≤ count1743 (baseVal q)) := rfl
theorem value1752 (q : Snake 81) : valuation q 1752 = decide (10 ≤ count1743 (baseVal q)) := rfl
theorem value1753 (q : Snake 81) : valuation q 1753 = decide (11 ≤ count1743 (baseVal q)) := rfl
theorem value1754 (q : Snake 81) : valuation q 1754 = decide (12 ≤ count1743 (baseVal q)) := rfl
theorem value1755 (q : Snake 81) : valuation q 1755 = decide (13 ≤ count1743 (baseVal q)) := rfl
theorem value1759 (q : Snake 81) : valuation q 1759 = decide (1 ≤ count1759 (baseVal q)) := rfl
theorem value1760 (q : Snake 81) : valuation q 1760 = decide (2 ≤ count1759 (baseVal q)) := rfl
theorem value1761 (q : Snake 81) : valuation q 1761 = decide (1 ≤ count1761 (baseVal q)) := rfl
theorem value1762 (q : Snake 81) : valuation q 1762 = decide (2 ≤ count1761 (baseVal q)) := rfl
theorem value1763 (q : Snake 81) : valuation q 1763 = decide (1 ≤ count1763 (baseVal q)) := rfl
theorem value1764 (q : Snake 81) : valuation q 1764 = decide (2 ≤ count1763 (baseVal q)) := rfl
theorem value1765 (q : Snake 81) : valuation q 1765 = decide (3 ≤ count1763 (baseVal q)) := rfl
theorem value1766 (q : Snake 81) : valuation q 1766 = decide (4 ≤ count1763 (baseVal q)) := rfl
theorem value1767 (q : Snake 81) : valuation q 1767 = decide (1 ≤ count1767 (baseVal q)) := rfl
theorem value1768 (q : Snake 81) : valuation q 1768 = decide (2 ≤ count1767 (baseVal q)) := rfl
theorem value1769 (q : Snake 81) : valuation q 1769 = decide (1 ≤ count1769 (baseVal q)) := rfl
theorem value1770 (q : Snake 81) : valuation q 1770 = decide (2 ≤ count1769 (baseVal q)) := rfl
theorem value1771 (q : Snake 81) : valuation q 1771 = decide (1 ≤ count1771 (baseVal q)) := rfl
theorem value1772 (q : Snake 81) : valuation q 1772 = decide (2 ≤ count1771 (baseVal q)) := rfl
theorem value1773 (q : Snake 81) : valuation q 1773 = decide (3 ≤ count1771 (baseVal q)) := rfl
theorem value1774 (q : Snake 81) : valuation q 1774 = decide (4 ≤ count1771 (baseVal q)) := rfl
theorem value1775 (q : Snake 81) : valuation q 1775 = decide (1 ≤ count1775 (baseVal q)) := rfl
theorem value1776 (q : Snake 81) : valuation q 1776 = decide (2 ≤ count1775 (baseVal q)) := rfl
theorem value1777 (q : Snake 81) : valuation q 1777 = decide (3 ≤ count1775 (baseVal q)) := rfl
theorem value1778 (q : Snake 81) : valuation q 1778 = decide (4 ≤ count1775 (baseVal q)) := rfl
theorem value1779 (q : Snake 81) : valuation q 1779 = decide (5 ≤ count1775 (baseVal q)) := rfl
theorem value1780 (q : Snake 81) : valuation q 1780 = decide (6 ≤ count1775 (baseVal q)) := rfl
theorem value1781 (q : Snake 81) : valuation q 1781 = decide (7 ≤ count1775 (baseVal q)) := rfl
theorem value1783 (q : Snake 81) : valuation q 1783 = decide (1 ≤ count1783 (baseVal q)) := rfl
theorem value1784 (q : Snake 81) : valuation q 1784 = decide (2 ≤ count1783 (baseVal q)) := rfl
theorem value1785 (q : Snake 81) : valuation q 1785 = decide (1 ≤ count1785 (baseVal q)) := rfl
theorem value1786 (q : Snake 81) : valuation q 1786 = decide (2 ≤ count1785 (baseVal q)) := rfl
theorem value1787 (q : Snake 81) : valuation q 1787 = decide (1 ≤ count1787 (baseVal q)) := rfl
theorem value1788 (q : Snake 81) : valuation q 1788 = decide (2 ≤ count1787 (baseVal q)) := rfl
theorem value1789 (q : Snake 81) : valuation q 1789 = decide (3 ≤ count1787 (baseVal q)) := rfl
theorem value1790 (q : Snake 81) : valuation q 1790 = decide (4 ≤ count1787 (baseVal q)) := rfl
theorem value1791 (q : Snake 81) : valuation q 1791 = decide (1 ≤ count1791 (baseVal q)) := rfl
theorem value1792 (q : Snake 81) : valuation q 1792 = decide (2 ≤ count1791 (baseVal q)) := rfl
theorem value1793 (q : Snake 81) : valuation q 1793 = decide (1 ≤ count1793 (baseVal q)) := rfl
theorem value1794 (q : Snake 81) : valuation q 1794 = decide (2 ≤ count1793 (baseVal q)) := rfl
theorem value1795 (q : Snake 81) : valuation q 1795 = decide (1 ≤ count1795 (baseVal q)) := rfl
theorem value1796 (q : Snake 81) : valuation q 1796 = decide (2 ≤ count1795 (baseVal q)) := rfl
theorem value1797 (q : Snake 81) : valuation q 1797 = decide (3 ≤ count1795 (baseVal q)) := rfl
theorem value1798 (q : Snake 81) : valuation q 1798 = decide (4 ≤ count1795 (baseVal q)) := rfl
theorem value1799 (q : Snake 81) : valuation q 1799 = decide (1 ≤ count1799 (baseVal q)) := rfl
theorem value1800 (q : Snake 81) : valuation q 1800 = decide (2 ≤ count1799 (baseVal q)) := rfl
theorem value1801 (q : Snake 81) : valuation q 1801 = decide (3 ≤ count1799 (baseVal q)) := rfl
theorem value1802 (q : Snake 81) : valuation q 1802 = decide (4 ≤ count1799 (baseVal q)) := rfl
theorem value1803 (q : Snake 81) : valuation q 1803 = decide (5 ≤ count1799 (baseVal q)) := rfl
theorem value1804 (q : Snake 81) : valuation q 1804 = decide (6 ≤ count1799 (baseVal q)) := rfl
theorem value1807 (q : Snake 81) : valuation q 1807 = decide (1 ≤ count1807 (baseVal q)) := rfl
theorem value1808 (q : Snake 81) : valuation q 1808 = decide (2 ≤ count1807 (baseVal q)) := rfl
theorem value1809 (q : Snake 81) : valuation q 1809 = decide (3 ≤ count1807 (baseVal q)) := rfl
theorem value1810 (q : Snake 81) : valuation q 1810 = decide (4 ≤ count1807 (baseVal q)) := rfl
theorem value1811 (q : Snake 81) : valuation q 1811 = decide (5 ≤ count1807 (baseVal q)) := rfl
theorem value1812 (q : Snake 81) : valuation q 1812 = decide (6 ≤ count1807 (baseVal q)) := rfl
theorem value1813 (q : Snake 81) : valuation q 1813 = decide (7 ≤ count1807 (baseVal q)) := rfl
theorem value1814 (q : Snake 81) : valuation q 1814 = decide (8 ≤ count1807 (baseVal q)) := rfl
theorem value1815 (q : Snake 81) : valuation q 1815 = decide (9 ≤ count1807 (baseVal q)) := rfl
theorem value1816 (q : Snake 81) : valuation q 1816 = decide (10 ≤ count1807 (baseVal q)) := rfl
theorem value1817 (q : Snake 81) : valuation q 1817 = decide (11 ≤ count1807 (baseVal q)) := rfl
theorem value1829 (q : Snake 81) : valuation q 1829 = decide (7 ≤ count1823 (baseVal q)) := rfl
theorem value1830 (q : Snake 81) : valuation q 1830 = decide (8 ≤ count1823 (baseVal q)) := rfl
theorem value1831 (q : Snake 81) : valuation q 1831 = decide (9 ≤ count1823 (baseVal q)) := rfl
theorem value1832 (q : Snake 81) : valuation q 1832 = decide (10 ≤ count1823 (baseVal q)) := rfl
theorem value1833 (q : Snake 81) : valuation q 1833 = decide (11 ≤ count1823 (baseVal q)) := rfl
theorem value1834 (q : Snake 81) : valuation q 1834 = decide (12 ≤ count1823 (baseVal q)) := rfl
theorem value1835 (q : Snake 81) : valuation q 1835 = decide (13 ≤ count1823 (baseVal q)) := rfl
theorem value1836 (q : Snake 81) : valuation q 1836 = decide (14 ≤ count1823 (baseVal q)) := rfl
theorem value1837 (q : Snake 81) : valuation q 1837 = decide (15 ≤ count1823 (baseVal q)) := rfl
theorem value1838 (q : Snake 81) : valuation q 1838 = decide (16 ≤ count1823 (baseVal q)) := rfl
theorem value1839 (q : Snake 81) : valuation q 1839 = decide (17 ≤ count1823 (baseVal q)) := rfl
theorem value1840 (q : Snake 81) : valuation q 1840 = decide (18 ≤ count1823 (baseVal q)) := rfl
theorem value1841 (q : Snake 81) : valuation q 1841 = decide (19 ≤ count1823 (baseVal q)) := rfl
theorem value1870 (q : Snake 81) : valuation q 1870 = decide (24 ≤ count1847 (baseVal q)) := rfl
theorem meaningNeg127 (b : Nat → Bool) : literal (valuationOf b) (-127) = decide (1 ≤ countLit b [-127]) := by
  change literal b (-127) = decide (1 ≤ countLit b [-127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-127) <;> decide
theorem meaningNeg126 (b : Nat → Bool) : literal (valuationOf b) (-126) = decide (1 ≤ countLit b [-126]) := by
  change literal b (-126) = decide (1 ≤ countLit b [-126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-126) <;> decide
theorem meaningNeg123 (b : Nat → Bool) : literal (valuationOf b) (-123) = decide (1 ≤ countLit b [-123]) := by
  change literal b (-123) = decide (1 ≤ countLit b [-123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-123) <;> decide
theorem meaningNeg122 (b : Nat → Bool) : literal (valuationOf b) (-122) = decide (1 ≤ countLit b [-122]) := by
  change literal b (-122) = decide (1 ≤ countLit b [-122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-122) <;> decide
theorem meaningNeg120 (b : Nat → Bool) : literal (valuationOf b) (-120) = decide (1 ≤ countLit b [-120]) := by
  change literal b (-120) = decide (1 ≤ countLit b [-120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-120) <;> decide
theorem meaningNeg118 (b : Nat → Bool) : literal (valuationOf b) (-118) = decide (1 ≤ countLit b [-118]) := by
  change literal b (-118) = decide (1 ≤ countLit b [-118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-118) <;> decide
theorem meaningNeg114 (b : Nat → Bool) : literal (valuationOf b) (-114) = decide (1 ≤ countLit b [-114]) := by
  change literal b (-114) = decide (1 ≤ countLit b [-114])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-114) <;> decide
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
theorem meaningNeg91 (b : Nat → Bool) : literal (valuationOf b) (-91) = decide (1 ≤ countLit b [-91]) := by
  change literal b (-91) = decide (1 ≤ countLit b [-91])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-91) <;> decide
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
theorem meaningNeg77 (b : Nat → Bool) : literal (valuationOf b) (-77) = decide (1 ≤ countLit b [-77]) := by
  change literal b (-77) = decide (1 ≤ countLit b [-77])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-77) <;> decide
theorem meaningNeg72 (b : Nat → Bool) : literal (valuationOf b) (-72) = decide (1 ≤ countLit b [-72]) := by
  change literal b (-72) = decide (1 ≤ countLit b [-72])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-72) <;> decide
theorem meaningNeg71 (b : Nat → Bool) : literal (valuationOf b) (-71) = decide (1 ≤ countLit b [-71]) := by
  change literal b (-71) = decide (1 ≤ countLit b [-71])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-71) <;> decide
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
theorem meaningNeg60 (b : Nat → Bool) : literal (valuationOf b) (-60) = decide (1 ≤ countLit b [-60]) := by
  change literal b (-60) = decide (1 ≤ countLit b [-60])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-60) <;> decide
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
theorem meaningNeg51 (b : Nat → Bool) : literal (valuationOf b) (-51) = decide (1 ≤ countLit b [-51]) := by
  change literal b (-51) = decide (1 ≤ countLit b [-51])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-51) <;> decide
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
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
theorem meaningNeg39 (b : Nat → Bool) : literal (valuationOf b) (-39) = decide (1 ≤ countLit b [-39]) := by
  change literal b (-39) = decide (1 ≤ countLit b [-39])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-39) <;> decide
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
theorem meaning136 (b : Nat → Bool) : literal (valuationOf b) (136) = decide (1 ≤ countLit b [136]) := by
  change literal b (136) = decide (1 ≤ countLit b [136])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (136) <;> decide
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
theorem meaning148 (b : Nat → Bool) : literal (valuationOf b) (148) = decide (1 ≤ countLit b [148]) := by
  change literal b (148) = decide (1 ≤ countLit b [148])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (148) <;> decide
theorem meaning149 (b : Nat → Bool) : literal (valuationOf b) (149) = decide (1 ≤ countLit b [149]) := by
  change literal b (149) = decide (1 ≤ countLit b [149])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (149) <;> decide
theorem meaning150 (b : Nat → Bool) : literal (valuationOf b) (150) = decide (1 ≤ countLit b [150]) := by
  change literal b (150) = decide (1 ≤ countLit b [150])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (150) <;> decide
theorem meaning156 (b : Nat → Bool) : literal (valuationOf b) (156) = decide (1 ≤ countLit b [156]) := by
  change literal b (156) = decide (1 ≤ countLit b [156])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (156) <;> decide
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
theorem meaning164 (b : Nat → Bool) : literal (valuationOf b) (164) = decide (1 ≤ countLit b [164]) := by
  change literal b (164) = decide (1 ≤ countLit b [164])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (164) <;> decide
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
theorem meaning177 (b : Nat → Bool) : literal (valuationOf b) (177) = decide (1 ≤ countLit b [177]) := by
  change literal b (177) = decide (1 ≤ countLit b [177])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (177) <;> decide
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
theorem meaning188 (b : Nat → Bool) : literal (valuationOf b) (188) = decide (1 ≤ countLit b [188]) := by
  change literal b (188) = decide (1 ≤ countLit b [188])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (188) <;> decide
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
theorem meaning197 (b : Nat → Bool) : literal (valuationOf b) (197) = decide (1 ≤ countLit b [197]) := by
  change literal b (197) = decide (1 ≤ countLit b [197])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (197) <;> decide
theorem meaning200 (b : Nat → Bool) : literal (valuationOf b) (200) = decide (1 ≤ countLit b [200]) := by
  change literal b (200) = decide (1 ≤ countLit b [200])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (200) <;> decide
theorem meaning201 (b : Nat → Bool) : literal (valuationOf b) (201) = decide (1 ≤ countLit b [201]) := by
  change literal b (201) = decide (1 ≤ countLit b [201])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (201) <;> decide
theorem meaning202 (b : Nat → Bool) : literal (valuationOf b) (202) = decide (1 ≤ countLit b [202]) := by
  change literal b (202) = decide (1 ≤ countLit b [202])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (202) <;> decide
theorem meaning203 (b : Nat → Bool) : literal (valuationOf b) (203) = decide (1 ≤ countLit b [203]) := by
  change literal b (203) = decide (1 ≤ countLit b [203])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (203) <;> decide
theorem meaning210 (b : Nat → Bool) : literal (valuationOf b) (210) = decide (1 ≤ countLit b [210]) := by
  change literal b (210) = decide (1 ≤ countLit b [210])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (210) <;> decide
theorem meaning212 (b : Nat → Bool) : literal (valuationOf b) (212) = decide (1 ≤ countLit b [212]) := by
  change literal b (212) = decide (1 ≤ countLit b [212])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (212) <;> decide
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) (215) = decide (1 ≤ countLit b [215]) := by
  change literal b (215) = decide (1 ≤ countLit b [215])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (215) <;> decide
theorem meaning216 (b : Nat → Bool) : literal (valuationOf b) (216) = decide (1 ≤ countLit b [216]) := by
  change literal b (216) = decide (1 ≤ countLit b [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (216) <;> decide
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) (219) = decide (1 ≤ countLit b [219]) := by
  change literal b (219) = decide (1 ≤ countLit b [219])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (219) <;> decide
theorem meaning220 (b : Nat → Bool) : literal (valuationOf b) (220) = decide (1 ≤ countLit b [220]) := by
  change literal b (220) = decide (1 ≤ countLit b [220])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (220) <;> decide
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
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) (228) = decide (1 ≤ countLit b [228]) := by
  change literal b (228) = decide (1 ≤ countLit b [228])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (228) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) (231) = decide (1 ≤ countLit b [231]) := by
  change literal b (231) = decide (1 ≤ countLit b [231])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (231) <;> decide
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) (232) = decide (1 ≤ countLit b [232]) := by
  change literal b (232) = decide (1 ≤ countLit b [232])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (232) <;> decide
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) (233) = decide (1 ≤ countLit b [233]) := by
  change literal b (233) = decide (1 ≤ countLit b [233])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (233) <;> decide
theorem meaning236 (b : Nat → Bool) : literal (valuationOf b) (236) = decide (1 ≤ countLit b [236]) := by
  change literal b (236) = decide (1 ≤ countLit b [236])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (236) <;> decide
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) (238) = decide (1 ≤ countLit b [238]) := by
  change literal b (238) = decide (1 ≤ countLit b [238])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (238) <;> decide
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) (242) = decide (1 ≤ countLit b [242]) := by
  change literal b (242) = decide (1 ≤ countLit b [242])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (242) <;> decide
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) (243) = decide (1 ≤ countLit b [243]) := by
  change literal b (243) = decide (1 ≤ countLit b [243])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (243) <;> decide
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) (244) = decide (1 ≤ countLit b [244]) := by
  change literal b (244) = decide (1 ≤ countLit b [244])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (244) <;> decide
theorem meaning246 (b : Nat → Bool) : literal (valuationOf b) (246) = decide (1 ≤ countLit b [246]) := by
  change literal b (246) = decide (1 ≤ countLit b [246])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (246) <;> decide
theorem meaning248 (b : Nat → Bool) : literal (valuationOf b) (248) = decide (1 ≤ countLit b [248]) := by
  change literal b (248) = decide (1 ≤ countLit b [248])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (248) <;> decide
theorem meaning252 (b : Nat → Bool) : literal (valuationOf b) (252) = decide (1 ≤ countLit b [252]) := by
  change literal b (252) = decide (1 ≤ countLit b [252])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (252) <;> decide
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning274 (b : Nat → Bool) : literal (valuationOf b) 274 = decide (2 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning278 (b : Nat → Bool) : literal (valuationOf b) 278 = decide (2 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning308 (b : Nat → Bool) : literal (valuationOf b) 308 = decide (2 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning310 (b : Nat → Bool) : literal (valuationOf b) 310 = decide (2 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning396 (b : Nat → Bool) : literal (valuationOf b) 396 = decide (2 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning434 (b : Nat → Bool) : literal (valuationOf b) 434 = decide (2 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning444 (b : Nat → Bool) : literal (valuationOf b) 444 = decide (2 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning452 (b : Nat → Bool) : literal (valuationOf b) 452 = decide (2 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning468 (b : Nat → Bool) : literal (valuationOf b) 468 = decide (2 ≤ count467 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning479 (b : Nat → Bool) : literal (valuationOf b) 479 = decide (1 ≤ count479 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning482 (b : Nat → Bool) : literal (valuationOf b) 482 = decide (2 ≤ count481 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning487 (b : Nat → Bool) : literal (valuationOf b) 487 = decide (1 ≤ count487 b) := rfl
theorem meaning489 (b : Nat → Bool) : literal (valuationOf b) 489 = decide (1 ≤ count489 b) := rfl
theorem meaning493 (b : Nat → Bool) : literal (valuationOf b) 493 = decide (1 ≤ count493 b) := rfl
theorem meaning495 (b : Nat → Bool) : literal (valuationOf b) 495 = decide (1 ≤ count495 b) := rfl
theorem meaning496 (b : Nat → Bool) : literal (valuationOf b) 496 = decide (2 ≤ count495 b) := rfl
theorem meaning497 (b : Nat → Bool) : literal (valuationOf b) 497 = decide (1 ≤ count497 b) := rfl
theorem meaning498 (b : Nat → Bool) : literal (valuationOf b) 498 = decide (2 ≤ count497 b) := rfl
theorem meaning499 (b : Nat → Bool) : literal (valuationOf b) 499 = decide (1 ≤ count499 b) := rfl
theorem meaning500 (b : Nat → Bool) : literal (valuationOf b) 500 = decide (2 ≤ count499 b) := rfl
theorem meaning501 (b : Nat → Bool) : literal (valuationOf b) 501 = decide (1 ≤ count501 b) := rfl
theorem meaning502 (b : Nat → Bool) : literal (valuationOf b) 502 = decide (2 ≤ count501 b) := rfl
theorem meaning504 (b : Nat → Bool) : literal (valuationOf b) 504 = decide (2 ≤ count503 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (1 ≤ count1543 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (1 ≤ count1545 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (2 ≤ count1545 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (1 ≤ count1547 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (2 ≤ count1547 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (3 ≤ count1547 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (1 ≤ count1551 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (2 ≤ count1551 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (2 ≤ count1553 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (2 ≤ count1555 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (3 ≤ count1555 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (4 ≤ count1555 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (2 ≤ count1559 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (3 ≤ count1559 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (4 ≤ count1559 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (5 ≤ count1559 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (6 ≤ count1559 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (7 ≤ count1559 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (1 ≤ count1567 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (2 ≤ count1567 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (1 ≤ count1569 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (2 ≤ count1569 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (1 ≤ count1571 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (2 ≤ count1571 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (3 ≤ count1571 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (4 ≤ count1571 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (1 ≤ count1575 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (2 ≤ count1575 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (1 ≤ count1577 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (2 ≤ count1577 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (1 ≤ count1579 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (2 ≤ count1579 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (3 ≤ count1579 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (4 ≤ count1579 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (1 ≤ count1583 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (2 ≤ count1583 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (3 ≤ count1583 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (4 ≤ count1583 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (5 ≤ count1583 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (3 ≤ count1591 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (4 ≤ count1591 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (5 ≤ count1591 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (6 ≤ count1591 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (7 ≤ count1591 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (8 ≤ count1591 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (9 ≤ count1591 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (10 ≤ count1591 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (11 ≤ count1591 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (1 ≤ count1607 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (2 ≤ count1607 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (1 ≤ count1609 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (2 ≤ count1609 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (1 ≤ count1611 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (2 ≤ count1611 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (3 ≤ count1611 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (4 ≤ count1611 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (1 ≤ count1615 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (2 ≤ count1615 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (1 ≤ count1617 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (2 ≤ count1617 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (1 ≤ count1619 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (2 ≤ count1619 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (3 ≤ count1619 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (1 ≤ count1623 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (2 ≤ count1623 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (3 ≤ count1623 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (4 ≤ count1623 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (5 ≤ count1623 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (6 ≤ count1623 b) := rfl
theorem meaning1631 (b : Nat → Bool) : literal (valuationOf b) 1631 = decide (1 ≤ count1631 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (2 ≤ count1631 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (1 ≤ count1633 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (2 ≤ count1633 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (1 ≤ count1635 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (2 ≤ count1635 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (3 ≤ count1635 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (4 ≤ count1635 b) := rfl
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
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (3 ≤ count1647 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (4 ≤ count1647 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (5 ≤ count1647 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (6 ≤ count1647 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (1 ≤ count1655 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (2 ≤ count1655 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (3 ≤ count1655 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (4 ≤ count1655 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (5 ≤ count1655 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (6 ≤ count1655 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (7 ≤ count1655 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (8 ≤ count1655 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (9 ≤ count1655 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (5 ≤ count1671 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (6 ≤ count1671 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (7 ≤ count1671 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (8 ≤ count1671 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (9 ≤ count1671 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (10 ≤ count1671 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (11 ≤ count1671 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (12 ≤ count1671 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (13 ≤ count1671 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (14 ≤ count1671 b) := rfl
theorem meaning1685 (b : Nat → Bool) : literal (valuationOf b) 1685 = decide (15 ≤ count1671 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (16 ≤ count1671 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (17 ≤ count1671 b) := rfl
theorem meaning1695 (b : Nat → Bool) : literal (valuationOf b) 1695 = decide (1 ≤ count1695 b) := rfl
theorem meaning1696 (b : Nat → Bool) : literal (valuationOf b) 1696 = decide (2 ≤ count1695 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (1 ≤ count1697 b) := rfl
theorem meaning1698 (b : Nat → Bool) : literal (valuationOf b) 1698 = decide (2 ≤ count1697 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (1 ≤ count1699 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (2 ≤ count1699 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (3 ≤ count1699 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (4 ≤ count1699 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (1 ≤ count1703 b) := rfl
theorem meaning1704 (b : Nat → Bool) : literal (valuationOf b) 1704 = decide (2 ≤ count1703 b) := rfl
theorem meaning1705 (b : Nat → Bool) : literal (valuationOf b) 1705 = decide (1 ≤ count1705 b) := rfl
theorem meaning1706 (b : Nat → Bool) : literal (valuationOf b) 1706 = decide (2 ≤ count1705 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (1 ≤ count1707 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (2 ≤ count1707 b) := rfl
theorem meaning1709 (b : Nat → Bool) : literal (valuationOf b) 1709 = decide (3 ≤ count1707 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (4 ≤ count1707 b) := rfl
theorem meaning1711 (b : Nat → Bool) : literal (valuationOf b) 1711 = decide (1 ≤ count1711 b) := rfl
theorem meaning1712 (b : Nat → Bool) : literal (valuationOf b) 1712 = decide (2 ≤ count1711 b) := rfl
theorem meaning1713 (b : Nat → Bool) : literal (valuationOf b) 1713 = decide (3 ≤ count1711 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (4 ≤ count1711 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (5 ≤ count1711 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (6 ≤ count1711 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (7 ≤ count1711 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (1 ≤ count1719 b) := rfl
theorem meaning1720 (b : Nat → Bool) : literal (valuationOf b) 1720 = decide (2 ≤ count1719 b) := rfl
theorem meaning1721 (b : Nat → Bool) : literal (valuationOf b) 1721 = decide (1 ≤ count1721 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (2 ≤ count1721 b) := rfl
theorem meaning1723 (b : Nat → Bool) : literal (valuationOf b) 1723 = decide (1 ≤ count1723 b) := rfl
theorem meaning1724 (b : Nat → Bool) : literal (valuationOf b) 1724 = decide (2 ≤ count1723 b) := rfl
theorem meaning1725 (b : Nat → Bool) : literal (valuationOf b) 1725 = decide (3 ≤ count1723 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (4 ≤ count1723 b) := rfl
theorem meaning1727 (b : Nat → Bool) : literal (valuationOf b) 1727 = decide (1 ≤ count1727 b) := rfl
theorem meaning1728 (b : Nat → Bool) : literal (valuationOf b) 1728 = decide (2 ≤ count1727 b) := rfl
theorem meaning1729 (b : Nat → Bool) : literal (valuationOf b) 1729 = decide (1 ≤ count1729 b) := rfl
theorem meaning1730 (b : Nat → Bool) : literal (valuationOf b) 1730 = decide (2 ≤ count1729 b) := rfl
theorem meaning1731 (b : Nat → Bool) : literal (valuationOf b) 1731 = decide (1 ≤ count1731 b) := rfl
theorem meaning1732 (b : Nat → Bool) : literal (valuationOf b) 1732 = decide (2 ≤ count1731 b) := rfl
theorem meaning1733 (b : Nat → Bool) : literal (valuationOf b) 1733 = decide (3 ≤ count1731 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (4 ≤ count1731 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (1 ≤ count1735 b) := rfl
theorem meaning1736 (b : Nat → Bool) : literal (valuationOf b) 1736 = decide (2 ≤ count1735 b) := rfl
theorem meaning1737 (b : Nat → Bool) : literal (valuationOf b) 1737 = decide (3 ≤ count1735 b) := rfl
theorem meaning1738 (b : Nat → Bool) : literal (valuationOf b) 1738 = decide (4 ≤ count1735 b) := rfl
theorem meaning1739 (b : Nat → Bool) : literal (valuationOf b) 1739 = decide (5 ≤ count1735 b) := rfl
theorem meaning1740 (b : Nat → Bool) : literal (valuationOf b) 1740 = decide (6 ≤ count1735 b) := rfl
theorem meaning1741 (b : Nat → Bool) : literal (valuationOf b) 1741 = decide (7 ≤ count1735 b) := rfl
theorem meaning1742 (b : Nat → Bool) : literal (valuationOf b) 1742 = decide (8 ≤ count1735 b) := rfl
theorem meaning1745 (b : Nat → Bool) : literal (valuationOf b) 1745 = decide (3 ≤ count1743 b) := rfl
theorem meaning1746 (b : Nat → Bool) : literal (valuationOf b) 1746 = decide (4 ≤ count1743 b) := rfl
theorem meaning1747 (b : Nat → Bool) : literal (valuationOf b) 1747 = decide (5 ≤ count1743 b) := rfl
theorem meaning1748 (b : Nat → Bool) : literal (valuationOf b) 1748 = decide (6 ≤ count1743 b) := rfl
theorem meaning1749 (b : Nat → Bool) : literal (valuationOf b) 1749 = decide (7 ≤ count1743 b) := rfl
theorem meaning1750 (b : Nat → Bool) : literal (valuationOf b) 1750 = decide (8 ≤ count1743 b) := rfl
theorem meaning1751 (b : Nat → Bool) : literal (valuationOf b) 1751 = decide (9 ≤ count1743 b) := rfl
theorem meaning1752 (b : Nat → Bool) : literal (valuationOf b) 1752 = decide (10 ≤ count1743 b) := rfl
theorem meaning1753 (b : Nat → Bool) : literal (valuationOf b) 1753 = decide (11 ≤ count1743 b) := rfl
theorem meaning1754 (b : Nat → Bool) : literal (valuationOf b) 1754 = decide (12 ≤ count1743 b) := rfl
theorem meaning1755 (b : Nat → Bool) : literal (valuationOf b) 1755 = decide (13 ≤ count1743 b) := rfl
theorem meaning1759 (b : Nat → Bool) : literal (valuationOf b) 1759 = decide (1 ≤ count1759 b) := rfl
theorem meaning1760 (b : Nat → Bool) : literal (valuationOf b) 1760 = decide (2 ≤ count1759 b) := rfl
theorem meaning1761 (b : Nat → Bool) : literal (valuationOf b) 1761 = decide (1 ≤ count1761 b) := rfl
theorem meaning1762 (b : Nat → Bool) : literal (valuationOf b) 1762 = decide (2 ≤ count1761 b) := rfl
theorem meaning1763 (b : Nat → Bool) : literal (valuationOf b) 1763 = decide (1 ≤ count1763 b) := rfl
theorem meaning1764 (b : Nat → Bool) : literal (valuationOf b) 1764 = decide (2 ≤ count1763 b) := rfl
theorem meaning1765 (b : Nat → Bool) : literal (valuationOf b) 1765 = decide (3 ≤ count1763 b) := rfl
theorem meaning1766 (b : Nat → Bool) : literal (valuationOf b) 1766 = decide (4 ≤ count1763 b) := rfl
theorem meaning1767 (b : Nat → Bool) : literal (valuationOf b) 1767 = decide (1 ≤ count1767 b) := rfl
theorem meaning1768 (b : Nat → Bool) : literal (valuationOf b) 1768 = decide (2 ≤ count1767 b) := rfl
theorem meaning1769 (b : Nat → Bool) : literal (valuationOf b) 1769 = decide (1 ≤ count1769 b) := rfl
theorem meaning1770 (b : Nat → Bool) : literal (valuationOf b) 1770 = decide (2 ≤ count1769 b) := rfl
theorem meaning1771 (b : Nat → Bool) : literal (valuationOf b) 1771 = decide (1 ≤ count1771 b) := rfl
theorem meaning1772 (b : Nat → Bool) : literal (valuationOf b) 1772 = decide (2 ≤ count1771 b) := rfl
theorem meaning1773 (b : Nat → Bool) : literal (valuationOf b) 1773 = decide (3 ≤ count1771 b) := rfl
theorem meaning1774 (b : Nat → Bool) : literal (valuationOf b) 1774 = decide (4 ≤ count1771 b) := rfl
theorem meaning1775 (b : Nat → Bool) : literal (valuationOf b) 1775 = decide (1 ≤ count1775 b) := rfl
theorem meaning1776 (b : Nat → Bool) : literal (valuationOf b) 1776 = decide (2 ≤ count1775 b) := rfl
theorem meaning1777 (b : Nat → Bool) : literal (valuationOf b) 1777 = decide (3 ≤ count1775 b) := rfl
theorem meaning1778 (b : Nat → Bool) : literal (valuationOf b) 1778 = decide (4 ≤ count1775 b) := rfl
theorem meaning1779 (b : Nat → Bool) : literal (valuationOf b) 1779 = decide (5 ≤ count1775 b) := rfl
theorem meaning1780 (b : Nat → Bool) : literal (valuationOf b) 1780 = decide (6 ≤ count1775 b) := rfl
theorem meaning1781 (b : Nat → Bool) : literal (valuationOf b) 1781 = decide (7 ≤ count1775 b) := rfl
theorem meaning1783 (b : Nat → Bool) : literal (valuationOf b) 1783 = decide (1 ≤ count1783 b) := rfl
theorem meaning1784 (b : Nat → Bool) : literal (valuationOf b) 1784 = decide (2 ≤ count1783 b) := rfl
theorem meaning1785 (b : Nat → Bool) : literal (valuationOf b) 1785 = decide (1 ≤ count1785 b) := rfl
theorem meaning1786 (b : Nat → Bool) : literal (valuationOf b) 1786 = decide (2 ≤ count1785 b) := rfl
theorem meaning1787 (b : Nat → Bool) : literal (valuationOf b) 1787 = decide (1 ≤ count1787 b) := rfl
theorem meaning1788 (b : Nat → Bool) : literal (valuationOf b) 1788 = decide (2 ≤ count1787 b) := rfl
theorem meaning1789 (b : Nat → Bool) : literal (valuationOf b) 1789 = decide (3 ≤ count1787 b) := rfl
theorem meaning1790 (b : Nat → Bool) : literal (valuationOf b) 1790 = decide (4 ≤ count1787 b) := rfl
theorem meaning1791 (b : Nat → Bool) : literal (valuationOf b) 1791 = decide (1 ≤ count1791 b) := rfl
theorem meaning1792 (b : Nat → Bool) : literal (valuationOf b) 1792 = decide (2 ≤ count1791 b) := rfl
theorem meaning1793 (b : Nat → Bool) : literal (valuationOf b) 1793 = decide (1 ≤ count1793 b) := rfl
theorem meaning1794 (b : Nat → Bool) : literal (valuationOf b) 1794 = decide (2 ≤ count1793 b) := rfl
theorem meaning1795 (b : Nat → Bool) : literal (valuationOf b) 1795 = decide (1 ≤ count1795 b) := rfl
theorem meaning1796 (b : Nat → Bool) : literal (valuationOf b) 1796 = decide (2 ≤ count1795 b) := rfl
theorem meaning1797 (b : Nat → Bool) : literal (valuationOf b) 1797 = decide (3 ≤ count1795 b) := rfl
theorem meaning1798 (b : Nat → Bool) : literal (valuationOf b) 1798 = decide (4 ≤ count1795 b) := rfl
theorem meaning1799 (b : Nat → Bool) : literal (valuationOf b) 1799 = decide (1 ≤ count1799 b) := rfl
theorem meaning1800 (b : Nat → Bool) : literal (valuationOf b) 1800 = decide (2 ≤ count1799 b) := rfl
theorem meaning1801 (b : Nat → Bool) : literal (valuationOf b) 1801 = decide (3 ≤ count1799 b) := rfl
theorem meaning1802 (b : Nat → Bool) : literal (valuationOf b) 1802 = decide (4 ≤ count1799 b) := rfl
theorem meaning1803 (b : Nat → Bool) : literal (valuationOf b) 1803 = decide (5 ≤ count1799 b) := rfl
theorem meaning1804 (b : Nat → Bool) : literal (valuationOf b) 1804 = decide (6 ≤ count1799 b) := rfl
theorem meaning1807 (b : Nat → Bool) : literal (valuationOf b) 1807 = decide (1 ≤ count1807 b) := rfl
theorem meaning1808 (b : Nat → Bool) : literal (valuationOf b) 1808 = decide (2 ≤ count1807 b) := rfl
theorem meaning1809 (b : Nat → Bool) : literal (valuationOf b) 1809 = decide (3 ≤ count1807 b) := rfl
theorem meaning1810 (b : Nat → Bool) : literal (valuationOf b) 1810 = decide (4 ≤ count1807 b) := rfl
theorem meaning1811 (b : Nat → Bool) : literal (valuationOf b) 1811 = decide (5 ≤ count1807 b) := rfl
theorem meaning1812 (b : Nat → Bool) : literal (valuationOf b) 1812 = decide (6 ≤ count1807 b) := rfl
theorem meaning1813 (b : Nat → Bool) : literal (valuationOf b) 1813 = decide (7 ≤ count1807 b) := rfl
theorem meaning1814 (b : Nat → Bool) : literal (valuationOf b) 1814 = decide (8 ≤ count1807 b) := rfl
theorem meaning1815 (b : Nat → Bool) : literal (valuationOf b) 1815 = decide (9 ≤ count1807 b) := rfl
theorem meaning1816 (b : Nat → Bool) : literal (valuationOf b) 1816 = decide (10 ≤ count1807 b) := rfl
theorem meaning1817 (b : Nat → Bool) : literal (valuationOf b) 1817 = decide (11 ≤ count1807 b) := rfl
theorem meaning1829 (b : Nat → Bool) : literal (valuationOf b) 1829 = decide (7 ≤ count1823 b) := rfl
theorem meaning1830 (b : Nat → Bool) : literal (valuationOf b) 1830 = decide (8 ≤ count1823 b) := rfl
theorem meaning1831 (b : Nat → Bool) : literal (valuationOf b) 1831 = decide (9 ≤ count1823 b) := rfl
theorem meaning1832 (b : Nat → Bool) : literal (valuationOf b) 1832 = decide (10 ≤ count1823 b) := rfl
theorem meaning1833 (b : Nat → Bool) : literal (valuationOf b) 1833 = decide (11 ≤ count1823 b) := rfl
theorem meaning1834 (b : Nat → Bool) : literal (valuationOf b) 1834 = decide (12 ≤ count1823 b) := rfl
theorem meaning1835 (b : Nat → Bool) : literal (valuationOf b) 1835 = decide (13 ≤ count1823 b) := rfl
theorem meaning1836 (b : Nat → Bool) : literal (valuationOf b) 1836 = decide (14 ≤ count1823 b) := rfl
theorem meaning1837 (b : Nat → Bool) : literal (valuationOf b) 1837 = decide (15 ≤ count1823 b) := rfl
theorem meaning1838 (b : Nat → Bool) : literal (valuationOf b) 1838 = decide (16 ≤ count1823 b) := rfl
theorem meaning1839 (b : Nat → Bool) : literal (valuationOf b) 1839 = decide (17 ≤ count1823 b) := rfl
theorem meaning1840 (b : Nat → Bool) : literal (valuationOf b) 1840 = decide (18 ≤ count1823 b) := rfl
theorem meaning1841 (b : Nat → Bool) : literal (valuationOf b) 1841 = decide (19 ≤ count1823 b) := rfl
theorem meaning1870 (b : Nat → Bool) : literal (valuationOf b) 1870 = decide (24 ≤ count1847 b) := rfl
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
end Snake9.Regrowth.E112052
