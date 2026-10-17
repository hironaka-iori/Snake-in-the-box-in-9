import TreeRup
namespace B112E149
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
structure Block0 (p : Nat → Bool) : Prop where
  clause1 : p 1 = false ∨ p 2 = false ∨ p 3 = false ∨ p 6 = false
  clause2 : p 2 = false ∨ p 101 = true ∨ p 1 = true ∨ p 5 = true
  clause3 : p 5 = false ∨ p 2 = false ∨ p 3 = false ∨ p 10 = false
  clause4 : p 5 = false ∨ p 2 = false ∨ p 8 = false ∨ p 10 = false
  clause5 : p 5 = false ∨ p 3 = false ∨ p 8 = false ∨ p 10 = false
  clause6 : p 6 = false ∨ p 1 = true ∨ p 7 = true
  clause7 : p 6 = false ∨ p 105 = true ∨ p 1 = true
  clause8 : p 7 = false ∨ p 3 = false ∨ p 6 = false ∨ p 8 = false
  clause9 : p 8 = false ∨ p 5 = true ∨ p 7 = true
  clause10 : p 8 = false ∨ p 107 = true ∨ p 5 = true
  clause11 : p 10 = false ∨ p 109 = true ∨ p 5 = true
  clause12 : p 12 = false ∨ p 111 = true ∨ p 34 = true
  clause13 : p 13 = false ∨ p 14 = false ∨ p 15 = false ∨ p 18 = false
  clause14 : p 14 = false ∨ p 13 = false ∨ p 17 = false ∨ p 31 = false
  clause15 : p 14 = false ∨ p 113 = true ∨ p 17 = true ∨ p 19 = true ∨ p 31 = true
  clause16 : p 14 = false ∨ p 113 = true ∨ p 13 = true ∨ p 19 = true ∨ p 31 = true
  clause17 : p 14 = false ∨ p 113 = true ∨ p 13 = true ∨ p 17 = true ∨ p 19 = true
  clause18 : p 15 = false ∨ p 13 = false ∨ p 16 = false ∨ p 17 = false
  clause19 : p 16 = false ∨ p 15 = false ∨ p 23 = false ∨ p 33 = false
  clause20 : p 17 = false ∨ p 14 = false ∨ p 15 = false ∨ p 22 = false
  clause21 : p 17 = false ∨ p 14 = false ∨ p 15 = false ∨ p 24 = false
  clause22 : p 17 = false ∨ p 14 = false ∨ p 22 = false ∨ p 24 = false
  clause23 : p 17 = false ∨ p 15 = false ∨ p 22 = false ∨ p 24 = false
  clause24 : p 18 = false ∨ p 117 = true ∨ p 13 = true ∨ p 19 = true ∨ p 26 = true
  clause25 : p 18 = false ∨ p 117 = true ∨ p 13 = true ∨ p 19 = true ∨ p 21 = true
  clause26 : p 19 = false ∨ p 14 = false ∨ p 18 = false ∨ p 20 = false
  clause27 : p 19 = false ∨ p 14 = false ∨ p 18 = false ∨ p 22 = false
  clause28 : p 19 = false ∨ p 14 = false ∨ p 18 = false ∨ p 34 = false
  clause29 : p 19 = false ∨ p 14 = false ∨ p 20 = false ∨ p 22 = false
  clause30 : p 19 = false ∨ p 14 = false ∨ p 20 = false ∨ p 34 = false
  clause31 : p 19 = false ∨ p 14 = false ∨ p 22 = false ∨ p 34 = false
  clause32 : p 19 = false ∨ p 18 = false ∨ p 20 = false ∨ p 22 = false
structure Block1 (p : Nat → Bool) : Prop where
  clause33 : p 19 = false ∨ p 18 = false ∨ p 20 = false ∨ p 34 = false
  clause34 : p 19 = false ∨ p 20 = false ∨ p 22 = false ∨ p 34 = false
  clause35 : p 20 = false ∨ p 119 = true ∨ p 19 = true ∨ p 28 = true ∨ p 35 = true
  clause36 : p 21 = false ∨ p 15 = false ∨ p 18 = false ∨ p 22 = false
  clause37 : p 22 = false ∨ p 17 = true ∨ p 19 = true ∨ p 21 = true
  clause38 : p 22 = false ∨ p 121 = true ∨ p 19 = true ∨ p 21 = true
  clause39 : p 22 = false ∨ p 121 = true ∨ p 17 = true ∨ p 19 = true
  clause40 : p 23 = false ∨ p 122 = true ∨ p 16 = true ∨ p 29 = true
  clause41 : p 23 = false ∨ p 122 = true ∨ p 16 = true ∨ p 25 = true
  clause42 : p 24 = false ∨ p 123 = true ∨ p 17 = true
  clause43 : p 25 = false ∨ p 124 = true ∨ p 24 = true ∨ p 30 = true
  clause44 : p 26 = false ∨ p 18 = false ∨ p 27 = false ∨ p 42 = false
  clause45 : p 28 = false ∨ p 20 = false ∨ p 27 = false ∨ p 30 = false
  clause46 : p 31 = false ∨ p 14 = false ∨ p 32 = false ∨ p 34 = false
  clause47 : p 31 = false ∨ p 130 = true ∨ p 32 = true ∨ p 34 = true
  clause48 : p 32 = false ∨ p 131 = true ∨ p 31 = true ∨ p 35 = true
  clause49 : p 33 = false ∨ p 16 = true ∨ p 36 = true
  clause50 : p 33 = false ∨ p 132 = true ∨ p 36 = true
  clause51 : p 33 = false ∨ p 132 = true ∨ p 16 = true
  clause52 : p 34 = false ∨ p 133 = true ∨ p 19 = true ∨ p 31 = true ∨ p 35 = true
  clause53 : p 35 = false ∨ p 20 = false ∨ p 32 = false ∨ p 34 = false
  clause54 : p 35 = false ∨ p 20 = false ∨ p 32 = false ∨ p 37 = false
  clause55 : p 35 = false ∨ p 20 = false ∨ p 34 = false ∨ p 37 = false
  clause56 : p 35 = false ∨ p 32 = false ∨ p 34 = false ∨ p 37 = false
  clause57 : p 36 = false ∨ p 135 = true ∨ p 37 = true
  clause58 : p 37 = false ∨ p 136 = true ∨ p 35 = true ∨ p 45 = true
  clause59 : p 38 = false ∨ p 39 = false ∨ p 41 = false ∨ p 42 = false
  clause60 : p 39 = false ∨ p 138 = true ∨ p 40 = true
  clause61 : p 39 = false ∨ p 138 = true ∨ p 38 = true
  clause62 : p 40 = false ∨ p 139 = true ∨ p 32 = true
  clause63 : p 41 = false ∨ p 38 = true ∨ p 43 = true
  clause64 : p 41 = false ∨ p 140 = true ∨ p 38 = true
structure Block2 (p : Nat → Bool) : Prop where
  clause65 : p 43 = false ∨ p 41 = false ∨ p 42 = false ∨ p 44 = false
  clause66 : p 143 = false ∨ p 44 = true
  clause67 : p 44 = false ∨ p 43 = true ∨ p 45 = true
  clause68 : p 44 = false ∨ p 143 = true ∨ p 45 = true
  clause69 : p 44 = false ∨ p 143 = true ∨ p 43 = true
  clause70 : p 45 = false ∨ p 30 = false ∨ p 37 = false ∨ p 44 = false
  clause71 : p 50 = false ∨ p 149 = true ∨ p 72 = true
  clause72 : p 60 = false ∨ p 159 = true ∨ p 62 = true
  clause73 : p 61 = false ∨ p 160 = true ∨ p 60 = true
  clause74 : p 62 = false ∨ p 161 = true ∨ p 12 = true
  clause75 : p 63 = false ∨ p 162 = true ∨ p 64 = true
  clause76 : p 64 = false ∨ p 163 = true ∨ p 65 = true
  clause77 : p 65 = false ∨ p 164 = true ∨ p 61 = true
  clause78 : p 66 = false ∨ p 165 = true ∨ p 63 = true
  clause79 : p 67 = false ∨ p 166 = true ∨ p 66 = true
  clause80 : p 68 = false ∨ p 167 = true ∨ p 67 = true
  clause81 : p 69 = false ∨ p 68 = true
  clause82 : p 69 = true
  clause83 : p 72 = false ∨ p 50 = false ∨ p 74 = false ∨ p 76 = false
  clause84 : p 72 = false ∨ p 50 = false ∨ p 74 = false ∨ p 89 = false
  clause85 : p 72 = false ∨ p 50 = false ∨ p 76 = false ∨ p 89 = false
  clause86 : p 72 = false ∨ p 74 = false ∨ p 76 = false ∨ p 89 = false
  clause87 : p 74 = false ∨ p 173 = true ∨ p 72 = true
  clause88 : p 81 = false ∨ p 180 = true ∨ p 82 = true
  clause89 : p 82 = false ∨ p 80 = false ∨ p 81 = false ∨ p 83 = false
  clause90 : p 83 = false ∨ p 182 = true ∨ p 82 = true
  clause91 : p 89 = false ∨ p 188 = true ∨ p 72 = true ∨ p 90 = true
  clause92 : p 90 = false ∨ p 86 = false ∨ p 89 = false ∨ p 92 = false
  clause93 : p 111 = false
  clause94 : p 124 = false
  clause95 : p 130 = false
  clause96 : p 135 = false
structure Block3 (p : Nat → Bool) : Prop where
  clause97 : p 139 = false
  clause98 : p 159 = false
  clause99 : p 162 = false
  clause100 : p 164 = false
  clause101 : p 166 = false
  clause102 : p 101 = false ∨ p 199 = true
  clause103 : p 199 = false ∨ p 201 = true
  clause104 : p 105 = false ∨ p 203 = true
  clause105 : p 203 = false ∨ p 205 = true
  clause106 : p 201 = false ∨ p 205 = false ∨ p 208 = true
  clause107 : p 107 = false ∨ p 209 = true
  clause108 : p 209 = false ∨ p 211 = true
  clause109 : p 109 = false ∨ p 215 = true
  clause110 : p 211 = false ∨ p 215 = false ∨ p 218 = true
  clause111 : p 218 = false ∨ p 220 = true
  clause112 : p 208 = false ∨ p 220 = true
  clause113 : p 113 = false ∨ p 221 = true
  clause114 : p 221 = false ∨ p 223 = true
  clause115 : p 117 = false ∨ p 225 = true
  clause116 : p 225 = false ∨ p 227 = true
  clause117 : p 227 = false ∨ p 229 = true
  clause118 : p 223 = false ∨ p 229 = true
  clause119 : p 119 = false ∨ p 231 = true
  clause120 : p 231 = false ∨ p 233 = true
  clause121 : p 123 = false ∨ p 235 = true
  clause122 : p 122 = false ∨ p 235 = true
  clause123 : p 235 = false ∨ p 237 = true
  clause124 : p 121 = false ∨ p 237 = true
  clause125 : p 121 = false ∨ p 235 = false ∨ p 238 = true
  clause126 : p 237 = false ∨ p 239 = true
  clause127 : p 238 = false ∨ p 240 = true
  clause128 : p 233 = false ∨ p 239 = true
structure Block4 (p : Nat → Bool) : Prop where
  clause129 : p 233 = false ∨ p 237 = false ∨ p 240 = true
  clause130 : p 239 = false ∨ p 241 = true
  clause131 : p 240 = false ∨ p 242 = true
  clause132 : p 229 = false ∨ p 241 = true
  clause133 : p 229 = false ∨ p 239 = false ∨ p 242 = true
  clause134 : p 241 = false ∨ p 243 = true
  clause135 : p 242 = false ∨ p 244 = true
  clause136 : p 220 = false ∨ p 244 = true
  clause137 : p 132 = false ∨ p 255 = true
  clause138 : p 131 = false ∨ p 255 = true
  clause139 : p 131 = false ∨ p 132 = false ∨ p 256 = true
  clause140 : p 255 = false ∨ p 257 = true
  clause141 : p 256 = false ∨ p 258 = true
  clause142 : p 133 = false ∨ p 261 = true
  clause143 : p 261 = false ∨ p 263 = true
  clause144 : p 257 = false ∨ p 263 = true
  clause145 : p 257 = false ∨ p 261 = false ∨ p 264 = true
  clause146 : p 258 = false ∨ p 264 = true
  clause147 : p 263 = false ∨ p 265 = true
  clause148 : p 264 = false ∨ p 266 = true
  clause149 : p 138 = false ∨ p 267 = true
  clause150 : p 267 = false ∨ p 269 = true
  clause151 : p 136 = false ∨ p 269 = true
  clause152 : p 140 = false ∨ p 271 = true
  clause153 : p 271 = false ∨ p 273 = true
  clause154 : p 269 = false ∨ p 275 = true
  clause155 : p 269 = false ∨ p 273 = false ∨ p 276 = true
  clause156 : p 143 = false ∨ p 277 = true
  clause157 : p 277 = false ∨ p 279 = true
  clause158 : p 279 = false ∨ p 287 = true
  clause159 : p 287 = false ∨ p 289 = true
  clause160 : p 275 = false ∨ p 287 = false ∨ p 290 = true
structure Block5 (p : Nat → Bool) : Prop where
  clause161 : p 276 = false ∨ p 290 = true
  clause162 : p 289 = false ∨ p 291 = true
  clause163 : p 290 = false ∨ p 292 = true
  clause164 : p 265 = false ∨ p 291 = true
  clause165 : p 265 = false ∨ p 289 = false ∨ p 292 = true
  clause166 : p 266 = false ∨ p 292 = true
  clause167 : p 291 = false ∨ p 293 = true
  clause168 : p 292 = false ∨ p 294 = true
  clause169 : p 243 = false ∨ p 293 = true
  clause170 : p 243 = false ∨ p 291 = false ∨ p 294 = true
  clause171 : p 244 = false ∨ p 294 = true
  clause172 : p 149 = false ∨ p 297 = true
  clause173 : p 297 = false ∨ p 303 = true
  clause174 : p 160 = false ∨ p 309 = true
  clause175 : p 309 = false ∨ p 311 = true
  clause176 : p 311 = false ∨ p 313 = true
  clause177 : p 313 = false ∨ p 315 = true
  clause178 : p 303 = false ∨ p 315 = true
  clause179 : p 163 = false ∨ p 317 = true
  clause180 : p 317 = false ∨ p 319 = true
  clause181 : p 161 = false ∨ p 319 = true
  clause182 : p 165 = false ∨ p 321 = true
  clause183 : p 321 = false ∨ p 323 = true
  clause184 : p 323 = false ∨ p 325 = true
  clause185 : p 319 = false ∨ p 325 = true
  clause186 : p 167 = false ∨ p 329 = true
  clause187 : p 173 = false ∨ p 331 = true
  clause188 : p 331 = false ∨ p 333 = true
  clause189 : p 333 = false ∨ p 335 = true
  clause190 : p 329 = false ∨ p 335 = true
  clause191 : p 335 = false ∨ p 337 = true
  clause192 : p 325 = false ∨ p 337 = true
structure Block6 (p : Nat → Bool) : Prop where
  clause193 : p 337 = false ∨ p 339 = true
  clause194 : p 315 = false ∨ p 339 = true
  clause195 : p 315 = false ∨ p 337 = false ∨ p 340 = true
  clause196 : p 182 = false ∨ p 351 = true
  clause197 : p 180 = false ∨ p 351 = false ∨ p 354 = true
  clause198 : p 354 = false ∨ p 360 = true
  clause199 : p 360 = false ∨ p 362 = true
  clause200 : p 188 = false ∨ p 363 = true
  clause201 : p 363 = false ∨ p 365 = true
  clause202 : p 365 = false ∨ p 371 = true
  clause203 : p 371 = false ∨ p 385 = true
  clause204 : p 385 = false ∨ p 387 = true
  clause205 : p 362 = false ∨ p 388 = true
  clause206 : p 388 = false ∨ p 390 = true
  clause207 : p 339 = false ∨ p 389 = true
  clause208 : p 339 = false ∨ p 387 = false ∨ p 390 = true
  clause209 : p 340 = false ∨ p 390 = true
  clause210 : p 390 = false ∨ p 392 = true
  clause211 : p 293 = false ∨ p 389 = false ∨ p 392 = true
  clause212 : p 294 = false ∨ p 392 = true
  clause213 : p 392 = false
  clause214 : p 6 = true ∨ p 1149 = true
  clause215 : p 3 = true ∨ p 1149 = true
  clause216 : p 1149 = false ∨ p 1151 = true
  clause217 : p 2 = true ∨ p 1151 = true
  clause218 : p 2 = true ∨ p 1149 = false ∨ p 1152 = true
  clause219 : p 10 = true ∨ p 1154 = true
  clause220 : p 1154 = false ∨ p 1156 = true
  clause221 : p 8 = true ∨ p 1156 = true
  clause222 : p 8 = true ∨ p 1154 = false ∨ p 1157 = true
  clause223 : p 1157 = false ∨ p 1160 = true
  clause224 : p 1151 = false ∨ p 1156 = false ∨ p 1160 = true
structure Block7 (p : Nat → Bool) : Prop where
  clause225 : p 1152 = false ∨ p 1160 = true
  clause226 : p 18 = true ∨ p 1165 = true
  clause227 : p 15 = true ∨ p 1165 = true
  clause228 : p 15 = true ∨ p 18 = true ∨ p 1166 = true
  clause229 : p 1165 = false ∨ p 1167 = true
  clause230 : p 1166 = false ∨ p 1168 = true
  clause231 : p 14 = true ∨ p 1167 = true
  clause232 : p 14 = true ∨ p 1165 = false ∨ p 1168 = true
  clause233 : p 23 = true ∨ p 1170 = true
  clause234 : p 22 = true ∨ p 1170 = true
  clause235 : p 1170 = false ∨ p 1172 = true
  clause236 : p 20 = true ∨ p 1172 = true
  clause237 : p 20 = true ∨ p 1170 = false ∨ p 1173 = true
  clause238 : p 1172 = false ∨ p 1175 = true
  clause239 : p 1173 = false ∨ p 1176 = true
  clause240 : p 1167 = false ∨ p 1175 = true
  clause241 : p 1167 = false ∨ p 1172 = false ∨ p 1176 = true
  clause242 : p 1168 = false ∨ p 1176 = true
  clause243 : p 1160 = false ∨ p 1182 = true
  clause244 : p 1160 = false ∨ p 1175 = false ∨ p 1183 = true
  clause245 : p 1160 = false ∨ p 1176 = false ∨ p 1184 = true
  clause246 : p 30 = true ∨ p 1190 = true
  clause247 : p 27 = true ∨ p 1190 = true
  clause248 : p 1190 = false ∨ p 1192 = true
  clause249 : p 24 = true ∨ p 1192 = true
  clause250 : p 24 = true ∨ p 1190 = false ∨ p 1193 = true
  clause251 : p 34 = true ∨ p 1195 = true
  clause252 : p 33 = true ∨ p 1195 = true
  clause253 : p 1195 = false ∨ p 1197 = true
  clause254 : p 32 = true ∨ p 1197 = true
  clause255 : p 1197 = false ∨ p 1200 = true
  clause256 : p 1192 = false ∨ p 1200 = true
structure Block8 (p : Nat → Bool) : Prop where
  clause257 : p 1192 = false ∨ p 1197 = false ∨ p 1201 = true
  clause258 : p 1193 = false ∨ p 1201 = true
  clause259 : p 1193 = false ∨ p 1197 = false ∨ p 1202 = true
  clause260 : p 41 = true ∨ p 1206 = true
  clause261 : p 39 = true ∨ p 1206 = true
  clause262 : p 39 = true ∨ p 41 = true ∨ p 1207 = true
  clause263 : p 1206 = false ∨ p 1208 = true
  clause264 : p 1207 = false ∨ p 1209 = true
  clause265 : p 37 = true ∨ p 1208 = true
  clause266 : p 37 = true ∨ p 1206 = false ∨ p 1209 = true
  clause267 : p 44 = true ∨ p 1211 = true
  clause268 : p 1211 = false ∨ p 1213 = true
  clause269 : p 42 = true ∨ p 1213 = true
  clause270 : p 42 = true ∨ p 1211 = false ∨ p 1214 = true
  clause271 : p 1213 = false ∨ p 1216 = true
  clause272 : p 1214 = false ∨ p 1217 = true
  clause273 : p 1208 = false ∨ p 1216 = true
  clause274 : p 1208 = false ∨ p 1213 = false ∨ p 1217 = true
  clause275 : p 1209 = false ∨ p 1217 = true
  clause276 : p 1217 = false ∨ p 1223 = true
  clause277 : p 1200 = false ∨ p 1216 = false ∨ p 1223 = true
  clause278 : p 1200 = false ∨ p 1217 = false ∨ p 1224 = true
  clause279 : p 1201 = false ∨ p 1216 = false ∨ p 1224 = true
  clause280 : p 1201 = false ∨ p 1217 = false ∨ p 1225 = true
  clause281 : p 1202 = false ∨ p 1224 = true
  clause282 : p 1202 = false ∨ p 1216 = false ∨ p 1225 = true
  clause283 : p 1182 = false ∨ p 1225 = false ∨ p 1236 = true
  clause284 : p 1183 = false ∨ p 1224 = false ∨ p 1236 = true
  clause285 : p 1184 = false ∨ p 1223 = false ∨ p 1236 = true
  clause286 : p 50 = true ∨ p 1240 = true
  clause287 : p 1240 = false ∨ p 1242 = true
  clause288 : p 1242 = false ∨ p 1250 = true
structure Block9 (p : Nat → Bool) : Prop where
  clause289 : p 1250 = false ∨ p 1272 = true
  clause290 : p 76 = true ∨ p 1281 = true
  clause291 : p 1281 = false ∨ p 1283 = true
  clause292 : p 74 = true ∨ p 1283 = true
  clause293 : p 74 = true ∨ p 1281 = false ∨ p 1284 = true
  clause294 : p 83 = true ∨ p 1286 = true
  clause295 : p 81 = true ∨ p 1286 = true
  clause296 : p 1286 = false ∨ p 1288 = true
  clause297 : p 80 = true ∨ p 1288 = true
  clause298 : p 1288 = false ∨ p 1291 = true
  clause299 : p 1283 = false ∨ p 1288 = false ∨ p 1292 = true
  clause300 : p 1284 = false ∨ p 1288 = false ∨ p 1293 = true
  clause301 : p 89 = true ∨ p 1297 = true
  clause302 : p 1297 = false ∨ p 1299 = true
  clause303 : p 86 = true ∨ p 1299 = true
  clause304 : p 92 = true ∨ p 1302 = true
  clause305 : p 1302 = false ∨ p 1306 = true
  clause306 : p 1306 = false ∨ p 1310 = true
  clause307 : p 1299 = false ∨ p 1310 = true
  clause308 : p 1291 = false ∨ p 1310 = false ∨ p 1318 = true
  clause309 : p 1292 = false ∨ p 1318 = true
  clause310 : p 1292 = false ∨ p 1310 = false ∨ p 1319 = true
  clause311 : p 1293 = false ∨ p 1319 = true
  clause312 : p 1319 = false ∨ p 1328 = true
  clause313 : p 1272 = false ∨ p 1318 = false ∨ p 1328 = true
  clause314 : p 1236 = false ∨ p 1328 = false ∨ p 1343 = true
  clause315 : p 1343 = false
  clause316 : p 15 = false ∨ p 17 = false ∨ p 21 = false ∨ p 22 = false
  clause317 : p 23 = false ∨ p 25 = false ∨ p 29 = false ∨ p 30 = false
structure Constraints (p : Nat → Bool) : Prop where
  block0 : Block0 p
  block1 : Block1 p
  block2 : Block2 p
  block3 : Block3 p
  block4 : Block4 p
  block5 : Block5 p
  block6 : Block6 p
  block7 : Block7 p
  block8 : Block8 p
  block9 : Block9 p
def c1 : List Lit := [(1, false), (2, false), (3, false), (6, false)]
theorem step1 (p : Nat → Bool) (h : Constraints p) : clause p c1 = true := by
  simpa only [c1,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause1
def c2 : List Lit := [(2, false), (101, true), (1, true), (5, true)]
theorem step2 (p : Nat → Bool) (h : Constraints p) : clause p c2 = true := by
  simpa only [c2,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause2
def c3 : List Lit := [(5, false), (2, false), (3, false), (10, false)]
theorem step3 (p : Nat → Bool) (h : Constraints p) : clause p c3 = true := by
  simpa only [c3,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause3
def c4 : List Lit := [(5, false), (2, false), (8, false), (10, false)]
theorem step4 (p : Nat → Bool) (h : Constraints p) : clause p c4 = true := by
  simpa only [c4,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause4
def c5 : List Lit := [(5, false), (3, false), (8, false), (10, false)]
theorem step5 (p : Nat → Bool) (h : Constraints p) : clause p c5 = true := by
  simpa only [c5,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause5
def c6 : List Lit := [(6, false), (1, true), (7, true)]
theorem step6 (p : Nat → Bool) (h : Constraints p) : clause p c6 = true := by
  simpa only [c6,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause6
def c7 : List Lit := [(6, false), (105, true), (1, true)]
theorem step7 (p : Nat → Bool) (h : Constraints p) : clause p c7 = true := by
  simpa only [c7,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause7
def c8 : List Lit := [(7, false), (3, false), (6, false), (8, false)]
theorem step8 (p : Nat → Bool) (h : Constraints p) : clause p c8 = true := by
  simpa only [c8,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause8
def c9 : List Lit := [(8, false), (5, true), (7, true)]
theorem step9 (p : Nat → Bool) (h : Constraints p) : clause p c9 = true := by
  simpa only [c9,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause9
def c10 : List Lit := [(8, false), (107, true), (5, true)]
theorem step10 (p : Nat → Bool) (h : Constraints p) : clause p c10 = true := by
  simpa only [c10,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause10
def c11 : List Lit := [(10, false), (109, true), (5, true)]
theorem step11 (p : Nat → Bool) (h : Constraints p) : clause p c11 = true := by
  simpa only [c11,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause11
def c12 : List Lit := [(12, false), (111, true), (34, true)]
theorem step12 (p : Nat → Bool) (h : Constraints p) : clause p c12 = true := by
  simpa only [c12,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause12
def c13 : List Lit := [(13, false), (14, false), (15, false), (18, false)]
theorem step13 (p : Nat → Bool) (h : Constraints p) : clause p c13 = true := by
  simpa only [c13,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause13
def c14 : List Lit := [(14, false), (13, false), (17, false), (31, false)]
theorem step14 (p : Nat → Bool) (h : Constraints p) : clause p c14 = true := by
  simpa only [c14,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause14
def c15 : List Lit := [(14, false), (113, true), (17, true), (19, true), (31, true)]
theorem step15 (p : Nat → Bool) (h : Constraints p) : clause p c15 = true := by
  simpa only [c15,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause15
def c16 : List Lit := [(14, false), (113, true), (13, true), (19, true), (31, true)]
theorem step16 (p : Nat → Bool) (h : Constraints p) : clause p c16 = true := by
  simpa only [c16,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause16
def c17 : List Lit := [(14, false), (113, true), (13, true), (17, true), (19, true)]
theorem step17 (p : Nat → Bool) (h : Constraints p) : clause p c17 = true := by
  simpa only [c17,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause17
def c18 : List Lit := [(15, false), (13, false), (16, false), (17, false)]
theorem step18 (p : Nat → Bool) (h : Constraints p) : clause p c18 = true := by
  simpa only [c18,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause18
def c19 : List Lit := [(16, false), (15, false), (23, false), (33, false)]
theorem step19 (p : Nat → Bool) (h : Constraints p) : clause p c19 = true := by
  simpa only [c19,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause19
def c20 : List Lit := [(17, false), (14, false), (15, false), (22, false)]
theorem step20 (p : Nat → Bool) (h : Constraints p) : clause p c20 = true := by
  simpa only [c20,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause20
def c21 : List Lit := [(17, false), (14, false), (15, false), (24, false)]
theorem step21 (p : Nat → Bool) (h : Constraints p) : clause p c21 = true := by
  simpa only [c21,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause21
def c22 : List Lit := [(17, false), (14, false), (22, false), (24, false)]
theorem step22 (p : Nat → Bool) (h : Constraints p) : clause p c22 = true := by
  simpa only [c22,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause22
def c23 : List Lit := [(17, false), (15, false), (22, false), (24, false)]
theorem step23 (p : Nat → Bool) (h : Constraints p) : clause p c23 = true := by
  simpa only [c23,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause23
def c24 : List Lit := [(18, false), (117, true), (13, true), (19, true), (26, true)]
theorem step24 (p : Nat → Bool) (h : Constraints p) : clause p c24 = true := by
  simpa only [c24,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause24
def c25 : List Lit := [(18, false), (117, true), (13, true), (19, true), (21, true)]
theorem step25 (p : Nat → Bool) (h : Constraints p) : clause p c25 = true := by
  simpa only [c25,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause25
def c26 : List Lit := [(19, false), (14, false), (18, false), (20, false)]
theorem step26 (p : Nat → Bool) (h : Constraints p) : clause p c26 = true := by
  simpa only [c26,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause26
def c27 : List Lit := [(19, false), (14, false), (18, false), (22, false)]
theorem step27 (p : Nat → Bool) (h : Constraints p) : clause p c27 = true := by
  simpa only [c27,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause27
def c28 : List Lit := [(19, false), (14, false), (18, false), (34, false)]
theorem step28 (p : Nat → Bool) (h : Constraints p) : clause p c28 = true := by
  simpa only [c28,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause28
def c29 : List Lit := [(19, false), (14, false), (20, false), (22, false)]
theorem step29 (p : Nat → Bool) (h : Constraints p) : clause p c29 = true := by
  simpa only [c29,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause29
def c30 : List Lit := [(19, false), (14, false), (20, false), (34, false)]
theorem step30 (p : Nat → Bool) (h : Constraints p) : clause p c30 = true := by
  simpa only [c30,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause30
def c31 : List Lit := [(19, false), (14, false), (22, false), (34, false)]
theorem step31 (p : Nat → Bool) (h : Constraints p) : clause p c31 = true := by
  simpa only [c31,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause31
def c32 : List Lit := [(19, false), (18, false), (20, false), (22, false)]
theorem step32 (p : Nat → Bool) (h : Constraints p) : clause p c32 = true := by
  simpa only [c32,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause32
def c33 : List Lit := [(19, false), (18, false), (20, false), (34, false)]
theorem step33 (p : Nat → Bool) (h : Constraints p) : clause p c33 = true := by
  simpa only [c33,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause33
def c34 : List Lit := [(19, false), (20, false), (22, false), (34, false)]
theorem step34 (p : Nat → Bool) (h : Constraints p) : clause p c34 = true := by
  simpa only [c34,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause34
def c35 : List Lit := [(20, false), (119, true), (19, true), (28, true), (35, true)]
theorem step35 (p : Nat → Bool) (h : Constraints p) : clause p c35 = true := by
  simpa only [c35,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause35
def c36 : List Lit := [(21, false), (15, false), (18, false), (22, false)]
theorem step36 (p : Nat → Bool) (h : Constraints p) : clause p c36 = true := by
  simpa only [c36,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause36
def c37 : List Lit := [(22, false), (17, true), (19, true), (21, true)]
theorem step37 (p : Nat → Bool) (h : Constraints p) : clause p c37 = true := by
  simpa only [c37,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause37
def c38 : List Lit := [(22, false), (121, true), (19, true), (21, true)]
theorem step38 (p : Nat → Bool) (h : Constraints p) : clause p c38 = true := by
  simpa only [c38,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause38
def c39 : List Lit := [(22, false), (121, true), (17, true), (19, true)]
theorem step39 (p : Nat → Bool) (h : Constraints p) : clause p c39 = true := by
  simpa only [c39,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause39
def c40 : List Lit := [(23, false), (122, true), (16, true), (29, true)]
theorem step40 (p : Nat → Bool) (h : Constraints p) : clause p c40 = true := by
  simpa only [c40,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause40
def c41 : List Lit := [(23, false), (122, true), (16, true), (25, true)]
theorem step41 (p : Nat → Bool) (h : Constraints p) : clause p c41 = true := by
  simpa only [c41,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause41
def c42 : List Lit := [(24, false), (123, true), (17, true)]
theorem step42 (p : Nat → Bool) (h : Constraints p) : clause p c42 = true := by
  simpa only [c42,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause42
def c43 : List Lit := [(25, false), (124, true), (24, true), (30, true)]
theorem step43 (p : Nat → Bool) (h : Constraints p) : clause p c43 = true := by
  simpa only [c43,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause43
def c44 : List Lit := [(26, false), (18, false), (27, false), (42, false)]
theorem step44 (p : Nat → Bool) (h : Constraints p) : clause p c44 = true := by
  simpa only [c44,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause44
def c45 : List Lit := [(28, false), (20, false), (27, false), (30, false)]
theorem step45 (p : Nat → Bool) (h : Constraints p) : clause p c45 = true := by
  simpa only [c45,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause45
def c46 : List Lit := [(31, false), (14, false), (32, false), (34, false)]
theorem step46 (p : Nat → Bool) (h : Constraints p) : clause p c46 = true := by
  simpa only [c46,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause46
def c47 : List Lit := [(31, false), (130, true), (32, true), (34, true)]
theorem step47 (p : Nat → Bool) (h : Constraints p) : clause p c47 = true := by
  simpa only [c47,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause47
def c48 : List Lit := [(32, false), (131, true), (31, true), (35, true)]
theorem step48 (p : Nat → Bool) (h : Constraints p) : clause p c48 = true := by
  simpa only [c48,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause48
def c49 : List Lit := [(33, false), (16, true), (36, true)]
theorem step49 (p : Nat → Bool) (h : Constraints p) : clause p c49 = true := by
  simpa only [c49,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause49
def c50 : List Lit := [(33, false), (132, true), (36, true)]
theorem step50 (p : Nat → Bool) (h : Constraints p) : clause p c50 = true := by
  simpa only [c50,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause50
def c51 : List Lit := [(33, false), (132, true), (16, true)]
theorem step51 (p : Nat → Bool) (h : Constraints p) : clause p c51 = true := by
  simpa only [c51,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause51
def c52 : List Lit := [(34, false), (133, true), (19, true), (31, true), (35, true)]
theorem step52 (p : Nat → Bool) (h : Constraints p) : clause p c52 = true := by
  simpa only [c52,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause52
def c53 : List Lit := [(35, false), (20, false), (32, false), (34, false)]
theorem step53 (p : Nat → Bool) (h : Constraints p) : clause p c53 = true := by
  simpa only [c53,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause53
def c54 : List Lit := [(35, false), (20, false), (32, false), (37, false)]
theorem step54 (p : Nat → Bool) (h : Constraints p) : clause p c54 = true := by
  simpa only [c54,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause54
def c55 : List Lit := [(35, false), (20, false), (34, false), (37, false)]
theorem step55 (p : Nat → Bool) (h : Constraints p) : clause p c55 = true := by
  simpa only [c55,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause55
def c56 : List Lit := [(35, false), (32, false), (34, false), (37, false)]
theorem step56 (p : Nat → Bool) (h : Constraints p) : clause p c56 = true := by
  simpa only [c56,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause56
def c57 : List Lit := [(36, false), (135, true), (37, true)]
theorem step57 (p : Nat → Bool) (h : Constraints p) : clause p c57 = true := by
  simpa only [c57,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause57
def c58 : List Lit := [(37, false), (136, true), (35, true), (45, true)]
theorem step58 (p : Nat → Bool) (h : Constraints p) : clause p c58 = true := by
  simpa only [c58,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause58
def c59 : List Lit := [(38, false), (39, false), (41, false), (42, false)]
theorem step59 (p : Nat → Bool) (h : Constraints p) : clause p c59 = true := by
  simpa only [c59,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause59
def c60 : List Lit := [(39, false), (138, true), (40, true)]
theorem step60 (p : Nat → Bool) (h : Constraints p) : clause p c60 = true := by
  simpa only [c60,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause60
def c61 : List Lit := [(39, false), (138, true), (38, true)]
theorem step61 (p : Nat → Bool) (h : Constraints p) : clause p c61 = true := by
  simpa only [c61,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause61
def c62 : List Lit := [(40, false), (139, true), (32, true)]
theorem step62 (p : Nat → Bool) (h : Constraints p) : clause p c62 = true := by
  simpa only [c62,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause62
def c63 : List Lit := [(41, false), (38, true), (43, true)]
theorem step63 (p : Nat → Bool) (h : Constraints p) : clause p c63 = true := by
  simpa only [c63,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause63
def c64 : List Lit := [(41, false), (140, true), (38, true)]
theorem step64 (p : Nat → Bool) (h : Constraints p) : clause p c64 = true := by
  simpa only [c64,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause64
def c65 : List Lit := [(43, false), (41, false), (42, false), (44, false)]
theorem step65 (p : Nat → Bool) (h : Constraints p) : clause p c65 = true := by
  simpa only [c65,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause65
def c66 : List Lit := [(143, false), (44, true)]
theorem step66 (p : Nat → Bool) (h : Constraints p) : clause p c66 = true := by
  simpa only [c66,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause66
def c67 : List Lit := [(44, false), (43, true), (45, true)]
theorem step67 (p : Nat → Bool) (h : Constraints p) : clause p c67 = true := by
  simpa only [c67,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause67
def c68 : List Lit := [(44, false), (143, true), (45, true)]
theorem step68 (p : Nat → Bool) (h : Constraints p) : clause p c68 = true := by
  simpa only [c68,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause68
def c69 : List Lit := [(44, false), (143, true), (43, true)]
theorem step69 (p : Nat → Bool) (h : Constraints p) : clause p c69 = true := by
  simpa only [c69,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause69
def c70 : List Lit := [(45, false), (30, false), (37, false), (44, false)]
theorem step70 (p : Nat → Bool) (h : Constraints p) : clause p c70 = true := by
  simpa only [c70,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause70
def c71 : List Lit := [(50, false), (149, true), (72, true)]
theorem step71 (p : Nat → Bool) (h : Constraints p) : clause p c71 = true := by
  simpa only [c71,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause71
def c72 : List Lit := [(60, false), (159, true), (62, true)]
theorem step72 (p : Nat → Bool) (h : Constraints p) : clause p c72 = true := by
  simpa only [c72,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause72
def c73 : List Lit := [(61, false), (160, true), (60, true)]
theorem step73 (p : Nat → Bool) (h : Constraints p) : clause p c73 = true := by
  simpa only [c73,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause73
def c74 : List Lit := [(62, false), (161, true), (12, true)]
theorem step74 (p : Nat → Bool) (h : Constraints p) : clause p c74 = true := by
  simpa only [c74,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause74
def c75 : List Lit := [(63, false), (162, true), (64, true)]
theorem step75 (p : Nat → Bool) (h : Constraints p) : clause p c75 = true := by
  simpa only [c75,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause75
def c76 : List Lit := [(64, false), (163, true), (65, true)]
theorem step76 (p : Nat → Bool) (h : Constraints p) : clause p c76 = true := by
  simpa only [c76,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause76
def c77 : List Lit := [(65, false), (164, true), (61, true)]
theorem step77 (p : Nat → Bool) (h : Constraints p) : clause p c77 = true := by
  simpa only [c77,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause77
def c78 : List Lit := [(66, false), (165, true), (63, true)]
theorem step78 (p : Nat → Bool) (h : Constraints p) : clause p c78 = true := by
  simpa only [c78,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause78
def c79 : List Lit := [(67, false), (166, true), (66, true)]
theorem step79 (p : Nat → Bool) (h : Constraints p) : clause p c79 = true := by
  simpa only [c79,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause79
def c80 : List Lit := [(68, false), (167, true), (67, true)]
theorem step80 (p : Nat → Bool) (h : Constraints p) : clause p c80 = true := by
  simpa only [c80,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause80
def c81 : List Lit := [(69, false), (68, true)]
theorem step81 (p : Nat → Bool) (h : Constraints p) : clause p c81 = true := by
  simpa only [c81,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause81
def c82 : List Lit := [(69, true)]
theorem step82 (p : Nat → Bool) (h : Constraints p) : clause p c82 = true := by
  simpa only [c82,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause82
def c83 : List Lit := [(72, false), (50, false), (74, false), (76, false)]
theorem step83 (p : Nat → Bool) (h : Constraints p) : clause p c83 = true := by
  simpa only [c83,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause83
def c84 : List Lit := [(72, false), (50, false), (74, false), (89, false)]
theorem step84 (p : Nat → Bool) (h : Constraints p) : clause p c84 = true := by
  simpa only [c84,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause84
def c85 : List Lit := [(72, false), (50, false), (76, false), (89, false)]
theorem step85 (p : Nat → Bool) (h : Constraints p) : clause p c85 = true := by
  simpa only [c85,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause85
def c86 : List Lit := [(72, false), (74, false), (76, false), (89, false)]
theorem step86 (p : Nat → Bool) (h : Constraints p) : clause p c86 = true := by
  simpa only [c86,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause86
def c87 : List Lit := [(74, false), (173, true), (72, true)]
theorem step87 (p : Nat → Bool) (h : Constraints p) : clause p c87 = true := by
  simpa only [c87,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause87
def c88 : List Lit := [(81, false), (180, true), (82, true)]
theorem step88 (p : Nat → Bool) (h : Constraints p) : clause p c88 = true := by
  simpa only [c88,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause88
def c89 : List Lit := [(82, false), (80, false), (81, false), (83, false)]
theorem step89 (p : Nat → Bool) (h : Constraints p) : clause p c89 = true := by
  simpa only [c89,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause89
def c90 : List Lit := [(83, false), (182, true), (82, true)]
theorem step90 (p : Nat → Bool) (h : Constraints p) : clause p c90 = true := by
  simpa only [c90,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause90
def c91 : List Lit := [(89, false), (188, true), (72, true), (90, true)]
theorem step91 (p : Nat → Bool) (h : Constraints p) : clause p c91 = true := by
  simpa only [c91,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause91
def c92 : List Lit := [(90, false), (86, false), (89, false), (92, false)]
theorem step92 (p : Nat → Bool) (h : Constraints p) : clause p c92 = true := by
  simpa only [c92,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause92
def c93 : List Lit := [(111, false)]
theorem step93 (p : Nat → Bool) (h : Constraints p) : clause p c93 = true := by
  simpa only [c93,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause93
def c94 : List Lit := [(124, false)]
theorem step94 (p : Nat → Bool) (h : Constraints p) : clause p c94 = true := by
  simpa only [c94,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause94
def c95 : List Lit := [(130, false)]
theorem step95 (p : Nat → Bool) (h : Constraints p) : clause p c95 = true := by
  simpa only [c95,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause95
def c96 : List Lit := [(135, false)]
theorem step96 (p : Nat → Bool) (h : Constraints p) : clause p c96 = true := by
  simpa only [c96,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause96
def c97 : List Lit := [(139, false)]
theorem step97 (p : Nat → Bool) (h : Constraints p) : clause p c97 = true := by
  simpa only [c97,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause97
def c98 : List Lit := [(159, false)]
theorem step98 (p : Nat → Bool) (h : Constraints p) : clause p c98 = true := by
  simpa only [c98,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause98
def c99 : List Lit := [(162, false)]
theorem step99 (p : Nat → Bool) (h : Constraints p) : clause p c99 = true := by
  simpa only [c99,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause99
def c100 : List Lit := [(164, false)]
theorem step100 (p : Nat → Bool) (h : Constraints p) : clause p c100 = true := by
  simpa only [c100,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause100
def c101 : List Lit := [(166, false)]
theorem step101 (p : Nat → Bool) (h : Constraints p) : clause p c101 = true := by
  simpa only [c101,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause101
def c102 : List Lit := [(101, false), (199, true)]
theorem step102 (p : Nat → Bool) (h : Constraints p) : clause p c102 = true := by
  simpa only [c102,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause102
def c103 : List Lit := [(199, false), (201, true)]
theorem step103 (p : Nat → Bool) (h : Constraints p) : clause p c103 = true := by
  simpa only [c103,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause103
def c104 : List Lit := [(105, false), (203, true)]
theorem step104 (p : Nat → Bool) (h : Constraints p) : clause p c104 = true := by
  simpa only [c104,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause104
def c105 : List Lit := [(203, false), (205, true)]
theorem step105 (p : Nat → Bool) (h : Constraints p) : clause p c105 = true := by
  simpa only [c105,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause105
def c106 : List Lit := [(201, false), (205, false), (208, true)]
theorem step106 (p : Nat → Bool) (h : Constraints p) : clause p c106 = true := by
  simpa only [c106,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause106
def c107 : List Lit := [(107, false), (209, true)]
theorem step107 (p : Nat → Bool) (h : Constraints p) : clause p c107 = true := by
  simpa only [c107,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause107
def c108 : List Lit := [(209, false), (211, true)]
theorem step108 (p : Nat → Bool) (h : Constraints p) : clause p c108 = true := by
  simpa only [c108,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause108
def c109 : List Lit := [(109, false), (215, true)]
theorem step109 (p : Nat → Bool) (h : Constraints p) : clause p c109 = true := by
  simpa only [c109,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause109
def c110 : List Lit := [(211, false), (215, false), (218, true)]
theorem step110 (p : Nat → Bool) (h : Constraints p) : clause p c110 = true := by
  simpa only [c110,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause110
def c111 : List Lit := [(218, false), (220, true)]
theorem step111 (p : Nat → Bool) (h : Constraints p) : clause p c111 = true := by
  simpa only [c111,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause111
def c112 : List Lit := [(208, false), (220, true)]
theorem step112 (p : Nat → Bool) (h : Constraints p) : clause p c112 = true := by
  simpa only [c112,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause112
def c113 : List Lit := [(113, false), (221, true)]
theorem step113 (p : Nat → Bool) (h : Constraints p) : clause p c113 = true := by
  simpa only [c113,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause113
def c114 : List Lit := [(221, false), (223, true)]
theorem step114 (p : Nat → Bool) (h : Constraints p) : clause p c114 = true := by
  simpa only [c114,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause114
def c115 : List Lit := [(117, false), (225, true)]
theorem step115 (p : Nat → Bool) (h : Constraints p) : clause p c115 = true := by
  simpa only [c115,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause115
def c116 : List Lit := [(225, false), (227, true)]
theorem step116 (p : Nat → Bool) (h : Constraints p) : clause p c116 = true := by
  simpa only [c116,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause116
def c117 : List Lit := [(227, false), (229, true)]
theorem step117 (p : Nat → Bool) (h : Constraints p) : clause p c117 = true := by
  simpa only [c117,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause117
def c118 : List Lit := [(223, false), (229, true)]
theorem step118 (p : Nat → Bool) (h : Constraints p) : clause p c118 = true := by
  simpa only [c118,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause118
def c119 : List Lit := [(119, false), (231, true)]
theorem step119 (p : Nat → Bool) (h : Constraints p) : clause p c119 = true := by
  simpa only [c119,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause119
def c120 : List Lit := [(231, false), (233, true)]
theorem step120 (p : Nat → Bool) (h : Constraints p) : clause p c120 = true := by
  simpa only [c120,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause120
def c121 : List Lit := [(123, false), (235, true)]
theorem step121 (p : Nat → Bool) (h : Constraints p) : clause p c121 = true := by
  simpa only [c121,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause121
def c122 : List Lit := [(122, false), (235, true)]
theorem step122 (p : Nat → Bool) (h : Constraints p) : clause p c122 = true := by
  simpa only [c122,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause122
def c123 : List Lit := [(235, false), (237, true)]
theorem step123 (p : Nat → Bool) (h : Constraints p) : clause p c123 = true := by
  simpa only [c123,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause123
def c124 : List Lit := [(121, false), (237, true)]
theorem step124 (p : Nat → Bool) (h : Constraints p) : clause p c124 = true := by
  simpa only [c124,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause124
def c125 : List Lit := [(121, false), (235, false), (238, true)]
theorem step125 (p : Nat → Bool) (h : Constraints p) : clause p c125 = true := by
  simpa only [c125,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause125
def c126 : List Lit := [(237, false), (239, true)]
theorem step126 (p : Nat → Bool) (h : Constraints p) : clause p c126 = true := by
  simpa only [c126,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause126
def c127 : List Lit := [(238, false), (240, true)]
theorem step127 (p : Nat → Bool) (h : Constraints p) : clause p c127 = true := by
  simpa only [c127,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause127
def c128 : List Lit := [(233, false), (239, true)]
theorem step128 (p : Nat → Bool) (h : Constraints p) : clause p c128 = true := by
  simpa only [c128,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause128
def c129 : List Lit := [(233, false), (237, false), (240, true)]
theorem step129 (p : Nat → Bool) (h : Constraints p) : clause p c129 = true := by
  simpa only [c129,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause129
def c130 : List Lit := [(239, false), (241, true)]
theorem step130 (p : Nat → Bool) (h : Constraints p) : clause p c130 = true := by
  simpa only [c130,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause130
def c131 : List Lit := [(240, false), (242, true)]
theorem step131 (p : Nat → Bool) (h : Constraints p) : clause p c131 = true := by
  simpa only [c131,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause131
def c132 : List Lit := [(229, false), (241, true)]
theorem step132 (p : Nat → Bool) (h : Constraints p) : clause p c132 = true := by
  simpa only [c132,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause132
def c133 : List Lit := [(229, false), (239, false), (242, true)]
theorem step133 (p : Nat → Bool) (h : Constraints p) : clause p c133 = true := by
  simpa only [c133,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause133
def c134 : List Lit := [(241, false), (243, true)]
theorem step134 (p : Nat → Bool) (h : Constraints p) : clause p c134 = true := by
  simpa only [c134,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause134
def c135 : List Lit := [(242, false), (244, true)]
theorem step135 (p : Nat → Bool) (h : Constraints p) : clause p c135 = true := by
  simpa only [c135,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause135
def c136 : List Lit := [(220, false), (244, true)]
theorem step136 (p : Nat → Bool) (h : Constraints p) : clause p c136 = true := by
  simpa only [c136,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause136
def c137 : List Lit := [(132, false), (255, true)]
theorem step137 (p : Nat → Bool) (h : Constraints p) : clause p c137 = true := by
  simpa only [c137,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause137
def c138 : List Lit := [(131, false), (255, true)]
theorem step138 (p : Nat → Bool) (h : Constraints p) : clause p c138 = true := by
  simpa only [c138,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause138
def c139 : List Lit := [(131, false), (132, false), (256, true)]
theorem step139 (p : Nat → Bool) (h : Constraints p) : clause p c139 = true := by
  simpa only [c139,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause139
def c140 : List Lit := [(255, false), (257, true)]
theorem step140 (p : Nat → Bool) (h : Constraints p) : clause p c140 = true := by
  simpa only [c140,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause140
def c141 : List Lit := [(256, false), (258, true)]
theorem step141 (p : Nat → Bool) (h : Constraints p) : clause p c141 = true := by
  simpa only [c141,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause141
def c142 : List Lit := [(133, false), (261, true)]
theorem step142 (p : Nat → Bool) (h : Constraints p) : clause p c142 = true := by
  simpa only [c142,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause142
def c143 : List Lit := [(261, false), (263, true)]
theorem step143 (p : Nat → Bool) (h : Constraints p) : clause p c143 = true := by
  simpa only [c143,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause143
def c144 : List Lit := [(257, false), (263, true)]
theorem step144 (p : Nat → Bool) (h : Constraints p) : clause p c144 = true := by
  simpa only [c144,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause144
def c145 : List Lit := [(257, false), (261, false), (264, true)]
theorem step145 (p : Nat → Bool) (h : Constraints p) : clause p c145 = true := by
  simpa only [c145,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause145
def c146 : List Lit := [(258, false), (264, true)]
theorem step146 (p : Nat → Bool) (h : Constraints p) : clause p c146 = true := by
  simpa only [c146,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause146
def c147 : List Lit := [(263, false), (265, true)]
theorem step147 (p : Nat → Bool) (h : Constraints p) : clause p c147 = true := by
  simpa only [c147,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause147
def c148 : List Lit := [(264, false), (266, true)]
theorem step148 (p : Nat → Bool) (h : Constraints p) : clause p c148 = true := by
  simpa only [c148,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause148
def c149 : List Lit := [(138, false), (267, true)]
theorem step149 (p : Nat → Bool) (h : Constraints p) : clause p c149 = true := by
  simpa only [c149,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause149
def c150 : List Lit := [(267, false), (269, true)]
theorem step150 (p : Nat → Bool) (h : Constraints p) : clause p c150 = true := by
  simpa only [c150,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause150
def c151 : List Lit := [(136, false), (269, true)]
theorem step151 (p : Nat → Bool) (h : Constraints p) : clause p c151 = true := by
  simpa only [c151,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause151
def c152 : List Lit := [(140, false), (271, true)]
theorem step152 (p : Nat → Bool) (h : Constraints p) : clause p c152 = true := by
  simpa only [c152,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause152
def c153 : List Lit := [(271, false), (273, true)]
theorem step153 (p : Nat → Bool) (h : Constraints p) : clause p c153 = true := by
  simpa only [c153,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause153
def c154 : List Lit := [(269, false), (275, true)]
theorem step154 (p : Nat → Bool) (h : Constraints p) : clause p c154 = true := by
  simpa only [c154,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause154
def c155 : List Lit := [(269, false), (273, false), (276, true)]
theorem step155 (p : Nat → Bool) (h : Constraints p) : clause p c155 = true := by
  simpa only [c155,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause155
def c156 : List Lit := [(143, false), (277, true)]
theorem step156 (p : Nat → Bool) (h : Constraints p) : clause p c156 = true := by
  simpa only [c156,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause156
def c157 : List Lit := [(277, false), (279, true)]
theorem step157 (p : Nat → Bool) (h : Constraints p) : clause p c157 = true := by
  simpa only [c157,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause157
def c158 : List Lit := [(279, false), (287, true)]
theorem step158 (p : Nat → Bool) (h : Constraints p) : clause p c158 = true := by
  simpa only [c158,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause158
def c159 : List Lit := [(287, false), (289, true)]
theorem step159 (p : Nat → Bool) (h : Constraints p) : clause p c159 = true := by
  simpa only [c159,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause159
def c160 : List Lit := [(275, false), (287, false), (290, true)]
theorem step160 (p : Nat → Bool) (h : Constraints p) : clause p c160 = true := by
  simpa only [c160,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause160
def c161 : List Lit := [(276, false), (290, true)]
theorem step161 (p : Nat → Bool) (h : Constraints p) : clause p c161 = true := by
  simpa only [c161,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause161
def c162 : List Lit := [(289, false), (291, true)]
theorem step162 (p : Nat → Bool) (h : Constraints p) : clause p c162 = true := by
  simpa only [c162,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause162
def c163 : List Lit := [(290, false), (292, true)]
theorem step163 (p : Nat → Bool) (h : Constraints p) : clause p c163 = true := by
  simpa only [c163,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause163
def c164 : List Lit := [(265, false), (291, true)]
theorem step164 (p : Nat → Bool) (h : Constraints p) : clause p c164 = true := by
  simpa only [c164,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause164
def c165 : List Lit := [(265, false), (289, false), (292, true)]
theorem step165 (p : Nat → Bool) (h : Constraints p) : clause p c165 = true := by
  simpa only [c165,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause165
def c166 : List Lit := [(266, false), (292, true)]
theorem step166 (p : Nat → Bool) (h : Constraints p) : clause p c166 = true := by
  simpa only [c166,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause166
def c167 : List Lit := [(291, false), (293, true)]
theorem step167 (p : Nat → Bool) (h : Constraints p) : clause p c167 = true := by
  simpa only [c167,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause167
def c168 : List Lit := [(292, false), (294, true)]
theorem step168 (p : Nat → Bool) (h : Constraints p) : clause p c168 = true := by
  simpa only [c168,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause168
def c169 : List Lit := [(243, false), (293, true)]
theorem step169 (p : Nat → Bool) (h : Constraints p) : clause p c169 = true := by
  simpa only [c169,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause169
def c170 : List Lit := [(243, false), (291, false), (294, true)]
theorem step170 (p : Nat → Bool) (h : Constraints p) : clause p c170 = true := by
  simpa only [c170,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause170
def c171 : List Lit := [(244, false), (294, true)]
theorem step171 (p : Nat → Bool) (h : Constraints p) : clause p c171 = true := by
  simpa only [c171,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause171
def c172 : List Lit := [(149, false), (297, true)]
theorem step172 (p : Nat → Bool) (h : Constraints p) : clause p c172 = true := by
  simpa only [c172,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause172
def c173 : List Lit := [(297, false), (303, true)]
theorem step173 (p : Nat → Bool) (h : Constraints p) : clause p c173 = true := by
  simpa only [c173,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause173
def c174 : List Lit := [(160, false), (309, true)]
theorem step174 (p : Nat → Bool) (h : Constraints p) : clause p c174 = true := by
  simpa only [c174,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause174
def c175 : List Lit := [(309, false), (311, true)]
theorem step175 (p : Nat → Bool) (h : Constraints p) : clause p c175 = true := by
  simpa only [c175,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause175
def c176 : List Lit := [(311, false), (313, true)]
theorem step176 (p : Nat → Bool) (h : Constraints p) : clause p c176 = true := by
  simpa only [c176,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause176
def c177 : List Lit := [(313, false), (315, true)]
theorem step177 (p : Nat → Bool) (h : Constraints p) : clause p c177 = true := by
  simpa only [c177,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause177
def c178 : List Lit := [(303, false), (315, true)]
theorem step178 (p : Nat → Bool) (h : Constraints p) : clause p c178 = true := by
  simpa only [c178,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause178
def c179 : List Lit := [(163, false), (317, true)]
theorem step179 (p : Nat → Bool) (h : Constraints p) : clause p c179 = true := by
  simpa only [c179,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause179
def c180 : List Lit := [(317, false), (319, true)]
theorem step180 (p : Nat → Bool) (h : Constraints p) : clause p c180 = true := by
  simpa only [c180,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause180
def c181 : List Lit := [(161, false), (319, true)]
theorem step181 (p : Nat → Bool) (h : Constraints p) : clause p c181 = true := by
  simpa only [c181,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause181
def c182 : List Lit := [(165, false), (321, true)]
theorem step182 (p : Nat → Bool) (h : Constraints p) : clause p c182 = true := by
  simpa only [c182,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause182
def c183 : List Lit := [(321, false), (323, true)]
theorem step183 (p : Nat → Bool) (h : Constraints p) : clause p c183 = true := by
  simpa only [c183,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause183
def c184 : List Lit := [(323, false), (325, true)]
theorem step184 (p : Nat → Bool) (h : Constraints p) : clause p c184 = true := by
  simpa only [c184,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause184
def c185 : List Lit := [(319, false), (325, true)]
theorem step185 (p : Nat → Bool) (h : Constraints p) : clause p c185 = true := by
  simpa only [c185,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause185
def c186 : List Lit := [(167, false), (329, true)]
theorem step186 (p : Nat → Bool) (h : Constraints p) : clause p c186 = true := by
  simpa only [c186,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause186
def c187 : List Lit := [(173, false), (331, true)]
theorem step187 (p : Nat → Bool) (h : Constraints p) : clause p c187 = true := by
  simpa only [c187,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause187
def c188 : List Lit := [(331, false), (333, true)]
theorem step188 (p : Nat → Bool) (h : Constraints p) : clause p c188 = true := by
  simpa only [c188,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause188
def c189 : List Lit := [(333, false), (335, true)]
theorem step189 (p : Nat → Bool) (h : Constraints p) : clause p c189 = true := by
  simpa only [c189,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause189
def c190 : List Lit := [(329, false), (335, true)]
theorem step190 (p : Nat → Bool) (h : Constraints p) : clause p c190 = true := by
  simpa only [c190,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause190
def c191 : List Lit := [(335, false), (337, true)]
theorem step191 (p : Nat → Bool) (h : Constraints p) : clause p c191 = true := by
  simpa only [c191,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause191
def c192 : List Lit := [(325, false), (337, true)]
theorem step192 (p : Nat → Bool) (h : Constraints p) : clause p c192 = true := by
  simpa only [c192,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause192
def c193 : List Lit := [(337, false), (339, true)]
theorem step193 (p : Nat → Bool) (h : Constraints p) : clause p c193 = true := by
  simpa only [c193,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause193
def c194 : List Lit := [(315, false), (339, true)]
theorem step194 (p : Nat → Bool) (h : Constraints p) : clause p c194 = true := by
  simpa only [c194,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause194
def c195 : List Lit := [(315, false), (337, false), (340, true)]
theorem step195 (p : Nat → Bool) (h : Constraints p) : clause p c195 = true := by
  simpa only [c195,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause195
def c196 : List Lit := [(182, false), (351, true)]
theorem step196 (p : Nat → Bool) (h : Constraints p) : clause p c196 = true := by
  simpa only [c196,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause196
def c197 : List Lit := [(180, false), (351, false), (354, true)]
theorem step197 (p : Nat → Bool) (h : Constraints p) : clause p c197 = true := by
  simpa only [c197,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause197
def c198 : List Lit := [(354, false), (360, true)]
theorem step198 (p : Nat → Bool) (h : Constraints p) : clause p c198 = true := by
  simpa only [c198,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause198
def c199 : List Lit := [(360, false), (362, true)]
theorem step199 (p : Nat → Bool) (h : Constraints p) : clause p c199 = true := by
  simpa only [c199,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause199
def c200 : List Lit := [(188, false), (363, true)]
theorem step200 (p : Nat → Bool) (h : Constraints p) : clause p c200 = true := by
  simpa only [c200,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause200
def c201 : List Lit := [(363, false), (365, true)]
theorem step201 (p : Nat → Bool) (h : Constraints p) : clause p c201 = true := by
  simpa only [c201,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause201
def c202 : List Lit := [(365, false), (371, true)]
theorem step202 (p : Nat → Bool) (h : Constraints p) : clause p c202 = true := by
  simpa only [c202,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause202
def c203 : List Lit := [(371, false), (385, true)]
theorem step203 (p : Nat → Bool) (h : Constraints p) : clause p c203 = true := by
  simpa only [c203,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause203
def c204 : List Lit := [(385, false), (387, true)]
theorem step204 (p : Nat → Bool) (h : Constraints p) : clause p c204 = true := by
  simpa only [c204,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause204
def c205 : List Lit := [(362, false), (388, true)]
theorem step205 (p : Nat → Bool) (h : Constraints p) : clause p c205 = true := by
  simpa only [c205,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause205
def c206 : List Lit := [(388, false), (390, true)]
theorem step206 (p : Nat → Bool) (h : Constraints p) : clause p c206 = true := by
  simpa only [c206,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause206
def c207 : List Lit := [(339, false), (389, true)]
theorem step207 (p : Nat → Bool) (h : Constraints p) : clause p c207 = true := by
  simpa only [c207,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause207
def c208 : List Lit := [(339, false), (387, false), (390, true)]
theorem step208 (p : Nat → Bool) (h : Constraints p) : clause p c208 = true := by
  simpa only [c208,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause208
def c209 : List Lit := [(340, false), (390, true)]
theorem step209 (p : Nat → Bool) (h : Constraints p) : clause p c209 = true := by
  simpa only [c209,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause209
def c210 : List Lit := [(390, false), (392, true)]
theorem step210 (p : Nat → Bool) (h : Constraints p) : clause p c210 = true := by
  simpa only [c210,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause210
def c211 : List Lit := [(293, false), (389, false), (392, true)]
theorem step211 (p : Nat → Bool) (h : Constraints p) : clause p c211 = true := by
  simpa only [c211,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause211
def c212 : List Lit := [(294, false), (392, true)]
theorem step212 (p : Nat → Bool) (h : Constraints p) : clause p c212 = true := by
  simpa only [c212,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause212
def c213 : List Lit := [(392, false)]
theorem step213 (p : Nat → Bool) (h : Constraints p) : clause p c213 = true := by
  simpa only [c213,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause213
def c214 : List Lit := [(6, true), (1149, true)]
theorem step214 (p : Nat → Bool) (h : Constraints p) : clause p c214 = true := by
  simpa only [c214,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause214
def c215 : List Lit := [(3, true), (1149, true)]
theorem step215 (p : Nat → Bool) (h : Constraints p) : clause p c215 = true := by
  simpa only [c215,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause215
def c216 : List Lit := [(1149, false), (1151, true)]
theorem step216 (p : Nat → Bool) (h : Constraints p) : clause p c216 = true := by
  simpa only [c216,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause216
def c217 : List Lit := [(2, true), (1151, true)]
theorem step217 (p : Nat → Bool) (h : Constraints p) : clause p c217 = true := by
  simpa only [c217,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause217
def c218 : List Lit := [(2, true), (1149, false), (1152, true)]
theorem step218 (p : Nat → Bool) (h : Constraints p) : clause p c218 = true := by
  simpa only [c218,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause218
def c219 : List Lit := [(10, true), (1154, true)]
theorem step219 (p : Nat → Bool) (h : Constraints p) : clause p c219 = true := by
  simpa only [c219,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause219
def c220 : List Lit := [(1154, false), (1156, true)]
theorem step220 (p : Nat → Bool) (h : Constraints p) : clause p c220 = true := by
  simpa only [c220,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause220
def c221 : List Lit := [(8, true), (1156, true)]
theorem step221 (p : Nat → Bool) (h : Constraints p) : clause p c221 = true := by
  simpa only [c221,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause221
def c222 : List Lit := [(8, true), (1154, false), (1157, true)]
theorem step222 (p : Nat → Bool) (h : Constraints p) : clause p c222 = true := by
  simpa only [c222,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause222
def c223 : List Lit := [(1157, false), (1160, true)]
theorem step223 (p : Nat → Bool) (h : Constraints p) : clause p c223 = true := by
  simpa only [c223,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause223
def c224 : List Lit := [(1151, false), (1156, false), (1160, true)]
theorem step224 (p : Nat → Bool) (h : Constraints p) : clause p c224 = true := by
  simpa only [c224,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause224
def c225 : List Lit := [(1152, false), (1160, true)]
theorem step225 (p : Nat → Bool) (h : Constraints p) : clause p c225 = true := by
  simpa only [c225,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause225
def c226 : List Lit := [(18, true), (1165, true)]
theorem step226 (p : Nat → Bool) (h : Constraints p) : clause p c226 = true := by
  simpa only [c226,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause226
def c227 : List Lit := [(15, true), (1165, true)]
theorem step227 (p : Nat → Bool) (h : Constraints p) : clause p c227 = true := by
  simpa only [c227,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause227
def c228 : List Lit := [(15, true), (18, true), (1166, true)]
theorem step228 (p : Nat → Bool) (h : Constraints p) : clause p c228 = true := by
  simpa only [c228,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause228
def c229 : List Lit := [(1165, false), (1167, true)]
theorem step229 (p : Nat → Bool) (h : Constraints p) : clause p c229 = true := by
  simpa only [c229,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause229
def c230 : List Lit := [(1166, false), (1168, true)]
theorem step230 (p : Nat → Bool) (h : Constraints p) : clause p c230 = true := by
  simpa only [c230,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause230
def c231 : List Lit := [(14, true), (1167, true)]
theorem step231 (p : Nat → Bool) (h : Constraints p) : clause p c231 = true := by
  simpa only [c231,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause231
def c232 : List Lit := [(14, true), (1165, false), (1168, true)]
theorem step232 (p : Nat → Bool) (h : Constraints p) : clause p c232 = true := by
  simpa only [c232,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause232
def c233 : List Lit := [(23, true), (1170, true)]
theorem step233 (p : Nat → Bool) (h : Constraints p) : clause p c233 = true := by
  simpa only [c233,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause233
def c234 : List Lit := [(22, true), (1170, true)]
theorem step234 (p : Nat → Bool) (h : Constraints p) : clause p c234 = true := by
  simpa only [c234,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause234
def c235 : List Lit := [(1170, false), (1172, true)]
theorem step235 (p : Nat → Bool) (h : Constraints p) : clause p c235 = true := by
  simpa only [c235,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause235
def c236 : List Lit := [(20, true), (1172, true)]
theorem step236 (p : Nat → Bool) (h : Constraints p) : clause p c236 = true := by
  simpa only [c236,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause236
def c237 : List Lit := [(20, true), (1170, false), (1173, true)]
theorem step237 (p : Nat → Bool) (h : Constraints p) : clause p c237 = true := by
  simpa only [c237,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause237
def c238 : List Lit := [(1172, false), (1175, true)]
theorem step238 (p : Nat → Bool) (h : Constraints p) : clause p c238 = true := by
  simpa only [c238,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause238
def c239 : List Lit := [(1173, false), (1176, true)]
theorem step239 (p : Nat → Bool) (h : Constraints p) : clause p c239 = true := by
  simpa only [c239,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause239
def c240 : List Lit := [(1167, false), (1175, true)]
theorem step240 (p : Nat → Bool) (h : Constraints p) : clause p c240 = true := by
  simpa only [c240,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause240
def c241 : List Lit := [(1167, false), (1172, false), (1176, true)]
theorem step241 (p : Nat → Bool) (h : Constraints p) : clause p c241 = true := by
  simpa only [c241,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause241
def c242 : List Lit := [(1168, false), (1176, true)]
theorem step242 (p : Nat → Bool) (h : Constraints p) : clause p c242 = true := by
  simpa only [c242,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause242
def c243 : List Lit := [(1160, false), (1182, true)]
theorem step243 (p : Nat → Bool) (h : Constraints p) : clause p c243 = true := by
  simpa only [c243,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause243
def c244 : List Lit := [(1160, false), (1175, false), (1183, true)]
theorem step244 (p : Nat → Bool) (h : Constraints p) : clause p c244 = true := by
  simpa only [c244,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause244
def c245 : List Lit := [(1160, false), (1176, false), (1184, true)]
theorem step245 (p : Nat → Bool) (h : Constraints p) : clause p c245 = true := by
  simpa only [c245,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause245
def c246 : List Lit := [(30, true), (1190, true)]
theorem step246 (p : Nat → Bool) (h : Constraints p) : clause p c246 = true := by
  simpa only [c246,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause246
def c247 : List Lit := [(27, true), (1190, true)]
theorem step247 (p : Nat → Bool) (h : Constraints p) : clause p c247 = true := by
  simpa only [c247,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause247
def c248 : List Lit := [(1190, false), (1192, true)]
theorem step248 (p : Nat → Bool) (h : Constraints p) : clause p c248 = true := by
  simpa only [c248,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause248
def c249 : List Lit := [(24, true), (1192, true)]
theorem step249 (p : Nat → Bool) (h : Constraints p) : clause p c249 = true := by
  simpa only [c249,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause249
def c250 : List Lit := [(24, true), (1190, false), (1193, true)]
theorem step250 (p : Nat → Bool) (h : Constraints p) : clause p c250 = true := by
  simpa only [c250,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause250
def c251 : List Lit := [(34, true), (1195, true)]
theorem step251 (p : Nat → Bool) (h : Constraints p) : clause p c251 = true := by
  simpa only [c251,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause251
def c252 : List Lit := [(33, true), (1195, true)]
theorem step252 (p : Nat → Bool) (h : Constraints p) : clause p c252 = true := by
  simpa only [c252,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause252
def c253 : List Lit := [(1195, false), (1197, true)]
theorem step253 (p : Nat → Bool) (h : Constraints p) : clause p c253 = true := by
  simpa only [c253,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause253
def c254 : List Lit := [(32, true), (1197, true)]
theorem step254 (p : Nat → Bool) (h : Constraints p) : clause p c254 = true := by
  simpa only [c254,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause254
def c255 : List Lit := [(1197, false), (1200, true)]
theorem step255 (p : Nat → Bool) (h : Constraints p) : clause p c255 = true := by
  simpa only [c255,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause255
def c256 : List Lit := [(1192, false), (1200, true)]
theorem step256 (p : Nat → Bool) (h : Constraints p) : clause p c256 = true := by
  simpa only [c256,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause256
def c257 : List Lit := [(1192, false), (1197, false), (1201, true)]
theorem step257 (p : Nat → Bool) (h : Constraints p) : clause p c257 = true := by
  simpa only [c257,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause257
def c258 : List Lit := [(1193, false), (1201, true)]
theorem step258 (p : Nat → Bool) (h : Constraints p) : clause p c258 = true := by
  simpa only [c258,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause258
def c259 : List Lit := [(1193, false), (1197, false), (1202, true)]
theorem step259 (p : Nat → Bool) (h : Constraints p) : clause p c259 = true := by
  simpa only [c259,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause259
def c260 : List Lit := [(41, true), (1206, true)]
theorem step260 (p : Nat → Bool) (h : Constraints p) : clause p c260 = true := by
  simpa only [c260,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause260
def c261 : List Lit := [(39, true), (1206, true)]
theorem step261 (p : Nat → Bool) (h : Constraints p) : clause p c261 = true := by
  simpa only [c261,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause261
def c262 : List Lit := [(39, true), (41, true), (1207, true)]
theorem step262 (p : Nat → Bool) (h : Constraints p) : clause p c262 = true := by
  simpa only [c262,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause262
def c263 : List Lit := [(1206, false), (1208, true)]
theorem step263 (p : Nat → Bool) (h : Constraints p) : clause p c263 = true := by
  simpa only [c263,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause263
def c264 : List Lit := [(1207, false), (1209, true)]
theorem step264 (p : Nat → Bool) (h : Constraints p) : clause p c264 = true := by
  simpa only [c264,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause264
def c265 : List Lit := [(37, true), (1208, true)]
theorem step265 (p : Nat → Bool) (h : Constraints p) : clause p c265 = true := by
  simpa only [c265,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause265
def c266 : List Lit := [(37, true), (1206, false), (1209, true)]
theorem step266 (p : Nat → Bool) (h : Constraints p) : clause p c266 = true := by
  simpa only [c266,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause266
def c267 : List Lit := [(44, true), (1211, true)]
theorem step267 (p : Nat → Bool) (h : Constraints p) : clause p c267 = true := by
  simpa only [c267,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause267
def c268 : List Lit := [(1211, false), (1213, true)]
theorem step268 (p : Nat → Bool) (h : Constraints p) : clause p c268 = true := by
  simpa only [c268,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause268
def c269 : List Lit := [(42, true), (1213, true)]
theorem step269 (p : Nat → Bool) (h : Constraints p) : clause p c269 = true := by
  simpa only [c269,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause269
def c270 : List Lit := [(42, true), (1211, false), (1214, true)]
theorem step270 (p : Nat → Bool) (h : Constraints p) : clause p c270 = true := by
  simpa only [c270,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause270
def c271 : List Lit := [(1213, false), (1216, true)]
theorem step271 (p : Nat → Bool) (h : Constraints p) : clause p c271 = true := by
  simpa only [c271,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause271
def c272 : List Lit := [(1214, false), (1217, true)]
theorem step272 (p : Nat → Bool) (h : Constraints p) : clause p c272 = true := by
  simpa only [c272,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause272
def c273 : List Lit := [(1208, false), (1216, true)]
theorem step273 (p : Nat → Bool) (h : Constraints p) : clause p c273 = true := by
  simpa only [c273,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause273
def c274 : List Lit := [(1208, false), (1213, false), (1217, true)]
theorem step274 (p : Nat → Bool) (h : Constraints p) : clause p c274 = true := by
  simpa only [c274,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause274
def c275 : List Lit := [(1209, false), (1217, true)]
theorem step275 (p : Nat → Bool) (h : Constraints p) : clause p c275 = true := by
  simpa only [c275,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause275
def c276 : List Lit := [(1217, false), (1223, true)]
theorem step276 (p : Nat → Bool) (h : Constraints p) : clause p c276 = true := by
  simpa only [c276,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause276
def c277 : List Lit := [(1200, false), (1216, false), (1223, true)]
theorem step277 (p : Nat → Bool) (h : Constraints p) : clause p c277 = true := by
  simpa only [c277,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause277
def c278 : List Lit := [(1200, false), (1217, false), (1224, true)]
theorem step278 (p : Nat → Bool) (h : Constraints p) : clause p c278 = true := by
  simpa only [c278,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause278
def c279 : List Lit := [(1201, false), (1216, false), (1224, true)]
theorem step279 (p : Nat → Bool) (h : Constraints p) : clause p c279 = true := by
  simpa only [c279,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause279
def c280 : List Lit := [(1201, false), (1217, false), (1225, true)]
theorem step280 (p : Nat → Bool) (h : Constraints p) : clause p c280 = true := by
  simpa only [c280,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause280
def c281 : List Lit := [(1202, false), (1224, true)]
theorem step281 (p : Nat → Bool) (h : Constraints p) : clause p c281 = true := by
  simpa only [c281,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause281
def c282 : List Lit := [(1202, false), (1216, false), (1225, true)]
theorem step282 (p : Nat → Bool) (h : Constraints p) : clause p c282 = true := by
  simpa only [c282,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause282
def c283 : List Lit := [(1182, false), (1225, false), (1236, true)]
theorem step283 (p : Nat → Bool) (h : Constraints p) : clause p c283 = true := by
  simpa only [c283,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause283
def c284 : List Lit := [(1183, false), (1224, false), (1236, true)]
theorem step284 (p : Nat → Bool) (h : Constraints p) : clause p c284 = true := by
  simpa only [c284,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause284
def c285 : List Lit := [(1184, false), (1223, false), (1236, true)]
theorem step285 (p : Nat → Bool) (h : Constraints p) : clause p c285 = true := by
  simpa only [c285,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause285
def c286 : List Lit := [(50, true), (1240, true)]
theorem step286 (p : Nat → Bool) (h : Constraints p) : clause p c286 = true := by
  simpa only [c286,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause286
def c287 : List Lit := [(1240, false), (1242, true)]
theorem step287 (p : Nat → Bool) (h : Constraints p) : clause p c287 = true := by
  simpa only [c287,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause287
def c288 : List Lit := [(1242, false), (1250, true)]
theorem step288 (p : Nat → Bool) (h : Constraints p) : clause p c288 = true := by
  simpa only [c288,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause288
def c289 : List Lit := [(1250, false), (1272, true)]
theorem step289 (p : Nat → Bool) (h : Constraints p) : clause p c289 = true := by
  simpa only [c289,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause289
def c290 : List Lit := [(76, true), (1281, true)]
theorem step290 (p : Nat → Bool) (h : Constraints p) : clause p c290 = true := by
  simpa only [c290,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause290
def c291 : List Lit := [(1281, false), (1283, true)]
theorem step291 (p : Nat → Bool) (h : Constraints p) : clause p c291 = true := by
  simpa only [c291,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause291
def c292 : List Lit := [(74, true), (1283, true)]
theorem step292 (p : Nat → Bool) (h : Constraints p) : clause p c292 = true := by
  simpa only [c292,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause292
def c293 : List Lit := [(74, true), (1281, false), (1284, true)]
theorem step293 (p : Nat → Bool) (h : Constraints p) : clause p c293 = true := by
  simpa only [c293,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause293
def c294 : List Lit := [(83, true), (1286, true)]
theorem step294 (p : Nat → Bool) (h : Constraints p) : clause p c294 = true := by
  simpa only [c294,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause294
def c295 : List Lit := [(81, true), (1286, true)]
theorem step295 (p : Nat → Bool) (h : Constraints p) : clause p c295 = true := by
  simpa only [c295,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause295
def c296 : List Lit := [(1286, false), (1288, true)]
theorem step296 (p : Nat → Bool) (h : Constraints p) : clause p c296 = true := by
  simpa only [c296,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause296
def c297 : List Lit := [(80, true), (1288, true)]
theorem step297 (p : Nat → Bool) (h : Constraints p) : clause p c297 = true := by
  simpa only [c297,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause297
def c298 : List Lit := [(1288, false), (1291, true)]
theorem step298 (p : Nat → Bool) (h : Constraints p) : clause p c298 = true := by
  simpa only [c298,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause298
def c299 : List Lit := [(1283, false), (1288, false), (1292, true)]
theorem step299 (p : Nat → Bool) (h : Constraints p) : clause p c299 = true := by
  simpa only [c299,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause299
def c300 : List Lit := [(1284, false), (1288, false), (1293, true)]
theorem step300 (p : Nat → Bool) (h : Constraints p) : clause p c300 = true := by
  simpa only [c300,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause300
def c301 : List Lit := [(89, true), (1297, true)]
theorem step301 (p : Nat → Bool) (h : Constraints p) : clause p c301 = true := by
  simpa only [c301,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause301
def c302 : List Lit := [(1297, false), (1299, true)]
theorem step302 (p : Nat → Bool) (h : Constraints p) : clause p c302 = true := by
  simpa only [c302,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause302
def c303 : List Lit := [(86, true), (1299, true)]
theorem step303 (p : Nat → Bool) (h : Constraints p) : clause p c303 = true := by
  simpa only [c303,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause303
def c304 : List Lit := [(92, true), (1302, true)]
theorem step304 (p : Nat → Bool) (h : Constraints p) : clause p c304 = true := by
  simpa only [c304,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause304
def c305 : List Lit := [(1302, false), (1306, true)]
theorem step305 (p : Nat → Bool) (h : Constraints p) : clause p c305 = true := by
  simpa only [c305,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause305
def c306 : List Lit := [(1306, false), (1310, true)]
theorem step306 (p : Nat → Bool) (h : Constraints p) : clause p c306 = true := by
  simpa only [c306,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause306
def c307 : List Lit := [(1299, false), (1310, true)]
theorem step307 (p : Nat → Bool) (h : Constraints p) : clause p c307 = true := by
  simpa only [c307,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause307
def c308 : List Lit := [(1291, false), (1310, false), (1318, true)]
theorem step308 (p : Nat → Bool) (h : Constraints p) : clause p c308 = true := by
  simpa only [c308,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause308
def c309 : List Lit := [(1292, false), (1318, true)]
theorem step309 (p : Nat → Bool) (h : Constraints p) : clause p c309 = true := by
  simpa only [c309,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause309
def c310 : List Lit := [(1292, false), (1310, false), (1319, true)]
theorem step310 (p : Nat → Bool) (h : Constraints p) : clause p c310 = true := by
  simpa only [c310,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause310
def c311 : List Lit := [(1293, false), (1319, true)]
theorem step311 (p : Nat → Bool) (h : Constraints p) : clause p c311 = true := by
  simpa only [c311,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause311
def c312 : List Lit := [(1319, false), (1328, true)]
theorem step312 (p : Nat → Bool) (h : Constraints p) : clause p c312 = true := by
  simpa only [c312,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause312
def c313 : List Lit := [(1272, false), (1318, false), (1328, true)]
theorem step313 (p : Nat → Bool) (h : Constraints p) : clause p c313 = true := by
  simpa only [c313,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause313
def c314 : List Lit := [(1236, false), (1328, false), (1343, true)]
theorem step314 (p : Nat → Bool) (h : Constraints p) : clause p c314 = true := by
  simpa only [c314,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause314
def c315 : List Lit := [(1343, false)]
theorem step315 (p : Nat → Bool) (h : Constraints p) : clause p c315 = true := by
  simpa only [c315,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause315
def c316 : List Lit := [(15, false), (17, false), (21, false), (22, false)]
theorem step316 (p : Nat → Bool) (h : Constraints p) : clause p c316 = true := by
  simpa only [c316,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause316
def c317 : List Lit := [(23, false), (25, false), (29, false), (30, false)]
theorem step317 (p : Nat → Bool) (h : Constraints p) : clause p c317 = true := by
  simpa only [c317,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause317
end B112E149
