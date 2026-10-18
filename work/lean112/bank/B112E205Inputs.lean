import TreeRup
namespace B112E205
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
structure Block0 (p : Nat → Bool) : Prop where
  clause1 : p 1 = false ∨ p 110 = true
  clause2 : p 2 = false ∨ p 111 = true ∨ p 1 = true
  clause3 : p 3 = false ∨ p 112 = true ∨ p 47 = true
  clause4 : p 3 = false ∨ p 112 = true ∨ p 5 = true
  clause5 : p 4 = false ∨ p 113 = true ∨ p 11 = true
  clause6 : p 4 = false ∨ p 113 = true ∨ p 5 = true
  clause7 : p 5 = false ∨ p 114 = true ∨ p 4 = true
  clause8 : p 5 = false ∨ p 114 = true ∨ p 3 = true
  clause9 : p 6 = false ∨ p 115 = true ∨ p 2 = true
  clause10 : p 7 = false ∨ p 116 = true ∨ p 8 = true
  clause11 : p 8 = false ∨ p 117 = true ∨ p 6 = true
  clause12 : p 9 = false ∨ p 118 = true ∨ p 7 = true
  clause13 : p 10 = false ∨ p 119 = true ∨ p 12 = true
  clause14 : p 11 = false ∨ p 120 = true ∨ p 10 = true
  clause15 : p 12 = false ∨ p 121 = true ∨ p 9 = true
  clause16 : p 14 = false ∨ p 123 = true ∨ p 16 = true ∨ p 17 = true ∨ p 23 = true
  clause17 : p 14 = false ∨ p 123 = true ∨ p 13 = true ∨ p 16 = true ∨ p 17 = true
  clause18 : p 16 = false ∨ p 14 = false ∨ p 19 = false ∨ p 25 = false
  clause19 : p 17 = false ∨ p 14 = false ∨ p 20 = false ∨ p 79 = false
  clause20 : p 22 = false ∨ p 23 = false ∨ p 24 = false ∨ p 27 = false
  clause21 : p 23 = false ∨ p 14 = false ∨ p 22 = false ∨ p 25 = false
  clause22 : p 24 = false ∨ p 15 = false ∨ p 25 = false ∨ p 26 = false
  clause23 : p 25 = false ∨ p 16 = true ∨ p 23 = true ∨ p 24 = true
  clause24 : p 25 = false ∨ p 134 = true ∨ p 16 = true ∨ p 24 = true
  clause25 : p 25 = false ∨ p 134 = true ∨ p 16 = true ∨ p 23 = true
  clause26 : p 33 = false ∨ p 34 = false ∨ p 35 = false ∨ p 38 = false
  clause27 : p 38 = false ∨ p 33 = true ∨ p 39 = true
  clause28 : p 38 = false ∨ p 147 = true ∨ p 33 = true
  clause29 : p 39 = false ∨ p 34 = false ∨ p 38 = false ∨ p 40 = false
  clause30 : p 40 = false ∨ p 149 = true ∨ p 44 = true
  clause31 : p 40 = false ∨ p 149 = true ∨ p 39 = true
  clause32 : p 41 = false ∨ p 150 = true
structure Block1 (p : Nat → Bool) : Prop where
  clause33 : p 43 = false ∨ p 152 = true ∨ p 41 = true ∨ p 42 = true ∨ p 44 = true
  clause34 : p 44 = false ∨ p 31 = false ∨ p 40 = false ∨ p 43 = false
  clause35 : p 44 = false ∨ p 153 = true ∨ p 31 = true ∨ p 40 = true
  clause36 : p 45 = false ∨ p 154 = true ∨ p 56 = true
  clause37 : p 46 = false ∨ p 50 = true
  clause38 : p 46 = false ∨ p 155 = true
  clause39 : p 47 = false ∨ p 3 = false ∨ p 45 = false ∨ p 53 = false
  clause40 : p 48 = false ∨ p 157 = true ∨ p 57 = true
  clause41 : p 49 = false ∨ p 158 = true ∨ p 48 = true
  clause42 : p 50 = false ∨ p 46 = false ∨ p 49 = false ∨ p 51 = false
  clause43 : p 50 = false ∨ p 159 = true ∨ p 46 = true ∨ p 49 = true
  clause44 : p 51 = false ∨ p 160 = true ∨ p 54 = true
  clause45 : p 51 = false ∨ p 160 = true ∨ p 50 = true
  clause46 : p 52 = false ∨ p 161 = true
  clause47 : p 53 = false ∨ p 162 = true ∨ p 52 = true ∨ p 54 = true
  clause48 : p 53 = false ∨ p 162 = true ∨ p 47 = true ∨ p 52 = true
  clause49 : p 54 = false ∨ p 163 = true ∨ p 53 = true
  clause50 : p 54 = false ∨ p 163 = true ∨ p 51 = true
  clause51 : p 56 = false ∨ p 45 = false ∨ p 59 = false ∨ p 61 = false
  clause52 : p 56 = false ∨ p 45 = false ∨ p 59 = false ∨ p 77 = false
  clause53 : p 56 = false ∨ p 45 = false ∨ p 61 = false ∨ p 77 = false
  clause54 : p 56 = false ∨ p 59 = false ∨ p 61 = false ∨ p 77 = false
  clause55 : p 57 = false ∨ p 48 = false ∨ p 58 = false ∨ p 68 = false
  clause56 : p 58 = false ∨ p 167 = true ∨ p 57 = true
  clause57 : p 59 = false ∨ p 56 = true ∨ p 58 = true
  clause58 : p 59 = false ∨ p 168 = true ∨ p 58 = true
  clause59 : p 59 = false ∨ p 168 = true ∨ p 56 = true
  clause60 : p 60 = false ∨ p 169 = true ∨ p 64 = true
  clause61 : p 60 = false ∨ p 169 = true ∨ p 61 = true
  clause62 : p 61 = false ∨ p 170 = true ∨ p 56 = true ∨ p 65 = true
  clause63 : p 61 = false ∨ p 170 = true ∨ p 56 = true ∨ p 60 = true
  clause64 : p 62 = false ∨ p 63 = false ∨ p 66 = false ∨ p 69 = false
structure Block2 (p : Nat → Bool) : Prop where
  clause65 : p 63 = false ∨ p 62 = true ∨ p 70 = true ∨ p 95 = true
  clause66 : p 64 = false ∨ p 173 = true ∨ p 60 = true ∨ p 65 = true
  clause67 : p 65 = false ∨ p 61 = false ∨ p 64 = false ∨ p 74 = false
  clause68 : p 65 = false ∨ p 61 = false ∨ p 74 = false ∨ p 98 = false
  clause69 : p 65 = false ∨ p 64 = false ∨ p 74 = false ∨ p 98 = false
  clause70 : p 66 = false ∨ p 175 = true ∨ p 62 = true
  clause71 : p 68 = false ∨ p 57 = false ∨ p 69 = false ∨ p 72 = false
  clause72 : p 68 = false ∨ p 57 = false ∨ p 69 = false ∨ p 101 = false
  clause73 : p 68 = false ∨ p 57 = false ∨ p 72 = false ∨ p 101 = false
  clause74 : p 68 = false ∨ p 69 = false ∨ p 72 = false ∨ p 101 = false
  clause75 : p 69 = false ∨ p 62 = true ∨ p 68 = true ∨ p 70 = true
  clause76 : p 69 = false ∨ p 62 = false ∨ p 68 = false ∨ p 70 = false
  clause77 : p 69 = false ∨ p 178 = true ∨ p 68 = true ∨ p 70 = true
  clause78 : p 69 = false ∨ p 178 = true ∨ p 62 = true ∨ p 70 = true
  clause79 : p 70 = false ∨ p 63 = false ∨ p 69 = false ∨ p 71 = false
  clause80 : p 70 = false ∨ p 179 = true ∨ p 63 = true ∨ p 71 = true
  clause81 : p 71 = false ∨ p 180 = true ∨ p 75 = true
  clause82 : p 71 = false ∨ p 180 = true ∨ p 70 = true
  clause83 : p 72 = false ∨ p 181 = true ∨ p 73 = true
  clause84 : p 72 = false ∨ p 181 = true ∨ p 68 = true
  clause85 : p 73 = false ∨ p 182 = true ∨ p 72 = true
  clause86 : p 74 = false ∨ p 65 = false ∨ p 73 = false ∨ p 75 = false
  clause87 : p 74 = false ∨ p 183 = true ∨ p 73 = true ∨ p 75 = true
  clause88 : p 74 = false ∨ p 183 = true ∨ p 65 = true ∨ p 73 = true
  clause89 : p 75 = false ∨ p 184 = true ∨ p 74 = true
  clause90 : p 75 = false ∨ p 184 = true ∨ p 71 = true
  clause91 : p 76 = false ∨ p 15 = false ∨ p 77 = false ∨ p 80 = false
  clause92 : p 77 = false ∨ p 16 = false ∨ p 56 = false ∨ p 76 = false
  clause93 : p 78 = false ∨ p 79 = false ∨ p 82 = false ∨ p 85 = false
  clause94 : p 79 = false ∨ p 17 = false ∨ p 78 = false ∨ p 86 = false
  clause95 : p 79 = false ∨ p 188 = true ∨ p 17 = true ∨ p 78 = true ∨ p 95 = true
  clause96 : p 80 = false ∨ p 189 = true ∨ p 76 = true ∨ p 81 = true ∨ p 90 = true
structure Block3 (p : Nat → Bool) : Prop where
  clause97 : p 81 = false ∨ p 77 = false ∨ p 80 = false ∨ p 91 = false
  clause98 : p 81 = false ∨ p 80 = false ∨ p 91 = false ∨ p 98 = false
  clause99 : p 82 = false ∨ p 78 = true ∨ p 83 = true
  clause100 : p 82 = false ∨ p 191 = true ∨ p 78 = true
  clause101 : p 83 = false ∨ p 192 = true ∨ p 80 = true
  clause102 : p 84 = false ∨ p 22 = false ∨ p 85 = false ∨ p 88 = false
  clause103 : p 84 = false ∨ p 57 = false ∨ p 85 = false ∨ p 88 = false
  clause104 : p 84 = false ∨ p 85 = false ∨ p 88 = false ∨ p 101 = false
  clause105 : p 85 = false ∨ p 78 = false ∨ p 84 = false ∨ p 86 = false
  clause106 : p 85 = false ∨ p 194 = true ∨ p 84 = true ∨ p 86 = true
  clause107 : p 85 = false ∨ p 194 = true ∨ p 78 = true ∨ p 86 = true
  clause108 : p 85 = false ∨ p 194 = true ∨ p 78 = true ∨ p 84 = true
  clause109 : p 86 = false ∨ p 79 = false ∨ p 85 = false ∨ p 87 = false
  clause110 : p 87 = false ∨ p 86 = true ∨ p 92 = true
  clause111 : p 87 = false ∨ p 196 = true ∨ p 92 = true
  clause112 : p 87 = false ∨ p 196 = true ∨ p 86 = true
  clause113 : p 88 = false ∨ p 197 = true ∨ p 27 = true ∨ p 84 = true ∨ p 90 = true
  clause114 : p 89 = false ∨ p 198 = true ∨ p 88 = true
  clause115 : p 90 = false ∨ p 80 = false ∨ p 88 = false ∨ p 91 = false
  clause116 : p 90 = false ∨ p 80 = false ∨ p 88 = false ∨ p 106 = false
  clause117 : p 90 = false ∨ p 80 = false ∨ p 91 = false ∨ p 106 = false
  clause118 : p 90 = false ∨ p 88 = false ∨ p 91 = false ∨ p 106 = false
  clause119 : p 91 = false ∨ p 200 = true ∨ p 81 = true ∨ p 90 = true ∨ p 92 = true
  clause120 : p 91 = false ∨ p 200 = true ∨ p 81 = true ∨ p 89 = true ∨ p 90 = true
  clause121 : p 92 = false ∨ p 31 = false ∨ p 87 = false ∨ p 91 = false
  clause122 : p 93 = false ∨ p 94 = true ∨ p 101 = true
  clause123 : p 202 = false ∨ p 94 = false ∨ p 101 = false
  clause124 : p 93 = true
  clause125 : p 202 = true
  clause126 : p 94 = false ∨ p 203 = true ∨ p 95 = true ∨ p 102 = true
  clause127 : p 95 = false ∨ p 63 = false ∨ p 79 = false ∨ p 94 = false
  clause128 : p 95 = false ∨ p 63 = false ∨ p 97 = false ∨ p 99 = false
structure Block4 (p : Nat → Bool) : Prop where
  clause129 : p 95 = false ∨ p 79 = false ∨ p 94 = false ∨ p 97 = false
  clause130 : p 95 = false ∨ p 79 = false ∨ p 94 = false ∨ p 99 = false
  clause131 : p 95 = false ∨ p 79 = false ∨ p 97 = false ∨ p 99 = false
  clause132 : p 95 = false ∨ p 94 = false ∨ p 97 = false ∨ p 99 = false
  clause133 : p 97 = false ∨ p 206 = true ∨ p 95 = true ∨ p 100 = true
  clause134 : p 97 = false ∨ p 206 = true ∨ p 95 = true ∨ p 96 = true
  clause135 : p 98 = false ∨ p 207 = true ∨ p 65 = true ∨ p 81 = true ∨ p 100 = true
  clause136 : p 99 = false ∨ p 208 = true ∨ p 100 = true ∨ p 108 = true
  clause137 : p 99 = false ∨ p 208 = true ∨ p 95 = true ∨ p 100 = true
  clause138 : p 100 = false ∨ p 97 = false ∨ p 98 = false ∨ p 99 = false
  clause139 : p 101 = false ∨ p 68 = false ∨ p 93 = false ∨ p 102 = false
  clause140 : p 102 = false ∨ p 211 = true ∨ p 101 = true ∨ p 104 = true
  clause141 : p 103 = false ∨ p 101 = false ∨ p 104 = false ∨ p 105 = false
  clause142 : p 103 = false ∨ p 101 = false ∨ p 104 = false ∨ p 106 = false
  clause143 : p 103 = false ∨ p 101 = false ∨ p 105 = false ∨ p 106 = false
  clause144 : p 103 = false ∨ p 104 = false ∨ p 105 = false ∨ p 106 = false
  clause145 : p 104 = false ∨ p 102 = true ∨ p 103 = true
  clause146 : p 104 = false ∨ p 213 = true ∨ p 103 = true
  clause147 : p 105 = false ∨ p 96 = false ∨ p 103 = false ∨ p 109 = false
  clause148 : p 105 = false ∨ p 214 = true ∨ p 103 = true ∨ p 109 = true
  clause149 : p 106 = false ∨ p 42 = false ∨ p 103 = false ∨ p 109 = false
  clause150 : p 106 = false ∨ p 215 = true ∨ p 90 = true ∨ p 103 = true ∨ p 109 = true
  clause151 : p 107 = false ∨ p 216 = true ∨ p 109 = true
  clause152 : p 107 = false ∨ p 216 = true ∨ p 108 = true
  clause153 : p 108 = false ∨ p 217 = true ∨ p 107 = true
  clause154 : p 108 = false ∨ p 217 = true ∨ p 99 = true
  clause155 : p 109 = false ∨ p 105 = false ∨ p 106 = false ∨ p 107 = false
  clause156 : p 109 = false ∨ p 218 = true ∨ p 105 = true ∨ p 106 = true
  clause157 : p 110 = false
  clause158 : p 114 = false
  clause159 : p 115 = false
  clause160 : p 116 = false
structure Block5 (p : Nat → Bool) : Prop where
  clause161 : p 120 = false
  clause162 : p 121 = false
  clause163 : p 150 = false
  clause164 : p 153 = false
  clause165 : p 157 = false
  clause166 : p 159 = false
  clause167 : p 161 = false
  clause168 : p 163 = false
  clause169 : p 167 = false
  clause170 : p 169 = false
  clause171 : p 179 = false
  clause172 : p 182 = false
  clause173 : p 184 = false
  clause174 : p 192 = false
  clause175 : p 198 = false
  clause176 : p 211 = false
  clause177 : p 217 = false
  clause178 : p 218 = false
  clause179 : p 112 = false ∨ p 219 = true
  clause180 : p 111 = false ∨ p 219 = true
  clause181 : p 111 = false ∨ p 112 = false ∨ p 220 = true
  clause182 : p 219 = false ∨ p 221 = true
  clause183 : p 220 = false ∨ p 222 = true
  clause184 : p 113 = false ∨ p 225 = true
  clause185 : p 225 = false ∨ p 227 = true
  clause186 : p 221 = false ∨ p 227 = true
  clause187 : p 221 = false ∨ p 225 = false ∨ p 228 = true
  clause188 : p 222 = false ∨ p 228 = true
  clause189 : p 118 = false ∨ p 229 = true
  clause190 : p 117 = false ∨ p 229 = true
  clause191 : p 229 = false ∨ p 231 = true
  clause192 : p 119 = false ∨ p 233 = true
structure Block6 (p : Nat → Bool) : Prop where
  clause193 : p 233 = false ∨ p 237 = true
  clause194 : p 237 = false ∨ p 239 = true
  clause195 : p 231 = false ∨ p 239 = true
  clause196 : p 239 = false ∨ p 241 = true
  clause197 : p 227 = false ∨ p 241 = true
  clause198 : p 228 = false ∨ p 242 = true
  clause199 : p 123 = false ∨ p 245 = true
  clause200 : p 245 = false ∨ p 253 = true
  clause201 : p 134 = false ∨ p 259 = true
  clause202 : p 259 = false ∨ p 263 = true
  clause203 : p 263 = false ∨ p 265 = true
  clause204 : p 265 = false ∨ p 267 = true
  clause205 : p 253 = false ∨ p 267 = true
  clause206 : p 241 = false ∨ p 269 = true
  clause207 : p 241 = false ∨ p 267 = false ∨ p 270 = true
  clause208 : p 242 = false ∨ p 270 = true
  clause209 : p 147 = false ∨ p 285 = true
  clause210 : p 149 = false ∨ p 287 = true
  clause211 : p 287 = false ∨ p 289 = true
  clause212 : p 285 = false ∨ p 289 = true
  clause213 : p 289 = false ∨ p 291 = true
  clause214 : p 291 = false ∨ p 293 = true
  clause215 : p 152 = false ∨ p 295 = true
  clause216 : p 295 = false ∨ p 297 = true
  clause217 : p 154 = false ∨ p 299 = true
  clause218 : p 155 = false ∨ p 301 = true
  clause219 : p 301 = false ∨ p 303 = true
  clause220 : p 299 = false ∨ p 303 = true
  clause221 : p 303 = false ∨ p 305 = true
  clause222 : p 297 = false ∨ p 305 = true
  clause223 : p 158 = false ∨ p 307 = true
  clause224 : p 307 = false ∨ p 309 = true
structure Block7 (p : Nat → Bool) : Prop where
  clause225 : p 160 = false ∨ p 311 = true
  clause226 : p 162 = false ∨ p 313 = true
  clause227 : p 313 = false ∨ p 315 = true
  clause228 : p 311 = false ∨ p 315 = true
  clause229 : p 315 = false ∨ p 317 = true
  clause230 : p 309 = false ∨ p 317 = true
  clause231 : p 317 = false ∨ p 319 = true
  clause232 : p 305 = false ∨ p 319 = true
  clause233 : p 319 = false ∨ p 321 = true
  clause234 : p 293 = false ∨ p 321 = true
  clause235 : p 269 = false ∨ p 323 = true
  clause236 : p 269 = false ∨ p 321 = false ∨ p 324 = true
  clause237 : p 270 = false ∨ p 324 = true
  clause238 : p 168 = false ∨ p 329 = true
  clause239 : p 329 = false ∨ p 331 = true
  clause240 : p 331 = false ∨ p 333 = true
  clause241 : p 170 = false ∨ p 337 = true
  clause242 : p 173 = false ∨ p 339 = true
  clause243 : p 175 = false ∨ p 341 = true
  clause244 : p 341 = false ∨ p 343 = true
  clause245 : p 339 = false ∨ p 343 = true
  clause246 : p 343 = false ∨ p 345 = true
  clause247 : p 337 = false ∨ p 345 = true
  clause248 : p 345 = false ∨ p 347 = true
  clause249 : p 333 = false ∨ p 347 = true
  clause250 : p 333 = false ∨ p 345 = false ∨ p 348 = true
  clause251 : p 178 = false ∨ p 349 = true
  clause252 : p 349 = false ∨ p 351 = true
  clause253 : p 181 = false ∨ p 353 = true
  clause254 : p 180 = false ∨ p 353 = true
  clause255 : p 183 = false ∨ p 355 = true
  clause256 : p 355 = false ∨ p 357 = true
structure Block8 (p : Nat → Bool) : Prop where
  clause257 : p 353 = false ∨ p 357 = true
  clause258 : p 357 = false ∨ p 359 = true
  clause259 : p 351 = false ∨ p 359 = true
  clause260 : p 351 = false ∨ p 357 = false ∨ p 360 = true
  clause261 : p 188 = false ∨ p 365 = true
  clause262 : p 189 = false ∨ p 367 = true
  clause263 : p 367 = false ∨ p 369 = true
  clause264 : p 365 = false ∨ p 369 = true
  clause265 : p 369 = false ∨ p 371 = true
  clause266 : p 371 = false ∨ p 373 = true
  clause267 : p 359 = false ∨ p 373 = true
  clause268 : p 360 = false ∨ p 374 = true
  clause269 : p 373 = false ∨ p 375 = true
  clause270 : p 374 = false ∨ p 376 = true
  clause271 : p 347 = false ∨ p 375 = true
  clause272 : p 348 = false ∨ p 376 = true
  clause273 : p 191 = false ∨ p 379 = true
  clause274 : p 196 = false ∨ p 381 = true
  clause275 : p 381 = false ∨ p 383 = true
  clause276 : p 194 = false ∨ p 383 = true
  clause277 : p 194 = false ∨ p 381 = false ∨ p 384 = true
  clause278 : p 383 = false ∨ p 385 = true
  clause279 : p 384 = false ∨ p 386 = true
  clause280 : p 379 = false ∨ p 385 = true
  clause281 : p 379 = false ∨ p 383 = false ∨ p 386 = true
  clause282 : p 197 = false ∨ p 389 = true
  clause283 : p 200 = false ∨ p 391 = true
  clause284 : p 203 = false ∨ p 393 = true
  clause285 : p 393 = false ∨ p 395 = true
  clause286 : p 391 = false ∨ p 395 = true
  clause287 : p 395 = false ∨ p 397 = true
  clause288 : p 389 = false ∨ p 397 = true
structure Block9 (p : Nat → Bool) : Prop where
  clause289 : p 397 = false ∨ p 399 = true
  clause290 : p 385 = false ∨ p 399 = true
  clause291 : p 385 = false ∨ p 397 = false ∨ p 400 = true
  clause292 : p 386 = false ∨ p 400 = true
  clause293 : p 207 = false ∨ p 401 = true
  clause294 : p 206 = false ∨ p 401 = true
  clause295 : p 206 = false ∨ p 207 = false ∨ p 402 = true
  clause296 : p 401 = false ∨ p 403 = true
  clause297 : p 402 = false ∨ p 404 = true
  clause298 : p 208 = false ∨ p 405 = true
  clause299 : p 405 = false ∨ p 409 = true
  clause300 : p 409 = false ∨ p 411 = true
  clause301 : p 403 = false ∨ p 411 = true
  clause302 : p 403 = false ∨ p 409 = false ∨ p 412 = true
  clause303 : p 404 = false ∨ p 412 = true
  clause304 : p 214 = false ∨ p 413 = true
  clause305 : p 213 = false ∨ p 413 = true
  clause306 : p 213 = false ∨ p 214 = false ∨ p 414 = true
  clause307 : p 413 = false ∨ p 415 = true
  clause308 : p 414 = false ∨ p 416 = true
  clause309 : p 216 = false ∨ p 417 = true
  clause310 : p 215 = false ∨ p 417 = true
  clause311 : p 215 = false ∨ p 216 = false ∨ p 418 = true
  clause312 : p 417 = false ∨ p 421 = true
  clause313 : p 418 = false ∨ p 422 = true
  clause314 : p 421 = false ∨ p 423 = true
  clause315 : p 422 = false ∨ p 424 = true
  clause316 : p 415 = false ∨ p 423 = true
  clause317 : p 415 = false ∨ p 421 = false ∨ p 424 = true
  clause318 : p 416 = false ∨ p 424 = true
  clause319 : p 423 = false ∨ p 425 = true
  clause320 : p 424 = false ∨ p 426 = true
structure Block10 (p : Nat → Bool) : Prop where
  clause321 : p 411 = false ∨ p 425 = true
  clause322 : p 411 = false ∨ p 423 = false ∨ p 426 = true
  clause323 : p 412 = false ∨ p 426 = true
  clause324 : p 425 = false ∨ p 427 = true
  clause325 : p 426 = false ∨ p 428 = true
  clause326 : p 399 = false ∨ p 427 = true
  clause327 : p 399 = false ∨ p 425 = false ∨ p 428 = true
  clause328 : p 400 = false ∨ p 428 = true
  clause329 : p 427 = false ∨ p 429 = true
  clause330 : p 428 = false ∨ p 430 = true
  clause331 : p 375 = false ∨ p 429 = true
  clause332 : p 375 = false ∨ p 427 = false ∨ p 430 = true
  clause333 : p 376 = false ∨ p 430 = true
  clause334 : p 430 = false ∨ p 432 = true
  clause335 : p 323 = false ∨ p 429 = false ∨ p 432 = true
  clause336 : p 324 = false ∨ p 432 = true
  clause337 : p 432 = false
  clause338 : p 3 = true ∨ p 1315 = true
  clause339 : p 3 = true ∨ p 4 = true ∨ p 1316 = true
  clause340 : p 1315 = false ∨ p 1317 = true
  clause341 : p 1316 = false ∨ p 1318 = true
  clause342 : p 2 = true ∨ p 1317 = true
  clause343 : p 2 = true ∨ p 1315 = false ∨ p 1318 = true
  clause344 : p 2 = true ∨ p 1316 = false ∨ p 1319 = true
  clause345 : p 9 = true ∨ p 10 = true ∨ p 1321 = true
  clause346 : p 8 = true ∨ p 1322 = true
  clause347 : p 8 = true ∨ p 1321 = false ∨ p 1324 = true
  clause348 : p 1317 = false ∨ p 1325 = true
  clause349 : p 1317 = false ∨ p 1322 = false ∨ p 1326 = true
  clause350 : p 1317 = false ∨ p 1324 = false ∨ p 1328 = true
  clause351 : p 1318 = false ∨ p 1326 = true
  clause352 : p 1319 = false ∨ p 1324 = false ∨ p 1330 = true
structure Block11 (p : Nat → Bool) : Prop where
  clause353 : p 19 = true ∨ p 1331 = true
  clause354 : p 15 = true ∨ p 1331 = true
  clause355 : p 1331 = false ∨ p 1333 = true
  clause356 : p 14 = true ∨ p 1333 = true
  clause357 : p 14 = true ∨ p 1331 = false ∨ p 1334 = true
  clause358 : p 22 = true ∨ p 1336 = true
  clause359 : p 20 = true ∨ p 22 = true ∨ p 1337 = true
  clause360 : p 26 = true ∨ p 1338 = true
  clause361 : p 25 = true ∨ p 1338 = true
  clause362 : p 1338 = false ∨ p 1340 = true
  clause363 : p 1336 = false ∨ p 1340 = true
  clause364 : p 1337 = false ∨ p 1341 = true
  clause365 : p 1340 = false ∨ p 1344 = true
  clause366 : p 1341 = false ∨ p 1345 = true
  clause367 : p 1333 = false ∨ p 1344 = true
  clause368 : p 1333 = false ∨ p 1340 = false ∨ p 1345 = true
  clause369 : p 1334 = false ∨ p 1345 = true
  clause370 : p 1344 = false ∨ p 1351 = true
  clause371 : p 1345 = false ∨ p 1352 = true
  clause372 : p 1325 = false ∨ p 1344 = false ∨ p 1352 = true
  clause373 : p 1326 = false ∨ p 1344 = false ∨ p 1353 = true
  clause374 : p 1326 = false ∨ p 1345 = false ∨ p 1354 = true
  clause375 : p 1328 = false ∨ p 1354 = true
  clause376 : p 1328 = false ∨ p 1344 = false ∨ p 1355 = true
  clause377 : p 1330 = false ∨ p 1344 = false ∨ p 1357 = true
  clause378 : p 34 = true ∨ p 1363 = true
  clause379 : p 31 = true ∨ p 1363 = true
  clause380 : p 31 = true ∨ p 34 = true ∨ p 1364 = true
  clause381 : p 1363 = false ∨ p 1365 = true
  clause382 : p 1364 = false ∨ p 1366 = true
  clause383 : p 40 = true ∨ p 1368 = true
  clause384 : p 38 = true ∨ p 1368 = true
structure Block12 (p : Nat → Bool) : Prop where
  clause385 : p 38 = true ∨ p 40 = true ∨ p 1369 = true
  clause386 : p 1368 = false ∨ p 1370 = true
  clause387 : p 1369 = false ∨ p 1371 = true
  clause388 : p 35 = true ∨ p 1370 = true
  clause389 : p 35 = true ∨ p 1368 = false ∨ p 1371 = true
  clause390 : p 1370 = false ∨ p 1373 = true
  clause391 : p 1371 = false ∨ p 1374 = true
  clause392 : p 1365 = false ∨ p 1373 = true
  clause393 : p 1365 = false ∨ p 1370 = false ∨ p 1374 = true
  clause394 : p 1366 = false ∨ p 1374 = true
  clause395 : p 46 = true ∨ p 1379 = true
  clause396 : p 45 = true ∨ p 46 = true ∨ p 1380 = true
  clause397 : p 1379 = false ∨ p 1381 = true
  clause398 : p 1380 = false ∨ p 1382 = true
  clause399 : p 43 = true ∨ p 1380 = false ∨ p 1383 = true
  clause400 : p 51 = true ∨ p 1384 = true
  clause401 : p 49 = true ∨ p 1384 = true
  clause402 : p 49 = true ∨ p 51 = true ∨ p 1385 = true
  clause403 : p 53 = true ∨ p 1386 = true
  clause404 : p 53 = true ∨ p 57 = true ∨ p 1387 = true
  clause405 : p 1386 = false ∨ p 1388 = true
  clause406 : p 1384 = false ∨ p 1388 = true
  clause407 : p 1384 = false ∨ p 1386 = false ∨ p 1389 = true
  clause408 : p 1385 = false ∨ p 1389 = true
  clause409 : p 1385 = false ∨ p 1386 = false ∨ p 1390 = true
  clause410 : p 1385 = false ∨ p 1387 = false ∨ p 1391 = true
  clause411 : p 1388 = false ∨ p 1392 = true
  clause412 : p 1381 = false ∨ p 1392 = true
  clause413 : p 1381 = false ∨ p 1388 = false ∨ p 1393 = true
  clause414 : p 1381 = false ∨ p 1389 = false ∨ p 1394 = true
  clause415 : p 1381 = false ∨ p 1391 = false ∨ p 1396 = true
  clause416 : p 1382 = false ∨ p 1393 = true
structure Block13 (p : Nat → Bool) : Prop where
  clause417 : p 1382 = false ∨ p 1389 = false ∨ p 1395 = true
  clause418 : p 1382 = false ∨ p 1390 = false ∨ p 1396 = true
  clause419 : p 1383 = false ∨ p 1394 = true
  clause420 : p 1373 = false ∨ p 1392 = false ∨ p 1400 = true
  clause421 : p 1373 = false ∨ p 1393 = false ∨ p 1401 = true
  clause422 : p 1373 = false ∨ p 1394 = false ∨ p 1402 = true
  clause423 : p 1373 = false ∨ p 1395 = false ∨ p 1403 = true
  clause424 : p 1373 = false ∨ p 1396 = false ∨ p 1404 = true
  clause425 : p 1374 = false ∨ p 1392 = false ∨ p 1401 = true
  clause426 : p 1374 = false ∨ p 1393 = false ∨ p 1402 = true
  clause427 : p 1351 = false ∨ p 1401 = false ∨ p 1414 = true
  clause428 : p 1351 = false ∨ p 1402 = false ∨ p 1415 = true
  clause429 : p 1351 = false ∨ p 1403 = false ∨ p 1416 = true
  clause430 : p 1351 = false ∨ p 1404 = false ∨ p 1417 = true
  clause431 : p 1352 = false ∨ p 1400 = false ∨ p 1414 = true
  clause432 : p 1352 = false ∨ p 1402 = false ∨ p 1416 = true
  clause433 : p 1353 = false ∨ p 1400 = false ∨ p 1415 = true
  clause434 : p 1353 = false ∨ p 1401 = false ∨ p 1416 = true
  clause435 : p 1354 = false ∨ p 1400 = false ∨ p 1416 = true
  clause436 : p 1355 = false ∨ p 1400 = false ∨ p 1417 = true
  clause437 : p 1357 = false ∨ p 1400 = false ∨ p 1419 = true
  clause438 : p 63 = true ∨ p 1423 = true
  clause439 : p 61 = true ∨ p 1423 = true
  clause440 : p 61 = true ∨ p 63 = true ∨ p 1424 = true
  clause441 : p 1423 = false ∨ p 1425 = true
  clause442 : p 1424 = false ∨ p 1426 = true
  clause443 : p 59 = true ∨ p 1425 = true
  clause444 : p 59 = true ∨ p 1423 = false ∨ p 1426 = true
  clause445 : p 69 = true ∨ p 1428 = true
  clause446 : p 66 = true ∨ p 1428 = true
  clause447 : p 1428 = false ∨ p 1430 = true
  clause448 : p 64 = true ∨ p 1430 = true
structure Block14 (p : Nat → Bool) : Prop where
  clause449 : p 64 = true ∨ p 1428 = false ∨ p 1431 = true
  clause450 : p 1430 = false ∨ p 1433 = true
  clause451 : p 1431 = false ∨ p 1434 = true
  clause452 : p 1425 = false ∨ p 1433 = true
  clause453 : p 1425 = false ∨ p 1430 = false ∨ p 1434 = true
  clause454 : p 1425 = false ∨ p 1431 = false ∨ p 1435 = true
  clause455 : p 1426 = false ∨ p 1434 = true
  clause456 : p 1426 = false ∨ p 1430 = false ∨ p 1435 = true
  clause457 : p 74 = true ∨ p 1439 = true
  clause458 : p 72 = true ∨ p 1439 = true
  clause459 : p 72 = true ∨ p 74 = true ∨ p 1440 = true
  clause460 : p 1439 = false ∨ p 1441 = true
  clause461 : p 1440 = false ∨ p 1442 = true
  clause462 : p 71 = true ∨ p 1441 = true
  clause463 : p 71 = true ∨ p 1439 = false ∨ p 1442 = true
  clause464 : p 71 = true ∨ p 1440 = false ∨ p 1443 = true
  clause465 : p 79 = true ∨ p 1444 = true
  clause466 : p 77 = true ∨ p 1444 = true
  clause467 : p 77 = true ∨ p 79 = true ∨ p 1445 = true
  clause468 : p 82 = true ∨ p 1446 = true
  clause469 : p 80 = true ∨ p 1446 = true
  clause470 : p 80 = true ∨ p 82 = true ∨ p 1447 = true
  clause471 : p 1446 = false ∨ p 1448 = true
  clause472 : p 1447 = false ∨ p 1449 = true
  clause473 : p 1444 = false ∨ p 1448 = true
  clause474 : p 1444 = false ∨ p 1446 = false ∨ p 1449 = true
  clause475 : p 1445 = false ∨ p 1449 = true
  clause476 : p 1445 = false ∨ p 1446 = false ∨ p 1450 = true
  clause477 : p 1448 = false ∨ p 1452 = true
  clause478 : p 1449 = false ∨ p 1453 = true
  clause479 : p 1441 = false ∨ p 1452 = true
  clause480 : p 1441 = false ∨ p 1448 = false ∨ p 1453 = true
structure Block15 (p : Nat → Bool) : Prop where
  clause481 : p 1441 = false ∨ p 1449 = false ∨ p 1454 = true
  clause482 : p 1441 = false ∨ p 1450 = false ∨ p 1455 = true
  clause483 : p 1442 = false ∨ p 1453 = true
  clause484 : p 1442 = false ∨ p 1448 = false ∨ p 1454 = true
  clause485 : p 1442 = false ∨ p 1449 = false ∨ p 1455 = true
  clause486 : p 1443 = false ∨ p 1454 = true
  clause487 : p 1443 = false ∨ p 1448 = false ∨ p 1455 = true
  clause488 : p 1453 = false ∨ p 1460 = true
  clause489 : p 1433 = false ∨ p 1452 = false ∨ p 1460 = true
  clause490 : p 1433 = false ∨ p 1453 = false ∨ p 1461 = true
  clause491 : p 1433 = false ∨ p 1454 = false ∨ p 1462 = true
  clause492 : p 1433 = false ∨ p 1455 = false ∨ p 1463 = true
  clause493 : p 1434 = false ∨ p 1460 = true
  clause494 : p 1434 = false ∨ p 1452 = false ∨ p 1461 = true
  clause495 : p 1434 = false ∨ p 1453 = false ∨ p 1462 = true
  clause496 : p 1434 = false ∨ p 1454 = false ∨ p 1463 = true
  clause497 : p 1435 = false ∨ p 1461 = true
  clause498 : p 1435 = false ∨ p 1452 = false ∨ p 1462 = true
  clause499 : p 1435 = false ∨ p 1453 = false ∨ p 1463 = true
  clause500 : p 88 = true ∨ p 1471 = true
  clause501 : p 87 = true ∨ p 1471 = true
  clause502 : p 87 = true ∨ p 88 = true ∨ p 1472 = true
  clause503 : p 1471 = false ∨ p 1473 = true
  clause504 : p 1472 = false ∨ p 1474 = true
  clause505 : p 85 = true ∨ p 1473 = true
  clause506 : p 85 = true ∨ p 1471 = false ∨ p 1474 = true
  clause507 : p 85 = true ∨ p 1472 = false ∨ p 1475 = true
  clause508 : p 97 = true ∨ p 1476 = true
  clause509 : p 94 = true ∨ p 1476 = true
  clause510 : p 94 = true ∨ p 97 = true ∨ p 1477 = true
  clause511 : p 1476 = false ∨ p 1478 = true
  clause512 : p 1477 = false ∨ p 1479 = true
structure Block16 (p : Nat → Bool) : Prop where
  clause513 : p 91 = true ∨ p 1478 = true
  clause514 : p 91 = true ∨ p 1476 = false ∨ p 1479 = true
  clause515 : p 91 = true ∨ p 1477 = false ∨ p 1480 = true
  clause516 : p 1478 = false ∨ p 1481 = true
  clause517 : p 1479 = false ∨ p 1482 = true
  clause518 : p 1480 = false ∨ p 1483 = true
  clause519 : p 1473 = false ∨ p 1481 = true
  clause520 : p 1473 = false ∨ p 1478 = false ∨ p 1482 = true
  clause521 : p 1473 = false ∨ p 1479 = false ∨ p 1483 = true
  clause522 : p 1473 = false ∨ p 1480 = false ∨ p 1484 = true
  clause523 : p 1474 = false ∨ p 1482 = true
  clause524 : p 1474 = false ∨ p 1478 = false ∨ p 1483 = true
  clause525 : p 1474 = false ∨ p 1479 = false ∨ p 1484 = true
  clause526 : p 1475 = false ∨ p 1478 = false ∨ p 1484 = true
  clause527 : p 101 = true ∨ p 1487 = true
  clause528 : p 99 = true ∨ p 1487 = true
  clause529 : p 99 = true ∨ p 101 = true ∨ p 1488 = true
  clause530 : p 1487 = false ∨ p 1489 = true
  clause531 : p 1488 = false ∨ p 1490 = true
  clause532 : p 98 = true ∨ p 1489 = true
  clause533 : p 98 = true ∨ p 1487 = false ∨ p 1490 = true
  clause534 : p 98 = true ∨ p 1488 = false ∨ p 1491 = true
  clause535 : p 105 = true ∨ p 1492 = true
  clause536 : p 104 = true ∨ p 1492 = true
  clause537 : p 104 = true ∨ p 105 = true ∨ p 1493 = true
  clause538 : p 107 = true ∨ p 1494 = true
  clause539 : p 106 = true ∨ p 1494 = true
  clause540 : p 106 = true ∨ p 107 = true ∨ p 1495 = true
  clause541 : p 1494 = false ∨ p 1496 = true
  clause542 : p 1495 = false ∨ p 1497 = true
  clause543 : p 1492 = false ∨ p 1496 = true
  clause544 : p 1492 = false ∨ p 1494 = false ∨ p 1497 = true
structure Block17 (p : Nat → Bool) : Prop where
  clause545 : p 1493 = false ∨ p 1497 = true
  clause546 : p 1493 = false ∨ p 1494 = false ∨ p 1498 = true
  clause547 : p 1496 = false ∨ p 1500 = true
  clause548 : p 1497 = false ∨ p 1501 = true
  clause549 : p 1498 = false ∨ p 1502 = true
  clause550 : p 1489 = false ∨ p 1496 = false ∨ p 1501 = true
  clause551 : p 1490 = false ∨ p 1496 = false ∨ p 1502 = true
  clause552 : p 1490 = false ∨ p 1497 = false ∨ p 1503 = true
  clause553 : p 1491 = false ∨ p 1496 = false ∨ p 1503 = true
  clause554 : p 1500 = false ∨ p 1507 = true
  clause555 : p 1501 = false ∨ p 1508 = true
  clause556 : p 1502 = false ∨ p 1509 = true
  clause557 : p 1481 = false ∨ p 1500 = false ∨ p 1508 = true
  clause558 : p 1481 = false ∨ p 1501 = false ∨ p 1509 = true
  clause559 : p 1481 = false ∨ p 1502 = false ∨ p 1510 = true
  clause560 : p 1481 = false ∨ p 1503 = false ∨ p 1511 = true
  clause561 : p 1482 = false ∨ p 1500 = false ∨ p 1509 = true
  clause562 : p 1482 = false ∨ p 1501 = false ∨ p 1510 = true
  clause563 : p 1482 = false ∨ p 1502 = false ∨ p 1511 = true
  clause564 : p 1483 = false ∨ p 1500 = false ∨ p 1510 = true
  clause565 : p 1483 = false ∨ p 1501 = false ∨ p 1511 = true
  clause566 : p 1484 = false ∨ p 1500 = false ∨ p 1511 = true
  clause567 : p 1460 = false ∨ p 1507 = false ∨ p 1521 = true
  clause568 : p 1460 = false ∨ p 1509 = false ∨ p 1523 = true
  clause569 : p 1460 = false ∨ p 1510 = false ∨ p 1524 = true
  clause570 : p 1460 = false ∨ p 1511 = false ∨ p 1525 = true
  clause571 : p 1461 = false ∨ p 1508 = false ∨ p 1523 = true
  clause572 : p 1461 = false ∨ p 1509 = false ∨ p 1524 = true
  clause573 : p 1461 = false ∨ p 1510 = false ∨ p 1525 = true
  clause574 : p 1461 = false ∨ p 1511 = false ∨ p 1526 = true
  clause575 : p 1462 = false ∨ p 1508 = false ∨ p 1524 = true
  clause576 : p 1462 = false ∨ p 1509 = false ∨ p 1525 = true
structure Block18 (p : Nat → Bool) : Prop where
  clause577 : p 1462 = false ∨ p 1510 = false ∨ p 1526 = true
  clause578 : p 1463 = false ∨ p 1508 = false ∨ p 1525 = true
  clause579 : p 1414 = false ∨ p 1526 = false ∨ p 1542 = true
  clause580 : p 1415 = false ∨ p 1525 = false ∨ p 1542 = true
  clause581 : p 1416 = false ∨ p 1524 = false ∨ p 1542 = true
  clause582 : p 1417 = false ∨ p 1523 = false ∨ p 1542 = true
  clause583 : p 1419 = false ∨ p 1521 = false ∨ p 1542 = true
  clause584 : p 1542 = false
  clause585 : p 13 = false ∨ p 14 = false ∨ p 22 = false ∨ p 23 = false
  clause586 : p 60 = false ∨ p 61 = false ∨ p 64 = false ∨ p 65 = false
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
  block10 : Block10 p
  block11 : Block11 p
  block12 : Block12 p
  block13 : Block13 p
  block14 : Block14 p
  block15 : Block15 p
  block16 : Block16 p
  block17 : Block17 p
  block18 : Block18 p
def c1 : List Lit := [(1, false), (110, true)]
theorem step1 (p : Nat → Bool) (h : Constraints p) : clause p c1 = true := by
  simpa only [c1,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause1
def c2 : List Lit := [(2, false), (111, true), (1, true)]
theorem step2 (p : Nat → Bool) (h : Constraints p) : clause p c2 = true := by
  simpa only [c2,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause2
def c3 : List Lit := [(3, false), (112, true), (47, true)]
theorem step3 (p : Nat → Bool) (h : Constraints p) : clause p c3 = true := by
  simpa only [c3,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause3
def c4 : List Lit := [(3, false), (112, true), (5, true)]
theorem step4 (p : Nat → Bool) (h : Constraints p) : clause p c4 = true := by
  simpa only [c4,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause4
def c5 : List Lit := [(4, false), (113, true), (11, true)]
theorem step5 (p : Nat → Bool) (h : Constraints p) : clause p c5 = true := by
  simpa only [c5,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause5
def c6 : List Lit := [(4, false), (113, true), (5, true)]
theorem step6 (p : Nat → Bool) (h : Constraints p) : clause p c6 = true := by
  simpa only [c6,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause6
def c7 : List Lit := [(5, false), (114, true), (4, true)]
theorem step7 (p : Nat → Bool) (h : Constraints p) : clause p c7 = true := by
  simpa only [c7,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause7
def c8 : List Lit := [(5, false), (114, true), (3, true)]
theorem step8 (p : Nat → Bool) (h : Constraints p) : clause p c8 = true := by
  simpa only [c8,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause8
def c9 : List Lit := [(6, false), (115, true), (2, true)]
theorem step9 (p : Nat → Bool) (h : Constraints p) : clause p c9 = true := by
  simpa only [c9,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause9
def c10 : List Lit := [(7, false), (116, true), (8, true)]
theorem step10 (p : Nat → Bool) (h : Constraints p) : clause p c10 = true := by
  simpa only [c10,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause10
def c11 : List Lit := [(8, false), (117, true), (6, true)]
theorem step11 (p : Nat → Bool) (h : Constraints p) : clause p c11 = true := by
  simpa only [c11,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause11
def c12 : List Lit := [(9, false), (118, true), (7, true)]
theorem step12 (p : Nat → Bool) (h : Constraints p) : clause p c12 = true := by
  simpa only [c12,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause12
def c13 : List Lit := [(10, false), (119, true), (12, true)]
theorem step13 (p : Nat → Bool) (h : Constraints p) : clause p c13 = true := by
  simpa only [c13,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause13
def c14 : List Lit := [(11, false), (120, true), (10, true)]
theorem step14 (p : Nat → Bool) (h : Constraints p) : clause p c14 = true := by
  simpa only [c14,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause14
def c15 : List Lit := [(12, false), (121, true), (9, true)]
theorem step15 (p : Nat → Bool) (h : Constraints p) : clause p c15 = true := by
  simpa only [c15,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause15
def c16 : List Lit := [(14, false), (123, true), (16, true), (17, true), (23, true)]
theorem step16 (p : Nat → Bool) (h : Constraints p) : clause p c16 = true := by
  simpa only [c16,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause16
def c17 : List Lit := [(14, false), (123, true), (13, true), (16, true), (17, true)]
theorem step17 (p : Nat → Bool) (h : Constraints p) : clause p c17 = true := by
  simpa only [c17,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause17
def c18 : List Lit := [(16, false), (14, false), (19, false), (25, false)]
theorem step18 (p : Nat → Bool) (h : Constraints p) : clause p c18 = true := by
  simpa only [c18,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause18
def c19 : List Lit := [(17, false), (14, false), (20, false), (79, false)]
theorem step19 (p : Nat → Bool) (h : Constraints p) : clause p c19 = true := by
  simpa only [c19,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause19
def c20 : List Lit := [(22, false), (23, false), (24, false), (27, false)]
theorem step20 (p : Nat → Bool) (h : Constraints p) : clause p c20 = true := by
  simpa only [c20,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause20
def c21 : List Lit := [(23, false), (14, false), (22, false), (25, false)]
theorem step21 (p : Nat → Bool) (h : Constraints p) : clause p c21 = true := by
  simpa only [c21,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause21
def c22 : List Lit := [(24, false), (15, false), (25, false), (26, false)]
theorem step22 (p : Nat → Bool) (h : Constraints p) : clause p c22 = true := by
  simpa only [c22,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause22
def c23 : List Lit := [(25, false), (16, true), (23, true), (24, true)]
theorem step23 (p : Nat → Bool) (h : Constraints p) : clause p c23 = true := by
  simpa only [c23,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause23
def c24 : List Lit := [(25, false), (134, true), (16, true), (24, true)]
theorem step24 (p : Nat → Bool) (h : Constraints p) : clause p c24 = true := by
  simpa only [c24,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause24
def c25 : List Lit := [(25, false), (134, true), (16, true), (23, true)]
theorem step25 (p : Nat → Bool) (h : Constraints p) : clause p c25 = true := by
  simpa only [c25,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause25
def c26 : List Lit := [(33, false), (34, false), (35, false), (38, false)]
theorem step26 (p : Nat → Bool) (h : Constraints p) : clause p c26 = true := by
  simpa only [c26,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause26
def c27 : List Lit := [(38, false), (33, true), (39, true)]
theorem step27 (p : Nat → Bool) (h : Constraints p) : clause p c27 = true := by
  simpa only [c27,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause27
def c28 : List Lit := [(38, false), (147, true), (33, true)]
theorem step28 (p : Nat → Bool) (h : Constraints p) : clause p c28 = true := by
  simpa only [c28,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause28
def c29 : List Lit := [(39, false), (34, false), (38, false), (40, false)]
theorem step29 (p : Nat → Bool) (h : Constraints p) : clause p c29 = true := by
  simpa only [c29,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause29
def c30 : List Lit := [(40, false), (149, true), (44, true)]
theorem step30 (p : Nat → Bool) (h : Constraints p) : clause p c30 = true := by
  simpa only [c30,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause30
def c31 : List Lit := [(40, false), (149, true), (39, true)]
theorem step31 (p : Nat → Bool) (h : Constraints p) : clause p c31 = true := by
  simpa only [c31,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause31
def c32 : List Lit := [(41, false), (150, true)]
theorem step32 (p : Nat → Bool) (h : Constraints p) : clause p c32 = true := by
  simpa only [c32,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause32
def c33 : List Lit := [(43, false), (152, true), (41, true), (42, true), (44, true)]
theorem step33 (p : Nat → Bool) (h : Constraints p) : clause p c33 = true := by
  simpa only [c33,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause33
def c34 : List Lit := [(44, false), (31, false), (40, false), (43, false)]
theorem step34 (p : Nat → Bool) (h : Constraints p) : clause p c34 = true := by
  simpa only [c34,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause34
def c35 : List Lit := [(44, false), (153, true), (31, true), (40, true)]
theorem step35 (p : Nat → Bool) (h : Constraints p) : clause p c35 = true := by
  simpa only [c35,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause35
def c36 : List Lit := [(45, false), (154, true), (56, true)]
theorem step36 (p : Nat → Bool) (h : Constraints p) : clause p c36 = true := by
  simpa only [c36,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause36
def c37 : List Lit := [(46, false), (50, true)]
theorem step37 (p : Nat → Bool) (h : Constraints p) : clause p c37 = true := by
  simpa only [c37,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause37
def c38 : List Lit := [(46, false), (155, true)]
theorem step38 (p : Nat → Bool) (h : Constraints p) : clause p c38 = true := by
  simpa only [c38,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause38
def c39 : List Lit := [(47, false), (3, false), (45, false), (53, false)]
theorem step39 (p : Nat → Bool) (h : Constraints p) : clause p c39 = true := by
  simpa only [c39,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause39
def c40 : List Lit := [(48, false), (157, true), (57, true)]
theorem step40 (p : Nat → Bool) (h : Constraints p) : clause p c40 = true := by
  simpa only [c40,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause40
def c41 : List Lit := [(49, false), (158, true), (48, true)]
theorem step41 (p : Nat → Bool) (h : Constraints p) : clause p c41 = true := by
  simpa only [c41,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause41
def c42 : List Lit := [(50, false), (46, false), (49, false), (51, false)]
theorem step42 (p : Nat → Bool) (h : Constraints p) : clause p c42 = true := by
  simpa only [c42,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause42
def c43 : List Lit := [(50, false), (159, true), (46, true), (49, true)]
theorem step43 (p : Nat → Bool) (h : Constraints p) : clause p c43 = true := by
  simpa only [c43,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause43
def c44 : List Lit := [(51, false), (160, true), (54, true)]
theorem step44 (p : Nat → Bool) (h : Constraints p) : clause p c44 = true := by
  simpa only [c44,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause44
def c45 : List Lit := [(51, false), (160, true), (50, true)]
theorem step45 (p : Nat → Bool) (h : Constraints p) : clause p c45 = true := by
  simpa only [c45,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause45
def c46 : List Lit := [(52, false), (161, true)]
theorem step46 (p : Nat → Bool) (h : Constraints p) : clause p c46 = true := by
  simpa only [c46,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause46
def c47 : List Lit := [(53, false), (162, true), (52, true), (54, true)]
theorem step47 (p : Nat → Bool) (h : Constraints p) : clause p c47 = true := by
  simpa only [c47,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause47
def c48 : List Lit := [(53, false), (162, true), (47, true), (52, true)]
theorem step48 (p : Nat → Bool) (h : Constraints p) : clause p c48 = true := by
  simpa only [c48,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause48
def c49 : List Lit := [(54, false), (163, true), (53, true)]
theorem step49 (p : Nat → Bool) (h : Constraints p) : clause p c49 = true := by
  simpa only [c49,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause49
def c50 : List Lit := [(54, false), (163, true), (51, true)]
theorem step50 (p : Nat → Bool) (h : Constraints p) : clause p c50 = true := by
  simpa only [c50,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause50
def c51 : List Lit := [(56, false), (45, false), (59, false), (61, false)]
theorem step51 (p : Nat → Bool) (h : Constraints p) : clause p c51 = true := by
  simpa only [c51,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause51
def c52 : List Lit := [(56, false), (45, false), (59, false), (77, false)]
theorem step52 (p : Nat → Bool) (h : Constraints p) : clause p c52 = true := by
  simpa only [c52,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause52
def c53 : List Lit := [(56, false), (45, false), (61, false), (77, false)]
theorem step53 (p : Nat → Bool) (h : Constraints p) : clause p c53 = true := by
  simpa only [c53,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause53
def c54 : List Lit := [(56, false), (59, false), (61, false), (77, false)]
theorem step54 (p : Nat → Bool) (h : Constraints p) : clause p c54 = true := by
  simpa only [c54,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause54
def c55 : List Lit := [(57, false), (48, false), (58, false), (68, false)]
theorem step55 (p : Nat → Bool) (h : Constraints p) : clause p c55 = true := by
  simpa only [c55,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause55
def c56 : List Lit := [(58, false), (167, true), (57, true)]
theorem step56 (p : Nat → Bool) (h : Constraints p) : clause p c56 = true := by
  simpa only [c56,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause56
def c57 : List Lit := [(59, false), (56, true), (58, true)]
theorem step57 (p : Nat → Bool) (h : Constraints p) : clause p c57 = true := by
  simpa only [c57,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause57
def c58 : List Lit := [(59, false), (168, true), (58, true)]
theorem step58 (p : Nat → Bool) (h : Constraints p) : clause p c58 = true := by
  simpa only [c58,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause58
def c59 : List Lit := [(59, false), (168, true), (56, true)]
theorem step59 (p : Nat → Bool) (h : Constraints p) : clause p c59 = true := by
  simpa only [c59,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause59
def c60 : List Lit := [(60, false), (169, true), (64, true)]
theorem step60 (p : Nat → Bool) (h : Constraints p) : clause p c60 = true := by
  simpa only [c60,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause60
def c61 : List Lit := [(60, false), (169, true), (61, true)]
theorem step61 (p : Nat → Bool) (h : Constraints p) : clause p c61 = true := by
  simpa only [c61,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause61
def c62 : List Lit := [(61, false), (170, true), (56, true), (65, true)]
theorem step62 (p : Nat → Bool) (h : Constraints p) : clause p c62 = true := by
  simpa only [c62,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause62
def c63 : List Lit := [(61, false), (170, true), (56, true), (60, true)]
theorem step63 (p : Nat → Bool) (h : Constraints p) : clause p c63 = true := by
  simpa only [c63,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause63
def c64 : List Lit := [(62, false), (63, false), (66, false), (69, false)]
theorem step64 (p : Nat → Bool) (h : Constraints p) : clause p c64 = true := by
  simpa only [c64,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause64
def c65 : List Lit := [(63, false), (62, true), (70, true), (95, true)]
theorem step65 (p : Nat → Bool) (h : Constraints p) : clause p c65 = true := by
  simpa only [c65,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause65
def c66 : List Lit := [(64, false), (173, true), (60, true), (65, true)]
theorem step66 (p : Nat → Bool) (h : Constraints p) : clause p c66 = true := by
  simpa only [c66,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause66
def c67 : List Lit := [(65, false), (61, false), (64, false), (74, false)]
theorem step67 (p : Nat → Bool) (h : Constraints p) : clause p c67 = true := by
  simpa only [c67,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause67
def c68 : List Lit := [(65, false), (61, false), (74, false), (98, false)]
theorem step68 (p : Nat → Bool) (h : Constraints p) : clause p c68 = true := by
  simpa only [c68,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause68
def c69 : List Lit := [(65, false), (64, false), (74, false), (98, false)]
theorem step69 (p : Nat → Bool) (h : Constraints p) : clause p c69 = true := by
  simpa only [c69,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause69
def c70 : List Lit := [(66, false), (175, true), (62, true)]
theorem step70 (p : Nat → Bool) (h : Constraints p) : clause p c70 = true := by
  simpa only [c70,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause70
def c71 : List Lit := [(68, false), (57, false), (69, false), (72, false)]
theorem step71 (p : Nat → Bool) (h : Constraints p) : clause p c71 = true := by
  simpa only [c71,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause71
def c72 : List Lit := [(68, false), (57, false), (69, false), (101, false)]
theorem step72 (p : Nat → Bool) (h : Constraints p) : clause p c72 = true := by
  simpa only [c72,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause72
def c73 : List Lit := [(68, false), (57, false), (72, false), (101, false)]
theorem step73 (p : Nat → Bool) (h : Constraints p) : clause p c73 = true := by
  simpa only [c73,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause73
def c74 : List Lit := [(68, false), (69, false), (72, false), (101, false)]
theorem step74 (p : Nat → Bool) (h : Constraints p) : clause p c74 = true := by
  simpa only [c74,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause74
def c75 : List Lit := [(69, false), (62, true), (68, true), (70, true)]
theorem step75 (p : Nat → Bool) (h : Constraints p) : clause p c75 = true := by
  simpa only [c75,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause75
def c76 : List Lit := [(69, false), (62, false), (68, false), (70, false)]
theorem step76 (p : Nat → Bool) (h : Constraints p) : clause p c76 = true := by
  simpa only [c76,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause76
def c77 : List Lit := [(69, false), (178, true), (68, true), (70, true)]
theorem step77 (p : Nat → Bool) (h : Constraints p) : clause p c77 = true := by
  simpa only [c77,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause77
def c78 : List Lit := [(69, false), (178, true), (62, true), (70, true)]
theorem step78 (p : Nat → Bool) (h : Constraints p) : clause p c78 = true := by
  simpa only [c78,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause78
def c79 : List Lit := [(70, false), (63, false), (69, false), (71, false)]
theorem step79 (p : Nat → Bool) (h : Constraints p) : clause p c79 = true := by
  simpa only [c79,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause79
def c80 : List Lit := [(70, false), (179, true), (63, true), (71, true)]
theorem step80 (p : Nat → Bool) (h : Constraints p) : clause p c80 = true := by
  simpa only [c80,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause80
def c81 : List Lit := [(71, false), (180, true), (75, true)]
theorem step81 (p : Nat → Bool) (h : Constraints p) : clause p c81 = true := by
  simpa only [c81,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause81
def c82 : List Lit := [(71, false), (180, true), (70, true)]
theorem step82 (p : Nat → Bool) (h : Constraints p) : clause p c82 = true := by
  simpa only [c82,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause82
def c83 : List Lit := [(72, false), (181, true), (73, true)]
theorem step83 (p : Nat → Bool) (h : Constraints p) : clause p c83 = true := by
  simpa only [c83,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause83
def c84 : List Lit := [(72, false), (181, true), (68, true)]
theorem step84 (p : Nat → Bool) (h : Constraints p) : clause p c84 = true := by
  simpa only [c84,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause84
def c85 : List Lit := [(73, false), (182, true), (72, true)]
theorem step85 (p : Nat → Bool) (h : Constraints p) : clause p c85 = true := by
  simpa only [c85,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause85
def c86 : List Lit := [(74, false), (65, false), (73, false), (75, false)]
theorem step86 (p : Nat → Bool) (h : Constraints p) : clause p c86 = true := by
  simpa only [c86,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause86
def c87 : List Lit := [(74, false), (183, true), (73, true), (75, true)]
theorem step87 (p : Nat → Bool) (h : Constraints p) : clause p c87 = true := by
  simpa only [c87,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause87
def c88 : List Lit := [(74, false), (183, true), (65, true), (73, true)]
theorem step88 (p : Nat → Bool) (h : Constraints p) : clause p c88 = true := by
  simpa only [c88,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause88
def c89 : List Lit := [(75, false), (184, true), (74, true)]
theorem step89 (p : Nat → Bool) (h : Constraints p) : clause p c89 = true := by
  simpa only [c89,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause89
def c90 : List Lit := [(75, false), (184, true), (71, true)]
theorem step90 (p : Nat → Bool) (h : Constraints p) : clause p c90 = true := by
  simpa only [c90,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause90
def c91 : List Lit := [(76, false), (15, false), (77, false), (80, false)]
theorem step91 (p : Nat → Bool) (h : Constraints p) : clause p c91 = true := by
  simpa only [c91,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause91
def c92 : List Lit := [(77, false), (16, false), (56, false), (76, false)]
theorem step92 (p : Nat → Bool) (h : Constraints p) : clause p c92 = true := by
  simpa only [c92,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause92
def c93 : List Lit := [(78, false), (79, false), (82, false), (85, false)]
theorem step93 (p : Nat → Bool) (h : Constraints p) : clause p c93 = true := by
  simpa only [c93,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause93
def c94 : List Lit := [(79, false), (17, false), (78, false), (86, false)]
theorem step94 (p : Nat → Bool) (h : Constraints p) : clause p c94 = true := by
  simpa only [c94,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause94
def c95 : List Lit := [(79, false), (188, true), (17, true), (78, true), (95, true)]
theorem step95 (p : Nat → Bool) (h : Constraints p) : clause p c95 = true := by
  simpa only [c95,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause95
def c96 : List Lit := [(80, false), (189, true), (76, true), (81, true), (90, true)]
theorem step96 (p : Nat → Bool) (h : Constraints p) : clause p c96 = true := by
  simpa only [c96,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause96
def c97 : List Lit := [(81, false), (77, false), (80, false), (91, false)]
theorem step97 (p : Nat → Bool) (h : Constraints p) : clause p c97 = true := by
  simpa only [c97,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause97
def c98 : List Lit := [(81, false), (80, false), (91, false), (98, false)]
theorem step98 (p : Nat → Bool) (h : Constraints p) : clause p c98 = true := by
  simpa only [c98,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause98
def c99 : List Lit := [(82, false), (78, true), (83, true)]
theorem step99 (p : Nat → Bool) (h : Constraints p) : clause p c99 = true := by
  simpa only [c99,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause99
def c100 : List Lit := [(82, false), (191, true), (78, true)]
theorem step100 (p : Nat → Bool) (h : Constraints p) : clause p c100 = true := by
  simpa only [c100,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause100
def c101 : List Lit := [(83, false), (192, true), (80, true)]
theorem step101 (p : Nat → Bool) (h : Constraints p) : clause p c101 = true := by
  simpa only [c101,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause101
def c102 : List Lit := [(84, false), (22, false), (85, false), (88, false)]
theorem step102 (p : Nat → Bool) (h : Constraints p) : clause p c102 = true := by
  simpa only [c102,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause102
def c103 : List Lit := [(84, false), (57, false), (85, false), (88, false)]
theorem step103 (p : Nat → Bool) (h : Constraints p) : clause p c103 = true := by
  simpa only [c103,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause103
def c104 : List Lit := [(84, false), (85, false), (88, false), (101, false)]
theorem step104 (p : Nat → Bool) (h : Constraints p) : clause p c104 = true := by
  simpa only [c104,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause104
def c105 : List Lit := [(85, false), (78, false), (84, false), (86, false)]
theorem step105 (p : Nat → Bool) (h : Constraints p) : clause p c105 = true := by
  simpa only [c105,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause105
def c106 : List Lit := [(85, false), (194, true), (84, true), (86, true)]
theorem step106 (p : Nat → Bool) (h : Constraints p) : clause p c106 = true := by
  simpa only [c106,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause106
def c107 : List Lit := [(85, false), (194, true), (78, true), (86, true)]
theorem step107 (p : Nat → Bool) (h : Constraints p) : clause p c107 = true := by
  simpa only [c107,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause107
def c108 : List Lit := [(85, false), (194, true), (78, true), (84, true)]
theorem step108 (p : Nat → Bool) (h : Constraints p) : clause p c108 = true := by
  simpa only [c108,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause108
def c109 : List Lit := [(86, false), (79, false), (85, false), (87, false)]
theorem step109 (p : Nat → Bool) (h : Constraints p) : clause p c109 = true := by
  simpa only [c109,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause109
def c110 : List Lit := [(87, false), (86, true), (92, true)]
theorem step110 (p : Nat → Bool) (h : Constraints p) : clause p c110 = true := by
  simpa only [c110,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause110
def c111 : List Lit := [(87, false), (196, true), (92, true)]
theorem step111 (p : Nat → Bool) (h : Constraints p) : clause p c111 = true := by
  simpa only [c111,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause111
def c112 : List Lit := [(87, false), (196, true), (86, true)]
theorem step112 (p : Nat → Bool) (h : Constraints p) : clause p c112 = true := by
  simpa only [c112,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause112
def c113 : List Lit := [(88, false), (197, true), (27, true), (84, true), (90, true)]
theorem step113 (p : Nat → Bool) (h : Constraints p) : clause p c113 = true := by
  simpa only [c113,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause113
def c114 : List Lit := [(89, false), (198, true), (88, true)]
theorem step114 (p : Nat → Bool) (h : Constraints p) : clause p c114 = true := by
  simpa only [c114,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause114
def c115 : List Lit := [(90, false), (80, false), (88, false), (91, false)]
theorem step115 (p : Nat → Bool) (h : Constraints p) : clause p c115 = true := by
  simpa only [c115,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause115
def c116 : List Lit := [(90, false), (80, false), (88, false), (106, false)]
theorem step116 (p : Nat → Bool) (h : Constraints p) : clause p c116 = true := by
  simpa only [c116,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause116
def c117 : List Lit := [(90, false), (80, false), (91, false), (106, false)]
theorem step117 (p : Nat → Bool) (h : Constraints p) : clause p c117 = true := by
  simpa only [c117,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause117
def c118 : List Lit := [(90, false), (88, false), (91, false), (106, false)]
theorem step118 (p : Nat → Bool) (h : Constraints p) : clause p c118 = true := by
  simpa only [c118,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause118
def c119 : List Lit := [(91, false), (200, true), (81, true), (90, true), (92, true)]
theorem step119 (p : Nat → Bool) (h : Constraints p) : clause p c119 = true := by
  simpa only [c119,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause119
def c120 : List Lit := [(91, false), (200, true), (81, true), (89, true), (90, true)]
theorem step120 (p : Nat → Bool) (h : Constraints p) : clause p c120 = true := by
  simpa only [c120,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause120
def c121 : List Lit := [(92, false), (31, false), (87, false), (91, false)]
theorem step121 (p : Nat → Bool) (h : Constraints p) : clause p c121 = true := by
  simpa only [c121,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause121
def c122 : List Lit := [(93, false), (94, true), (101, true)]
theorem step122 (p : Nat → Bool) (h : Constraints p) : clause p c122 = true := by
  simpa only [c122,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause122
def c123 : List Lit := [(202, false), (94, false), (101, false)]
theorem step123 (p : Nat → Bool) (h : Constraints p) : clause p c123 = true := by
  simpa only [c123,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause123
def c124 : List Lit := [(93, true)]
theorem step124 (p : Nat → Bool) (h : Constraints p) : clause p c124 = true := by
  simpa only [c124,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause124
def c125 : List Lit := [(202, true)]
theorem step125 (p : Nat → Bool) (h : Constraints p) : clause p c125 = true := by
  simpa only [c125,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause125
def c126 : List Lit := [(94, false), (203, true), (95, true), (102, true)]
theorem step126 (p : Nat → Bool) (h : Constraints p) : clause p c126 = true := by
  simpa only [c126,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause126
def c127 : List Lit := [(95, false), (63, false), (79, false), (94, false)]
theorem step127 (p : Nat → Bool) (h : Constraints p) : clause p c127 = true := by
  simpa only [c127,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause127
def c128 : List Lit := [(95, false), (63, false), (97, false), (99, false)]
theorem step128 (p : Nat → Bool) (h : Constraints p) : clause p c128 = true := by
  simpa only [c128,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause128
def c129 : List Lit := [(95, false), (79, false), (94, false), (97, false)]
theorem step129 (p : Nat → Bool) (h : Constraints p) : clause p c129 = true := by
  simpa only [c129,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause129
def c130 : List Lit := [(95, false), (79, false), (94, false), (99, false)]
theorem step130 (p : Nat → Bool) (h : Constraints p) : clause p c130 = true := by
  simpa only [c130,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause130
def c131 : List Lit := [(95, false), (79, false), (97, false), (99, false)]
theorem step131 (p : Nat → Bool) (h : Constraints p) : clause p c131 = true := by
  simpa only [c131,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause131
def c132 : List Lit := [(95, false), (94, false), (97, false), (99, false)]
theorem step132 (p : Nat → Bool) (h : Constraints p) : clause p c132 = true := by
  simpa only [c132,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause132
def c133 : List Lit := [(97, false), (206, true), (95, true), (100, true)]
theorem step133 (p : Nat → Bool) (h : Constraints p) : clause p c133 = true := by
  simpa only [c133,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause133
def c134 : List Lit := [(97, false), (206, true), (95, true), (96, true)]
theorem step134 (p : Nat → Bool) (h : Constraints p) : clause p c134 = true := by
  simpa only [c134,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause134
def c135 : List Lit := [(98, false), (207, true), (65, true), (81, true), (100, true)]
theorem step135 (p : Nat → Bool) (h : Constraints p) : clause p c135 = true := by
  simpa only [c135,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause135
def c136 : List Lit := [(99, false), (208, true), (100, true), (108, true)]
theorem step136 (p : Nat → Bool) (h : Constraints p) : clause p c136 = true := by
  simpa only [c136,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause136
def c137 : List Lit := [(99, false), (208, true), (95, true), (100, true)]
theorem step137 (p : Nat → Bool) (h : Constraints p) : clause p c137 = true := by
  simpa only [c137,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause137
def c138 : List Lit := [(100, false), (97, false), (98, false), (99, false)]
theorem step138 (p : Nat → Bool) (h : Constraints p) : clause p c138 = true := by
  simpa only [c138,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause138
def c139 : List Lit := [(101, false), (68, false), (93, false), (102, false)]
theorem step139 (p : Nat → Bool) (h : Constraints p) : clause p c139 = true := by
  simpa only [c139,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause139
def c140 : List Lit := [(102, false), (211, true), (101, true), (104, true)]
theorem step140 (p : Nat → Bool) (h : Constraints p) : clause p c140 = true := by
  simpa only [c140,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause140
def c141 : List Lit := [(103, false), (101, false), (104, false), (105, false)]
theorem step141 (p : Nat → Bool) (h : Constraints p) : clause p c141 = true := by
  simpa only [c141,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause141
def c142 : List Lit := [(103, false), (101, false), (104, false), (106, false)]
theorem step142 (p : Nat → Bool) (h : Constraints p) : clause p c142 = true := by
  simpa only [c142,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause142
def c143 : List Lit := [(103, false), (101, false), (105, false), (106, false)]
theorem step143 (p : Nat → Bool) (h : Constraints p) : clause p c143 = true := by
  simpa only [c143,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause143
def c144 : List Lit := [(103, false), (104, false), (105, false), (106, false)]
theorem step144 (p : Nat → Bool) (h : Constraints p) : clause p c144 = true := by
  simpa only [c144,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause144
def c145 : List Lit := [(104, false), (102, true), (103, true)]
theorem step145 (p : Nat → Bool) (h : Constraints p) : clause p c145 = true := by
  simpa only [c145,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause145
def c146 : List Lit := [(104, false), (213, true), (103, true)]
theorem step146 (p : Nat → Bool) (h : Constraints p) : clause p c146 = true := by
  simpa only [c146,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause146
def c147 : List Lit := [(105, false), (96, false), (103, false), (109, false)]
theorem step147 (p : Nat → Bool) (h : Constraints p) : clause p c147 = true := by
  simpa only [c147,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause147
def c148 : List Lit := [(105, false), (214, true), (103, true), (109, true)]
theorem step148 (p : Nat → Bool) (h : Constraints p) : clause p c148 = true := by
  simpa only [c148,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause148
def c149 : List Lit := [(106, false), (42, false), (103, false), (109, false)]
theorem step149 (p : Nat → Bool) (h : Constraints p) : clause p c149 = true := by
  simpa only [c149,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause149
def c150 : List Lit := [(106, false), (215, true), (90, true), (103, true), (109, true)]
theorem step150 (p : Nat → Bool) (h : Constraints p) : clause p c150 = true := by
  simpa only [c150,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause150
def c151 : List Lit := [(107, false), (216, true), (109, true)]
theorem step151 (p : Nat → Bool) (h : Constraints p) : clause p c151 = true := by
  simpa only [c151,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause151
def c152 : List Lit := [(107, false), (216, true), (108, true)]
theorem step152 (p : Nat → Bool) (h : Constraints p) : clause p c152 = true := by
  simpa only [c152,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause152
def c153 : List Lit := [(108, false), (217, true), (107, true)]
theorem step153 (p : Nat → Bool) (h : Constraints p) : clause p c153 = true := by
  simpa only [c153,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause153
def c154 : List Lit := [(108, false), (217, true), (99, true)]
theorem step154 (p : Nat → Bool) (h : Constraints p) : clause p c154 = true := by
  simpa only [c154,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause154
def c155 : List Lit := [(109, false), (105, false), (106, false), (107, false)]
theorem step155 (p : Nat → Bool) (h : Constraints p) : clause p c155 = true := by
  simpa only [c155,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause155
def c156 : List Lit := [(109, false), (218, true), (105, true), (106, true)]
theorem step156 (p : Nat → Bool) (h : Constraints p) : clause p c156 = true := by
  simpa only [c156,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause156
def c157 : List Lit := [(110, false)]
theorem step157 (p : Nat → Bool) (h : Constraints p) : clause p c157 = true := by
  simpa only [c157,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause157
def c158 : List Lit := [(114, false)]
theorem step158 (p : Nat → Bool) (h : Constraints p) : clause p c158 = true := by
  simpa only [c158,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause158
def c159 : List Lit := [(115, false)]
theorem step159 (p : Nat → Bool) (h : Constraints p) : clause p c159 = true := by
  simpa only [c159,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause159
def c160 : List Lit := [(116, false)]
theorem step160 (p : Nat → Bool) (h : Constraints p) : clause p c160 = true := by
  simpa only [c160,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause160
def c161 : List Lit := [(120, false)]
theorem step161 (p : Nat → Bool) (h : Constraints p) : clause p c161 = true := by
  simpa only [c161,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause161
def c162 : List Lit := [(121, false)]
theorem step162 (p : Nat → Bool) (h : Constraints p) : clause p c162 = true := by
  simpa only [c162,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause162
def c163 : List Lit := [(150, false)]
theorem step163 (p : Nat → Bool) (h : Constraints p) : clause p c163 = true := by
  simpa only [c163,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause163
def c164 : List Lit := [(153, false)]
theorem step164 (p : Nat → Bool) (h : Constraints p) : clause p c164 = true := by
  simpa only [c164,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause164
def c165 : List Lit := [(157, false)]
theorem step165 (p : Nat → Bool) (h : Constraints p) : clause p c165 = true := by
  simpa only [c165,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause165
def c166 : List Lit := [(159, false)]
theorem step166 (p : Nat → Bool) (h : Constraints p) : clause p c166 = true := by
  simpa only [c166,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause166
def c167 : List Lit := [(161, false)]
theorem step167 (p : Nat → Bool) (h : Constraints p) : clause p c167 = true := by
  simpa only [c167,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause167
def c168 : List Lit := [(163, false)]
theorem step168 (p : Nat → Bool) (h : Constraints p) : clause p c168 = true := by
  simpa only [c168,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause168
def c169 : List Lit := [(167, false)]
theorem step169 (p : Nat → Bool) (h : Constraints p) : clause p c169 = true := by
  simpa only [c169,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause169
def c170 : List Lit := [(169, false)]
theorem step170 (p : Nat → Bool) (h : Constraints p) : clause p c170 = true := by
  simpa only [c170,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause170
def c171 : List Lit := [(179, false)]
theorem step171 (p : Nat → Bool) (h : Constraints p) : clause p c171 = true := by
  simpa only [c171,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause171
def c172 : List Lit := [(182, false)]
theorem step172 (p : Nat → Bool) (h : Constraints p) : clause p c172 = true := by
  simpa only [c172,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause172
def c173 : List Lit := [(184, false)]
theorem step173 (p : Nat → Bool) (h : Constraints p) : clause p c173 = true := by
  simpa only [c173,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause173
def c174 : List Lit := [(192, false)]
theorem step174 (p : Nat → Bool) (h : Constraints p) : clause p c174 = true := by
  simpa only [c174,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause174
def c175 : List Lit := [(198, false)]
theorem step175 (p : Nat → Bool) (h : Constraints p) : clause p c175 = true := by
  simpa only [c175,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause175
def c176 : List Lit := [(211, false)]
theorem step176 (p : Nat → Bool) (h : Constraints p) : clause p c176 = true := by
  simpa only [c176,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause176
def c177 : List Lit := [(217, false)]
theorem step177 (p : Nat → Bool) (h : Constraints p) : clause p c177 = true := by
  simpa only [c177,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause177
def c178 : List Lit := [(218, false)]
theorem step178 (p : Nat → Bool) (h : Constraints p) : clause p c178 = true := by
  simpa only [c178,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause178
def c179 : List Lit := [(112, false), (219, true)]
theorem step179 (p : Nat → Bool) (h : Constraints p) : clause p c179 = true := by
  simpa only [c179,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause179
def c180 : List Lit := [(111, false), (219, true)]
theorem step180 (p : Nat → Bool) (h : Constraints p) : clause p c180 = true := by
  simpa only [c180,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause180
def c181 : List Lit := [(111, false), (112, false), (220, true)]
theorem step181 (p : Nat → Bool) (h : Constraints p) : clause p c181 = true := by
  simpa only [c181,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause181
def c182 : List Lit := [(219, false), (221, true)]
theorem step182 (p : Nat → Bool) (h : Constraints p) : clause p c182 = true := by
  simpa only [c182,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause182
def c183 : List Lit := [(220, false), (222, true)]
theorem step183 (p : Nat → Bool) (h : Constraints p) : clause p c183 = true := by
  simpa only [c183,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause183
def c184 : List Lit := [(113, false), (225, true)]
theorem step184 (p : Nat → Bool) (h : Constraints p) : clause p c184 = true := by
  simpa only [c184,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause184
def c185 : List Lit := [(225, false), (227, true)]
theorem step185 (p : Nat → Bool) (h : Constraints p) : clause p c185 = true := by
  simpa only [c185,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause185
def c186 : List Lit := [(221, false), (227, true)]
theorem step186 (p : Nat → Bool) (h : Constraints p) : clause p c186 = true := by
  simpa only [c186,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause186
def c187 : List Lit := [(221, false), (225, false), (228, true)]
theorem step187 (p : Nat → Bool) (h : Constraints p) : clause p c187 = true := by
  simpa only [c187,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause187
def c188 : List Lit := [(222, false), (228, true)]
theorem step188 (p : Nat → Bool) (h : Constraints p) : clause p c188 = true := by
  simpa only [c188,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause188
def c189 : List Lit := [(118, false), (229, true)]
theorem step189 (p : Nat → Bool) (h : Constraints p) : clause p c189 = true := by
  simpa only [c189,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause189
def c190 : List Lit := [(117, false), (229, true)]
theorem step190 (p : Nat → Bool) (h : Constraints p) : clause p c190 = true := by
  simpa only [c190,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause190
def c191 : List Lit := [(229, false), (231, true)]
theorem step191 (p : Nat → Bool) (h : Constraints p) : clause p c191 = true := by
  simpa only [c191,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause191
def c192 : List Lit := [(119, false), (233, true)]
theorem step192 (p : Nat → Bool) (h : Constraints p) : clause p c192 = true := by
  simpa only [c192,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause192
def c193 : List Lit := [(233, false), (237, true)]
theorem step193 (p : Nat → Bool) (h : Constraints p) : clause p c193 = true := by
  simpa only [c193,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause193
def c194 : List Lit := [(237, false), (239, true)]
theorem step194 (p : Nat → Bool) (h : Constraints p) : clause p c194 = true := by
  simpa only [c194,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause194
def c195 : List Lit := [(231, false), (239, true)]
theorem step195 (p : Nat → Bool) (h : Constraints p) : clause p c195 = true := by
  simpa only [c195,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause195
def c196 : List Lit := [(239, false), (241, true)]
theorem step196 (p : Nat → Bool) (h : Constraints p) : clause p c196 = true := by
  simpa only [c196,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause196
def c197 : List Lit := [(227, false), (241, true)]
theorem step197 (p : Nat → Bool) (h : Constraints p) : clause p c197 = true := by
  simpa only [c197,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause197
def c198 : List Lit := [(228, false), (242, true)]
theorem step198 (p : Nat → Bool) (h : Constraints p) : clause p c198 = true := by
  simpa only [c198,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause198
def c199 : List Lit := [(123, false), (245, true)]
theorem step199 (p : Nat → Bool) (h : Constraints p) : clause p c199 = true := by
  simpa only [c199,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause199
def c200 : List Lit := [(245, false), (253, true)]
theorem step200 (p : Nat → Bool) (h : Constraints p) : clause p c200 = true := by
  simpa only [c200,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause200
def c201 : List Lit := [(134, false), (259, true)]
theorem step201 (p : Nat → Bool) (h : Constraints p) : clause p c201 = true := by
  simpa only [c201,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause201
def c202 : List Lit := [(259, false), (263, true)]
theorem step202 (p : Nat → Bool) (h : Constraints p) : clause p c202 = true := by
  simpa only [c202,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause202
def c203 : List Lit := [(263, false), (265, true)]
theorem step203 (p : Nat → Bool) (h : Constraints p) : clause p c203 = true := by
  simpa only [c203,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause203
def c204 : List Lit := [(265, false), (267, true)]
theorem step204 (p : Nat → Bool) (h : Constraints p) : clause p c204 = true := by
  simpa only [c204,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause204
def c205 : List Lit := [(253, false), (267, true)]
theorem step205 (p : Nat → Bool) (h : Constraints p) : clause p c205 = true := by
  simpa only [c205,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause205
def c206 : List Lit := [(241, false), (269, true)]
theorem step206 (p : Nat → Bool) (h : Constraints p) : clause p c206 = true := by
  simpa only [c206,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause206
def c207 : List Lit := [(241, false), (267, false), (270, true)]
theorem step207 (p : Nat → Bool) (h : Constraints p) : clause p c207 = true := by
  simpa only [c207,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause207
def c208 : List Lit := [(242, false), (270, true)]
theorem step208 (p : Nat → Bool) (h : Constraints p) : clause p c208 = true := by
  simpa only [c208,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause208
def c209 : List Lit := [(147, false), (285, true)]
theorem step209 (p : Nat → Bool) (h : Constraints p) : clause p c209 = true := by
  simpa only [c209,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause209
def c210 : List Lit := [(149, false), (287, true)]
theorem step210 (p : Nat → Bool) (h : Constraints p) : clause p c210 = true := by
  simpa only [c210,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause210
def c211 : List Lit := [(287, false), (289, true)]
theorem step211 (p : Nat → Bool) (h : Constraints p) : clause p c211 = true := by
  simpa only [c211,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause211
def c212 : List Lit := [(285, false), (289, true)]
theorem step212 (p : Nat → Bool) (h : Constraints p) : clause p c212 = true := by
  simpa only [c212,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause212
def c213 : List Lit := [(289, false), (291, true)]
theorem step213 (p : Nat → Bool) (h : Constraints p) : clause p c213 = true := by
  simpa only [c213,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause213
def c214 : List Lit := [(291, false), (293, true)]
theorem step214 (p : Nat → Bool) (h : Constraints p) : clause p c214 = true := by
  simpa only [c214,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause214
def c215 : List Lit := [(152, false), (295, true)]
theorem step215 (p : Nat → Bool) (h : Constraints p) : clause p c215 = true := by
  simpa only [c215,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause215
def c216 : List Lit := [(295, false), (297, true)]
theorem step216 (p : Nat → Bool) (h : Constraints p) : clause p c216 = true := by
  simpa only [c216,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause216
def c217 : List Lit := [(154, false), (299, true)]
theorem step217 (p : Nat → Bool) (h : Constraints p) : clause p c217 = true := by
  simpa only [c217,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause217
def c218 : List Lit := [(155, false), (301, true)]
theorem step218 (p : Nat → Bool) (h : Constraints p) : clause p c218 = true := by
  simpa only [c218,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause218
def c219 : List Lit := [(301, false), (303, true)]
theorem step219 (p : Nat → Bool) (h : Constraints p) : clause p c219 = true := by
  simpa only [c219,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause219
def c220 : List Lit := [(299, false), (303, true)]
theorem step220 (p : Nat → Bool) (h : Constraints p) : clause p c220 = true := by
  simpa only [c220,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause220
def c221 : List Lit := [(303, false), (305, true)]
theorem step221 (p : Nat → Bool) (h : Constraints p) : clause p c221 = true := by
  simpa only [c221,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause221
def c222 : List Lit := [(297, false), (305, true)]
theorem step222 (p : Nat → Bool) (h : Constraints p) : clause p c222 = true := by
  simpa only [c222,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause222
def c223 : List Lit := [(158, false), (307, true)]
theorem step223 (p : Nat → Bool) (h : Constraints p) : clause p c223 = true := by
  simpa only [c223,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause223
def c224 : List Lit := [(307, false), (309, true)]
theorem step224 (p : Nat → Bool) (h : Constraints p) : clause p c224 = true := by
  simpa only [c224,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause224
def c225 : List Lit := [(160, false), (311, true)]
theorem step225 (p : Nat → Bool) (h : Constraints p) : clause p c225 = true := by
  simpa only [c225,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause225
def c226 : List Lit := [(162, false), (313, true)]
theorem step226 (p : Nat → Bool) (h : Constraints p) : clause p c226 = true := by
  simpa only [c226,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause226
def c227 : List Lit := [(313, false), (315, true)]
theorem step227 (p : Nat → Bool) (h : Constraints p) : clause p c227 = true := by
  simpa only [c227,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause227
def c228 : List Lit := [(311, false), (315, true)]
theorem step228 (p : Nat → Bool) (h : Constraints p) : clause p c228 = true := by
  simpa only [c228,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause228
def c229 : List Lit := [(315, false), (317, true)]
theorem step229 (p : Nat → Bool) (h : Constraints p) : clause p c229 = true := by
  simpa only [c229,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause229
def c230 : List Lit := [(309, false), (317, true)]
theorem step230 (p : Nat → Bool) (h : Constraints p) : clause p c230 = true := by
  simpa only [c230,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause230
def c231 : List Lit := [(317, false), (319, true)]
theorem step231 (p : Nat → Bool) (h : Constraints p) : clause p c231 = true := by
  simpa only [c231,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause231
def c232 : List Lit := [(305, false), (319, true)]
theorem step232 (p : Nat → Bool) (h : Constraints p) : clause p c232 = true := by
  simpa only [c232,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause232
def c233 : List Lit := [(319, false), (321, true)]
theorem step233 (p : Nat → Bool) (h : Constraints p) : clause p c233 = true := by
  simpa only [c233,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause233
def c234 : List Lit := [(293, false), (321, true)]
theorem step234 (p : Nat → Bool) (h : Constraints p) : clause p c234 = true := by
  simpa only [c234,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause234
def c235 : List Lit := [(269, false), (323, true)]
theorem step235 (p : Nat → Bool) (h : Constraints p) : clause p c235 = true := by
  simpa only [c235,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause235
def c236 : List Lit := [(269, false), (321, false), (324, true)]
theorem step236 (p : Nat → Bool) (h : Constraints p) : clause p c236 = true := by
  simpa only [c236,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause236
def c237 : List Lit := [(270, false), (324, true)]
theorem step237 (p : Nat → Bool) (h : Constraints p) : clause p c237 = true := by
  simpa only [c237,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause237
def c238 : List Lit := [(168, false), (329, true)]
theorem step238 (p : Nat → Bool) (h : Constraints p) : clause p c238 = true := by
  simpa only [c238,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause238
def c239 : List Lit := [(329, false), (331, true)]
theorem step239 (p : Nat → Bool) (h : Constraints p) : clause p c239 = true := by
  simpa only [c239,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause239
def c240 : List Lit := [(331, false), (333, true)]
theorem step240 (p : Nat → Bool) (h : Constraints p) : clause p c240 = true := by
  simpa only [c240,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause240
def c241 : List Lit := [(170, false), (337, true)]
theorem step241 (p : Nat → Bool) (h : Constraints p) : clause p c241 = true := by
  simpa only [c241,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause241
def c242 : List Lit := [(173, false), (339, true)]
theorem step242 (p : Nat → Bool) (h : Constraints p) : clause p c242 = true := by
  simpa only [c242,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause242
def c243 : List Lit := [(175, false), (341, true)]
theorem step243 (p : Nat → Bool) (h : Constraints p) : clause p c243 = true := by
  simpa only [c243,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause243
def c244 : List Lit := [(341, false), (343, true)]
theorem step244 (p : Nat → Bool) (h : Constraints p) : clause p c244 = true := by
  simpa only [c244,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause244
def c245 : List Lit := [(339, false), (343, true)]
theorem step245 (p : Nat → Bool) (h : Constraints p) : clause p c245 = true := by
  simpa only [c245,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause245
def c246 : List Lit := [(343, false), (345, true)]
theorem step246 (p : Nat → Bool) (h : Constraints p) : clause p c246 = true := by
  simpa only [c246,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause246
def c247 : List Lit := [(337, false), (345, true)]
theorem step247 (p : Nat → Bool) (h : Constraints p) : clause p c247 = true := by
  simpa only [c247,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause247
def c248 : List Lit := [(345, false), (347, true)]
theorem step248 (p : Nat → Bool) (h : Constraints p) : clause p c248 = true := by
  simpa only [c248,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause248
def c249 : List Lit := [(333, false), (347, true)]
theorem step249 (p : Nat → Bool) (h : Constraints p) : clause p c249 = true := by
  simpa only [c249,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause249
def c250 : List Lit := [(333, false), (345, false), (348, true)]
theorem step250 (p : Nat → Bool) (h : Constraints p) : clause p c250 = true := by
  simpa only [c250,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause250
def c251 : List Lit := [(178, false), (349, true)]
theorem step251 (p : Nat → Bool) (h : Constraints p) : clause p c251 = true := by
  simpa only [c251,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause251
def c252 : List Lit := [(349, false), (351, true)]
theorem step252 (p : Nat → Bool) (h : Constraints p) : clause p c252 = true := by
  simpa only [c252,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause252
def c253 : List Lit := [(181, false), (353, true)]
theorem step253 (p : Nat → Bool) (h : Constraints p) : clause p c253 = true := by
  simpa only [c253,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause253
def c254 : List Lit := [(180, false), (353, true)]
theorem step254 (p : Nat → Bool) (h : Constraints p) : clause p c254 = true := by
  simpa only [c254,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause254
def c255 : List Lit := [(183, false), (355, true)]
theorem step255 (p : Nat → Bool) (h : Constraints p) : clause p c255 = true := by
  simpa only [c255,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause255
def c256 : List Lit := [(355, false), (357, true)]
theorem step256 (p : Nat → Bool) (h : Constraints p) : clause p c256 = true := by
  simpa only [c256,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause256
def c257 : List Lit := [(353, false), (357, true)]
theorem step257 (p : Nat → Bool) (h : Constraints p) : clause p c257 = true := by
  simpa only [c257,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause257
def c258 : List Lit := [(357, false), (359, true)]
theorem step258 (p : Nat → Bool) (h : Constraints p) : clause p c258 = true := by
  simpa only [c258,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause258
def c259 : List Lit := [(351, false), (359, true)]
theorem step259 (p : Nat → Bool) (h : Constraints p) : clause p c259 = true := by
  simpa only [c259,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause259
def c260 : List Lit := [(351, false), (357, false), (360, true)]
theorem step260 (p : Nat → Bool) (h : Constraints p) : clause p c260 = true := by
  simpa only [c260,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause260
def c261 : List Lit := [(188, false), (365, true)]
theorem step261 (p : Nat → Bool) (h : Constraints p) : clause p c261 = true := by
  simpa only [c261,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause261
def c262 : List Lit := [(189, false), (367, true)]
theorem step262 (p : Nat → Bool) (h : Constraints p) : clause p c262 = true := by
  simpa only [c262,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause262
def c263 : List Lit := [(367, false), (369, true)]
theorem step263 (p : Nat → Bool) (h : Constraints p) : clause p c263 = true := by
  simpa only [c263,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause263
def c264 : List Lit := [(365, false), (369, true)]
theorem step264 (p : Nat → Bool) (h : Constraints p) : clause p c264 = true := by
  simpa only [c264,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause264
def c265 : List Lit := [(369, false), (371, true)]
theorem step265 (p : Nat → Bool) (h : Constraints p) : clause p c265 = true := by
  simpa only [c265,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause265
def c266 : List Lit := [(371, false), (373, true)]
theorem step266 (p : Nat → Bool) (h : Constraints p) : clause p c266 = true := by
  simpa only [c266,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause266
def c267 : List Lit := [(359, false), (373, true)]
theorem step267 (p : Nat → Bool) (h : Constraints p) : clause p c267 = true := by
  simpa only [c267,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause267
def c268 : List Lit := [(360, false), (374, true)]
theorem step268 (p : Nat → Bool) (h : Constraints p) : clause p c268 = true := by
  simpa only [c268,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause268
def c269 : List Lit := [(373, false), (375, true)]
theorem step269 (p : Nat → Bool) (h : Constraints p) : clause p c269 = true := by
  simpa only [c269,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause269
def c270 : List Lit := [(374, false), (376, true)]
theorem step270 (p : Nat → Bool) (h : Constraints p) : clause p c270 = true := by
  simpa only [c270,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause270
def c271 : List Lit := [(347, false), (375, true)]
theorem step271 (p : Nat → Bool) (h : Constraints p) : clause p c271 = true := by
  simpa only [c271,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause271
def c272 : List Lit := [(348, false), (376, true)]
theorem step272 (p : Nat → Bool) (h : Constraints p) : clause p c272 = true := by
  simpa only [c272,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause272
def c273 : List Lit := [(191, false), (379, true)]
theorem step273 (p : Nat → Bool) (h : Constraints p) : clause p c273 = true := by
  simpa only [c273,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause273
def c274 : List Lit := [(196, false), (381, true)]
theorem step274 (p : Nat → Bool) (h : Constraints p) : clause p c274 = true := by
  simpa only [c274,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause274
def c275 : List Lit := [(381, false), (383, true)]
theorem step275 (p : Nat → Bool) (h : Constraints p) : clause p c275 = true := by
  simpa only [c275,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause275
def c276 : List Lit := [(194, false), (383, true)]
theorem step276 (p : Nat → Bool) (h : Constraints p) : clause p c276 = true := by
  simpa only [c276,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause276
def c277 : List Lit := [(194, false), (381, false), (384, true)]
theorem step277 (p : Nat → Bool) (h : Constraints p) : clause p c277 = true := by
  simpa only [c277,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause277
def c278 : List Lit := [(383, false), (385, true)]
theorem step278 (p : Nat → Bool) (h : Constraints p) : clause p c278 = true := by
  simpa only [c278,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause278
def c279 : List Lit := [(384, false), (386, true)]
theorem step279 (p : Nat → Bool) (h : Constraints p) : clause p c279 = true := by
  simpa only [c279,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause279
def c280 : List Lit := [(379, false), (385, true)]
theorem step280 (p : Nat → Bool) (h : Constraints p) : clause p c280 = true := by
  simpa only [c280,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause280
def c281 : List Lit := [(379, false), (383, false), (386, true)]
theorem step281 (p : Nat → Bool) (h : Constraints p) : clause p c281 = true := by
  simpa only [c281,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause281
def c282 : List Lit := [(197, false), (389, true)]
theorem step282 (p : Nat → Bool) (h : Constraints p) : clause p c282 = true := by
  simpa only [c282,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause282
def c283 : List Lit := [(200, false), (391, true)]
theorem step283 (p : Nat → Bool) (h : Constraints p) : clause p c283 = true := by
  simpa only [c283,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause283
def c284 : List Lit := [(203, false), (393, true)]
theorem step284 (p : Nat → Bool) (h : Constraints p) : clause p c284 = true := by
  simpa only [c284,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause284
def c285 : List Lit := [(393, false), (395, true)]
theorem step285 (p : Nat → Bool) (h : Constraints p) : clause p c285 = true := by
  simpa only [c285,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause285
def c286 : List Lit := [(391, false), (395, true)]
theorem step286 (p : Nat → Bool) (h : Constraints p) : clause p c286 = true := by
  simpa only [c286,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause286
def c287 : List Lit := [(395, false), (397, true)]
theorem step287 (p : Nat → Bool) (h : Constraints p) : clause p c287 = true := by
  simpa only [c287,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause287
def c288 : List Lit := [(389, false), (397, true)]
theorem step288 (p : Nat → Bool) (h : Constraints p) : clause p c288 = true := by
  simpa only [c288,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause288
def c289 : List Lit := [(397, false), (399, true)]
theorem step289 (p : Nat → Bool) (h : Constraints p) : clause p c289 = true := by
  simpa only [c289,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause289
def c290 : List Lit := [(385, false), (399, true)]
theorem step290 (p : Nat → Bool) (h : Constraints p) : clause p c290 = true := by
  simpa only [c290,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause290
def c291 : List Lit := [(385, false), (397, false), (400, true)]
theorem step291 (p : Nat → Bool) (h : Constraints p) : clause p c291 = true := by
  simpa only [c291,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause291
def c292 : List Lit := [(386, false), (400, true)]
theorem step292 (p : Nat → Bool) (h : Constraints p) : clause p c292 = true := by
  simpa only [c292,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause292
def c293 : List Lit := [(207, false), (401, true)]
theorem step293 (p : Nat → Bool) (h : Constraints p) : clause p c293 = true := by
  simpa only [c293,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause293
def c294 : List Lit := [(206, false), (401, true)]
theorem step294 (p : Nat → Bool) (h : Constraints p) : clause p c294 = true := by
  simpa only [c294,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause294
def c295 : List Lit := [(206, false), (207, false), (402, true)]
theorem step295 (p : Nat → Bool) (h : Constraints p) : clause p c295 = true := by
  simpa only [c295,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause295
def c296 : List Lit := [(401, false), (403, true)]
theorem step296 (p : Nat → Bool) (h : Constraints p) : clause p c296 = true := by
  simpa only [c296,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause296
def c297 : List Lit := [(402, false), (404, true)]
theorem step297 (p : Nat → Bool) (h : Constraints p) : clause p c297 = true := by
  simpa only [c297,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause297
def c298 : List Lit := [(208, false), (405, true)]
theorem step298 (p : Nat → Bool) (h : Constraints p) : clause p c298 = true := by
  simpa only [c298,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause298
def c299 : List Lit := [(405, false), (409, true)]
theorem step299 (p : Nat → Bool) (h : Constraints p) : clause p c299 = true := by
  simpa only [c299,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause299
def c300 : List Lit := [(409, false), (411, true)]
theorem step300 (p : Nat → Bool) (h : Constraints p) : clause p c300 = true := by
  simpa only [c300,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause300
def c301 : List Lit := [(403, false), (411, true)]
theorem step301 (p : Nat → Bool) (h : Constraints p) : clause p c301 = true := by
  simpa only [c301,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause301
def c302 : List Lit := [(403, false), (409, false), (412, true)]
theorem step302 (p : Nat → Bool) (h : Constraints p) : clause p c302 = true := by
  simpa only [c302,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause302
def c303 : List Lit := [(404, false), (412, true)]
theorem step303 (p : Nat → Bool) (h : Constraints p) : clause p c303 = true := by
  simpa only [c303,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause303
def c304 : List Lit := [(214, false), (413, true)]
theorem step304 (p : Nat → Bool) (h : Constraints p) : clause p c304 = true := by
  simpa only [c304,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause304
def c305 : List Lit := [(213, false), (413, true)]
theorem step305 (p : Nat → Bool) (h : Constraints p) : clause p c305 = true := by
  simpa only [c305,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause305
def c306 : List Lit := [(213, false), (214, false), (414, true)]
theorem step306 (p : Nat → Bool) (h : Constraints p) : clause p c306 = true := by
  simpa only [c306,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause306
def c307 : List Lit := [(413, false), (415, true)]
theorem step307 (p : Nat → Bool) (h : Constraints p) : clause p c307 = true := by
  simpa only [c307,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause307
def c308 : List Lit := [(414, false), (416, true)]
theorem step308 (p : Nat → Bool) (h : Constraints p) : clause p c308 = true := by
  simpa only [c308,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause308
def c309 : List Lit := [(216, false), (417, true)]
theorem step309 (p : Nat → Bool) (h : Constraints p) : clause p c309 = true := by
  simpa only [c309,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause309
def c310 : List Lit := [(215, false), (417, true)]
theorem step310 (p : Nat → Bool) (h : Constraints p) : clause p c310 = true := by
  simpa only [c310,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause310
def c311 : List Lit := [(215, false), (216, false), (418, true)]
theorem step311 (p : Nat → Bool) (h : Constraints p) : clause p c311 = true := by
  simpa only [c311,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause311
def c312 : List Lit := [(417, false), (421, true)]
theorem step312 (p : Nat → Bool) (h : Constraints p) : clause p c312 = true := by
  simpa only [c312,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause312
def c313 : List Lit := [(418, false), (422, true)]
theorem step313 (p : Nat → Bool) (h : Constraints p) : clause p c313 = true := by
  simpa only [c313,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause313
def c314 : List Lit := [(421, false), (423, true)]
theorem step314 (p : Nat → Bool) (h : Constraints p) : clause p c314 = true := by
  simpa only [c314,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause314
def c315 : List Lit := [(422, false), (424, true)]
theorem step315 (p : Nat → Bool) (h : Constraints p) : clause p c315 = true := by
  simpa only [c315,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause315
def c316 : List Lit := [(415, false), (423, true)]
theorem step316 (p : Nat → Bool) (h : Constraints p) : clause p c316 = true := by
  simpa only [c316,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause316
def c317 : List Lit := [(415, false), (421, false), (424, true)]
theorem step317 (p : Nat → Bool) (h : Constraints p) : clause p c317 = true := by
  simpa only [c317,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause317
def c318 : List Lit := [(416, false), (424, true)]
theorem step318 (p : Nat → Bool) (h : Constraints p) : clause p c318 = true := by
  simpa only [c318,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause318
def c319 : List Lit := [(423, false), (425, true)]
theorem step319 (p : Nat → Bool) (h : Constraints p) : clause p c319 = true := by
  simpa only [c319,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause319
def c320 : List Lit := [(424, false), (426, true)]
theorem step320 (p : Nat → Bool) (h : Constraints p) : clause p c320 = true := by
  simpa only [c320,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause320
def c321 : List Lit := [(411, false), (425, true)]
theorem step321 (p : Nat → Bool) (h : Constraints p) : clause p c321 = true := by
  simpa only [c321,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause321
def c322 : List Lit := [(411, false), (423, false), (426, true)]
theorem step322 (p : Nat → Bool) (h : Constraints p) : clause p c322 = true := by
  simpa only [c322,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause322
def c323 : List Lit := [(412, false), (426, true)]
theorem step323 (p : Nat → Bool) (h : Constraints p) : clause p c323 = true := by
  simpa only [c323,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause323
def c324 : List Lit := [(425, false), (427, true)]
theorem step324 (p : Nat → Bool) (h : Constraints p) : clause p c324 = true := by
  simpa only [c324,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause324
def c325 : List Lit := [(426, false), (428, true)]
theorem step325 (p : Nat → Bool) (h : Constraints p) : clause p c325 = true := by
  simpa only [c325,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause325
def c326 : List Lit := [(399, false), (427, true)]
theorem step326 (p : Nat → Bool) (h : Constraints p) : clause p c326 = true := by
  simpa only [c326,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause326
def c327 : List Lit := [(399, false), (425, false), (428, true)]
theorem step327 (p : Nat → Bool) (h : Constraints p) : clause p c327 = true := by
  simpa only [c327,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause327
def c328 : List Lit := [(400, false), (428, true)]
theorem step328 (p : Nat → Bool) (h : Constraints p) : clause p c328 = true := by
  simpa only [c328,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause328
def c329 : List Lit := [(427, false), (429, true)]
theorem step329 (p : Nat → Bool) (h : Constraints p) : clause p c329 = true := by
  simpa only [c329,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause329
def c330 : List Lit := [(428, false), (430, true)]
theorem step330 (p : Nat → Bool) (h : Constraints p) : clause p c330 = true := by
  simpa only [c330,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause330
def c331 : List Lit := [(375, false), (429, true)]
theorem step331 (p : Nat → Bool) (h : Constraints p) : clause p c331 = true := by
  simpa only [c331,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause331
def c332 : List Lit := [(375, false), (427, false), (430, true)]
theorem step332 (p : Nat → Bool) (h : Constraints p) : clause p c332 = true := by
  simpa only [c332,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause332
def c333 : List Lit := [(376, false), (430, true)]
theorem step333 (p : Nat → Bool) (h : Constraints p) : clause p c333 = true := by
  simpa only [c333,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause333
def c334 : List Lit := [(430, false), (432, true)]
theorem step334 (p : Nat → Bool) (h : Constraints p) : clause p c334 = true := by
  simpa only [c334,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause334
def c335 : List Lit := [(323, false), (429, false), (432, true)]
theorem step335 (p : Nat → Bool) (h : Constraints p) : clause p c335 = true := by
  simpa only [c335,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause335
def c336 : List Lit := [(324, false), (432, true)]
theorem step336 (p : Nat → Bool) (h : Constraints p) : clause p c336 = true := by
  simpa only [c336,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause336
def c337 : List Lit := [(432, false)]
theorem step337 (p : Nat → Bool) (h : Constraints p) : clause p c337 = true := by
  simpa only [c337,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause337
def c338 : List Lit := [(3, true), (1315, true)]
theorem step338 (p : Nat → Bool) (h : Constraints p) : clause p c338 = true := by
  simpa only [c338,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause338
def c339 : List Lit := [(3, true), (4, true), (1316, true)]
theorem step339 (p : Nat → Bool) (h : Constraints p) : clause p c339 = true := by
  simpa only [c339,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause339
def c340 : List Lit := [(1315, false), (1317, true)]
theorem step340 (p : Nat → Bool) (h : Constraints p) : clause p c340 = true := by
  simpa only [c340,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause340
def c341 : List Lit := [(1316, false), (1318, true)]
theorem step341 (p : Nat → Bool) (h : Constraints p) : clause p c341 = true := by
  simpa only [c341,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause341
def c342 : List Lit := [(2, true), (1317, true)]
theorem step342 (p : Nat → Bool) (h : Constraints p) : clause p c342 = true := by
  simpa only [c342,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause342
def c343 : List Lit := [(2, true), (1315, false), (1318, true)]
theorem step343 (p : Nat → Bool) (h : Constraints p) : clause p c343 = true := by
  simpa only [c343,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause343
def c344 : List Lit := [(2, true), (1316, false), (1319, true)]
theorem step344 (p : Nat → Bool) (h : Constraints p) : clause p c344 = true := by
  simpa only [c344,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause344
def c345 : List Lit := [(9, true), (10, true), (1321, true)]
theorem step345 (p : Nat → Bool) (h : Constraints p) : clause p c345 = true := by
  simpa only [c345,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause345
def c346 : List Lit := [(8, true), (1322, true)]
theorem step346 (p : Nat → Bool) (h : Constraints p) : clause p c346 = true := by
  simpa only [c346,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause346
def c347 : List Lit := [(8, true), (1321, false), (1324, true)]
theorem step347 (p : Nat → Bool) (h : Constraints p) : clause p c347 = true := by
  simpa only [c347,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause347
def c348 : List Lit := [(1317, false), (1325, true)]
theorem step348 (p : Nat → Bool) (h : Constraints p) : clause p c348 = true := by
  simpa only [c348,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause348
def c349 : List Lit := [(1317, false), (1322, false), (1326, true)]
theorem step349 (p : Nat → Bool) (h : Constraints p) : clause p c349 = true := by
  simpa only [c349,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause349
def c350 : List Lit := [(1317, false), (1324, false), (1328, true)]
theorem step350 (p : Nat → Bool) (h : Constraints p) : clause p c350 = true := by
  simpa only [c350,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause350
def c351 : List Lit := [(1318, false), (1326, true)]
theorem step351 (p : Nat → Bool) (h : Constraints p) : clause p c351 = true := by
  simpa only [c351,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause351
def c352 : List Lit := [(1319, false), (1324, false), (1330, true)]
theorem step352 (p : Nat → Bool) (h : Constraints p) : clause p c352 = true := by
  simpa only [c352,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause352
def c353 : List Lit := [(19, true), (1331, true)]
theorem step353 (p : Nat → Bool) (h : Constraints p) : clause p c353 = true := by
  simpa only [c353,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause353
def c354 : List Lit := [(15, true), (1331, true)]
theorem step354 (p : Nat → Bool) (h : Constraints p) : clause p c354 = true := by
  simpa only [c354,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause354
def c355 : List Lit := [(1331, false), (1333, true)]
theorem step355 (p : Nat → Bool) (h : Constraints p) : clause p c355 = true := by
  simpa only [c355,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause355
def c356 : List Lit := [(14, true), (1333, true)]
theorem step356 (p : Nat → Bool) (h : Constraints p) : clause p c356 = true := by
  simpa only [c356,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause356
def c357 : List Lit := [(14, true), (1331, false), (1334, true)]
theorem step357 (p : Nat → Bool) (h : Constraints p) : clause p c357 = true := by
  simpa only [c357,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause357
def c358 : List Lit := [(22, true), (1336, true)]
theorem step358 (p : Nat → Bool) (h : Constraints p) : clause p c358 = true := by
  simpa only [c358,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause358
def c359 : List Lit := [(20, true), (22, true), (1337, true)]
theorem step359 (p : Nat → Bool) (h : Constraints p) : clause p c359 = true := by
  simpa only [c359,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause359
def c360 : List Lit := [(26, true), (1338, true)]
theorem step360 (p : Nat → Bool) (h : Constraints p) : clause p c360 = true := by
  simpa only [c360,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause360
def c361 : List Lit := [(25, true), (1338, true)]
theorem step361 (p : Nat → Bool) (h : Constraints p) : clause p c361 = true := by
  simpa only [c361,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause361
def c362 : List Lit := [(1338, false), (1340, true)]
theorem step362 (p : Nat → Bool) (h : Constraints p) : clause p c362 = true := by
  simpa only [c362,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause362
def c363 : List Lit := [(1336, false), (1340, true)]
theorem step363 (p : Nat → Bool) (h : Constraints p) : clause p c363 = true := by
  simpa only [c363,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause363
def c364 : List Lit := [(1337, false), (1341, true)]
theorem step364 (p : Nat → Bool) (h : Constraints p) : clause p c364 = true := by
  simpa only [c364,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause364
def c365 : List Lit := [(1340, false), (1344, true)]
theorem step365 (p : Nat → Bool) (h : Constraints p) : clause p c365 = true := by
  simpa only [c365,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause365
def c366 : List Lit := [(1341, false), (1345, true)]
theorem step366 (p : Nat → Bool) (h : Constraints p) : clause p c366 = true := by
  simpa only [c366,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause366
def c367 : List Lit := [(1333, false), (1344, true)]
theorem step367 (p : Nat → Bool) (h : Constraints p) : clause p c367 = true := by
  simpa only [c367,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause367
def c368 : List Lit := [(1333, false), (1340, false), (1345, true)]
theorem step368 (p : Nat → Bool) (h : Constraints p) : clause p c368 = true := by
  simpa only [c368,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause368
def c369 : List Lit := [(1334, false), (1345, true)]
theorem step369 (p : Nat → Bool) (h : Constraints p) : clause p c369 = true := by
  simpa only [c369,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause369
def c370 : List Lit := [(1344, false), (1351, true)]
theorem step370 (p : Nat → Bool) (h : Constraints p) : clause p c370 = true := by
  simpa only [c370,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause370
def c371 : List Lit := [(1345, false), (1352, true)]
theorem step371 (p : Nat → Bool) (h : Constraints p) : clause p c371 = true := by
  simpa only [c371,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause371
def c372 : List Lit := [(1325, false), (1344, false), (1352, true)]
theorem step372 (p : Nat → Bool) (h : Constraints p) : clause p c372 = true := by
  simpa only [c372,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause372
def c373 : List Lit := [(1326, false), (1344, false), (1353, true)]
theorem step373 (p : Nat → Bool) (h : Constraints p) : clause p c373 = true := by
  simpa only [c373,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause373
def c374 : List Lit := [(1326, false), (1345, false), (1354, true)]
theorem step374 (p : Nat → Bool) (h : Constraints p) : clause p c374 = true := by
  simpa only [c374,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause374
def c375 : List Lit := [(1328, false), (1354, true)]
theorem step375 (p : Nat → Bool) (h : Constraints p) : clause p c375 = true := by
  simpa only [c375,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause375
def c376 : List Lit := [(1328, false), (1344, false), (1355, true)]
theorem step376 (p : Nat → Bool) (h : Constraints p) : clause p c376 = true := by
  simpa only [c376,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause376
def c377 : List Lit := [(1330, false), (1344, false), (1357, true)]
theorem step377 (p : Nat → Bool) (h : Constraints p) : clause p c377 = true := by
  simpa only [c377,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause377
def c378 : List Lit := [(34, true), (1363, true)]
theorem step378 (p : Nat → Bool) (h : Constraints p) : clause p c378 = true := by
  simpa only [c378,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause378
def c379 : List Lit := [(31, true), (1363, true)]
theorem step379 (p : Nat → Bool) (h : Constraints p) : clause p c379 = true := by
  simpa only [c379,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause379
def c380 : List Lit := [(31, true), (34, true), (1364, true)]
theorem step380 (p : Nat → Bool) (h : Constraints p) : clause p c380 = true := by
  simpa only [c380,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause380
def c381 : List Lit := [(1363, false), (1365, true)]
theorem step381 (p : Nat → Bool) (h : Constraints p) : clause p c381 = true := by
  simpa only [c381,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause381
def c382 : List Lit := [(1364, false), (1366, true)]
theorem step382 (p : Nat → Bool) (h : Constraints p) : clause p c382 = true := by
  simpa only [c382,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause382
def c383 : List Lit := [(40, true), (1368, true)]
theorem step383 (p : Nat → Bool) (h : Constraints p) : clause p c383 = true := by
  simpa only [c383,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause383
def c384 : List Lit := [(38, true), (1368, true)]
theorem step384 (p : Nat → Bool) (h : Constraints p) : clause p c384 = true := by
  simpa only [c384,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause384
def c385 : List Lit := [(38, true), (40, true), (1369, true)]
theorem step385 (p : Nat → Bool) (h : Constraints p) : clause p c385 = true := by
  simpa only [c385,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause385
def c386 : List Lit := [(1368, false), (1370, true)]
theorem step386 (p : Nat → Bool) (h : Constraints p) : clause p c386 = true := by
  simpa only [c386,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause386
def c387 : List Lit := [(1369, false), (1371, true)]
theorem step387 (p : Nat → Bool) (h : Constraints p) : clause p c387 = true := by
  simpa only [c387,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause387
def c388 : List Lit := [(35, true), (1370, true)]
theorem step388 (p : Nat → Bool) (h : Constraints p) : clause p c388 = true := by
  simpa only [c388,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause388
def c389 : List Lit := [(35, true), (1368, false), (1371, true)]
theorem step389 (p : Nat → Bool) (h : Constraints p) : clause p c389 = true := by
  simpa only [c389,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause389
def c390 : List Lit := [(1370, false), (1373, true)]
theorem step390 (p : Nat → Bool) (h : Constraints p) : clause p c390 = true := by
  simpa only [c390,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause390
def c391 : List Lit := [(1371, false), (1374, true)]
theorem step391 (p : Nat → Bool) (h : Constraints p) : clause p c391 = true := by
  simpa only [c391,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause391
def c392 : List Lit := [(1365, false), (1373, true)]
theorem step392 (p : Nat → Bool) (h : Constraints p) : clause p c392 = true := by
  simpa only [c392,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause392
def c393 : List Lit := [(1365, false), (1370, false), (1374, true)]
theorem step393 (p : Nat → Bool) (h : Constraints p) : clause p c393 = true := by
  simpa only [c393,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause393
def c394 : List Lit := [(1366, false), (1374, true)]
theorem step394 (p : Nat → Bool) (h : Constraints p) : clause p c394 = true := by
  simpa only [c394,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause394
def c395 : List Lit := [(46, true), (1379, true)]
theorem step395 (p : Nat → Bool) (h : Constraints p) : clause p c395 = true := by
  simpa only [c395,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause395
def c396 : List Lit := [(45, true), (46, true), (1380, true)]
theorem step396 (p : Nat → Bool) (h : Constraints p) : clause p c396 = true := by
  simpa only [c396,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause396
def c397 : List Lit := [(1379, false), (1381, true)]
theorem step397 (p : Nat → Bool) (h : Constraints p) : clause p c397 = true := by
  simpa only [c397,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause397
def c398 : List Lit := [(1380, false), (1382, true)]
theorem step398 (p : Nat → Bool) (h : Constraints p) : clause p c398 = true := by
  simpa only [c398,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause398
def c399 : List Lit := [(43, true), (1380, false), (1383, true)]
theorem step399 (p : Nat → Bool) (h : Constraints p) : clause p c399 = true := by
  simpa only [c399,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause399
def c400 : List Lit := [(51, true), (1384, true)]
theorem step400 (p : Nat → Bool) (h : Constraints p) : clause p c400 = true := by
  simpa only [c400,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause400
def c401 : List Lit := [(49, true), (1384, true)]
theorem step401 (p : Nat → Bool) (h : Constraints p) : clause p c401 = true := by
  simpa only [c401,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause401
def c402 : List Lit := [(49, true), (51, true), (1385, true)]
theorem step402 (p : Nat → Bool) (h : Constraints p) : clause p c402 = true := by
  simpa only [c402,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause402
def c403 : List Lit := [(53, true), (1386, true)]
theorem step403 (p : Nat → Bool) (h : Constraints p) : clause p c403 = true := by
  simpa only [c403,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause403
def c404 : List Lit := [(53, true), (57, true), (1387, true)]
theorem step404 (p : Nat → Bool) (h : Constraints p) : clause p c404 = true := by
  simpa only [c404,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause404
def c405 : List Lit := [(1386, false), (1388, true)]
theorem step405 (p : Nat → Bool) (h : Constraints p) : clause p c405 = true := by
  simpa only [c405,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause405
def c406 : List Lit := [(1384, false), (1388, true)]
theorem step406 (p : Nat → Bool) (h : Constraints p) : clause p c406 = true := by
  simpa only [c406,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause406
def c407 : List Lit := [(1384, false), (1386, false), (1389, true)]
theorem step407 (p : Nat → Bool) (h : Constraints p) : clause p c407 = true := by
  simpa only [c407,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause407
def c408 : List Lit := [(1385, false), (1389, true)]
theorem step408 (p : Nat → Bool) (h : Constraints p) : clause p c408 = true := by
  simpa only [c408,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause408
def c409 : List Lit := [(1385, false), (1386, false), (1390, true)]
theorem step409 (p : Nat → Bool) (h : Constraints p) : clause p c409 = true := by
  simpa only [c409,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause409
def c410 : List Lit := [(1385, false), (1387, false), (1391, true)]
theorem step410 (p : Nat → Bool) (h : Constraints p) : clause p c410 = true := by
  simpa only [c410,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause410
def c411 : List Lit := [(1388, false), (1392, true)]
theorem step411 (p : Nat → Bool) (h : Constraints p) : clause p c411 = true := by
  simpa only [c411,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause411
def c412 : List Lit := [(1381, false), (1392, true)]
theorem step412 (p : Nat → Bool) (h : Constraints p) : clause p c412 = true := by
  simpa only [c412,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause412
def c413 : List Lit := [(1381, false), (1388, false), (1393, true)]
theorem step413 (p : Nat → Bool) (h : Constraints p) : clause p c413 = true := by
  simpa only [c413,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause413
def c414 : List Lit := [(1381, false), (1389, false), (1394, true)]
theorem step414 (p : Nat → Bool) (h : Constraints p) : clause p c414 = true := by
  simpa only [c414,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause414
def c415 : List Lit := [(1381, false), (1391, false), (1396, true)]
theorem step415 (p : Nat → Bool) (h : Constraints p) : clause p c415 = true := by
  simpa only [c415,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause415
def c416 : List Lit := [(1382, false), (1393, true)]
theorem step416 (p : Nat → Bool) (h : Constraints p) : clause p c416 = true := by
  simpa only [c416,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause416
def c417 : List Lit := [(1382, false), (1389, false), (1395, true)]
theorem step417 (p : Nat → Bool) (h : Constraints p) : clause p c417 = true := by
  simpa only [c417,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause417
def c418 : List Lit := [(1382, false), (1390, false), (1396, true)]
theorem step418 (p : Nat → Bool) (h : Constraints p) : clause p c418 = true := by
  simpa only [c418,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause418
def c419 : List Lit := [(1383, false), (1394, true)]
theorem step419 (p : Nat → Bool) (h : Constraints p) : clause p c419 = true := by
  simpa only [c419,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause419
def c420 : List Lit := [(1373, false), (1392, false), (1400, true)]
theorem step420 (p : Nat → Bool) (h : Constraints p) : clause p c420 = true := by
  simpa only [c420,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause420
def c421 : List Lit := [(1373, false), (1393, false), (1401, true)]
theorem step421 (p : Nat → Bool) (h : Constraints p) : clause p c421 = true := by
  simpa only [c421,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause421
def c422 : List Lit := [(1373, false), (1394, false), (1402, true)]
theorem step422 (p : Nat → Bool) (h : Constraints p) : clause p c422 = true := by
  simpa only [c422,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause422
def c423 : List Lit := [(1373, false), (1395, false), (1403, true)]
theorem step423 (p : Nat → Bool) (h : Constraints p) : clause p c423 = true := by
  simpa only [c423,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause423
def c424 : List Lit := [(1373, false), (1396, false), (1404, true)]
theorem step424 (p : Nat → Bool) (h : Constraints p) : clause p c424 = true := by
  simpa only [c424,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause424
def c425 : List Lit := [(1374, false), (1392, false), (1401, true)]
theorem step425 (p : Nat → Bool) (h : Constraints p) : clause p c425 = true := by
  simpa only [c425,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause425
def c426 : List Lit := [(1374, false), (1393, false), (1402, true)]
theorem step426 (p : Nat → Bool) (h : Constraints p) : clause p c426 = true := by
  simpa only [c426,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause426
def c427 : List Lit := [(1351, false), (1401, false), (1414, true)]
theorem step427 (p : Nat → Bool) (h : Constraints p) : clause p c427 = true := by
  simpa only [c427,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause427
def c428 : List Lit := [(1351, false), (1402, false), (1415, true)]
theorem step428 (p : Nat → Bool) (h : Constraints p) : clause p c428 = true := by
  simpa only [c428,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause428
def c429 : List Lit := [(1351, false), (1403, false), (1416, true)]
theorem step429 (p : Nat → Bool) (h : Constraints p) : clause p c429 = true := by
  simpa only [c429,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause429
def c430 : List Lit := [(1351, false), (1404, false), (1417, true)]
theorem step430 (p : Nat → Bool) (h : Constraints p) : clause p c430 = true := by
  simpa only [c430,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause430
def c431 : List Lit := [(1352, false), (1400, false), (1414, true)]
theorem step431 (p : Nat → Bool) (h : Constraints p) : clause p c431 = true := by
  simpa only [c431,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause431
def c432 : List Lit := [(1352, false), (1402, false), (1416, true)]
theorem step432 (p : Nat → Bool) (h : Constraints p) : clause p c432 = true := by
  simpa only [c432,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause432
def c433 : List Lit := [(1353, false), (1400, false), (1415, true)]
theorem step433 (p : Nat → Bool) (h : Constraints p) : clause p c433 = true := by
  simpa only [c433,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause433
def c434 : List Lit := [(1353, false), (1401, false), (1416, true)]
theorem step434 (p : Nat → Bool) (h : Constraints p) : clause p c434 = true := by
  simpa only [c434,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause434
def c435 : List Lit := [(1354, false), (1400, false), (1416, true)]
theorem step435 (p : Nat → Bool) (h : Constraints p) : clause p c435 = true := by
  simpa only [c435,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause435
def c436 : List Lit := [(1355, false), (1400, false), (1417, true)]
theorem step436 (p : Nat → Bool) (h : Constraints p) : clause p c436 = true := by
  simpa only [c436,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause436
def c437 : List Lit := [(1357, false), (1400, false), (1419, true)]
theorem step437 (p : Nat → Bool) (h : Constraints p) : clause p c437 = true := by
  simpa only [c437,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause437
def c438 : List Lit := [(63, true), (1423, true)]
theorem step438 (p : Nat → Bool) (h : Constraints p) : clause p c438 = true := by
  simpa only [c438,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause438
def c439 : List Lit := [(61, true), (1423, true)]
theorem step439 (p : Nat → Bool) (h : Constraints p) : clause p c439 = true := by
  simpa only [c439,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause439
def c440 : List Lit := [(61, true), (63, true), (1424, true)]
theorem step440 (p : Nat → Bool) (h : Constraints p) : clause p c440 = true := by
  simpa only [c440,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause440
def c441 : List Lit := [(1423, false), (1425, true)]
theorem step441 (p : Nat → Bool) (h : Constraints p) : clause p c441 = true := by
  simpa only [c441,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause441
def c442 : List Lit := [(1424, false), (1426, true)]
theorem step442 (p : Nat → Bool) (h : Constraints p) : clause p c442 = true := by
  simpa only [c442,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause442
def c443 : List Lit := [(59, true), (1425, true)]
theorem step443 (p : Nat → Bool) (h : Constraints p) : clause p c443 = true := by
  simpa only [c443,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause443
def c444 : List Lit := [(59, true), (1423, false), (1426, true)]
theorem step444 (p : Nat → Bool) (h : Constraints p) : clause p c444 = true := by
  simpa only [c444,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause444
def c445 : List Lit := [(69, true), (1428, true)]
theorem step445 (p : Nat → Bool) (h : Constraints p) : clause p c445 = true := by
  simpa only [c445,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause445
def c446 : List Lit := [(66, true), (1428, true)]
theorem step446 (p : Nat → Bool) (h : Constraints p) : clause p c446 = true := by
  simpa only [c446,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause446
def c447 : List Lit := [(1428, false), (1430, true)]
theorem step447 (p : Nat → Bool) (h : Constraints p) : clause p c447 = true := by
  simpa only [c447,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause447
def c448 : List Lit := [(64, true), (1430, true)]
theorem step448 (p : Nat → Bool) (h : Constraints p) : clause p c448 = true := by
  simpa only [c448,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause448
def c449 : List Lit := [(64, true), (1428, false), (1431, true)]
theorem step449 (p : Nat → Bool) (h : Constraints p) : clause p c449 = true := by
  simpa only [c449,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause449
def c450 : List Lit := [(1430, false), (1433, true)]
theorem step450 (p : Nat → Bool) (h : Constraints p) : clause p c450 = true := by
  simpa only [c450,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause450
def c451 : List Lit := [(1431, false), (1434, true)]
theorem step451 (p : Nat → Bool) (h : Constraints p) : clause p c451 = true := by
  simpa only [c451,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause451
def c452 : List Lit := [(1425, false), (1433, true)]
theorem step452 (p : Nat → Bool) (h : Constraints p) : clause p c452 = true := by
  simpa only [c452,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause452
def c453 : List Lit := [(1425, false), (1430, false), (1434, true)]
theorem step453 (p : Nat → Bool) (h : Constraints p) : clause p c453 = true := by
  simpa only [c453,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause453
def c454 : List Lit := [(1425, false), (1431, false), (1435, true)]
theorem step454 (p : Nat → Bool) (h : Constraints p) : clause p c454 = true := by
  simpa only [c454,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause454
def c455 : List Lit := [(1426, false), (1434, true)]
theorem step455 (p : Nat → Bool) (h : Constraints p) : clause p c455 = true := by
  simpa only [c455,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause455
def c456 : List Lit := [(1426, false), (1430, false), (1435, true)]
theorem step456 (p : Nat → Bool) (h : Constraints p) : clause p c456 = true := by
  simpa only [c456,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause456
def c457 : List Lit := [(74, true), (1439, true)]
theorem step457 (p : Nat → Bool) (h : Constraints p) : clause p c457 = true := by
  simpa only [c457,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause457
def c458 : List Lit := [(72, true), (1439, true)]
theorem step458 (p : Nat → Bool) (h : Constraints p) : clause p c458 = true := by
  simpa only [c458,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause458
def c459 : List Lit := [(72, true), (74, true), (1440, true)]
theorem step459 (p : Nat → Bool) (h : Constraints p) : clause p c459 = true := by
  simpa only [c459,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause459
def c460 : List Lit := [(1439, false), (1441, true)]
theorem step460 (p : Nat → Bool) (h : Constraints p) : clause p c460 = true := by
  simpa only [c460,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause460
def c461 : List Lit := [(1440, false), (1442, true)]
theorem step461 (p : Nat → Bool) (h : Constraints p) : clause p c461 = true := by
  simpa only [c461,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause461
def c462 : List Lit := [(71, true), (1441, true)]
theorem step462 (p : Nat → Bool) (h : Constraints p) : clause p c462 = true := by
  simpa only [c462,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause462
def c463 : List Lit := [(71, true), (1439, false), (1442, true)]
theorem step463 (p : Nat → Bool) (h : Constraints p) : clause p c463 = true := by
  simpa only [c463,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause463
def c464 : List Lit := [(71, true), (1440, false), (1443, true)]
theorem step464 (p : Nat → Bool) (h : Constraints p) : clause p c464 = true := by
  simpa only [c464,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause464
def c465 : List Lit := [(79, true), (1444, true)]
theorem step465 (p : Nat → Bool) (h : Constraints p) : clause p c465 = true := by
  simpa only [c465,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause465
def c466 : List Lit := [(77, true), (1444, true)]
theorem step466 (p : Nat → Bool) (h : Constraints p) : clause p c466 = true := by
  simpa only [c466,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause466
def c467 : List Lit := [(77, true), (79, true), (1445, true)]
theorem step467 (p : Nat → Bool) (h : Constraints p) : clause p c467 = true := by
  simpa only [c467,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause467
def c468 : List Lit := [(82, true), (1446, true)]
theorem step468 (p : Nat → Bool) (h : Constraints p) : clause p c468 = true := by
  simpa only [c468,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause468
def c469 : List Lit := [(80, true), (1446, true)]
theorem step469 (p : Nat → Bool) (h : Constraints p) : clause p c469 = true := by
  simpa only [c469,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause469
def c470 : List Lit := [(80, true), (82, true), (1447, true)]
theorem step470 (p : Nat → Bool) (h : Constraints p) : clause p c470 = true := by
  simpa only [c470,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause470
def c471 : List Lit := [(1446, false), (1448, true)]
theorem step471 (p : Nat → Bool) (h : Constraints p) : clause p c471 = true := by
  simpa only [c471,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause471
def c472 : List Lit := [(1447, false), (1449, true)]
theorem step472 (p : Nat → Bool) (h : Constraints p) : clause p c472 = true := by
  simpa only [c472,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause472
def c473 : List Lit := [(1444, false), (1448, true)]
theorem step473 (p : Nat → Bool) (h : Constraints p) : clause p c473 = true := by
  simpa only [c473,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause473
def c474 : List Lit := [(1444, false), (1446, false), (1449, true)]
theorem step474 (p : Nat → Bool) (h : Constraints p) : clause p c474 = true := by
  simpa only [c474,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause474
def c475 : List Lit := [(1445, false), (1449, true)]
theorem step475 (p : Nat → Bool) (h : Constraints p) : clause p c475 = true := by
  simpa only [c475,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause475
def c476 : List Lit := [(1445, false), (1446, false), (1450, true)]
theorem step476 (p : Nat → Bool) (h : Constraints p) : clause p c476 = true := by
  simpa only [c476,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause476
def c477 : List Lit := [(1448, false), (1452, true)]
theorem step477 (p : Nat → Bool) (h : Constraints p) : clause p c477 = true := by
  simpa only [c477,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause477
def c478 : List Lit := [(1449, false), (1453, true)]
theorem step478 (p : Nat → Bool) (h : Constraints p) : clause p c478 = true := by
  simpa only [c478,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause478
def c479 : List Lit := [(1441, false), (1452, true)]
theorem step479 (p : Nat → Bool) (h : Constraints p) : clause p c479 = true := by
  simpa only [c479,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause479
def c480 : List Lit := [(1441, false), (1448, false), (1453, true)]
theorem step480 (p : Nat → Bool) (h : Constraints p) : clause p c480 = true := by
  simpa only [c480,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause480
def c481 : List Lit := [(1441, false), (1449, false), (1454, true)]
theorem step481 (p : Nat → Bool) (h : Constraints p) : clause p c481 = true := by
  simpa only [c481,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause481
def c482 : List Lit := [(1441, false), (1450, false), (1455, true)]
theorem step482 (p : Nat → Bool) (h : Constraints p) : clause p c482 = true := by
  simpa only [c482,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause482
def c483 : List Lit := [(1442, false), (1453, true)]
theorem step483 (p : Nat → Bool) (h : Constraints p) : clause p c483 = true := by
  simpa only [c483,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause483
def c484 : List Lit := [(1442, false), (1448, false), (1454, true)]
theorem step484 (p : Nat → Bool) (h : Constraints p) : clause p c484 = true := by
  simpa only [c484,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause484
def c485 : List Lit := [(1442, false), (1449, false), (1455, true)]
theorem step485 (p : Nat → Bool) (h : Constraints p) : clause p c485 = true := by
  simpa only [c485,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause485
def c486 : List Lit := [(1443, false), (1454, true)]
theorem step486 (p : Nat → Bool) (h : Constraints p) : clause p c486 = true := by
  simpa only [c486,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause486
def c487 : List Lit := [(1443, false), (1448, false), (1455, true)]
theorem step487 (p : Nat → Bool) (h : Constraints p) : clause p c487 = true := by
  simpa only [c487,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause487
def c488 : List Lit := [(1453, false), (1460, true)]
theorem step488 (p : Nat → Bool) (h : Constraints p) : clause p c488 = true := by
  simpa only [c488,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause488
def c489 : List Lit := [(1433, false), (1452, false), (1460, true)]
theorem step489 (p : Nat → Bool) (h : Constraints p) : clause p c489 = true := by
  simpa only [c489,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause489
def c490 : List Lit := [(1433, false), (1453, false), (1461, true)]
theorem step490 (p : Nat → Bool) (h : Constraints p) : clause p c490 = true := by
  simpa only [c490,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause490
def c491 : List Lit := [(1433, false), (1454, false), (1462, true)]
theorem step491 (p : Nat → Bool) (h : Constraints p) : clause p c491 = true := by
  simpa only [c491,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause491
def c492 : List Lit := [(1433, false), (1455, false), (1463, true)]
theorem step492 (p : Nat → Bool) (h : Constraints p) : clause p c492 = true := by
  simpa only [c492,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause492
def c493 : List Lit := [(1434, false), (1460, true)]
theorem step493 (p : Nat → Bool) (h : Constraints p) : clause p c493 = true := by
  simpa only [c493,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause493
def c494 : List Lit := [(1434, false), (1452, false), (1461, true)]
theorem step494 (p : Nat → Bool) (h : Constraints p) : clause p c494 = true := by
  simpa only [c494,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause494
def c495 : List Lit := [(1434, false), (1453, false), (1462, true)]
theorem step495 (p : Nat → Bool) (h : Constraints p) : clause p c495 = true := by
  simpa only [c495,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause495
def c496 : List Lit := [(1434, false), (1454, false), (1463, true)]
theorem step496 (p : Nat → Bool) (h : Constraints p) : clause p c496 = true := by
  simpa only [c496,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause496
def c497 : List Lit := [(1435, false), (1461, true)]
theorem step497 (p : Nat → Bool) (h : Constraints p) : clause p c497 = true := by
  simpa only [c497,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause497
def c498 : List Lit := [(1435, false), (1452, false), (1462, true)]
theorem step498 (p : Nat → Bool) (h : Constraints p) : clause p c498 = true := by
  simpa only [c498,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause498
def c499 : List Lit := [(1435, false), (1453, false), (1463, true)]
theorem step499 (p : Nat → Bool) (h : Constraints p) : clause p c499 = true := by
  simpa only [c499,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause499
def c500 : List Lit := [(88, true), (1471, true)]
theorem step500 (p : Nat → Bool) (h : Constraints p) : clause p c500 = true := by
  simpa only [c500,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause500
def c501 : List Lit := [(87, true), (1471, true)]
theorem step501 (p : Nat → Bool) (h : Constraints p) : clause p c501 = true := by
  simpa only [c501,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause501
def c502 : List Lit := [(87, true), (88, true), (1472, true)]
theorem step502 (p : Nat → Bool) (h : Constraints p) : clause p c502 = true := by
  simpa only [c502,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause502
def c503 : List Lit := [(1471, false), (1473, true)]
theorem step503 (p : Nat → Bool) (h : Constraints p) : clause p c503 = true := by
  simpa only [c503,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause503
def c504 : List Lit := [(1472, false), (1474, true)]
theorem step504 (p : Nat → Bool) (h : Constraints p) : clause p c504 = true := by
  simpa only [c504,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause504
def c505 : List Lit := [(85, true), (1473, true)]
theorem step505 (p : Nat → Bool) (h : Constraints p) : clause p c505 = true := by
  simpa only [c505,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause505
def c506 : List Lit := [(85, true), (1471, false), (1474, true)]
theorem step506 (p : Nat → Bool) (h : Constraints p) : clause p c506 = true := by
  simpa only [c506,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause506
def c507 : List Lit := [(85, true), (1472, false), (1475, true)]
theorem step507 (p : Nat → Bool) (h : Constraints p) : clause p c507 = true := by
  simpa only [c507,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause507
def c508 : List Lit := [(97, true), (1476, true)]
theorem step508 (p : Nat → Bool) (h : Constraints p) : clause p c508 = true := by
  simpa only [c508,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause508
def c509 : List Lit := [(94, true), (1476, true)]
theorem step509 (p : Nat → Bool) (h : Constraints p) : clause p c509 = true := by
  simpa only [c509,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause509
def c510 : List Lit := [(94, true), (97, true), (1477, true)]
theorem step510 (p : Nat → Bool) (h : Constraints p) : clause p c510 = true := by
  simpa only [c510,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause510
def c511 : List Lit := [(1476, false), (1478, true)]
theorem step511 (p : Nat → Bool) (h : Constraints p) : clause p c511 = true := by
  simpa only [c511,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause511
def c512 : List Lit := [(1477, false), (1479, true)]
theorem step512 (p : Nat → Bool) (h : Constraints p) : clause p c512 = true := by
  simpa only [c512,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause512
def c513 : List Lit := [(91, true), (1478, true)]
theorem step513 (p : Nat → Bool) (h : Constraints p) : clause p c513 = true := by
  simpa only [c513,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause513
def c514 : List Lit := [(91, true), (1476, false), (1479, true)]
theorem step514 (p : Nat → Bool) (h : Constraints p) : clause p c514 = true := by
  simpa only [c514,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause514
def c515 : List Lit := [(91, true), (1477, false), (1480, true)]
theorem step515 (p : Nat → Bool) (h : Constraints p) : clause p c515 = true := by
  simpa only [c515,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause515
def c516 : List Lit := [(1478, false), (1481, true)]
theorem step516 (p : Nat → Bool) (h : Constraints p) : clause p c516 = true := by
  simpa only [c516,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause516
def c517 : List Lit := [(1479, false), (1482, true)]
theorem step517 (p : Nat → Bool) (h : Constraints p) : clause p c517 = true := by
  simpa only [c517,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause517
def c518 : List Lit := [(1480, false), (1483, true)]
theorem step518 (p : Nat → Bool) (h : Constraints p) : clause p c518 = true := by
  simpa only [c518,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause518
def c519 : List Lit := [(1473, false), (1481, true)]
theorem step519 (p : Nat → Bool) (h : Constraints p) : clause p c519 = true := by
  simpa only [c519,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause519
def c520 : List Lit := [(1473, false), (1478, false), (1482, true)]
theorem step520 (p : Nat → Bool) (h : Constraints p) : clause p c520 = true := by
  simpa only [c520,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause520
def c521 : List Lit := [(1473, false), (1479, false), (1483, true)]
theorem step521 (p : Nat → Bool) (h : Constraints p) : clause p c521 = true := by
  simpa only [c521,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause521
def c522 : List Lit := [(1473, false), (1480, false), (1484, true)]
theorem step522 (p : Nat → Bool) (h : Constraints p) : clause p c522 = true := by
  simpa only [c522,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause522
def c523 : List Lit := [(1474, false), (1482, true)]
theorem step523 (p : Nat → Bool) (h : Constraints p) : clause p c523 = true := by
  simpa only [c523,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause523
def c524 : List Lit := [(1474, false), (1478, false), (1483, true)]
theorem step524 (p : Nat → Bool) (h : Constraints p) : clause p c524 = true := by
  simpa only [c524,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause524
def c525 : List Lit := [(1474, false), (1479, false), (1484, true)]
theorem step525 (p : Nat → Bool) (h : Constraints p) : clause p c525 = true := by
  simpa only [c525,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause525
def c526 : List Lit := [(1475, false), (1478, false), (1484, true)]
theorem step526 (p : Nat → Bool) (h : Constraints p) : clause p c526 = true := by
  simpa only [c526,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause526
def c527 : List Lit := [(101, true), (1487, true)]
theorem step527 (p : Nat → Bool) (h : Constraints p) : clause p c527 = true := by
  simpa only [c527,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause527
def c528 : List Lit := [(99, true), (1487, true)]
theorem step528 (p : Nat → Bool) (h : Constraints p) : clause p c528 = true := by
  simpa only [c528,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause528
def c529 : List Lit := [(99, true), (101, true), (1488, true)]
theorem step529 (p : Nat → Bool) (h : Constraints p) : clause p c529 = true := by
  simpa only [c529,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause529
def c530 : List Lit := [(1487, false), (1489, true)]
theorem step530 (p : Nat → Bool) (h : Constraints p) : clause p c530 = true := by
  simpa only [c530,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause530
def c531 : List Lit := [(1488, false), (1490, true)]
theorem step531 (p : Nat → Bool) (h : Constraints p) : clause p c531 = true := by
  simpa only [c531,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause531
def c532 : List Lit := [(98, true), (1489, true)]
theorem step532 (p : Nat → Bool) (h : Constraints p) : clause p c532 = true := by
  simpa only [c532,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause532
def c533 : List Lit := [(98, true), (1487, false), (1490, true)]
theorem step533 (p : Nat → Bool) (h : Constraints p) : clause p c533 = true := by
  simpa only [c533,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause533
def c534 : List Lit := [(98, true), (1488, false), (1491, true)]
theorem step534 (p : Nat → Bool) (h : Constraints p) : clause p c534 = true := by
  simpa only [c534,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause534
def c535 : List Lit := [(105, true), (1492, true)]
theorem step535 (p : Nat → Bool) (h : Constraints p) : clause p c535 = true := by
  simpa only [c535,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause535
def c536 : List Lit := [(104, true), (1492, true)]
theorem step536 (p : Nat → Bool) (h : Constraints p) : clause p c536 = true := by
  simpa only [c536,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause536
def c537 : List Lit := [(104, true), (105, true), (1493, true)]
theorem step537 (p : Nat → Bool) (h : Constraints p) : clause p c537 = true := by
  simpa only [c537,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause537
def c538 : List Lit := [(107, true), (1494, true)]
theorem step538 (p : Nat → Bool) (h : Constraints p) : clause p c538 = true := by
  simpa only [c538,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause538
def c539 : List Lit := [(106, true), (1494, true)]
theorem step539 (p : Nat → Bool) (h : Constraints p) : clause p c539 = true := by
  simpa only [c539,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause539
def c540 : List Lit := [(106, true), (107, true), (1495, true)]
theorem step540 (p : Nat → Bool) (h : Constraints p) : clause p c540 = true := by
  simpa only [c540,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause540
def c541 : List Lit := [(1494, false), (1496, true)]
theorem step541 (p : Nat → Bool) (h : Constraints p) : clause p c541 = true := by
  simpa only [c541,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause541
def c542 : List Lit := [(1495, false), (1497, true)]
theorem step542 (p : Nat → Bool) (h : Constraints p) : clause p c542 = true := by
  simpa only [c542,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause542
def c543 : List Lit := [(1492, false), (1496, true)]
theorem step543 (p : Nat → Bool) (h : Constraints p) : clause p c543 = true := by
  simpa only [c543,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause543
def c544 : List Lit := [(1492, false), (1494, false), (1497, true)]
theorem step544 (p : Nat → Bool) (h : Constraints p) : clause p c544 = true := by
  simpa only [c544,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause544
def c545 : List Lit := [(1493, false), (1497, true)]
theorem step545 (p : Nat → Bool) (h : Constraints p) : clause p c545 = true := by
  simpa only [c545,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause545
def c546 : List Lit := [(1493, false), (1494, false), (1498, true)]
theorem step546 (p : Nat → Bool) (h : Constraints p) : clause p c546 = true := by
  simpa only [c546,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause546
def c547 : List Lit := [(1496, false), (1500, true)]
theorem step547 (p : Nat → Bool) (h : Constraints p) : clause p c547 = true := by
  simpa only [c547,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause547
def c548 : List Lit := [(1497, false), (1501, true)]
theorem step548 (p : Nat → Bool) (h : Constraints p) : clause p c548 = true := by
  simpa only [c548,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause548
def c549 : List Lit := [(1498, false), (1502, true)]
theorem step549 (p : Nat → Bool) (h : Constraints p) : clause p c549 = true := by
  simpa only [c549,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause549
def c550 : List Lit := [(1489, false), (1496, false), (1501, true)]
theorem step550 (p : Nat → Bool) (h : Constraints p) : clause p c550 = true := by
  simpa only [c550,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause550
def c551 : List Lit := [(1490, false), (1496, false), (1502, true)]
theorem step551 (p : Nat → Bool) (h : Constraints p) : clause p c551 = true := by
  simpa only [c551,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause551
def c552 : List Lit := [(1490, false), (1497, false), (1503, true)]
theorem step552 (p : Nat → Bool) (h : Constraints p) : clause p c552 = true := by
  simpa only [c552,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause552
def c553 : List Lit := [(1491, false), (1496, false), (1503, true)]
theorem step553 (p : Nat → Bool) (h : Constraints p) : clause p c553 = true := by
  simpa only [c553,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause553
def c554 : List Lit := [(1500, false), (1507, true)]
theorem step554 (p : Nat → Bool) (h : Constraints p) : clause p c554 = true := by
  simpa only [c554,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause554
def c555 : List Lit := [(1501, false), (1508, true)]
theorem step555 (p : Nat → Bool) (h : Constraints p) : clause p c555 = true := by
  simpa only [c555,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause555
def c556 : List Lit := [(1502, false), (1509, true)]
theorem step556 (p : Nat → Bool) (h : Constraints p) : clause p c556 = true := by
  simpa only [c556,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause556
def c557 : List Lit := [(1481, false), (1500, false), (1508, true)]
theorem step557 (p : Nat → Bool) (h : Constraints p) : clause p c557 = true := by
  simpa only [c557,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause557
def c558 : List Lit := [(1481, false), (1501, false), (1509, true)]
theorem step558 (p : Nat → Bool) (h : Constraints p) : clause p c558 = true := by
  simpa only [c558,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause558
def c559 : List Lit := [(1481, false), (1502, false), (1510, true)]
theorem step559 (p : Nat → Bool) (h : Constraints p) : clause p c559 = true := by
  simpa only [c559,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause559
def c560 : List Lit := [(1481, false), (1503, false), (1511, true)]
theorem step560 (p : Nat → Bool) (h : Constraints p) : clause p c560 = true := by
  simpa only [c560,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause560
def c561 : List Lit := [(1482, false), (1500, false), (1509, true)]
theorem step561 (p : Nat → Bool) (h : Constraints p) : clause p c561 = true := by
  simpa only [c561,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause561
def c562 : List Lit := [(1482, false), (1501, false), (1510, true)]
theorem step562 (p : Nat → Bool) (h : Constraints p) : clause p c562 = true := by
  simpa only [c562,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause562
def c563 : List Lit := [(1482, false), (1502, false), (1511, true)]
theorem step563 (p : Nat → Bool) (h : Constraints p) : clause p c563 = true := by
  simpa only [c563,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause563
def c564 : List Lit := [(1483, false), (1500, false), (1510, true)]
theorem step564 (p : Nat → Bool) (h : Constraints p) : clause p c564 = true := by
  simpa only [c564,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause564
def c565 : List Lit := [(1483, false), (1501, false), (1511, true)]
theorem step565 (p : Nat → Bool) (h : Constraints p) : clause p c565 = true := by
  simpa only [c565,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause565
def c566 : List Lit := [(1484, false), (1500, false), (1511, true)]
theorem step566 (p : Nat → Bool) (h : Constraints p) : clause p c566 = true := by
  simpa only [c566,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause566
def c567 : List Lit := [(1460, false), (1507, false), (1521, true)]
theorem step567 (p : Nat → Bool) (h : Constraints p) : clause p c567 = true := by
  simpa only [c567,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause567
def c568 : List Lit := [(1460, false), (1509, false), (1523, true)]
theorem step568 (p : Nat → Bool) (h : Constraints p) : clause p c568 = true := by
  simpa only [c568,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause568
def c569 : List Lit := [(1460, false), (1510, false), (1524, true)]
theorem step569 (p : Nat → Bool) (h : Constraints p) : clause p c569 = true := by
  simpa only [c569,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause569
def c570 : List Lit := [(1460, false), (1511, false), (1525, true)]
theorem step570 (p : Nat → Bool) (h : Constraints p) : clause p c570 = true := by
  simpa only [c570,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause570
def c571 : List Lit := [(1461, false), (1508, false), (1523, true)]
theorem step571 (p : Nat → Bool) (h : Constraints p) : clause p c571 = true := by
  simpa only [c571,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause571
def c572 : List Lit := [(1461, false), (1509, false), (1524, true)]
theorem step572 (p : Nat → Bool) (h : Constraints p) : clause p c572 = true := by
  simpa only [c572,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause572
def c573 : List Lit := [(1461, false), (1510, false), (1525, true)]
theorem step573 (p : Nat → Bool) (h : Constraints p) : clause p c573 = true := by
  simpa only [c573,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause573
def c574 : List Lit := [(1461, false), (1511, false), (1526, true)]
theorem step574 (p : Nat → Bool) (h : Constraints p) : clause p c574 = true := by
  simpa only [c574,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause574
def c575 : List Lit := [(1462, false), (1508, false), (1524, true)]
theorem step575 (p : Nat → Bool) (h : Constraints p) : clause p c575 = true := by
  simpa only [c575,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause575
def c576 : List Lit := [(1462, false), (1509, false), (1525, true)]
theorem step576 (p : Nat → Bool) (h : Constraints p) : clause p c576 = true := by
  simpa only [c576,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause576
def c577 : List Lit := [(1462, false), (1510, false), (1526, true)]
theorem step577 (p : Nat → Bool) (h : Constraints p) : clause p c577 = true := by
  simpa only [c577,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause577
def c578 : List Lit := [(1463, false), (1508, false), (1525, true)]
theorem step578 (p : Nat → Bool) (h : Constraints p) : clause p c578 = true := by
  simpa only [c578,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause578
def c579 : List Lit := [(1414, false), (1526, false), (1542, true)]
theorem step579 (p : Nat → Bool) (h : Constraints p) : clause p c579 = true := by
  simpa only [c579,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause579
def c580 : List Lit := [(1415, false), (1525, false), (1542, true)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true := by
  simpa only [c580,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause580
def c581 : List Lit := [(1416, false), (1524, false), (1542, true)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true := by
  simpa only [c581,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause581
def c582 : List Lit := [(1417, false), (1523, false), (1542, true)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true := by
  simpa only [c582,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause582
def c583 : List Lit := [(1419, false), (1521, false), (1542, true)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true := by
  simpa only [c583,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause583
def c584 : List Lit := [(1542, false)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true := by
  simpa only [c584,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause584
def c585 : List Lit := [(13, false), (14, false), (22, false), (23, false)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true := by
  simpa only [c585,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause585
def c586 : List Lit := [(60, false), (61, false), (64, false), (65, false)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true := by
  simpa only [c586,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause586
end B112E205
