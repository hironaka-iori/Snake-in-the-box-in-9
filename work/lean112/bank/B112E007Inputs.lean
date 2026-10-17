import TreeRup
namespace B112E007
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
structure Block0 (p : Nat → Bool) : Prop where
  clause1 : p 1 = false ∨ p 119 = true ∨ p 14 = true
  clause2 : p 2 = false ∨ p 120 = true ∨ p 7 = true
  clause3 : p 2 = false ∨ p 120 = true ∨ p 5 = true
  clause4 : p 3 = false ∨ p 121 = true ∨ p 1 = true ∨ p 10 = true
  clause5 : p 3 = false ∨ p 121 = true ∨ p 1 = true ∨ p 4 = true
  clause6 : p 4 = false ∨ p 122 = true ∨ p 5 = true
  clause7 : p 4 = false ∨ p 122 = true ∨ p 3 = true
  clause8 : p 5 = false ∨ p 123 = true ∨ p 4 = true
  clause9 : p 5 = false ∨ p 123 = true ∨ p 2 = true
  clause10 : p 6 = false ∨ p 7 = false ∨ p 12 = false ∨ p 26 = false
  clause11 : p 6 = false ∨ p 7 = false ∨ p 12 = false ∨ p 55 = false
  clause12 : p 6 = false ∨ p 7 = false ∨ p 26 = false ∨ p 55 = false
  clause13 : p 6 = false ∨ p 124 = true ∨ p 12 = true ∨ p 26 = true ∨ p 55 = true
  clause14 : p 7 = false ∨ p 125 = true ∨ p 6 = true ∨ p 58 = true
  clause15 : p 7 = false ∨ p 125 = true ∨ p 2 = true ∨ p 58 = true
  clause16 : p 7 = false ∨ p 125 = true ∨ p 2 = true ∨ p 6 = true
  clause17 : p 8 = false ∨ p 11 = false ∨ p 34 = false ∨ p 64 = false
  clause18 : p 8 = false ∨ p 126 = true ∨ p 11 = true ∨ p 34 = true
  clause19 : p 9 = false ∨ p 127 = true ∨ p 65 = true
  clause20 : p 10 = false ∨ p 3 = false ∨ p 37 = false ∨ p 68 = false
  clause21 : p 10 = false ∨ p 128 = true ∨ p 37 = true ∨ p 68 = true
  clause22 : p 129 = false ∨ p 11 = true
  clause23 : p 11 = false ∨ p 8 = true ∨ p 13 = true
  clause24 : p 11 = false ∨ p 129 = true ∨ p 13 = true
  clause25 : p 11 = false ∨ p 129 = true ∨ p 8 = true
  clause26 : p 12 = false ∨ p 6 = false ∨ p 13 = false ∨ p 41 = false
  clause27 : p 12 = false ∨ p 6 = false ∨ p 13 = false ∨ p 73 = false
  clause28 : p 12 = false ∨ p 6 = false ∨ p 41 = false ∨ p 73 = false
  clause29 : p 12 = false ∨ p 13 = false ∨ p 41 = false ∨ p 73 = false
  clause30 : p 12 = false ∨ p 130 = true ∨ p 6 = true ∨ p 9 = true ∨ p 41 = true ∨ p 73 = true
  clause31 : p 12 = false ∨ p 130 = true ∨ p 6 = true ∨ p 9 = true ∨ p 13 = true ∨ p 41 = true
  clause32 : p 13 = false ∨ p 131 = true ∨ p 12 = true
structure Block1 (p : Nat → Bool) : Prop where
  clause33 : p 13 = false ∨ p 131 = true ∨ p 11 = true
  clause34 : p 14 = false ∨ p 1 = false ∨ p 15 = false ∨ p 16 = false
  clause35 : p 14 = false ∨ p 1 = false ∨ p 15 = false ∨ p 24 = false
  clause36 : p 14 = false ∨ p 1 = false ∨ p 16 = false ∨ p 18 = false
  clause37 : p 14 = false ∨ p 1 = false ∨ p 16 = false ∨ p 24 = false
  clause38 : p 14 = false ∨ p 1 = false ∨ p 16 = false ∨ p 33 = false
  clause39 : p 14 = false ∨ p 1 = false ∨ p 18 = false ∨ p 33 = false
  clause40 : p 14 = false ∨ p 1 = false ∨ p 24 = false ∨ p 33 = false
  clause41 : p 14 = false ∨ p 16 = false ∨ p 18 = false ∨ p 24 = false
  clause42 : p 15 = false ∨ p 14 = false ∨ p 17 = false ∨ p 20 = false
  clause43 : p 15 = false ∨ p 14 = false ∨ p 17 = false ∨ p 25 = false
  clause44 : p 15 = false ∨ p 14 = false ∨ p 17 = false ∨ p 34 = false
  clause45 : p 15 = false ∨ p 14 = false ∨ p 20 = false ∨ p 25 = false
  clause46 : p 15 = false ∨ p 14 = false ∨ p 20 = false ∨ p 34 = false
  clause47 : p 15 = false ∨ p 14 = false ∨ p 25 = false ∨ p 34 = false
  clause48 : p 15 = false ∨ p 17 = false ∨ p 20 = false ∨ p 25 = false
  clause49 : p 15 = false ∨ p 17 = false ∨ p 20 = false ∨ p 34 = false
  clause50 : p 15 = false ∨ p 17 = false ∨ p 25 = false ∨ p 34 = false
  clause51 : p 15 = false ∨ p 20 = false ∨ p 25 = false ∨ p 34 = false
  clause52 : p 16 = false ∨ p 14 = false ∨ p 17 = false ∨ p 21 = false
  clause53 : p 16 = false ∨ p 14 = false ∨ p 17 = false ∨ p 26 = false
  clause54 : p 16 = false ∨ p 14 = false ∨ p 17 = false ∨ p 81 = false
  clause55 : p 16 = false ∨ p 14 = false ∨ p 21 = false ∨ p 26 = false
  clause56 : p 16 = false ∨ p 14 = false ∨ p 21 = false ∨ p 81 = false
  clause57 : p 16 = false ∨ p 14 = false ∨ p 26 = false ∨ p 81 = false
  clause58 : p 16 = false ∨ p 17 = false ∨ p 21 = false ∨ p 26 = false
  clause59 : p 16 = false ∨ p 17 = false ∨ p 21 = false ∨ p 81 = false
  clause60 : p 16 = false ∨ p 17 = false ∨ p 26 = false ∨ p 81 = false
  clause61 : p 16 = false ∨ p 21 = false ∨ p 26 = false ∨ p 81 = false
  clause62 : p 16 = false ∨ p 134 = true ∨ p 14 = true ∨ p 17 = true ∨ p 26 = true ∨ p 81 = true
  clause63 : p 17 = false ∨ p 15 = true ∨ p 16 = true ∨ p 19 = true ∨ p 27 = true ∨ p 82 = true
  clause64 : p 17 = false ∨ p 15 = false ∨ p 16 = false ∨ p 19 = false
structure Block2 (p : Nat → Bool) : Prop where
  clause65 : p 17 = false ∨ p 16 = false ∨ p 19 = false ∨ p 27 = false
  clause66 : p 17 = false ∨ p 135 = true ∨ p 15 = true ∨ p 16 = true ∨ p 27 = true ∨ p 82 = true
  clause67 : p 17 = false ∨ p 135 = true ∨ p 15 = true ∨ p 16 = true ∨ p 19 = true ∨ p 82 = true
  clause68 : p 17 = false ∨ p 135 = true ∨ p 15 = true ∨ p 16 = true ∨ p 19 = true ∨ p 27 = true
  clause69 : p 18 = false ∨ p 14 = false ∨ p 28 = false ∨ p 83 = false
  clause70 : p 18 = false ∨ p 136 = true ∨ p 14 = true ∨ p 83 = true
  clause71 : p 19 = false ∨ p 17 = false ∨ p 23 = false ∨ p 36 = false
  clause72 : p 19 = false ∨ p 17 = false ∨ p 23 = false ∨ p 85 = false
  clause73 : p 19 = false ∨ p 17 = false ∨ p 36 = false ∨ p 85 = false
  clause74 : p 20 = false ∨ p 138 = true ∨ p 22 = true ∨ p 38 = true ∨ p 87 = true
  clause75 : p 20 = false ∨ p 138 = true ∨ p 15 = true ∨ p 38 = true ∨ p 87 = true
  clause76 : p 20 = false ∨ p 138 = true ∨ p 15 = true ∨ p 22 = true ∨ p 38 = true
  clause77 : p 139 = false ∨ p 21 = true
  clause78 : p 21 = false ∨ p 16 = true ∨ p 29 = true ∨ p 88 = true
  clause79 : p 21 = false ∨ p 139 = true ∨ p 29 = true ∨ p 88 = true
  clause80 : p 21 = false ∨ p 139 = true ∨ p 16 = true ∨ p 88 = true
  clause81 : p 21 = false ∨ p 139 = true ∨ p 16 = true ∨ p 29 = true
  clause82 : p 22 = false ∨ p 140 = true ∨ p 23 = true
  clause83 : p 22 = false ∨ p 140 = true ∨ p 20 = true
  clause84 : p 23 = false ∨ p 141 = true ∨ p 22 = true ∨ p 32 = true
  clause85 : p 23 = false ∨ p 141 = true ∨ p 19 = true ∨ p 32 = true
  clause86 : p 23 = false ∨ p 141 = true ∨ p 19 = true ∨ p 22 = true
  clause87 : p 24 = false ∨ p 14 = false ∨ p 25 = false ∨ p 26 = false
  clause88 : p 24 = false ∨ p 14 = false ∨ p 25 = false ∨ p 28 = false
  clause89 : p 24 = false ∨ p 14 = false ∨ p 26 = false ∨ p 28 = false
  clause90 : p 24 = false ∨ p 25 = false ∨ p 26 = false ∨ p 28 = false
  clause91 : p 143 = false ∨ p 25 = true
  clause92 : p 25 = false ∨ p 15 = true ∨ p 24 = true ∨ p 27 = true ∨ p 91 = true
  clause93 : p 143 = false ∨ p 24 = false ∨ p 91 = false
  clause94 : p 143 = false ∨ p 27 = false ∨ p 91 = false
  clause95 : p 25 = false ∨ p 143 = true ∨ p 24 = true ∨ p 27 = true ∨ p 91 = true
  clause96 : p 25 = false ∨ p 143 = true ∨ p 15 = true ∨ p 27 = true ∨ p 91 = true
structure Block3 (p : Nat → Bool) : Prop where
  clause97 : p 25 = false ∨ p 143 = true ∨ p 15 = true ∨ p 24 = true ∨ p 91 = true
  clause98 : p 25 = false ∨ p 143 = true ∨ p 15 = true ∨ p 24 = true ∨ p 27 = true
  clause99 : p 26 = false ∨ p 6 = true ∨ p 16 = true ∨ p 24 = true ∨ p 27 = true ∨ p 29 = true ∨ p 41 = true
  clause100 : p 26 = false ∨ p 144 = true ∨ p 6 = true ∨ p 16 = true ∨ p 24 = true ∨ p 29 = true ∨ p 41 = true
  clause101 : p 26 = false ∨ p 144 = true ∨ p 6 = true ∨ p 16 = true ∨ p 24 = true ∨ p 27 = true ∨ p 41 = true
  clause102 : p 26 = false ∨ p 144 = true ∨ p 6 = true ∨ p 16 = true ∨ p 24 = true ∨ p 27 = true ∨ p 29 = true
  clause103 : p 27 = false ∨ p 17 = false ∨ p 25 = false ∨ p 26 = false
  clause104 : p 27 = false ∨ p 17 = false ∨ p 26 = false ∨ p 92 = false
  clause105 : p 27 = false ∨ p 25 = false ∨ p 26 = false ∨ p 92 = false
  clause106 : p 146 = false ∨ p 28 = true
  clause107 : p 28 = false ∨ p 146 = true ∨ p 24 = true ∨ p 30 = true
  clause108 : p 28 = false ∨ p 146 = true ∨ p 18 = true ∨ p 30 = true
  clause109 : p 28 = false ∨ p 146 = true ∨ p 18 = true ∨ p 24 = true
  clause110 : p 29 = false ∨ p 21 = false ∨ p 26 = false ∨ p 31 = false
  clause111 : p 29 = false ∨ p 21 = false ∨ p 26 = false ∨ p 47 = false
  clause112 : p 29 = false ∨ p 21 = false ∨ p 26 = false ∨ p 98 = false
  clause113 : p 29 = false ∨ p 21 = false ∨ p 31 = false ∨ p 47 = false
  clause114 : p 29 = false ∨ p 21 = false ∨ p 31 = false ∨ p 98 = false
  clause115 : p 29 = false ∨ p 21 = false ∨ p 47 = false ∨ p 98 = false
  clause116 : p 29 = false ∨ p 26 = false ∨ p 31 = false ∨ p 47 = false
  clause117 : p 29 = false ∨ p 26 = false ∨ p 31 = false ∨ p 98 = false
  clause118 : p 29 = false ∨ p 26 = false ∨ p 47 = false ∨ p 98 = false
  clause119 : p 29 = false ∨ p 31 = false ∨ p 47 = false ∨ p 98 = false
  clause120 : p 30 = false ∨ p 148 = true ∨ p 31 = true
  clause121 : p 32 = false ∨ p 150 = true ∨ p 31 = true
  clause122 : p 33 = false ∨ p 14 = false ∨ p 34 = false ∨ p 37 = false
  clause123 : p 34 = false ∨ p 8 = false ∨ p 15 = false ∨ p 33 = false
  clause124 : p 152 = false ∨ p 8 = false ∨ p 38 = false
  clause125 : p 34 = false ∨ p 152 = true ∨ p 15 = true ∨ p 33 = true ∨ p 38 = true
  clause126 : p 34 = false ∨ p 152 = true ∨ p 8 = true ∨ p 33 = true ∨ p 38 = true
  clause127 : p 35 = false ∨ p 36 = false ∨ p 40 = false ∨ p 43 = false
  clause128 : p 35 = false ∨ p 153 = true ∨ p 40 = true ∨ p 43 = true
structure Block4 (p : Nat → Bool) : Prop where
  clause129 : p 35 = false ∨ p 153 = true ∨ p 36 = true ∨ p 43 = true
  clause130 : p 36 = false ∨ p 19 = false ∨ p 35 = false ∨ p 44 = false
  clause131 : p 36 = false ∨ p 154 = true ∨ p 35 = true ∨ p 44 = true
  clause132 : p 37 = false ∨ p 10 = false ∨ p 33 = false ∨ p 39 = false
  clause133 : p 37 = false ∨ p 10 = false ∨ p 33 = false ∨ p 45 = false
  clause134 : p 37 = false ∨ p 10 = false ∨ p 39 = false ∨ p 45 = false
  clause135 : p 37 = false ∨ p 33 = false ∨ p 39 = false ∨ p 45 = false
  clause136 : p 37 = false ∨ p 38 = false ∨ p 39 = false ∨ p 45 = false
  clause137 : p 37 = false ∨ p 155 = true ∨ p 10 = true ∨ p 33 = true ∨ p 38 = true ∨ p 45 = true
  clause138 : p 38 = false ∨ p 20 = false ∨ p 34 = false ∨ p 37 = false
  clause139 : p 38 = false ∨ p 20 = false ∨ p 37 = false ∨ p 46 = false
  clause140 : p 38 = false ∨ p 34 = false ∨ p 37 = false ∨ p 46 = false
  clause141 : p 38 = false ∨ p 34 = false ∨ p 37 = false ∨ p 105 = false
  clause142 : p 38 = false ∨ p 37 = false ∨ p 46 = false ∨ p 105 = false
  clause143 : p 39 = false ∨ p 157 = true ∨ p 40 = true
  clause144 : p 39 = false ∨ p 157 = true ∨ p 37 = true
  clause145 : p 40 = false ∨ p 158 = true ∨ p 39 = true
  clause146 : p 40 = false ∨ p 158 = true ∨ p 35 = true
  clause147 : p 41 = false ∨ p 12 = false ∨ p 26 = false ∨ p 43 = false
  clause148 : p 41 = false ∨ p 12 = false ∨ p 26 = false ∨ p 47 = false
  clause149 : p 41 = false ∨ p 12 = false ∨ p 43 = false ∨ p 47 = false
  clause150 : p 41 = false ∨ p 159 = true ∨ p 12 = true ∨ p 26 = true ∨ p 43 = true
  clause151 : p 42 = false ∨ p 160 = true ∨ p 49 = true
  clause152 : p 42 = false ∨ p 160 = true ∨ p 44 = true
  clause153 : p 43 = false ∨ p 35 = false ∨ p 41 = false ∨ p 44 = false
  clause154 : p 43 = false ∨ p 35 = false ∨ p 44 = false ∨ p 114 = false
  clause155 : p 44 = false ∨ p 36 = false ∨ p 42 = false ∨ p 43 = false
  clause156 : p 44 = false ∨ p 162 = true ∨ p 42 = true ∨ p 43 = true
  clause157 : p 44 = false ∨ p 162 = true ∨ p 36 = true ∨ p 43 = true
  clause158 : p 45 = false ∨ p 37 = false ∨ p 46 = false ∨ p 47 = false
  clause159 : p 45 = false ∨ p 37 = false ∨ p 46 = false ∨ p 115 = false
  clause160 : p 45 = false ∨ p 37 = false ∨ p 47 = false ∨ p 115 = false
structure Block5 (p : Nat → Bool) : Prop where
  clause161 : p 45 = false ∨ p 46 = false ∨ p 47 = false ∨ p 115 = false
  clause162 : p 46 = false ∨ p 164 = true ∨ p 45 = true ∨ p 48 = true ∨ p 49 = true
  clause163 : p 46 = false ∨ p 164 = true ∨ p 38 = true ∨ p 45 = true ∨ p 48 = true
  clause164 : p 165 = false ∨ p 29 = false ∨ p 48 = false
  clause165 : p 47 = false ∨ p 165 = true ∨ p 41 = true ∨ p 45 = true ∨ p 48 = true
  clause166 : p 47 = false ∨ p 165 = true ∨ p 29 = true ∨ p 41 = true ∨ p 48 = true
  clause167 : p 47 = false ∨ p 165 = true ∨ p 29 = true ∨ p 41 = true ∨ p 45 = true
  clause168 : p 48 = false ∨ p 166 = true ∨ p 47 = true
  clause169 : p 48 = false ∨ p 166 = true ∨ p 46 = true
  clause170 : p 49 = false ∨ p 167 = true ∨ p 46 = true
  clause171 : p 49 = false ∨ p 167 = true ∨ p 42 = true
  clause172 : p 50 = false ∨ p 51 = false ∨ p 52 = false ∨ p 55 = false
  clause173 : p 50 = false ∨ p 51 = false ∨ p 52 = false ∨ p 65 = false
  clause174 : p 50 = false ∨ p 51 = false ∨ p 52 = false ∨ p 81 = false
  clause175 : p 50 = false ∨ p 51 = false ∨ p 55 = false ∨ p 65 = false
  clause176 : p 50 = false ∨ p 51 = false ∨ p 55 = false ∨ p 81 = false
  clause177 : p 50 = false ∨ p 51 = false ∨ p 65 = false ∨ p 81 = false
  clause178 : p 50 = false ∨ p 52 = false ∨ p 55 = false ∨ p 65 = false
  clause179 : p 50 = false ∨ p 52 = false ∨ p 55 = false ∨ p 81 = false
  clause180 : p 50 = false ∨ p 52 = false ∨ p 65 = false ∨ p 81 = false
  clause181 : p 50 = false ∨ p 55 = false ∨ p 65 = false ∨ p 81 = false
  clause182 : p 50 = false ∨ p 168 = true ∨ p 52 = true ∨ p 55 = true ∨ p 65 = true ∨ p 81 = true
  clause183 : p 50 = false ∨ p 168 = true ∨ p 51 = true ∨ p 55 = true ∨ p 65 = true ∨ p 81 = true
  clause184 : p 50 = false ∨ p 168 = true ∨ p 51 = true ∨ p 52 = true ∨ p 55 = true ∨ p 65 = true
  clause185 : p 51 = false ∨ p 50 = true ∨ p 56 = true ∨ p 82 = true
  clause186 : p 51 = false ∨ p 169 = true ∨ p 56 = true ∨ p 82 = true
  clause187 : p 51 = false ∨ p 169 = true ∨ p 50 = true ∨ p 82 = true
  clause188 : p 51 = false ∨ p 169 = true ∨ p 50 = true ∨ p 56 = true
  clause189 : p 170 = false ∨ p 52 = true
  clause190 : p 52 = false ∨ p 50 = true ∨ p 70 = true ∨ p 88 = true
  clause191 : p 52 = false ∨ p 170 = true ∨ p 70 = true ∨ p 88 = true
  clause192 : p 52 = false ∨ p 170 = true ∨ p 50 = true ∨ p 88 = true
structure Block6 (p : Nat → Bool) : Prop where
  clause193 : p 52 = false ∨ p 170 = true ∨ p 50 = true ∨ p 70 = true
  clause194 : p 53 = false ∨ p 54 = false ∨ p 55 = false ∨ p 57 = false
  clause195 : p 53 = false ∨ p 54 = false ∨ p 55 = false ∨ p 59 = false
  clause196 : p 53 = false ∨ p 54 = false ∨ p 57 = false ∨ p 59 = false
  clause197 : p 53 = false ∨ p 55 = false ∨ p 57 = false ∨ p 59 = false
  clause198 : p 53 = false ∨ p 171 = true ∨ p 54 = true ∨ p 55 = true ∨ p 59 = true
  clause199 : p 53 = false ∨ p 171 = true ∨ p 54 = true ∨ p 55 = true ∨ p 57 = true
  clause200 : p 172 = false ∨ p 54 = true
  clause201 : p 54 = false ∨ p 53 = true ∨ p 56 = true ∨ p 91 = true
  clause202 : p 172 = false ∨ p 53 = false ∨ p 91 = false
  clause203 : p 172 = false ∨ p 56 = false ∨ p 91 = false
  clause204 : p 54 = false ∨ p 172 = true ∨ p 56 = true ∨ p 91 = true
  clause205 : p 54 = false ∨ p 172 = true ∨ p 53 = true ∨ p 91 = true
  clause206 : p 54 = false ∨ p 172 = true ∨ p 53 = true ∨ p 56 = true
  clause207 : p 56 = false ∨ p 51 = false ∨ p 54 = false ∨ p 55 = false
  clause208 : p 56 = false ∨ p 51 = false ∨ p 54 = false ∨ p 92 = false
  clause209 : p 56 = false ∨ p 51 = false ∨ p 55 = false ∨ p 92 = false
  clause210 : p 56 = false ∨ p 54 = false ∨ p 55 = false ∨ p 92 = false
  clause211 : p 56 = false ∨ p 174 = true ∨ p 54 = true ∨ p 55 = true ∨ p 92 = true
  clause212 : p 56 = false ∨ p 174 = true ∨ p 51 = true ∨ p 55 = true ∨ p 92 = true
  clause213 : p 57 = false ∨ p 53 = true ∨ p 58 = true ∨ p 60 = true
  clause214 : p 57 = false ∨ p 175 = true ∨ p 58 = true ∨ p 60 = true
  clause215 : p 57 = false ∨ p 175 = true ∨ p 53 = true ∨ p 60 = true
  clause216 : p 57 = false ∨ p 175 = true ∨ p 53 = true ∨ p 58 = true
  clause217 : p 58 = false ∨ p 7 = false ∨ p 55 = false ∨ p 61 = false
  clause218 : p 58 = false ∨ p 7 = false ∨ p 57 = false ∨ p 61 = false
  clause219 : p 58 = false ∨ p 7 = false ∨ p 61 = false ∨ p 94 = false
  clause220 : p 58 = false ∨ p 55 = false ∨ p 57 = false ∨ p 61 = false
  clause221 : p 58 = false ∨ p 55 = false ∨ p 61 = false ∨ p 94 = false
  clause222 : p 58 = false ∨ p 57 = false ∨ p 61 = false ∨ p 94 = false
  clause223 : p 177 = false ∨ p 59 = true
  clause224 : p 59 = false ∨ p 53 = true ∨ p 60 = true ∨ p 96 = true
structure Block7 (p : Nat → Bool) : Prop where
  clause225 : p 59 = false ∨ p 177 = true ∨ p 60 = true ∨ p 96 = true
  clause226 : p 59 = false ∨ p 177 = true ∨ p 53 = true ∨ p 96 = true
  clause227 : p 59 = false ∨ p 177 = true ∨ p 53 = true ∨ p 60 = true
  clause228 : p 60 = false ∨ p 57 = false ∨ p 59 = false ∨ p 61 = false
  clause229 : p 61 = false ∨ p 58 = false ∨ p 60 = false ∨ p 62 = false
  clause230 : p 179 = false ∨ p 58 = false ∨ p 62 = false
  clause231 : p 61 = false ∨ p 179 = true ∨ p 58 = true ∨ p 60 = true
  clause232 : p 62 = false ∨ p 61 = true
  clause233 : p 62 = true
  clause234 : p 63 = false ∨ p 64 = false ∨ p 65 = false ∨ p 68 = false
  clause235 : p 63 = false ∨ p 181 = true ∨ p 65 = true ∨ p 68 = true
  clause236 : p 63 = false ∨ p 181 = true ∨ p 64 = true ∨ p 65 = true
  clause237 : p 64 = false ∨ p 182 = true ∨ p 63 = true ∨ p 69 = true
  clause238 : p 64 = false ∨ p 182 = true ∨ p 8 = true ∨ p 69 = true
  clause239 : p 64 = false ∨ p 182 = true ∨ p 8 = true ∨ p 63 = true
  clause240 : p 65 = false ∨ p 50 = false ∨ p 66 = false ∨ p 70 = false
  clause241 : p 65 = false ∨ p 50 = false ∨ p 66 = false ∨ p 73 = false
  clause242 : p 65 = false ∨ p 50 = false ∨ p 66 = false ∨ p 101 = false
  clause243 : p 65 = false ∨ p 50 = false ∨ p 73 = false ∨ p 101 = false
  clause244 : p 65 = false ∨ p 63 = false ∨ p 66 = false ∨ p 70 = false
  clause245 : p 65 = false ∨ p 63 = false ∨ p 66 = false ∨ p 73 = false
  clause246 : p 65 = false ∨ p 66 = false ∨ p 70 = false ∨ p 101 = false
  clause247 : p 65 = false ∨ p 66 = false ∨ p 73 = false ∨ p 101 = false
  clause248 : p 66 = false ∨ p 65 = false ∨ p 67 = false ∨ p 72 = false
  clause249 : p 66 = false ∨ p 184 = true ∨ p 65 = true ∨ p 72 = true
  clause250 : p 66 = false ∨ p 184 = true ∨ p 65 = true ∨ p 67 = true
  clause251 : p 67 = false ∨ p 185 = true ∨ p 75 = true
  clause252 : p 67 = false ∨ p 185 = true ∨ p 66 = true
  clause253 : p 68 = false ∨ p 10 = false ∨ p 63 = false ∨ p 71 = false
  clause254 : p 68 = false ∨ p 10 = false ∨ p 69 = false ∨ p 71 = false
  clause255 : p 68 = false ∨ p 186 = true ∨ p 63 = true ∨ p 69 = true ∨ p 70 = true ∨ p 71 = true
  clause256 : p 68 = false ∨ p 186 = true ∨ p 10 = true ∨ p 63 = true ∨ p 69 = true ∨ p 70 = true
structure Block8 (p : Nat → Bool) : Prop where
  clause257 : p 69 = false ∨ p 64 = false ∨ p 68 = false ∨ p 76 = false
  clause258 : p 69 = false ∨ p 64 = false ∨ p 76 = false ∨ p 105 = false
  clause259 : p 69 = false ∨ p 68 = false ∨ p 76 = false ∨ p 105 = false
  clause260 : p 70 = false ∨ p 52 = false ∨ p 65 = false ∨ p 68 = false
  clause261 : p 70 = false ∨ p 52 = false ∨ p 65 = false ∨ p 72 = false
  clause262 : p 70 = false ∨ p 52 = false ∨ p 65 = false ∨ p 77 = false
  clause263 : p 70 = false ∨ p 52 = false ∨ p 65 = false ∨ p 106 = false
  clause264 : p 70 = false ∨ p 52 = false ∨ p 68 = false ∨ p 72 = false
  clause265 : p 70 = false ∨ p 52 = false ∨ p 68 = false ∨ p 77 = false
  clause266 : p 70 = false ∨ p 52 = false ∨ p 68 = false ∨ p 106 = false
  clause267 : p 70 = false ∨ p 52 = false ∨ p 72 = false ∨ p 77 = false
  clause268 : p 70 = false ∨ p 52 = false ∨ p 72 = false ∨ p 106 = false
  clause269 : p 70 = false ∨ p 52 = false ∨ p 77 = false ∨ p 106 = false
  clause270 : p 70 = false ∨ p 65 = false ∨ p 68 = false ∨ p 72 = false
  clause271 : p 70 = false ∨ p 65 = false ∨ p 68 = false ∨ p 77 = false
  clause272 : p 70 = false ∨ p 65 = false ∨ p 68 = false ∨ p 106 = false
  clause273 : p 70 = false ∨ p 65 = false ∨ p 72 = false ∨ p 77 = false
  clause274 : p 70 = false ∨ p 65 = false ∨ p 72 = false ∨ p 106 = false
  clause275 : p 70 = false ∨ p 65 = false ∨ p 77 = false ∨ p 106 = false
  clause276 : p 70 = false ∨ p 68 = false ∨ p 72 = false ∨ p 77 = false
  clause277 : p 70 = false ∨ p 68 = false ∨ p 72 = false ∨ p 106 = false
  clause278 : p 70 = false ∨ p 68 = false ∨ p 77 = false ∨ p 106 = false
  clause279 : p 70 = false ∨ p 72 = false ∨ p 77 = false ∨ p 106 = false
  clause280 : p 70 = false ∨ p 188 = true ∨ p 52 = true ∨ p 68 = true ∨ p 72 = true ∨ p 77 = true ∨ p 106 = true
  clause281 : p 70 = false ∨ p 188 = true ∨ p 52 = true ∨ p 65 = true ∨ p 68 = true ∨ p 77 = true ∨ p 106 = true
  clause282 : p 71 = false ∨ p 189 = true ∨ p 72 = true
  clause283 : p 71 = false ∨ p 189 = true ∨ p 68 = true
  clause284 : p 72 = false ∨ p 66 = true ∨ p 70 = true ∨ p 71 = true
  clause285 : p 72 = false ∨ p 190 = true ∨ p 70 = true ∨ p 71 = true
  clause286 : p 72 = false ∨ p 190 = true ∨ p 66 = true ∨ p 71 = true
  clause287 : p 72 = false ∨ p 190 = true ∨ p 66 = true ∨ p 70 = true
  clause288 : p 73 = false ∨ p 12 = false ∨ p 55 = false ∨ p 77 = false
structure Block9 (p : Nat → Bool) : Prop where
  clause289 : p 73 = false ∨ p 12 = false ∨ p 65 = false ∨ p 77 = false
  clause290 : p 73 = false ∨ p 55 = false ∨ p 65 = false ∨ p 77 = false
  clause291 : p 73 = false ∨ p 191 = true ∨ p 55 = true ∨ p 65 = true ∨ p 77 = true
  clause292 : p 73 = false ∨ p 191 = true ∨ p 12 = true ∨ p 55 = true ∨ p 65 = true
  clause293 : p 74 = false ∨ p 192 = true ∨ p 79 = true
  clause294 : p 74 = false ∨ p 192 = true ∨ p 75 = true
  clause295 : p 75 = false ∨ p 193 = true ∨ p 74 = true
  clause296 : p 75 = false ∨ p 193 = true ∨ p 67 = true
  clause297 : p 76 = false ∨ p 69 = false ∨ p 78 = false ∨ p 79 = false
  clause298 : p 76 = false ∨ p 194 = true ∨ p 78 = true ∨ p 79 = true
  clause299 : p 76 = false ∨ p 194 = true ∨ p 69 = true ∨ p 79 = true
  clause300 : p 76 = false ∨ p 194 = true ∨ p 69 = true ∨ p 78 = true
  clause301 : p 77 = false ∨ p 70 = false ∨ p 73 = false ∨ p 78 = false
  clause302 : p 77 = false ∨ p 195 = true ∨ p 73 = true ∨ p 78 = true
  clause303 : p 77 = false ∨ p 195 = true ∨ p 70 = true ∨ p 78 = true
  clause304 : p 77 = false ∨ p 195 = true ∨ p 70 = true ∨ p 73 = true
  clause305 : p 78 = false ∨ p 196 = true ∨ p 77 = true
  clause306 : p 78 = false ∨ p 196 = true ∨ p 76 = true
  clause307 : p 79 = false ∨ p 197 = true ∨ p 76 = true
  clause308 : p 79 = false ∨ p 197 = true ∨ p 74 = true
  clause309 : p 80 = false ∨ p 14 = false ∨ p 81 = false ∨ p 83 = false
  clause310 : p 80 = false ∨ p 14 = false ∨ p 81 = false ∨ p 86 = false
  clause311 : p 80 = false ∨ p 81 = false ∨ p 83 = false ∨ p 86 = false
  clause312 : p 81 = false ∨ p 16 = false ∨ p 50 = false ∨ p 84 = false
  clause313 : p 81 = false ∨ p 16 = false ∨ p 50 = false ∨ p 88 = false
  clause314 : p 81 = false ∨ p 16 = false ∨ p 50 = false ∨ p 101 = false
  clause315 : p 81 = false ∨ p 16 = false ∨ p 82 = false ∨ p 101 = false
  clause316 : p 81 = false ∨ p 50 = false ∨ p 80 = false ∨ p 88 = false
  clause317 : p 81 = false ∨ p 50 = false ∨ p 80 = false ∨ p 101 = false
  clause318 : p 81 = false ∨ p 50 = false ∨ p 82 = false ∨ p 101 = false
  clause319 : p 81 = false ∨ p 50 = false ∨ p 84 = false ∨ p 88 = false
  clause320 : p 81 = false ∨ p 50 = false ∨ p 84 = false ∨ p 101 = false
structure Block10 (p : Nat → Bool) : Prop where
  clause321 : p 81 = false ∨ p 50 = false ∨ p 88 = false ∨ p 101 = false
  clause322 : p 81 = false ∨ p 80 = false ∨ p 82 = false ∨ p 88 = false
  clause323 : p 81 = false ∨ p 82 = false ∨ p 84 = false ∨ p 88 = false
  clause324 : p 81 = false ∨ p 199 = true ∨ p 50 = true ∨ p 80 = true ∨ p 82 = true ∨ p 84 = true ∨ p 88 = true ∨ p 101 = true
  clause325 : p 81 = false ∨ p 199 = true ∨ p 16 = true ∨ p 80 = true ∨ p 82 = true ∨ p 84 = true ∨ p 88 = true ∨ p 101 = true
  clause326 : p 81 = false ∨ p 199 = true ∨ p 16 = true ∨ p 50 = true ∨ p 80 = true ∨ p 84 = true ∨ p 88 = true ∨ p 101 = true
  clause327 : p 81 = false ∨ p 199 = true ∨ p 16 = true ∨ p 50 = true ∨ p 80 = true ∨ p 82 = true ∨ p 88 = true ∨ p 101 = true
  clause328 : p 81 = false ∨ p 199 = true ∨ p 16 = true ∨ p 50 = true ∨ p 80 = true ∨ p 82 = true ∨ p 84 = true ∨ p 101 = true
  clause329 : p 82 = false ∨ p 17 = false ∨ p 51 = false ∨ p 81 = false
  clause330 : p 82 = false ∨ p 17 = false ∨ p 51 = false ∨ p 85 = false
  clause331 : p 82 = false ∨ p 17 = false ∨ p 51 = false ∨ p 92 = false
  clause332 : p 82 = false ∨ p 17 = false ∨ p 51 = false ∨ p 102 = false
  clause333 : p 82 = false ∨ p 17 = false ∨ p 81 = false ∨ p 85 = false
  clause334 : p 82 = false ∨ p 17 = false ∨ p 81 = false ∨ p 92 = false
  clause335 : p 82 = false ∨ p 17 = false ∨ p 85 = false ∨ p 92 = false
  clause336 : p 82 = false ∨ p 17 = false ∨ p 85 = false ∨ p 102 = false
  clause337 : p 82 = false ∨ p 51 = false ∨ p 81 = false ∨ p 85 = false
  clause338 : p 82 = false ∨ p 51 = false ∨ p 81 = false ∨ p 92 = false
  clause339 : p 82 = false ∨ p 51 = false ∨ p 81 = false ∨ p 102 = false
  clause340 : p 82 = false ∨ p 51 = false ∨ p 85 = false ∨ p 92 = false
  clause341 : p 82 = false ∨ p 51 = false ∨ p 85 = false ∨ p 102 = false
  clause342 : p 82 = false ∨ p 51 = false ∨ p 92 = false ∨ p 102 = false
  clause343 : p 82 = false ∨ p 81 = false ∨ p 85 = false ∨ p 92 = false
  clause344 : p 82 = false ∨ p 81 = false ∨ p 85 = false ∨ p 102 = false
  clause345 : p 82 = false ∨ p 81 = false ∨ p 92 = false ∨ p 102 = false
  clause346 : p 82 = false ∨ p 85 = false ∨ p 92 = false ∨ p 102 = false
  clause347 : p 83 = false ∨ p 201 = true ∨ p 18 = true ∨ p 80 = true ∨ p 84 = true ∨ p 89 = true
  clause348 : p 84 = false ∨ p 81 = false ∨ p 83 = false ∨ p 85 = false
  clause349 : p 84 = false ∨ p 81 = false ∨ p 83 = false ∨ p 90 = false
  clause350 : p 84 = false ∨ p 81 = false ∨ p 83 = false ∨ p 94 = false
  clause351 : p 84 = false ∨ p 81 = false ∨ p 85 = false ∨ p 90 = false
  clause352 : p 84 = false ∨ p 81 = false ∨ p 85 = false ∨ p 94 = false
structure Block11 (p : Nat → Bool) : Prop where
  clause353 : p 84 = false ∨ p 81 = false ∨ p 90 = false ∨ p 94 = false
  clause354 : p 84 = false ∨ p 83 = false ∨ p 85 = false ∨ p 90 = false
  clause355 : p 84 = false ∨ p 83 = false ∨ p 85 = false ∨ p 94 = false
  clause356 : p 84 = false ∨ p 83 = false ∨ p 90 = false ∨ p 94 = false
  clause357 : p 84 = false ∨ p 85 = false ∨ p 90 = false ∨ p 94 = false
  clause358 : p 85 = false ∨ p 19 = true ∨ p 82 = true ∨ p 84 = true ∨ p 95 = true
  clause359 : p 85 = false ∨ p 203 = true ∨ p 82 = true ∨ p 84 = true ∨ p 95 = true
  clause360 : p 85 = false ∨ p 203 = true ∨ p 19 = true ∨ p 84 = true ∨ p 95 = true
  clause361 : p 85 = false ∨ p 203 = true ∨ p 19 = true ∨ p 82 = true ∨ p 95 = true
  clause362 : p 85 = false ∨ p 203 = true ∨ p 19 = true ∨ p 82 = true ∨ p 84 = true
  clause363 : p 86 = false ∨ p 204 = true ∨ p 87 = true ∨ p 88 = true ∨ p 89 = true ∨ p 96 = true
  clause364 : p 86 = false ∨ p 204 = true ∨ p 80 = true ∨ p 87 = true ∨ p 88 = true ∨ p 96 = true
  clause365 : p 87 = false ∨ p 20 = false ∨ p 86 = false ∨ p 97 = false
  clause366 : p 87 = false ∨ p 20 = false ∨ p 86 = false ∨ p 105 = false
  clause367 : p 87 = false ∨ p 86 = false ∨ p 97 = false ∨ p 105 = false
  clause368 : p 88 = false ∨ p 21 = false ∨ p 52 = false ∨ p 81 = false
  clause369 : p 88 = false ∨ p 21 = false ∨ p 52 = false ∨ p 86 = false
  clause370 : p 88 = false ∨ p 21 = false ∨ p 52 = false ∨ p 90 = false
  clause371 : p 88 = false ∨ p 21 = false ∨ p 52 = false ∨ p 98 = false
  clause372 : p 88 = false ∨ p 21 = false ∨ p 52 = false ∨ p 106 = false
  clause373 : p 88 = false ∨ p 21 = false ∨ p 81 = false ∨ p 86 = false
  clause374 : p 88 = false ∨ p 21 = false ∨ p 81 = false ∨ p 90 = false
  clause375 : p 88 = false ∨ p 21 = false ∨ p 81 = false ∨ p 98 = false
  clause376 : p 88 = false ∨ p 21 = false ∨ p 81 = false ∨ p 106 = false
  clause377 : p 88 = false ∨ p 21 = false ∨ p 86 = false ∨ p 90 = false
  clause378 : p 88 = false ∨ p 21 = false ∨ p 86 = false ∨ p 98 = false
  clause379 : p 88 = false ∨ p 21 = false ∨ p 86 = false ∨ p 106 = false
  clause380 : p 88 = false ∨ p 21 = false ∨ p 90 = false ∨ p 98 = false
  clause381 : p 88 = false ∨ p 21 = false ∨ p 90 = false ∨ p 106 = false
  clause382 : p 88 = false ∨ p 21 = false ∨ p 98 = false ∨ p 106 = false
  clause383 : p 88 = false ∨ p 52 = false ∨ p 81 = false ∨ p 86 = false
  clause384 : p 88 = false ∨ p 52 = false ∨ p 81 = false ∨ p 90 = false
structure Block12 (p : Nat → Bool) : Prop where
  clause385 : p 88 = false ∨ p 52 = false ∨ p 81 = false ∨ p 98 = false
  clause386 : p 88 = false ∨ p 52 = false ∨ p 81 = false ∨ p 106 = false
  clause387 : p 88 = false ∨ p 52 = false ∨ p 86 = false ∨ p 90 = false
  clause388 : p 88 = false ∨ p 52 = false ∨ p 86 = false ∨ p 98 = false
  clause389 : p 88 = false ∨ p 52 = false ∨ p 86 = false ∨ p 106 = false
  clause390 : p 88 = false ∨ p 52 = false ∨ p 90 = false ∨ p 98 = false
  clause391 : p 88 = false ∨ p 52 = false ∨ p 90 = false ∨ p 106 = false
  clause392 : p 88 = false ∨ p 52 = false ∨ p 98 = false ∨ p 106 = false
  clause393 : p 88 = false ∨ p 81 = false ∨ p 86 = false ∨ p 90 = false
  clause394 : p 88 = false ∨ p 81 = false ∨ p 86 = false ∨ p 98 = false
  clause395 : p 88 = false ∨ p 81 = false ∨ p 86 = false ∨ p 106 = false
  clause396 : p 88 = false ∨ p 81 = false ∨ p 90 = false ∨ p 98 = false
  clause397 : p 88 = false ∨ p 81 = false ∨ p 90 = false ∨ p 106 = false
  clause398 : p 88 = false ∨ p 81 = false ∨ p 98 = false ∨ p 106 = false
  clause399 : p 88 = false ∨ p 86 = false ∨ p 90 = false ∨ p 98 = false
  clause400 : p 88 = false ∨ p 86 = false ∨ p 90 = false ∨ p 106 = false
  clause401 : p 88 = false ∨ p 86 = false ∨ p 98 = false ∨ p 106 = false
  clause402 : p 88 = false ∨ p 90 = false ∨ p 98 = false ∨ p 106 = false
  clause403 : p 88 = false ∨ p 206 = true ∨ p 21 = true ∨ p 81 = true ∨ p 86 = true ∨ p 90 = true ∨ p 98 = true ∨ p 106 = true
  clause404 : p 88 = false ∨ p 206 = true ∨ p 21 = true ∨ p 52 = true ∨ p 81 = true ∨ p 86 = true ∨ p 98 = true ∨ p 106 = true
  clause405 : p 89 = false ∨ p 83 = false ∨ p 86 = false ∨ p 90 = false
  clause406 : p 89 = false ∨ p 207 = true ∨ p 86 = true ∨ p 90 = true
  clause407 : p 89 = false ∨ p 207 = true ∨ p 83 = true ∨ p 86 = true
  clause408 : p 208 = false ∨ p 90 = true
  clause409 : p 90 = false ∨ p 84 = true ∨ p 88 = true ∨ p 89 = true
  clause410 : p 208 = false ∨ p 84 = false ∨ p 88 = false
  clause411 : p 90 = false ∨ p 208 = true ∨ p 88 = true ∨ p 89 = true
  clause412 : p 90 = false ∨ p 208 = true ∨ p 84 = true ∨ p 89 = true
  clause413 : p 90 = false ∨ p 208 = true ∨ p 84 = true ∨ p 88 = true
  clause414 : p 91 = false ∨ p 25 = false ∨ p 54 = false ∨ p 92 = false
  clause415 : p 91 = false ∨ p 25 = false ∨ p 54 = false ∨ p 93 = false
  clause416 : p 91 = false ∨ p 25 = false ∨ p 54 = false ∨ p 97 = false
structure Block13 (p : Nat → Bool) : Prop where
  clause417 : p 91 = false ∨ p 25 = false ∨ p 54 = false ∨ p 111 = false
  clause418 : p 91 = false ∨ p 25 = false ∨ p 92 = false ∨ p 93 = false
  clause419 : p 91 = false ∨ p 25 = false ∨ p 92 = false ∨ p 97 = false
  clause420 : p 91 = false ∨ p 25 = false ∨ p 92 = false ∨ p 111 = false
  clause421 : p 91 = false ∨ p 25 = false ∨ p 93 = false ∨ p 97 = false
  clause422 : p 91 = false ∨ p 25 = false ∨ p 93 = false ∨ p 111 = false
  clause423 : p 91 = false ∨ p 25 = false ∨ p 97 = false ∨ p 111 = false
  clause424 : p 91 = false ∨ p 54 = false ∨ p 92 = false ∨ p 93 = false
  clause425 : p 91 = false ∨ p 54 = false ∨ p 92 = false ∨ p 97 = false
  clause426 : p 91 = false ∨ p 54 = false ∨ p 92 = false ∨ p 111 = false
  clause427 : p 91 = false ∨ p 54 = false ∨ p 93 = false ∨ p 97 = false
  clause428 : p 91 = false ∨ p 54 = false ∨ p 93 = false ∨ p 111 = false
  clause429 : p 91 = false ∨ p 54 = false ∨ p 97 = false ∨ p 111 = false
  clause430 : p 91 = false ∨ p 92 = false ∨ p 93 = false ∨ p 97 = false
  clause431 : p 91 = false ∨ p 92 = false ∨ p 93 = false ∨ p 111 = false
  clause432 : p 91 = false ∨ p 92 = false ∨ p 97 = false ∨ p 111 = false
  clause433 : p 91 = false ∨ p 93 = false ∨ p 97 = false ∨ p 111 = false
  clause434 : p 92 = false ∨ p 27 = false ∨ p 56 = false ∨ p 95 = false
  clause435 : p 92 = false ∨ p 56 = false ∨ p 91 = false ∨ p 95 = false
  clause436 : p 92 = false ∨ p 56 = false ∨ p 91 = false ∨ p 99 = false
  clause437 : p 92 = false ∨ p 56 = false ∨ p 91 = false ∨ p 112 = false
  clause438 : p 92 = false ∨ p 56 = false ∨ p 95 = false ∨ p 99 = false
  clause439 : p 92 = false ∨ p 56 = false ∨ p 95 = false ∨ p 112 = false
  clause440 : p 92 = false ∨ p 82 = false ∨ p 91 = false ∨ p 99 = false
  clause441 : p 92 = false ∨ p 91 = false ∨ p 95 = false ∨ p 99 = false
  clause442 : p 92 = false ∨ p 91 = false ∨ p 95 = false ∨ p 112 = false
  clause443 : p 92 = false ∨ p 91 = false ∨ p 99 = false ∨ p 112 = false
  clause444 : p 211 = false ∨ p 93 = true
  clause445 : p 93 = false ∨ p 91 = true ∨ p 95 = true ∨ p 100 = true
  clause446 : p 93 = false ∨ p 211 = true ∨ p 95 = true ∨ p 100 = true
  clause447 : p 93 = false ∨ p 211 = true ∨ p 91 = true ∨ p 100 = true
  clause448 : p 93 = false ∨ p 211 = true ∨ p 91 = true ∨ p 95 = true
structure Block14 (p : Nat → Bool) : Prop where
  clause449 : p 94 = false ∨ p 212 = true ∨ p 84 = true ∨ p 95 = true ∨ p 114 = true
  clause450 : p 94 = false ∨ p 212 = true ∨ p 58 = true ∨ p 84 = true ∨ p 95 = true
  clause451 : p 95 = false ∨ p 85 = false ∨ p 92 = false ∨ p 93 = false
  clause452 : p 95 = false ∨ p 85 = false ∨ p 92 = false ∨ p 94 = false
  clause453 : p 95 = false ∨ p 85 = false ∨ p 93 = false ∨ p 94 = false
  clause454 : p 95 = false ∨ p 92 = false ∨ p 93 = false ∨ p 94 = false
  clause455 : p 95 = false ∨ p 213 = true ∨ p 92 = true ∨ p 93 = true ∨ p 94 = true
  clause456 : p 95 = false ∨ p 213 = true ∨ p 85 = true ∨ p 92 = true ∨ p 94 = true
  clause457 : p 96 = false ∨ p 59 = false ∨ p 86 = false ∨ p 97 = false
  clause458 : p 96 = false ∨ p 59 = false ∨ p 86 = false ∨ p 98 = false
  clause459 : p 96 = false ∨ p 59 = false ∨ p 86 = false ∨ p 115 = false
  clause460 : p 96 = false ∨ p 59 = false ∨ p 97 = false ∨ p 98 = false
  clause461 : p 96 = false ∨ p 59 = false ∨ p 97 = false ∨ p 115 = false
  clause462 : p 96 = false ∨ p 59 = false ∨ p 98 = false ∨ p 115 = false
  clause463 : p 96 = false ∨ p 86 = false ∨ p 97 = false ∨ p 98 = false
  clause464 : p 96 = false ∨ p 86 = false ∨ p 97 = false ∨ p 115 = false
  clause465 : p 96 = false ∨ p 86 = false ∨ p 98 = false ∨ p 115 = false
  clause466 : p 96 = false ∨ p 97 = false ∨ p 98 = false ∨ p 115 = false
  clause467 : p 96 = false ∨ p 214 = true ∨ p 86 = true ∨ p 97 = true ∨ p 98 = true ∨ p 115 = true
  clause468 : p 97 = false ∨ p 87 = false ∨ p 91 = false ∨ p 99 = false
  clause469 : p 97 = false ∨ p 87 = false ∨ p 96 = false ∨ p 100 = false
  clause470 : p 97 = false ∨ p 87 = false ∨ p 99 = false ∨ p 100 = false
  clause471 : p 97 = false ∨ p 215 = true ∨ p 91 = true ∨ p 96 = true ∨ p 99 = true ∨ p 100 = true
  clause472 : p 97 = false ∨ p 215 = true ∨ p 87 = true ∨ p 96 = true ∨ p 99 = true ∨ p 100 = true
  clause473 : p 97 = false ∨ p 215 = true ∨ p 87 = true ∨ p 91 = true ∨ p 99 = true ∨ p 100 = true
  clause474 : p 98 = false ∨ p 29 = true ∨ p 88 = true ∨ p 96 = true ∨ p 99 = true
  clause475 : p 98 = false ∨ p 29 = false ∨ p 88 = false ∨ p 96 = false
  clause476 : p 98 = false ∨ p 216 = true ∨ p 88 = true ∨ p 96 = true ∨ p 99 = true
  clause477 : p 98 = false ∨ p 216 = true ∨ p 29 = true ∨ p 96 = true ∨ p 99 = true
  clause478 : p 98 = false ∨ p 216 = true ∨ p 29 = true ∨ p 88 = true ∨ p 99 = true
  clause479 : p 98 = false ∨ p 216 = true ∨ p 29 = true ∨ p 88 = true ∨ p 96 = true
  clause480 : p 99 = false ∨ p 92 = false ∨ p 97 = false ∨ p 98 = false
structure Block15 (p : Nat → Bool) : Prop where
  clause481 : p 99 = false ∨ p 217 = true ∨ p 92 = true ∨ p 97 = true
  clause482 : p 100 = false ∨ p 218 = true ∨ p 97 = true
  clause483 : p 100 = false ∨ p 218 = true ∨ p 93 = true
  clause484 : p 101 = false ∨ p 65 = false ∨ p 81 = false ∨ p 102 = false
  clause485 : p 101 = false ∨ p 65 = false ∨ p 81 = false ∨ p 106 = false
  clause486 : p 101 = false ∨ p 65 = false ∨ p 102 = false ∨ p 106 = false
  clause487 : p 101 = false ∨ p 81 = false ∨ p 102 = false ∨ p 106 = false
  clause488 : p 101 = false ∨ p 219 = true ∨ p 65 = true ∨ p 102 = true ∨ p 106 = true
  clause489 : p 101 = false ∨ p 219 = true ∨ p 65 = true ∨ p 81 = true ∨ p 106 = true
  clause490 : p 101 = false ∨ p 219 = true ∨ p 65 = true ∨ p 81 = true ∨ p 102 = true
  clause491 : p 102 = false ∨ p 82 = false ∨ p 101 = false ∨ p 112 = false
  clause492 : p 102 = false ∨ p 82 = false ∨ p 107 = false ∨ p 112 = false
  clause493 : p 102 = false ∨ p 220 = true ∨ p 101 = true ∨ p 107 = true ∨ p 112 = true
  clause494 : p 102 = false ∨ p 220 = true ∨ p 82 = true ∨ p 107 = true ∨ p 112 = true
  clause495 : p 102 = false ∨ p 220 = true ∨ p 82 = true ∨ p 101 = true ∨ p 112 = true
  clause496 : p 102 = false ∨ p 220 = true ∨ p 82 = true ∨ p 101 = true ∨ p 107 = true
  clause497 : p 103 = false ∨ p 83 = false ∨ p 104 = false ∨ p 113 = false
  clause498 : p 104 = false ∨ p 103 = true ∨ p 108 = true
  clause499 : p 104 = false ∨ p 222 = true ∨ p 108 = true
  clause500 : p 104 = false ∨ p 222 = true ∨ p 103 = true
  clause501 : p 105 = false ∨ p 223 = true ∨ p 38 = true ∨ p 87 = true ∨ p 107 = true ∨ p 108 = true
  clause502 : p 105 = false ∨ p 223 = true ∨ p 38 = true ∨ p 69 = true ∨ p 107 = true ∨ p 108 = true
  clause503 : p 106 = false ∨ p 70 = true ∨ p 88 = true ∨ p 101 = true ∨ p 107 = true
  clause504 : p 106 = false ∨ p 70 = false ∨ p 88 = false ∨ p 107 = false
  clause505 : p 106 = false ∨ p 224 = true ∨ p 88 = true ∨ p 101 = true ∨ p 107 = true
  clause506 : p 106 = false ∨ p 224 = true ∨ p 70 = true ∨ p 101 = true ∨ p 107 = true
  clause507 : p 106 = false ∨ p 224 = true ∨ p 70 = true ∨ p 88 = true ∨ p 107 = true
  clause508 : p 106 = false ∨ p 224 = true ∨ p 70 = true ∨ p 88 = true ∨ p 101 = true
  clause509 : p 107 = false ∨ p 102 = false ∨ p 105 = false ∨ p 106 = false
  clause510 : p 107 = false ∨ p 102 = false ∨ p 105 = false ∨ p 109 = false
  clause511 : p 107 = false ∨ p 102 = false ∨ p 106 = false ∨ p 109 = false
  clause512 : p 107 = false ∨ p 105 = false ∨ p 106 = false ∨ p 109 = false
structure Block16 (p : Nat → Bool) : Prop where
  clause513 : p 108 = false ∨ p 104 = false ∨ p 105 = false ∨ p 109 = false
  clause514 : p 108 = false ∨ p 226 = true ∨ p 105 = true ∨ p 109 = true
  clause515 : p 108 = false ∨ p 226 = true ∨ p 104 = true ∨ p 105 = true
  clause516 : p 227 = false ∨ p 109 = true
  clause517 : p 109 = false ∨ p 107 = false ∨ p 108 = false ∨ p 118 = false
  clause518 : p 109 = false ∨ p 227 = true ∨ p 107 = true ∨ p 108 = true
  clause519 : p 110 = false ∨ p 111 = false ∨ p 113 = false ∨ p 115 = false
  clause520 : p 110 = false ∨ p 228 = true ∨ p 113 = true ∨ p 115 = true
  clause521 : p 111 = false ∨ p 91 = true ∨ p 110 = true ∨ p 112 = true
  clause522 : p 111 = false ∨ p 229 = true ∨ p 110 = true ∨ p 112 = true
  clause523 : p 111 = false ∨ p 229 = true ∨ p 91 = true ∨ p 112 = true
  clause524 : p 111 = false ∨ p 229 = true ∨ p 91 = true ∨ p 110 = true
  clause525 : p 112 = false ∨ p 92 = false ∨ p 102 = false ∨ p 111 = false
  clause526 : p 112 = false ∨ p 230 = true ∨ p 92 = true ∨ p 111 = true
  clause527 : p 112 = false ∨ p 230 = true ∨ p 92 = true ∨ p 102 = true
  clause528 : p 113 = false ∨ p 103 = false ∨ p 110 = false ∨ p 114 = false
  clause529 : p 113 = false ∨ p 231 = true ∨ p 110 = true ∨ p 114 = true ∨ p 116 = true
  clause530 : p 113 = false ∨ p 231 = true ∨ p 103 = true ∨ p 110 = true ∨ p 116 = true
  clause531 : p 114 = false ∨ p 43 = false ∨ p 113 = false ∨ p 117 = false
  clause532 : p 114 = false ∨ p 94 = false ∨ p 113 = false ∨ p 117 = false
  clause533 : p 115 = false ∨ p 45 = true ∨ p 96 = true ∨ p 110 = true ∨ p 116 = true
  clause534 : p 115 = false ∨ p 45 = false ∨ p 96 = false ∨ p 110 = false
  clause535 : p 115 = false ∨ p 45 = false ∨ p 96 = false ∨ p 116 = false
  clause536 : p 115 = false ∨ p 233 = true ∨ p 96 = true ∨ p 110 = true ∨ p 116 = true
  clause537 : p 115 = false ∨ p 233 = true ∨ p 45 = true ∨ p 110 = true ∨ p 116 = true
  clause538 : p 115 = false ∨ p 233 = true ∨ p 45 = true ∨ p 96 = true ∨ p 116 = true
  clause539 : p 116 = false ∨ p 113 = false ∨ p 115 = false ∨ p 117 = false
  clause540 : p 117 = false ∨ p 235 = true ∨ p 116 = true ∨ p 118 = true
  clause541 : p 117 = false ∨ p 235 = true ∨ p 114 = true ∨ p 118 = true
  clause542 : p 117 = false ∨ p 235 = true ∨ p 114 = true ∨ p 116 = true
  clause543 : p 118 = false ∨ p 236 = true ∨ p 109 = true
  clause544 : p 119 = false
structure Block17 (p : Nat → Bool) : Prop where
  clause545 : p 120 = false
  clause546 : p 122 = false
  clause547 : p 124 = false
  clause548 : p 126 = false
  clause549 : p 127 = false
  clause550 : p 128 = false
  clause551 : p 131 = false
  clause552 : p 133 = false
  clause553 : p 134 = false
  clause554 : p 136 = false
  clause555 : p 137 = false
  clause556 : p 140 = false
  clause557 : p 142 = false
  clause558 : p 145 = false
  clause559 : p 147 = false
  clause560 : p 148 = false
  clause561 : p 150 = false
  clause562 : p 151 = false
  clause563 : p 153 = false
  clause564 : p 156 = false
  clause565 : p 157 = false
  clause566 : p 159 = false
  clause567 : p 162 = false
  clause568 : p 163 = false
  clause569 : p 166 = false
  clause570 : p 167 = false
  clause571 : p 168 = false
  clause572 : p 171 = false
  clause573 : p 174 = false
  clause574 : p 176 = false
  clause575 : p 178 = false
  clause576 : p 181 = false
structure Block18 (p : Nat → Bool) : Prop where
  clause577 : p 184 = false
  clause578 : p 187 = false
  clause579 : p 188 = false
  clause580 : p 189 = false
  clause581 : p 191 = false
  clause582 : p 193 = false
  clause583 : p 196 = false
  clause584 : p 197 = false
  clause585 : p 198 = false
  clause586 : p 200 = false
  clause587 : p 202 = false
  clause588 : p 205 = false
  clause589 : p 206 = false
  clause590 : p 207 = false
  clause591 : p 209 = false
  clause592 : p 213 = false
  clause593 : p 214 = false
  clause594 : p 217 = false
  clause595 : p 218 = false
  clause596 : p 219 = false
  clause597 : p 221 = false
  clause598 : p 225 = false
  clause599 : p 226 = false
  clause600 : p 228 = false
  clause601 : p 230 = false
  clause602 : p 232 = false
  clause603 : p 234 = false
  clause604 : p 236 = false
  clause605 : p 121 = false ∨ p 237 = true
  clause606 : p 237 = false ∨ p 239 = true
  clause607 : p 123 = false ∨ p 241 = true
  clause608 : p 125 = false ∨ p 243 = true
structure Block19 (p : Nat → Bool) : Prop where
  clause609 : p 243 = false ∨ p 245 = true
  clause610 : p 241 = false ∨ p 245 = true
  clause611 : p 245 = false ∨ p 247 = true
  clause612 : p 239 = false ∨ p 247 = true
  clause613 : p 130 = false ∨ p 253 = true
  clause614 : p 129 = false ∨ p 253 = true
  clause615 : p 132 = false ∨ p 255 = true
  clause616 : p 255 = false ∨ p 257 = true
  clause617 : p 253 = false ∨ p 257 = true
  clause618 : p 257 = false ∨ p 259 = true
  clause619 : p 259 = false ∨ p 261 = true
  clause620 : p 247 = false ∨ p 261 = true
  clause621 : p 135 = false ∨ p 263 = true
  clause622 : p 263 = false ∨ p 265 = true
  clause623 : p 139 = false ∨ p 269 = true
  clause624 : p 138 = false ∨ p 269 = true
  clause625 : p 138 = false ∨ p 139 = false ∨ p 270 = true
  clause626 : p 269 = false ∨ p 271 = true
  clause627 : p 270 = false ∨ p 272 = true
  clause628 : p 271 = false ∨ p 273 = true
  clause629 : p 272 = false ∨ p 274 = true
  clause630 : p 265 = false ∨ p 273 = true
  clause631 : p 265 = false ∨ p 271 = false ∨ p 274 = true
  clause632 : p 141 = false ∨ p 275 = true
  clause633 : p 143 = false ∨ p 277 = true
  clause634 : p 277 = false ∨ p 279 = true
  clause635 : p 275 = false ∨ p 279 = true
  clause636 : p 144 = false ∨ p 281 = true
  clause637 : p 146 = false ∨ p 283 = true
  clause638 : p 283 = false ∨ p 285 = true
  clause639 : p 281 = false ∨ p 285 = true
  clause640 : p 281 = false ∨ p 283 = false ∨ p 286 = true
structure Block20 (p : Nat → Bool) : Prop where
  clause641 : p 285 = false ∨ p 287 = true
  clause642 : p 286 = false ∨ p 288 = true
  clause643 : p 279 = false ∨ p 287 = true
  clause644 : p 279 = false ∨ p 285 = false ∨ p 288 = true
  clause645 : p 287 = false ∨ p 289 = true
  clause646 : p 288 = false ∨ p 290 = true
  clause647 : p 273 = false ∨ p 289 = true
  clause648 : p 273 = false ∨ p 287 = false ∨ p 290 = true
  clause649 : p 274 = false ∨ p 290 = true
  clause650 : p 289 = false ∨ p 291 = true
  clause651 : p 290 = false ∨ p 292 = true
  clause652 : p 261 = false ∨ p 291 = true
  clause653 : p 261 = false ∨ p 289 = false ∨ p 292 = true
  clause654 : p 149 = false ∨ p 293 = true
  clause655 : p 293 = false ∨ p 295 = true
  clause656 : p 152 = false ∨ p 297 = true
  clause657 : p 154 = false ∨ p 299 = true
  clause658 : p 299 = false ∨ p 301 = true
  clause659 : p 297 = false ∨ p 301 = true
  clause660 : p 301 = false ∨ p 303 = true
  clause661 : p 295 = false ∨ p 303 = true
  clause662 : p 155 = false ∨ p 307 = true
  clause663 : p 158 = false ∨ p 309 = true
  clause664 : p 161 = false ∨ p 311 = true
  clause665 : p 160 = false ∨ p 311 = true
  clause666 : p 311 = false ∨ p 313 = true
  clause667 : p 309 = false ∨ p 313 = true
  clause668 : p 309 = false ∨ p 311 = false ∨ p 314 = true
  clause669 : p 313 = false ∨ p 315 = true
  clause670 : p 314 = false ∨ p 316 = true
  clause671 : p 307 = false ∨ p 315 = true
  clause672 : p 315 = false ∨ p 317 = true
structure Block21 (p : Nat → Bool) : Prop where
  clause673 : p 316 = false ∨ p 318 = true
  clause674 : p 303 = false ∨ p 317 = true
  clause675 : p 303 = false ∨ p 315 = false ∨ p 318 = true
  clause676 : p 164 = false ∨ p 319 = true
  clause677 : p 319 = false ∨ p 321 = true
  clause678 : p 165 = false ∨ p 323 = true
  clause679 : p 323 = false ∨ p 327 = true
  clause680 : p 327 = false ∨ p 329 = true
  clause681 : p 321 = false ∨ p 329 = true
  clause682 : p 321 = false ∨ p 327 = false ∨ p 330 = true
  clause683 : p 170 = false ∨ p 331 = true
  clause684 : p 169 = false ∨ p 331 = true
  clause685 : p 169 = false ∨ p 170 = false ∨ p 332 = true
  clause686 : p 172 = false ∨ p 333 = true
  clause687 : p 333 = false ∨ p 335 = true
  clause688 : p 331 = false ∨ p 335 = true
  clause689 : p 331 = false ∨ p 333 = false ∨ p 336 = true
  clause690 : p 332 = false ∨ p 336 = true
  clause691 : p 173 = false ∨ p 337 = true
  clause692 : p 175 = false ∨ p 339 = true
  clause693 : p 339 = false ∨ p 341 = true
  clause694 : p 337 = false ∨ p 341 = true
  clause695 : p 341 = false ∨ p 343 = true
  clause696 : p 335 = false ∨ p 343 = true
  clause697 : p 335 = false ∨ p 341 = false ∨ p 344 = true
  clause698 : p 336 = false ∨ p 344 = true
  clause699 : p 343 = false ∨ p 345 = true
  clause700 : p 344 = false ∨ p 346 = true
  clause701 : p 329 = false ∨ p 345 = true
  clause702 : p 329 = false ∨ p 343 = false ∨ p 346 = true
  clause703 : p 330 = false ∨ p 346 = true
  clause704 : p 345 = false ∨ p 347 = true
structure Block22 (p : Nat → Bool) : Prop where
  clause705 : p 346 = false ∨ p 348 = true
  clause706 : p 317 = false ∨ p 347 = true
  clause707 : p 317 = false ∨ p 345 = false ∨ p 348 = true
  clause708 : p 318 = false ∨ p 348 = true
  clause709 : p 347 = false ∨ p 349 = true
  clause710 : p 348 = false ∨ p 350 = true
  clause711 : p 291 = false ∨ p 349 = true
  clause712 : p 291 = false ∨ p 347 = false ∨ p 350 = true
  clause713 : p 292 = false ∨ p 350 = true
  clause714 : p 179 = false ∨ p 351 = true
  clause715 : p 351 = false ∨ p 353 = true
  clause716 : p 177 = false ∨ p 353 = true
  clause717 : p 177 = false ∨ p 351 = false ∨ p 354 = true
  clause718 : p 182 = false ∨ p 355 = true
  clause719 : p 183 = false ∨ p 357 = true
  clause720 : p 357 = false ∨ p 359 = true
  clause721 : p 355 = false ∨ p 359 = true
  clause722 : p 359 = false ∨ p 361 = true
  clause723 : p 353 = false ∨ p 361 = true
  clause724 : p 354 = false ∨ p 362 = true
  clause725 : p 186 = false ∨ p 363 = true
  clause726 : p 363 = false ∨ p 365 = true
  clause727 : p 185 = false ∨ p 365 = true
  clause728 : p 190 = false ∨ p 369 = true
  clause729 : p 369 = false ∨ p 371 = true
  clause730 : p 371 = false ∨ p 373 = true
  clause731 : p 365 = false ∨ p 373 = true
  clause732 : p 365 = false ∨ p 371 = false ∨ p 374 = true
  clause733 : p 373 = false ∨ p 375 = true
  clause734 : p 374 = false ∨ p 376 = true
  clause735 : p 361 = false ∨ p 375 = true
  clause736 : p 361 = false ∨ p 373 = false ∨ p 376 = true
structure Block23 (p : Nat → Bool) : Prop where
  clause737 : p 362 = false ∨ p 376 = true
  clause738 : p 194 = false ∨ p 377 = true
  clause739 : p 377 = false ∨ p 379 = true
  clause740 : p 192 = false ∨ p 379 = true
  clause741 : p 195 = false ∨ p 381 = true
  clause742 : p 381 = false ∨ p 385 = true
  clause743 : p 385 = false ∨ p 387 = true
  clause744 : p 379 = false ∨ p 387 = true
  clause745 : p 199 = false ∨ p 389 = true
  clause746 : p 201 = false ∨ p 391 = true
  clause747 : p 391 = false ∨ p 393 = true
  clause748 : p 389 = false ∨ p 393 = true
  clause749 : p 204 = false ∨ p 395 = true
  clause750 : p 203 = false ∨ p 395 = true
  clause751 : p 395 = false ∨ p 399 = true
  clause752 : p 399 = false ∨ p 401 = true
  clause753 : p 393 = false ∨ p 401 = true
  clause754 : p 401 = false ∨ p 403 = true
  clause755 : p 387 = false ∨ p 403 = true
  clause756 : p 387 = false ∨ p 401 = false ∨ p 404 = true
  clause757 : p 403 = false ∨ p 405 = true
  clause758 : p 404 = false ∨ p 406 = true
  clause759 : p 375 = false ∨ p 405 = true
  clause760 : p 375 = false ∨ p 403 = false ∨ p 406 = true
  clause761 : p 376 = false ∨ p 406 = true
  clause762 : p 208 = false ∨ p 407 = true
  clause763 : p 407 = false ∨ p 409 = true
  clause764 : p 211 = false ∨ p 411 = true
  clause765 : p 210 = false ∨ p 411 = true
  clause766 : p 212 = false ∨ p 413 = true
  clause767 : p 413 = false ∨ p 415 = true
  clause768 : p 411 = false ∨ p 415 = true
structure Block24 (p : Nat → Bool) : Prop where
  clause769 : p 411 = false ∨ p 413 = false ∨ p 416 = true
  clause770 : p 415 = false ∨ p 417 = true
  clause771 : p 416 = false ∨ p 418 = true
  clause772 : p 409 = false ∨ p 417 = true
  clause773 : p 409 = false ∨ p 415 = false ∨ p 418 = true
  clause774 : p 215 = false ∨ p 419 = true
  clause775 : p 216 = false ∨ p 421 = true
  clause776 : p 421 = false ∨ p 423 = true
  clause777 : p 419 = false ∨ p 423 = true
  clause778 : p 220 = false ∨ p 427 = true
  clause779 : p 427 = false ∨ p 429 = true
  clause780 : p 429 = false ∨ p 431 = true
  clause781 : p 423 = false ∨ p 431 = true
  clause782 : p 431 = false ∨ p 433 = true
  clause783 : p 417 = false ∨ p 433 = true
  clause784 : p 417 = false ∨ p 431 = false ∨ p 434 = true
  clause785 : p 418 = false ∨ p 434 = true
  clause786 : p 224 = false ∨ p 435 = true
  clause787 : p 223 = false ∨ p 435 = true
  clause788 : p 435 = false ∨ p 437 = true
  clause789 : p 222 = false ∨ p 437 = true
  clause790 : p 227 = false ∨ p 441 = true
  clause791 : p 441 = false ∨ p 443 = true
  clause792 : p 443 = false ∨ p 445 = true
  clause793 : p 437 = false ∨ p 445 = true
  clause794 : p 437 = false ∨ p 443 = false ∨ p 446 = true
  clause795 : p 229 = false ∨ p 447 = true
  clause796 : p 231 = false ∨ p 449 = true
  clause797 : p 449 = false ∨ p 451 = true
  clause798 : p 447 = false ∨ p 451 = true
  clause799 : p 447 = false ∨ p 449 = false ∨ p 452 = true
  clause800 : p 233 = false ∨ p 453 = true
structure Block25 (p : Nat → Bool) : Prop where
  clause801 : p 235 = false ∨ p 455 = true
  clause802 : p 455 = false ∨ p 457 = true
  clause803 : p 453 = false ∨ p 457 = true
  clause804 : p 453 = false ∨ p 455 = false ∨ p 458 = true
  clause805 : p 457 = false ∨ p 459 = true
  clause806 : p 458 = false ∨ p 460 = true
  clause807 : p 451 = false ∨ p 459 = true
  clause808 : p 451 = false ∨ p 457 = false ∨ p 460 = true
  clause809 : p 452 = false ∨ p 460 = true
  clause810 : p 459 = false ∨ p 461 = true
  clause811 : p 460 = false ∨ p 462 = true
  clause812 : p 445 = false ∨ p 461 = true
  clause813 : p 445 = false ∨ p 459 = false ∨ p 462 = true
  clause814 : p 446 = false ∨ p 462 = true
  clause815 : p 461 = false ∨ p 463 = true
  clause816 : p 462 = false ∨ p 464 = true
  clause817 : p 433 = false ∨ p 463 = true
  clause818 : p 433 = false ∨ p 461 = false ∨ p 464 = true
  clause819 : p 434 = false ∨ p 464 = true
  clause820 : p 463 = false ∨ p 465 = true
  clause821 : p 464 = false ∨ p 466 = true
  clause822 : p 405 = false ∨ p 465 = true
  clause823 : p 405 = false ∨ p 463 = false ∨ p 466 = true
  clause824 : p 406 = false ∨ p 466 = true
  clause825 : p 466 = false ∨ p 468 = true
  clause826 : p 349 = false ∨ p 465 = false ∨ p 468 = true
  clause827 : p 350 = false ∨ p 468 = true
  clause828 : p 468 = false
  clause829 : p 119 = true ∨ p 120 = true ∨ p 121 = true ∨ p 122 = true ∨ p 123 = true ∨ p 124 = true ∨ p 125 = true ∨ p 126 = true ∨ p 127 = true ∨ p 128 = true ∨ p 129 = true ∨ p 130 = true ∨ p 131 = true ∨ p 132 = true ∨ p 133 = true ∨ p 134 = true ∨ p 135 = true ∨ p 136 = true ∨ p 137 = true ∨ p 138 = true ∨ p 139 = true ∨ p 140 = true ∨ p 141 = true ∨ p 142 = true ∨ p 143 = true ∨ p 144 = true ∨ p 145 = true ∨ p 146 = true ∨ p 147 = true ∨ p 148 = true ∨ p 149 = true ∨ p 150 = true ∨ p 151 = true ∨ p 152 = true ∨ p 153 = true ∨ p 154 = true ∨ p 155 = true ∨ p 156 = true ∨ p 157 = true ∨ p 158 = true ∨ p 159 = true ∨ p 160 = true ∨ p 161 = true ∨ p 162 = true ∨ p 163 = true ∨ p 164 = true ∨ p 165 = true ∨ p 166 = true ∨ p 167 = true ∨ p 168 = true ∨ p 169 = true ∨ p 170 = true ∨ p 171 = true ∨ p 172 = true ∨ p 173 = true ∨ p 174 = true ∨ p 175 = true ∨ p 176 = true ∨ p 177 = true ∨ p 178 = true ∨ p 179 = true ∨ p 181 = true ∨ p 182 = true ∨ p 183 = true ∨ p 184 = true ∨ p 185 = true ∨ p 186 = true ∨ p 187 = true ∨ p 188 = true ∨ p 189 = true ∨ p 190 = true ∨ p 191 = true ∨ p 192 = true ∨ p 193 = true ∨ p 194 = true ∨ p 195 = true ∨ p 196 = true ∨ p 197 = true ∨ p 198 = true ∨ p 199 = true ∨ p 200 = true ∨ p 201 = true ∨ p 202 = true ∨ p 203 = true ∨ p 204 = true ∨ p 205 = true ∨ p 206 = true ∨ p 207 = true ∨ p 208 = true ∨ p 209 = true ∨ p 210 = true ∨ p 211 = true ∨ p 212 = true ∨ p 213 = true ∨ p 214 = true ∨ p 215 = true ∨ p 216 = true ∨ p 217 = true ∨ p 218 = true ∨ p 219 = true ∨ p 220 = true ∨ p 221 = true ∨ p 222 = true ∨ p 223 = true ∨ p 224 = true ∨ p 225 = true ∨ p 226 = true ∨ p 227 = true ∨ p 228 = true ∨ p 229 = true ∨ p 230 = true ∨ p 231 = true ∨ p 232 = true ∨ p 233 = true ∨ p 234 = true ∨ p 235 = true ∨ p 236 = true
  clause830 : p 7 = true ∨ p 1445 = true
  clause831 : p 5 = true ∨ p 1445 = true
  clause832 : p 5 = true ∨ p 7 = true ∨ p 1446 = true
structure Block26 (p : Nat → Bool) : Prop where
  clause833 : p 1445 = false ∨ p 1447 = true
  clause834 : p 1446 = false ∨ p 1448 = true
  clause835 : p 3 = true ∨ p 1447 = true
  clause836 : p 3 = true ∨ p 1445 = false ∨ p 1448 = true
  clause837 : p 3 = true ∨ p 1446 = false ∨ p 1449 = true
  clause838 : p 12 = true ∨ p 1450 = true
  clause839 : p 11 = true ∨ p 1450 = true
  clause840 : p 11 = true ∨ p 12 = true ∨ p 1451 = true
  clause841 : p 17 = true ∨ p 1452 = true
  clause842 : p 14 = true ∨ p 1452 = true
  clause843 : p 14 = true ∨ p 17 = true ∨ p 1453 = true
  clause844 : p 1452 = false ∨ p 1454 = true
  clause845 : p 1453 = false ∨ p 1455 = true
  clause846 : p 1450 = false ∨ p 1454 = true
  clause847 : p 1450 = false ∨ p 1452 = false ∨ p 1455 = true
  clause848 : p 1450 = false ∨ p 1453 = false ∨ p 1456 = true
  clause849 : p 1451 = false ∨ p 1455 = true
  clause850 : p 1451 = false ∨ p 1452 = false ∨ p 1456 = true
  clause851 : p 1451 = false ∨ p 1453 = false ∨ p 1457 = true
  clause852 : p 1454 = false ∨ p 1458 = true
  clause853 : p 1455 = false ∨ p 1459 = true
  clause854 : p 1456 = false ∨ p 1460 = true
  clause855 : p 1457 = false ∨ p 1461 = true
  clause856 : p 1447 = false ∨ p 1458 = true
  clause857 : p 1447 = false ∨ p 1454 = false ∨ p 1459 = true
  clause858 : p 1447 = false ∨ p 1455 = false ∨ p 1460 = true
  clause859 : p 1448 = false ∨ p 1459 = true
  clause860 : p 1448 = false ∨ p 1454 = false ∨ p 1460 = true
  clause861 : p 1448 = false ∨ p 1455 = false ∨ p 1461 = true
  clause862 : p 1448 = false ∨ p 1456 = false ∨ p 1462 = true
  clause863 : p 1449 = false ∨ p 1460 = true
  clause864 : p 1449 = false ∨ p 1454 = false ∨ p 1461 = true
structure Block27 (p : Nat → Bool) : Prop where
  clause865 : p 1449 = false ∨ p 1455 = false ∨ p 1462 = true
  clause866 : p 23 = true ∨ p 1465 = true
  clause867 : p 21 = true ∨ p 1465 = true
  clause868 : p 21 = true ∨ p 23 = true ∨ p 1466 = true
  clause869 : p 1465 = false ∨ p 1467 = true
  clause870 : p 1466 = false ∨ p 1468 = true
  clause871 : p 20 = true ∨ p 1467 = true
  clause872 : p 20 = true ∨ p 1465 = false ∨ p 1468 = true
  clause873 : p 20 = true ∨ p 1466 = false ∨ p 1469 = true
  clause874 : p 26 = true ∨ p 1470 = true
  clause875 : p 25 = true ∨ p 1470 = true
  clause876 : p 25 = true ∨ p 26 = true ∨ p 1471 = true
  clause877 : p 31 = true ∨ p 1472 = true
  clause878 : p 28 = true ∨ p 1472 = true
  clause879 : p 28 = true ∨ p 31 = true ∨ p 1473 = true
  clause880 : p 1472 = false ∨ p 1474 = true
  clause881 : p 1473 = false ∨ p 1475 = true
  clause882 : p 1470 = false ∨ p 1474 = true
  clause883 : p 1470 = false ∨ p 1472 = false ∨ p 1475 = true
  clause884 : p 1470 = false ∨ p 1473 = false ∨ p 1476 = true
  clause885 : p 1471 = false ∨ p 1475 = true
  clause886 : p 1471 = false ∨ p 1472 = false ∨ p 1476 = true
  clause887 : p 1474 = false ∨ p 1478 = true
  clause888 : p 1475 = false ∨ p 1479 = true
  clause889 : p 1476 = false ∨ p 1480 = true
  clause890 : p 1467 = false ∨ p 1478 = true
  clause891 : p 1467 = false ∨ p 1474 = false ∨ p 1479 = true
  clause892 : p 1467 = false ∨ p 1475 = false ∨ p 1480 = true
  clause893 : p 1467 = false ∨ p 1476 = false ∨ p 1481 = true
  clause894 : p 1468 = false ∨ p 1479 = true
  clause895 : p 1468 = false ∨ p 1474 = false ∨ p 1480 = true
  clause896 : p 1468 = false ∨ p 1475 = false ∨ p 1481 = true
structure Block28 (p : Nat → Bool) : Prop where
  clause897 : p 1468 = false ∨ p 1476 = false ∨ p 1482 = true
  clause898 : p 1469 = false ∨ p 1480 = true
  clause899 : p 1469 = false ∨ p 1474 = false ∨ p 1481 = true
  clause900 : p 1469 = false ∨ p 1475 = false ∨ p 1482 = true
  clause901 : p 1478 = false ∨ p 1485 = true
  clause902 : p 1479 = false ∨ p 1486 = true
  clause903 : p 1480 = false ∨ p 1487 = true
  clause904 : p 1481 = false ∨ p 1488 = true
  clause905 : p 1482 = false ∨ p 1489 = true
  clause906 : p 1458 = false ∨ p 1485 = true
  clause907 : p 1458 = false ∨ p 1478 = false ∨ p 1486 = true
  clause908 : p 1458 = false ∨ p 1479 = false ∨ p 1487 = true
  clause909 : p 1458 = false ∨ p 1480 = false ∨ p 1488 = true
  clause910 : p 1458 = false ∨ p 1481 = false ∨ p 1489 = true
  clause911 : p 1459 = false ∨ p 1486 = true
  clause912 : p 1459 = false ∨ p 1478 = false ∨ p 1487 = true
  clause913 : p 1459 = false ∨ p 1479 = false ∨ p 1488 = true
  clause914 : p 1459 = false ∨ p 1480 = false ∨ p 1489 = true
  clause915 : p 1459 = false ∨ p 1481 = false ∨ p 1490 = true
  clause916 : p 1460 = false ∨ p 1487 = true
  clause917 : p 1460 = false ∨ p 1478 = false ∨ p 1488 = true
  clause918 : p 1460 = false ∨ p 1479 = false ∨ p 1489 = true
  clause919 : p 1460 = false ∨ p 1480 = false ∨ p 1490 = true
  clause920 : p 1461 = false ∨ p 1488 = true
  clause921 : p 1461 = false ∨ p 1478 = false ∨ p 1489 = true
  clause922 : p 1461 = false ∨ p 1479 = false ∨ p 1490 = true
  clause923 : p 1462 = false ∨ p 1478 = false ∨ p 1490 = true
  clause924 : p 37 = true ∨ p 1499 = true
  clause925 : p 36 = true ∨ p 1499 = true
  clause926 : p 36 = true ∨ p 37 = true ∨ p 1500 = true
  clause927 : p 1499 = false ∨ p 1501 = true
  clause928 : p 1500 = false ∨ p 1502 = true
structure Block29 (p : Nat → Bool) : Prop where
  clause929 : p 34 = true ∨ p 1501 = true
  clause930 : p 34 = true ∨ p 1499 = false ∨ p 1502 = true
  clause931 : p 42 = true ∨ p 1504 = true
  clause932 : p 40 = true ∨ p 1504 = true
  clause933 : p 40 = true ∨ p 42 = true ∨ p 1505 = true
  clause934 : p 46 = true ∨ p 1506 = true
  clause935 : p 43 = true ∨ p 1506 = true
  clause936 : p 43 = true ∨ p 46 = true ∨ p 1507 = true
  clause937 : p 1506 = false ∨ p 1508 = true
  clause938 : p 1507 = false ∨ p 1509 = true
  clause939 : p 1504 = false ∨ p 1508 = true
  clause940 : p 1504 = false ∨ p 1506 = false ∨ p 1509 = true
  clause941 : p 1504 = false ∨ p 1507 = false ∨ p 1510 = true
  clause942 : p 1505 = false ∨ p 1509 = true
  clause943 : p 1505 = false ∨ p 1506 = false ∨ p 1510 = true
  clause944 : p 1505 = false ∨ p 1507 = false ∨ p 1511 = true
  clause945 : p 1508 = false ∨ p 1512 = true
  clause946 : p 1509 = false ∨ p 1513 = true
  clause947 : p 1510 = false ∨ p 1514 = true
  clause948 : p 1511 = false ∨ p 1515 = true
  clause949 : p 1501 = false ∨ p 1512 = true
  clause950 : p 1501 = false ∨ p 1508 = false ∨ p 1513 = true
  clause951 : p 1501 = false ∨ p 1509 = false ∨ p 1514 = true
  clause952 : p 1501 = false ∨ p 1510 = false ∨ p 1515 = true
  clause953 : p 1501 = false ∨ p 1511 = false ∨ p 1516 = true
  clause954 : p 1502 = false ∨ p 1513 = true
  clause955 : p 1502 = false ∨ p 1508 = false ∨ p 1514 = true
  clause956 : p 1502 = false ∨ p 1511 = false ∨ p 1517 = true
  clause957 : p 52 = true ∨ p 1519 = true
  clause958 : p 51 = true ∨ p 1519 = true
  clause959 : p 51 = true ∨ p 52 = true ∨ p 1520 = true
  clause960 : p 1519 = false ∨ p 1521 = true
structure Block30 (p : Nat → Bool) : Prop where
  clause961 : p 1520 = false ∨ p 1522 = true
  clause962 : p 47 = true ∨ p 1521 = true
  clause963 : p 47 = true ∨ p 1519 = false ∨ p 1522 = true
  clause964 : p 47 = true ∨ p 1520 = false ∨ p 1523 = true
  clause965 : p 55 = true ∨ p 1524 = true
  clause966 : p 54 = true ∨ p 1524 = true
  clause967 : p 54 = true ∨ p 55 = true ∨ p 1525 = true
  clause968 : p 59 = true ∨ p 1526 = true
  clause969 : p 57 = true ∨ p 1526 = true
  clause970 : p 57 = true ∨ p 59 = true ∨ p 1527 = true
  clause971 : p 1526 = false ∨ p 1528 = true
  clause972 : p 1527 = false ∨ p 1529 = true
  clause973 : p 1524 = false ∨ p 1528 = true
  clause974 : p 1524 = false ∨ p 1526 = false ∨ p 1529 = true
  clause975 : p 1524 = false ∨ p 1527 = false ∨ p 1530 = true
  clause976 : p 1525 = false ∨ p 1529 = true
  clause977 : p 1525 = false ∨ p 1526 = false ∨ p 1530 = true
  clause978 : p 1525 = false ∨ p 1527 = false ∨ p 1531 = true
  clause979 : p 1528 = false ∨ p 1532 = true
  clause980 : p 1529 = false ∨ p 1533 = true
  clause981 : p 1530 = false ∨ p 1534 = true
  clause982 : p 1531 = false ∨ p 1535 = true
  clause983 : p 1521 = false ∨ p 1528 = false ∨ p 1533 = true
  clause984 : p 1521 = false ∨ p 1529 = false ∨ p 1534 = true
  clause985 : p 1521 = false ∨ p 1530 = false ∨ p 1535 = true
  clause986 : p 1521 = false ∨ p 1531 = false ∨ p 1536 = true
  clause987 : p 1522 = false ∨ p 1528 = false ∨ p 1534 = true
  clause988 : p 1522 = false ∨ p 1529 = false ∨ p 1535 = true
  clause989 : p 1522 = false ∨ p 1530 = false ∨ p 1536 = true
  clause990 : p 1523 = false ∨ p 1528 = false ∨ p 1535 = true
  clause991 : p 1523 = false ∨ p 1529 = false ∨ p 1536 = true
  clause992 : p 1535 = false ∨ p 1542 = true
structure Block31 (p : Nat → Bool) : Prop where
  clause993 : p 1512 = false ∨ p 1532 = false ∨ p 1540 = true
  clause994 : p 1512 = false ∨ p 1533 = false ∨ p 1541 = true
  clause995 : p 1512 = false ∨ p 1534 = false ∨ p 1542 = true
  clause996 : p 1512 = false ∨ p 1535 = false ∨ p 1543 = true
  clause997 : p 1512 = false ∨ p 1536 = false ∨ p 1544 = true
  clause998 : p 1513 = false ∨ p 1533 = false ∨ p 1542 = true
  clause999 : p 1513 = false ∨ p 1534 = false ∨ p 1543 = true
  clause1000 : p 1513 = false ∨ p 1535 = false ∨ p 1544 = true
  clause1001 : p 1513 = false ∨ p 1536 = false ∨ p 1545 = true
  clause1002 : p 1514 = false ∨ p 1532 = false ∨ p 1542 = true
  clause1003 : p 1514 = false ∨ p 1533 = false ∨ p 1543 = true
  clause1004 : p 1514 = false ∨ p 1534 = false ∨ p 1544 = true
  clause1005 : p 1514 = false ∨ p 1535 = false ∨ p 1545 = true
  clause1006 : p 1514 = false ∨ p 1536 = false ∨ p 1546 = true
  clause1007 : p 1515 = false ∨ p 1533 = false ∨ p 1544 = true
  clause1008 : p 1515 = false ∨ p 1534 = false ∨ p 1545 = true
  clause1009 : p 1516 = false ∨ p 1533 = false ∨ p 1545 = true
  clause1010 : p 1517 = false ∨ p 1533 = false ∨ p 1546 = true
  clause1011 : p 1545 = false ∨ p 1559 = true
  clause1012 : p 1485 = false ∨ p 1541 = false ∨ p 1556 = true
  clause1013 : p 1485 = false ∨ p 1542 = false ∨ p 1557 = true
  clause1014 : p 1485 = false ∨ p 1543 = false ∨ p 1558 = true
  clause1015 : p 1485 = false ∨ p 1544 = false ∨ p 1559 = true
  clause1016 : p 1485 = false ∨ p 1545 = false ∨ p 1560 = true
  clause1017 : p 1485 = false ∨ p 1546 = false ∨ p 1561 = true
  clause1018 : p 1486 = false ∨ p 1541 = false ∨ p 1557 = true
  clause1019 : p 1486 = false ∨ p 1542 = false ∨ p 1558 = true
  clause1020 : p 1486 = false ∨ p 1543 = false ∨ p 1559 = true
  clause1021 : p 1486 = false ∨ p 1544 = false ∨ p 1560 = true
  clause1022 : p 1486 = false ∨ p 1545 = false ∨ p 1561 = true
  clause1023 : p 1487 = false ∨ p 1541 = false ∨ p 1558 = true
  clause1024 : p 1487 = false ∨ p 1542 = false ∨ p 1559 = true
structure Block32 (p : Nat → Bool) : Prop where
  clause1025 : p 1487 = false ∨ p 1543 = false ∨ p 1560 = true
  clause1026 : p 1487 = false ∨ p 1544 = false ∨ p 1561 = true
  clause1027 : p 1487 = false ∨ p 1545 = false ∨ p 1562 = true
  clause1028 : p 1488 = false ∨ p 1540 = false ∨ p 1558 = true
  clause1029 : p 1488 = false ∨ p 1541 = false ∨ p 1559 = true
  clause1030 : p 1488 = false ∨ p 1542 = false ∨ p 1560 = true
  clause1031 : p 1488 = false ∨ p 1543 = false ∨ p 1561 = true
  clause1032 : p 1488 = false ∨ p 1544 = false ∨ p 1562 = true
  clause1033 : p 1488 = false ∨ p 1545 = false ∨ p 1563 = true
  clause1034 : p 1489 = false ∨ p 1540 = false ∨ p 1559 = true
  clause1035 : p 1489 = false ∨ p 1541 = false ∨ p 1560 = true
  clause1036 : p 1489 = false ∨ p 1542 = false ∨ p 1561 = true
  clause1037 : p 1489 = false ∨ p 1543 = false ∨ p 1562 = true
  clause1038 : p 1490 = false ∨ p 1541 = false ∨ p 1561 = true
  clause1039 : p 1490 = false ∨ p 1542 = false ∨ p 1562 = true
  clause1040 : p 1490 = false ∨ p 1543 = false ∨ p 1563 = true
  clause1041 : p 65 = true ∨ p 1569 = true
  clause1042 : p 64 = true ∨ p 1569 = true
  clause1043 : p 64 = true ∨ p 65 = true ∨ p 1570 = true
  clause1044 : p 1569 = false ∨ p 1571 = true
  clause1045 : p 1570 = false ∨ p 1572 = true
  clause1046 : p 68 = true ∨ p 1574 = true
  clause1047 : p 67 = true ∨ p 1574 = true
  clause1048 : p 67 = true ∨ p 68 = true ∨ p 1575 = true
  clause1049 : p 74 = true ∨ p 1576 = true
  clause1050 : p 72 = true ∨ p 1576 = true
  clause1051 : p 72 = true ∨ p 74 = true ∨ p 1577 = true
  clause1052 : p 1576 = false ∨ p 1578 = true
  clause1053 : p 1577 = false ∨ p 1579 = true
  clause1054 : p 1574 = false ∨ p 1578 = true
  clause1055 : p 1574 = false ∨ p 1576 = false ∨ p 1579 = true
  clause1056 : p 1574 = false ∨ p 1577 = false ∨ p 1580 = true
structure Block33 (p : Nat → Bool) : Prop where
  clause1057 : p 1575 = false ∨ p 1576 = false ∨ p 1580 = true
  clause1058 : p 1575 = false ∨ p 1577 = false ∨ p 1581 = true
  clause1059 : p 1578 = false ∨ p 1582 = true
  clause1060 : p 1579 = false ∨ p 1583 = true
  clause1061 : p 1580 = false ∨ p 1584 = true
  clause1062 : p 1571 = false ∨ p 1582 = true
  clause1063 : p 1571 = false ∨ p 1578 = false ∨ p 1583 = true
  clause1064 : p 1571 = false ∨ p 1579 = false ∨ p 1584 = true
  clause1065 : p 1571 = false ∨ p 1580 = false ∨ p 1585 = true
  clause1066 : p 1571 = false ∨ p 1581 = false ∨ p 1586 = true
  clause1067 : p 1572 = false ∨ p 1583 = true
  clause1068 : p 1572 = false ∨ p 1578 = false ∨ p 1584 = true
  clause1069 : p 1572 = false ∨ p 1579 = false ∨ p 1585 = true
  clause1070 : p 81 = true ∨ p 1589 = true
  clause1071 : p 77 = true ∨ p 1589 = true
  clause1072 : p 77 = true ∨ p 81 = true ∨ p 1590 = true
  clause1073 : p 1589 = false ∨ p 1591 = true
  clause1074 : p 1590 = false ∨ p 1592 = true
  clause1075 : p 76 = true ∨ p 1591 = true
  clause1076 : p 76 = true ∨ p 1589 = false ∨ p 1592 = true
  clause1077 : p 76 = true ∨ p 1590 = false ∨ p 1593 = true
  clause1078 : p 85 = true ∨ p 1594 = true
  clause1079 : p 83 = true ∨ p 1594 = true
  clause1080 : p 83 = true ∨ p 85 = true ∨ p 1595 = true
  clause1081 : p 90 = true ∨ p 1596 = true
  clause1082 : p 86 = true ∨ p 1596 = true
  clause1083 : p 86 = true ∨ p 90 = true ∨ p 1597 = true
  clause1084 : p 1596 = false ∨ p 1598 = true
  clause1085 : p 1597 = false ∨ p 1599 = true
  clause1086 : p 1594 = false ∨ p 1598 = true
  clause1087 : p 1594 = false ∨ p 1596 = false ∨ p 1599 = true
  clause1088 : p 1594 = false ∨ p 1597 = false ∨ p 1600 = true
structure Block34 (p : Nat → Bool) : Prop where
  clause1089 : p 1595 = false ∨ p 1599 = true
  clause1090 : p 1595 = false ∨ p 1596 = false ∨ p 1600 = true
  clause1091 : p 1595 = false ∨ p 1597 = false ∨ p 1601 = true
  clause1092 : p 1598 = false ∨ p 1602 = true
  clause1093 : p 1599 = false ∨ p 1603 = true
  clause1094 : p 1600 = false ∨ p 1604 = true
  clause1095 : p 1601 = false ∨ p 1605 = true
  clause1096 : p 1591 = false ∨ p 1602 = true
  clause1097 : p 1591 = false ∨ p 1598 = false ∨ p 1603 = true
  clause1098 : p 1591 = false ∨ p 1599 = false ∨ p 1604 = true
  clause1099 : p 1591 = false ∨ p 1600 = false ∨ p 1605 = true
  clause1100 : p 1591 = false ∨ p 1601 = false ∨ p 1606 = true
  clause1101 : p 1592 = false ∨ p 1603 = true
  clause1102 : p 1592 = false ∨ p 1598 = false ∨ p 1604 = true
  clause1103 : p 1592 = false ∨ p 1599 = false ∨ p 1605 = true
  clause1104 : p 1592 = false ∨ p 1600 = false ∨ p 1606 = true
  clause1105 : p 1593 = false ∨ p 1598 = false ∨ p 1605 = true
  clause1106 : p 1593 = false ∨ p 1599 = false ∨ p 1606 = true
  clause1107 : p 1602 = false ∨ p 1609 = true
  clause1108 : p 1604 = false ∨ p 1611 = true
  clause1109 : p 1605 = false ∨ p 1612 = true
  clause1110 : p 1582 = false ∨ p 1602 = false ∨ p 1610 = true
  clause1111 : p 1582 = false ∨ p 1603 = false ∨ p 1611 = true
  clause1112 : p 1582 = false ∨ p 1604 = false ∨ p 1612 = true
  clause1113 : p 1582 = false ∨ p 1605 = false ∨ p 1613 = true
  clause1114 : p 1582 = false ∨ p 1606 = false ∨ p 1614 = true
  clause1115 : p 1583 = false ∨ p 1602 = false ∨ p 1611 = true
  clause1116 : p 1583 = false ∨ p 1603 = false ∨ p 1612 = true
  clause1117 : p 1583 = false ∨ p 1604 = false ∨ p 1613 = true
  clause1118 : p 1583 = false ∨ p 1605 = false ∨ p 1614 = true
  clause1119 : p 1583 = false ∨ p 1606 = false ∨ p 1615 = true
  clause1120 : p 1584 = false ∨ p 1602 = false ∨ p 1612 = true
structure Block35 (p : Nat → Bool) : Prop where
  clause1121 : p 1584 = false ∨ p 1603 = false ∨ p 1613 = true
  clause1122 : p 1584 = false ∨ p 1604 = false ∨ p 1614 = true
  clause1123 : p 1584 = false ∨ p 1605 = false ∨ p 1615 = true
  clause1124 : p 1584 = false ∨ p 1606 = false ∨ p 1616 = true
  clause1125 : p 1585 = false ∨ p 1612 = true
  clause1126 : p 1585 = false ∨ p 1602 = false ∨ p 1613 = true
  clause1127 : p 1585 = false ∨ p 1603 = false ∨ p 1614 = true
  clause1128 : p 1585 = false ∨ p 1604 = false ∨ p 1615 = true
  clause1129 : p 1585 = false ∨ p 1605 = false ∨ p 1616 = true
  clause1130 : p 1586 = false ∨ p 1613 = true
  clause1131 : p 1586 = false ∨ p 1602 = false ∨ p 1614 = true
  clause1132 : p 1586 = false ∨ p 1603 = false ∨ p 1615 = true
  clause1133 : p 1586 = false ∨ p 1604 = false ∨ p 1616 = true
  clause1134 : p 1586 = false ∨ p 1605 = false ∨ p 1617 = true
  clause1135 : p 94 = true ∨ p 1623 = true
  clause1136 : p 93 = true ∨ p 1623 = true
  clause1137 : p 93 = true ∨ p 94 = true ∨ p 1624 = true
  clause1138 : p 1623 = false ∨ p 1625 = true
  clause1139 : p 1624 = false ∨ p 1626 = true
  clause1140 : p 92 = true ∨ p 1625 = true
  clause1141 : p 92 = true ∨ p 1623 = false ∨ p 1626 = true
  clause1142 : p 92 = true ∨ p 1624 = false ∨ p 1627 = true
  clause1143 : p 98 = true ∨ p 1628 = true
  clause1144 : p 97 = true ∨ p 1628 = true
  clause1145 : p 97 = true ∨ p 98 = true ∨ p 1629 = true
  clause1146 : p 104 = true ∨ p 1630 = true
  clause1147 : p 102 = true ∨ p 1630 = true
  clause1148 : p 102 = true ∨ p 104 = true ∨ p 1631 = true
  clause1149 : p 1630 = false ∨ p 1632 = true
  clause1150 : p 1631 = false ∨ p 1633 = true
  clause1151 : p 1628 = false ∨ p 1632 = true
  clause1152 : p 1628 = false ∨ p 1630 = false ∨ p 1633 = true
structure Block36 (p : Nat → Bool) : Prop where
  clause1153 : p 1628 = false ∨ p 1631 = false ∨ p 1634 = true
  clause1154 : p 1629 = false ∨ p 1633 = true
  clause1155 : p 1629 = false ∨ p 1630 = false ∨ p 1634 = true
  clause1156 : p 1629 = false ∨ p 1631 = false ∨ p 1635 = true
  clause1157 : p 1632 = false ∨ p 1636 = true
  clause1158 : p 1633 = false ∨ p 1637 = true
  clause1159 : p 1634 = false ∨ p 1638 = true
  clause1160 : p 1625 = false ∨ p 1636 = true
  clause1161 : p 1625 = false ∨ p 1632 = false ∨ p 1637 = true
  clause1162 : p 1625 = false ∨ p 1633 = false ∨ p 1638 = true
  clause1163 : p 1625 = false ∨ p 1634 = false ∨ p 1639 = true
  clause1164 : p 1625 = false ∨ p 1635 = false ∨ p 1640 = true
  clause1165 : p 1626 = false ∨ p 1637 = true
  clause1166 : p 1626 = false ∨ p 1632 = false ∨ p 1638 = true
  clause1167 : p 1626 = false ∨ p 1633 = false ∨ p 1639 = true
  clause1168 : p 1626 = false ∨ p 1634 = false ∨ p 1640 = true
  clause1169 : p 1627 = false ∨ p 1638 = true
  clause1170 : p 1627 = false ∨ p 1632 = false ∨ p 1639 = true
  clause1171 : p 1627 = false ∨ p 1633 = false ∨ p 1640 = true
  clause1172 : p 1627 = false ∨ p 1634 = false ∨ p 1641 = true
  clause1173 : p 109 = true ∨ p 1643 = true
  clause1174 : p 106 = true ∨ p 1643 = true
  clause1175 : p 106 = true ∨ p 109 = true ∨ p 1644 = true
  clause1176 : p 1643 = false ∨ p 1645 = true
  clause1177 : p 1644 = false ∨ p 1646 = true
  clause1178 : p 105 = true ∨ p 1645 = true
  clause1179 : p 105 = true ∨ p 1643 = false ∨ p 1646 = true
  clause1180 : p 113 = true ∨ p 1648 = true
  clause1181 : p 111 = true ∨ p 1648 = true
  clause1182 : p 111 = true ∨ p 113 = true ∨ p 1649 = true
  clause1183 : p 117 = true ∨ p 1650 = true
  clause1184 : p 115 = true ∨ p 1650 = true
structure Block37 (p : Nat → Bool) : Prop where
  clause1185 : p 115 = true ∨ p 117 = true ∨ p 1651 = true
  clause1186 : p 1650 = false ∨ p 1652 = true
  clause1187 : p 1651 = false ∨ p 1653 = true
  clause1188 : p 1648 = false ∨ p 1652 = true
  clause1189 : p 1648 = false ∨ p 1650 = false ∨ p 1653 = true
  clause1190 : p 1649 = false ∨ p 1653 = true
  clause1191 : p 1652 = false ∨ p 1656 = true
  clause1192 : p 1653 = false ∨ p 1657 = true
  clause1193 : p 1645 = false ∨ p 1656 = true
  clause1194 : p 1645 = false ∨ p 1652 = false ∨ p 1657 = true
  clause1195 : p 1645 = false ∨ p 1653 = false ∨ p 1658 = true
  clause1196 : p 1646 = false ∨ p 1657 = true
  clause1197 : p 1646 = false ∨ p 1652 = false ∨ p 1658 = true
  clause1198 : p 1646 = false ∨ p 1653 = false ∨ p 1659 = true
  clause1199 : p 1657 = false ∨ p 1664 = true
  clause1200 : p 1658 = false ∨ p 1665 = true
  clause1201 : p 1659 = false ∨ p 1666 = true
  clause1202 : p 1636 = false ∨ p 1656 = false ∨ p 1664 = true
  clause1203 : p 1636 = false ∨ p 1657 = false ∨ p 1665 = true
  clause1204 : p 1636 = false ∨ p 1658 = false ∨ p 1666 = true
  clause1205 : p 1636 = false ∨ p 1659 = false ∨ p 1667 = true
  clause1206 : p 1637 = false ∨ p 1664 = true
  clause1207 : p 1637 = false ∨ p 1656 = false ∨ p 1665 = true
  clause1208 : p 1637 = false ∨ p 1657 = false ∨ p 1666 = true
  clause1209 : p 1637 = false ∨ p 1658 = false ∨ p 1667 = true
  clause1210 : p 1637 = false ∨ p 1659 = false ∨ p 1668 = true
  clause1211 : p 1638 = false ∨ p 1665 = true
  clause1212 : p 1638 = false ∨ p 1656 = false ∨ p 1666 = true
  clause1213 : p 1638 = false ∨ p 1657 = false ∨ p 1667 = true
  clause1214 : p 1638 = false ∨ p 1658 = false ∨ p 1668 = true
  clause1215 : p 1638 = false ∨ p 1659 = false ∨ p 1669 = true
  clause1216 : p 1639 = false ∨ p 1666 = true
structure Block38 (p : Nat → Bool) : Prop where
  clause1217 : p 1639 = false ∨ p 1656 = false ∨ p 1667 = true
  clause1218 : p 1639 = false ∨ p 1657 = false ∨ p 1668 = true
  clause1219 : p 1639 = false ∨ p 1658 = false ∨ p 1669 = true
  clause1220 : p 1640 = false ∨ p 1667 = true
  clause1221 : p 1640 = false ∨ p 1656 = false ∨ p 1668 = true
  clause1222 : p 1640 = false ∨ p 1657 = false ∨ p 1669 = true
  clause1223 : p 1641 = false ∨ p 1668 = true
  clause1224 : p 1641 = false ∨ p 1656 = false ∨ p 1669 = true
  clause1225 : p 1609 = false ∨ p 1667 = false ∨ p 1682 = true
  clause1226 : p 1609 = false ∨ p 1668 = false ∨ p 1683 = true
  clause1227 : p 1610 = false ∨ p 1665 = false ∨ p 1681 = true
  clause1228 : p 1610 = false ∨ p 1666 = false ∨ p 1682 = true
  clause1229 : p 1610 = false ∨ p 1667 = false ∨ p 1683 = true
  clause1230 : p 1610 = false ∨ p 1668 = false ∨ p 1684 = true
  clause1231 : p 1610 = false ∨ p 1669 = false ∨ p 1685 = true
  clause1232 : p 1611 = false ∨ p 1665 = false ∨ p 1682 = true
  clause1233 : p 1611 = false ∨ p 1666 = false ∨ p 1683 = true
  clause1234 : p 1611 = false ∨ p 1667 = false ∨ p 1684 = true
  clause1235 : p 1611 = false ∨ p 1668 = false ∨ p 1685 = true
  clause1236 : p 1611 = false ∨ p 1669 = false ∨ p 1686 = true
  clause1237 : p 1612 = false ∨ p 1664 = false ∨ p 1682 = true
  clause1238 : p 1612 = false ∨ p 1665 = false ∨ p 1683 = true
  clause1239 : p 1612 = false ∨ p 1666 = false ∨ p 1684 = true
  clause1240 : p 1612 = false ∨ p 1667 = false ∨ p 1685 = true
  clause1241 : p 1612 = false ∨ p 1668 = false ∨ p 1686 = true
  clause1242 : p 1612 = false ∨ p 1669 = false ∨ p 1687 = true
  clause1243 : p 1613 = false ∨ p 1664 = false ∨ p 1683 = true
  clause1244 : p 1613 = false ∨ p 1665 = false ∨ p 1684 = true
  clause1245 : p 1613 = false ∨ p 1666 = false ∨ p 1685 = true
  clause1246 : p 1613 = false ∨ p 1667 = false ∨ p 1686 = true
  clause1247 : p 1613 = false ∨ p 1668 = false ∨ p 1687 = true
  clause1248 : p 1613 = false ∨ p 1669 = false ∨ p 1688 = true
structure Block39 (p : Nat → Bool) : Prop where
  clause1249 : p 1614 = false ∨ p 1664 = false ∨ p 1684 = true
  clause1250 : p 1614 = false ∨ p 1665 = false ∨ p 1685 = true
  clause1251 : p 1614 = false ∨ p 1666 = false ∨ p 1686 = true
  clause1252 : p 1614 = false ∨ p 1667 = false ∨ p 1687 = true
  clause1253 : p 1614 = false ∨ p 1668 = false ∨ p 1688 = true
  clause1254 : p 1615 = false ∨ p 1665 = false ∨ p 1686 = true
  clause1255 : p 1615 = false ∨ p 1666 = false ∨ p 1687 = true
  clause1256 : p 1615 = false ∨ p 1667 = false ∨ p 1688 = true
  clause1257 : p 1616 = false ∨ p 1665 = false ∨ p 1687 = true
  clause1258 : p 1616 = false ∨ p 1666 = false ∨ p 1688 = true
  clause1259 : p 1617 = false ∨ p 1665 = false ∨ p 1688 = true
  clause1260 : p 1556 = false ∨ p 1688 = false ∨ p 1708 = true
  clause1261 : p 1557 = false ∨ p 1687 = false ∨ p 1708 = true
  clause1262 : p 1558 = false ∨ p 1686 = false ∨ p 1708 = true
  clause1263 : p 1559 = false ∨ p 1685 = false ∨ p 1708 = true
  clause1264 : p 1560 = false ∨ p 1684 = false ∨ p 1708 = true
  clause1265 : p 1561 = false ∨ p 1683 = false ∨ p 1708 = true
  clause1266 : p 1562 = false ∨ p 1682 = false ∨ p 1708 = true
  clause1267 : p 1563 = false ∨ p 1681 = false ∨ p 1708 = true
  clause1268 : p 1708 = false
  clause1269 : p 6 = false ∨ p 12 = false ∨ p 55 = false ∨ p 73 = false
  clause1270 : p 14 = false ∨ p 18 = false ∨ p 24 = false ∨ p 28 = false
  clause1271 : p 16 = false ∨ p 21 = false ∨ p 26 = false ∨ p 29 = false
  clause1272 : p 16 = false ∨ p 21 = false ∨ p 81 = false ∨ p 88 = false
  clause1273 : p 17 = false ∨ p 19 = false ∨ p 82 = false ∨ p 85 = false
  clause1274 : p 21 = false ∨ p 29 = false ∨ p 88 = false ∨ p 98 = false
  clause1275 : p 45 = false ∨ p 46 = false ∨ p 47 = false ∨ p 48 = false
  clause1276 : p 50 = false ∨ p 51 = false ∨ p 55 = false ∨ p 56 = false
  clause1277 : p 50 = false ∨ p 51 = false ∨ p 81 = false ∨ p 82 = false
  clause1278 : p 50 = false ∨ p 52 = false ∨ p 65 = false ∨ p 70 = false
  clause1279 : p 50 = false ∨ p 52 = false ∨ p 81 = false ∨ p 88 = false
  clause1280 : p 51 = false ∨ p 56 = false ∨ p 82 = false ∨ p 92 = false
structure Block40 (p : Nat → Bool) : Prop where
  clause1281 : p 52 = false ∨ p 70 = false ∨ p 88 = false ∨ p 106 = false
  clause1282 : p 53 = false ∨ p 54 = false ∨ p 55 = false ∨ p 56 = false
  clause1283 : p 54 = false ∨ p 56 = false ∨ p 91 = false ∨ p 92 = false
  clause1284 : p 65 = false ∨ p 66 = false ∨ p 70 = false ∨ p 72 = false
  clause1285 : p 65 = false ∨ p 70 = false ∨ p 73 = false ∨ p 77 = false
  clause1286 : p 65 = false ∨ p 70 = false ∨ p 101 = false ∨ p 106 = false
  clause1287 : p 81 = false ∨ p 84 = false ∨ p 88 = false ∨ p 90 = false
  clause1288 : p 81 = false ∨ p 88 = false ∨ p 101 = false ∨ p 106 = false
  clause1289 : p 82 = false ∨ p 92 = false ∨ p 102 = false ∨ p 112 = false
  clause1290 : p 83 = false ∨ p 84 = false ∨ p 89 = false ∨ p 90 = false
  clause1291 : p 86 = false ∨ p 87 = false ∨ p 96 = false ∨ p 97 = false
  clause1292 : p 86 = false ∨ p 88 = false ∨ p 89 = false ∨ p 90 = false
  clause1293 : p 86 = false ∨ p 88 = false ∨ p 96 = false ∨ p 98 = false
  clause1294 : p 91 = false ∨ p 92 = false ∨ p 93 = false ∨ p 95 = false
  clause1295 : p 91 = false ∨ p 92 = false ∨ p 111 = false ∨ p 112 = false
  clause1296 : p 91 = false ∨ p 93 = false ∨ p 97 = false ∨ p 100 = false
  clause1297 : p 96 = false ∨ p 97 = false ∨ p 98 = false ∨ p 99 = false
  clause1298 : p 101 = false ∨ p 102 = false ∨ p 106 = false ∨ p 107 = false
  clause1299 : p 113 = false ∨ p 114 = false ∨ p 116 = false ∨ p 117 = false
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
  block19 : Block19 p
  block20 : Block20 p
  block21 : Block21 p
  block22 : Block22 p
  block23 : Block23 p
  block24 : Block24 p
  block25 : Block25 p
  block26 : Block26 p
  block27 : Block27 p
  block28 : Block28 p
  block29 : Block29 p
  block30 : Block30 p
  block31 : Block31 p
  block32 : Block32 p
  block33 : Block33 p
  block34 : Block34 p
  block35 : Block35 p
  block36 : Block36 p
  block37 : Block37 p
  block38 : Block38 p
  block39 : Block39 p
  block40 : Block40 p
def c1 : List Lit := [(1, false), (119, true), (14, true)]
theorem step1 (p : Nat → Bool) (h : Constraints p) : clause p c1 = true := by
  simpa only [c1,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause1
def c2 : List Lit := [(2, false), (120, true), (7, true)]
theorem step2 (p : Nat → Bool) (h : Constraints p) : clause p c2 = true := by
  simpa only [c2,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause2
def c3 : List Lit := [(2, false), (120, true), (5, true)]
theorem step3 (p : Nat → Bool) (h : Constraints p) : clause p c3 = true := by
  simpa only [c3,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause3
def c4 : List Lit := [(3, false), (121, true), (1, true), (10, true)]
theorem step4 (p : Nat → Bool) (h : Constraints p) : clause p c4 = true := by
  simpa only [c4,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause4
def c5 : List Lit := [(3, false), (121, true), (1, true), (4, true)]
theorem step5 (p : Nat → Bool) (h : Constraints p) : clause p c5 = true := by
  simpa only [c5,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause5
def c6 : List Lit := [(4, false), (122, true), (5, true)]
theorem step6 (p : Nat → Bool) (h : Constraints p) : clause p c6 = true := by
  simpa only [c6,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause6
def c7 : List Lit := [(4, false), (122, true), (3, true)]
theorem step7 (p : Nat → Bool) (h : Constraints p) : clause p c7 = true := by
  simpa only [c7,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause7
def c8 : List Lit := [(5, false), (123, true), (4, true)]
theorem step8 (p : Nat → Bool) (h : Constraints p) : clause p c8 = true := by
  simpa only [c8,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause8
def c9 : List Lit := [(5, false), (123, true), (2, true)]
theorem step9 (p : Nat → Bool) (h : Constraints p) : clause p c9 = true := by
  simpa only [c9,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause9
def c10 : List Lit := [(6, false), (7, false), (12, false), (26, false)]
theorem step10 (p : Nat → Bool) (h : Constraints p) : clause p c10 = true := by
  simpa only [c10,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause10
def c11 : List Lit := [(6, false), (7, false), (12, false), (55, false)]
theorem step11 (p : Nat → Bool) (h : Constraints p) : clause p c11 = true := by
  simpa only [c11,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause11
def c12 : List Lit := [(6, false), (7, false), (26, false), (55, false)]
theorem step12 (p : Nat → Bool) (h : Constraints p) : clause p c12 = true := by
  simpa only [c12,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause12
def c13 : List Lit := [(6, false), (124, true), (12, true), (26, true), (55, true)]
theorem step13 (p : Nat → Bool) (h : Constraints p) : clause p c13 = true := by
  simpa only [c13,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause13
def c14 : List Lit := [(7, false), (125, true), (6, true), (58, true)]
theorem step14 (p : Nat → Bool) (h : Constraints p) : clause p c14 = true := by
  simpa only [c14,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause14
def c15 : List Lit := [(7, false), (125, true), (2, true), (58, true)]
theorem step15 (p : Nat → Bool) (h : Constraints p) : clause p c15 = true := by
  simpa only [c15,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause15
def c16 : List Lit := [(7, false), (125, true), (2, true), (6, true)]
theorem step16 (p : Nat → Bool) (h : Constraints p) : clause p c16 = true := by
  simpa only [c16,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause16
def c17 : List Lit := [(8, false), (11, false), (34, false), (64, false)]
theorem step17 (p : Nat → Bool) (h : Constraints p) : clause p c17 = true := by
  simpa only [c17,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause17
def c18 : List Lit := [(8, false), (126, true), (11, true), (34, true)]
theorem step18 (p : Nat → Bool) (h : Constraints p) : clause p c18 = true := by
  simpa only [c18,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause18
def c19 : List Lit := [(9, false), (127, true), (65, true)]
theorem step19 (p : Nat → Bool) (h : Constraints p) : clause p c19 = true := by
  simpa only [c19,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause19
def c20 : List Lit := [(10, false), (3, false), (37, false), (68, false)]
theorem step20 (p : Nat → Bool) (h : Constraints p) : clause p c20 = true := by
  simpa only [c20,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause20
def c21 : List Lit := [(10, false), (128, true), (37, true), (68, true)]
theorem step21 (p : Nat → Bool) (h : Constraints p) : clause p c21 = true := by
  simpa only [c21,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause21
def c22 : List Lit := [(129, false), (11, true)]
theorem step22 (p : Nat → Bool) (h : Constraints p) : clause p c22 = true := by
  simpa only [c22,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause22
def c23 : List Lit := [(11, false), (8, true), (13, true)]
theorem step23 (p : Nat → Bool) (h : Constraints p) : clause p c23 = true := by
  simpa only [c23,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause23
def c24 : List Lit := [(11, false), (129, true), (13, true)]
theorem step24 (p : Nat → Bool) (h : Constraints p) : clause p c24 = true := by
  simpa only [c24,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause24
def c25 : List Lit := [(11, false), (129, true), (8, true)]
theorem step25 (p : Nat → Bool) (h : Constraints p) : clause p c25 = true := by
  simpa only [c25,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause25
def c26 : List Lit := [(12, false), (6, false), (13, false), (41, false)]
theorem step26 (p : Nat → Bool) (h : Constraints p) : clause p c26 = true := by
  simpa only [c26,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause26
def c27 : List Lit := [(12, false), (6, false), (13, false), (73, false)]
theorem step27 (p : Nat → Bool) (h : Constraints p) : clause p c27 = true := by
  simpa only [c27,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause27
def c28 : List Lit := [(12, false), (6, false), (41, false), (73, false)]
theorem step28 (p : Nat → Bool) (h : Constraints p) : clause p c28 = true := by
  simpa only [c28,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause28
def c29 : List Lit := [(12, false), (13, false), (41, false), (73, false)]
theorem step29 (p : Nat → Bool) (h : Constraints p) : clause p c29 = true := by
  simpa only [c29,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause29
def c30 : List Lit := [(12, false), (130, true), (6, true), (9, true), (41, true), (73, true)]
theorem step30 (p : Nat → Bool) (h : Constraints p) : clause p c30 = true := by
  simpa only [c30,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause30
def c31 : List Lit := [(12, false), (130, true), (6, true), (9, true), (13, true), (41, true)]
theorem step31 (p : Nat → Bool) (h : Constraints p) : clause p c31 = true := by
  simpa only [c31,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause31
def c32 : List Lit := [(13, false), (131, true), (12, true)]
theorem step32 (p : Nat → Bool) (h : Constraints p) : clause p c32 = true := by
  simpa only [c32,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause32
def c33 : List Lit := [(13, false), (131, true), (11, true)]
theorem step33 (p : Nat → Bool) (h : Constraints p) : clause p c33 = true := by
  simpa only [c33,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause33
def c34 : List Lit := [(14, false), (1, false), (15, false), (16, false)]
theorem step34 (p : Nat → Bool) (h : Constraints p) : clause p c34 = true := by
  simpa only [c34,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause34
def c35 : List Lit := [(14, false), (1, false), (15, false), (24, false)]
theorem step35 (p : Nat → Bool) (h : Constraints p) : clause p c35 = true := by
  simpa only [c35,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause35
def c36 : List Lit := [(14, false), (1, false), (16, false), (18, false)]
theorem step36 (p : Nat → Bool) (h : Constraints p) : clause p c36 = true := by
  simpa only [c36,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause36
def c37 : List Lit := [(14, false), (1, false), (16, false), (24, false)]
theorem step37 (p : Nat → Bool) (h : Constraints p) : clause p c37 = true := by
  simpa only [c37,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause37
def c38 : List Lit := [(14, false), (1, false), (16, false), (33, false)]
theorem step38 (p : Nat → Bool) (h : Constraints p) : clause p c38 = true := by
  simpa only [c38,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause38
def c39 : List Lit := [(14, false), (1, false), (18, false), (33, false)]
theorem step39 (p : Nat → Bool) (h : Constraints p) : clause p c39 = true := by
  simpa only [c39,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause39
def c40 : List Lit := [(14, false), (1, false), (24, false), (33, false)]
theorem step40 (p : Nat → Bool) (h : Constraints p) : clause p c40 = true := by
  simpa only [c40,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause40
def c41 : List Lit := [(14, false), (16, false), (18, false), (24, false)]
theorem step41 (p : Nat → Bool) (h : Constraints p) : clause p c41 = true := by
  simpa only [c41,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause41
def c42 : List Lit := [(15, false), (14, false), (17, false), (20, false)]
theorem step42 (p : Nat → Bool) (h : Constraints p) : clause p c42 = true := by
  simpa only [c42,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause42
def c43 : List Lit := [(15, false), (14, false), (17, false), (25, false)]
theorem step43 (p : Nat → Bool) (h : Constraints p) : clause p c43 = true := by
  simpa only [c43,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause43
def c44 : List Lit := [(15, false), (14, false), (17, false), (34, false)]
theorem step44 (p : Nat → Bool) (h : Constraints p) : clause p c44 = true := by
  simpa only [c44,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause44
def c45 : List Lit := [(15, false), (14, false), (20, false), (25, false)]
theorem step45 (p : Nat → Bool) (h : Constraints p) : clause p c45 = true := by
  simpa only [c45,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause45
def c46 : List Lit := [(15, false), (14, false), (20, false), (34, false)]
theorem step46 (p : Nat → Bool) (h : Constraints p) : clause p c46 = true := by
  simpa only [c46,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause46
def c47 : List Lit := [(15, false), (14, false), (25, false), (34, false)]
theorem step47 (p : Nat → Bool) (h : Constraints p) : clause p c47 = true := by
  simpa only [c47,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause47
def c48 : List Lit := [(15, false), (17, false), (20, false), (25, false)]
theorem step48 (p : Nat → Bool) (h : Constraints p) : clause p c48 = true := by
  simpa only [c48,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause48
def c49 : List Lit := [(15, false), (17, false), (20, false), (34, false)]
theorem step49 (p : Nat → Bool) (h : Constraints p) : clause p c49 = true := by
  simpa only [c49,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause49
def c50 : List Lit := [(15, false), (17, false), (25, false), (34, false)]
theorem step50 (p : Nat → Bool) (h : Constraints p) : clause p c50 = true := by
  simpa only [c50,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause50
def c51 : List Lit := [(15, false), (20, false), (25, false), (34, false)]
theorem step51 (p : Nat → Bool) (h : Constraints p) : clause p c51 = true := by
  simpa only [c51,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause51
def c52 : List Lit := [(16, false), (14, false), (17, false), (21, false)]
theorem step52 (p : Nat → Bool) (h : Constraints p) : clause p c52 = true := by
  simpa only [c52,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause52
def c53 : List Lit := [(16, false), (14, false), (17, false), (26, false)]
theorem step53 (p : Nat → Bool) (h : Constraints p) : clause p c53 = true := by
  simpa only [c53,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause53
def c54 : List Lit := [(16, false), (14, false), (17, false), (81, false)]
theorem step54 (p : Nat → Bool) (h : Constraints p) : clause p c54 = true := by
  simpa only [c54,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause54
def c55 : List Lit := [(16, false), (14, false), (21, false), (26, false)]
theorem step55 (p : Nat → Bool) (h : Constraints p) : clause p c55 = true := by
  simpa only [c55,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause55
def c56 : List Lit := [(16, false), (14, false), (21, false), (81, false)]
theorem step56 (p : Nat → Bool) (h : Constraints p) : clause p c56 = true := by
  simpa only [c56,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause56
def c57 : List Lit := [(16, false), (14, false), (26, false), (81, false)]
theorem step57 (p : Nat → Bool) (h : Constraints p) : clause p c57 = true := by
  simpa only [c57,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause57
def c58 : List Lit := [(16, false), (17, false), (21, false), (26, false)]
theorem step58 (p : Nat → Bool) (h : Constraints p) : clause p c58 = true := by
  simpa only [c58,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause58
def c59 : List Lit := [(16, false), (17, false), (21, false), (81, false)]
theorem step59 (p : Nat → Bool) (h : Constraints p) : clause p c59 = true := by
  simpa only [c59,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause59
def c60 : List Lit := [(16, false), (17, false), (26, false), (81, false)]
theorem step60 (p : Nat → Bool) (h : Constraints p) : clause p c60 = true := by
  simpa only [c60,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause60
def c61 : List Lit := [(16, false), (21, false), (26, false), (81, false)]
theorem step61 (p : Nat → Bool) (h : Constraints p) : clause p c61 = true := by
  simpa only [c61,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause61
def c62 : List Lit := [(16, false), (134, true), (14, true), (17, true), (26, true), (81, true)]
theorem step62 (p : Nat → Bool) (h : Constraints p) : clause p c62 = true := by
  simpa only [c62,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause62
def c63 : List Lit := [(17, false), (15, true), (16, true), (19, true), (27, true), (82, true)]
theorem step63 (p : Nat → Bool) (h : Constraints p) : clause p c63 = true := by
  simpa only [c63,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause63
def c64 : List Lit := [(17, false), (15, false), (16, false), (19, false)]
theorem step64 (p : Nat → Bool) (h : Constraints p) : clause p c64 = true := by
  simpa only [c64,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause64
def c65 : List Lit := [(17, false), (16, false), (19, false), (27, false)]
theorem step65 (p : Nat → Bool) (h : Constraints p) : clause p c65 = true := by
  simpa only [c65,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause65
def c66 : List Lit := [(17, false), (135, true), (15, true), (16, true), (27, true), (82, true)]
theorem step66 (p : Nat → Bool) (h : Constraints p) : clause p c66 = true := by
  simpa only [c66,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause66
def c67 : List Lit := [(17, false), (135, true), (15, true), (16, true), (19, true), (82, true)]
theorem step67 (p : Nat → Bool) (h : Constraints p) : clause p c67 = true := by
  simpa only [c67,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause67
def c68 : List Lit := [(17, false), (135, true), (15, true), (16, true), (19, true), (27, true)]
theorem step68 (p : Nat → Bool) (h : Constraints p) : clause p c68 = true := by
  simpa only [c68,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause68
def c69 : List Lit := [(18, false), (14, false), (28, false), (83, false)]
theorem step69 (p : Nat → Bool) (h : Constraints p) : clause p c69 = true := by
  simpa only [c69,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause69
def c70 : List Lit := [(18, false), (136, true), (14, true), (83, true)]
theorem step70 (p : Nat → Bool) (h : Constraints p) : clause p c70 = true := by
  simpa only [c70,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause70
def c71 : List Lit := [(19, false), (17, false), (23, false), (36, false)]
theorem step71 (p : Nat → Bool) (h : Constraints p) : clause p c71 = true := by
  simpa only [c71,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause71
def c72 : List Lit := [(19, false), (17, false), (23, false), (85, false)]
theorem step72 (p : Nat → Bool) (h : Constraints p) : clause p c72 = true := by
  simpa only [c72,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause72
def c73 : List Lit := [(19, false), (17, false), (36, false), (85, false)]
theorem step73 (p : Nat → Bool) (h : Constraints p) : clause p c73 = true := by
  simpa only [c73,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause73
def c74 : List Lit := [(20, false), (138, true), (22, true), (38, true), (87, true)]
theorem step74 (p : Nat → Bool) (h : Constraints p) : clause p c74 = true := by
  simpa only [c74,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause74
def c75 : List Lit := [(20, false), (138, true), (15, true), (38, true), (87, true)]
theorem step75 (p : Nat → Bool) (h : Constraints p) : clause p c75 = true := by
  simpa only [c75,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause75
def c76 : List Lit := [(20, false), (138, true), (15, true), (22, true), (38, true)]
theorem step76 (p : Nat → Bool) (h : Constraints p) : clause p c76 = true := by
  simpa only [c76,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause76
def c77 : List Lit := [(139, false), (21, true)]
theorem step77 (p : Nat → Bool) (h : Constraints p) : clause p c77 = true := by
  simpa only [c77,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause77
def c78 : List Lit := [(21, false), (16, true), (29, true), (88, true)]
theorem step78 (p : Nat → Bool) (h : Constraints p) : clause p c78 = true := by
  simpa only [c78,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause78
def c79 : List Lit := [(21, false), (139, true), (29, true), (88, true)]
theorem step79 (p : Nat → Bool) (h : Constraints p) : clause p c79 = true := by
  simpa only [c79,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause79
def c80 : List Lit := [(21, false), (139, true), (16, true), (88, true)]
theorem step80 (p : Nat → Bool) (h : Constraints p) : clause p c80 = true := by
  simpa only [c80,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause80
def c81 : List Lit := [(21, false), (139, true), (16, true), (29, true)]
theorem step81 (p : Nat → Bool) (h : Constraints p) : clause p c81 = true := by
  simpa only [c81,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause81
def c82 : List Lit := [(22, false), (140, true), (23, true)]
theorem step82 (p : Nat → Bool) (h : Constraints p) : clause p c82 = true := by
  simpa only [c82,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause82
def c83 : List Lit := [(22, false), (140, true), (20, true)]
theorem step83 (p : Nat → Bool) (h : Constraints p) : clause p c83 = true := by
  simpa only [c83,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause83
def c84 : List Lit := [(23, false), (141, true), (22, true), (32, true)]
theorem step84 (p : Nat → Bool) (h : Constraints p) : clause p c84 = true := by
  simpa only [c84,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause84
def c85 : List Lit := [(23, false), (141, true), (19, true), (32, true)]
theorem step85 (p : Nat → Bool) (h : Constraints p) : clause p c85 = true := by
  simpa only [c85,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause85
def c86 : List Lit := [(23, false), (141, true), (19, true), (22, true)]
theorem step86 (p : Nat → Bool) (h : Constraints p) : clause p c86 = true := by
  simpa only [c86,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause86
def c87 : List Lit := [(24, false), (14, false), (25, false), (26, false)]
theorem step87 (p : Nat → Bool) (h : Constraints p) : clause p c87 = true := by
  simpa only [c87,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause87
def c88 : List Lit := [(24, false), (14, false), (25, false), (28, false)]
theorem step88 (p : Nat → Bool) (h : Constraints p) : clause p c88 = true := by
  simpa only [c88,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause88
def c89 : List Lit := [(24, false), (14, false), (26, false), (28, false)]
theorem step89 (p : Nat → Bool) (h : Constraints p) : clause p c89 = true := by
  simpa only [c89,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause89
def c90 : List Lit := [(24, false), (25, false), (26, false), (28, false)]
theorem step90 (p : Nat → Bool) (h : Constraints p) : clause p c90 = true := by
  simpa only [c90,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause90
def c91 : List Lit := [(143, false), (25, true)]
theorem step91 (p : Nat → Bool) (h : Constraints p) : clause p c91 = true := by
  simpa only [c91,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause91
def c92 : List Lit := [(25, false), (15, true), (24, true), (27, true), (91, true)]
theorem step92 (p : Nat → Bool) (h : Constraints p) : clause p c92 = true := by
  simpa only [c92,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause92
def c93 : List Lit := [(143, false), (24, false), (91, false)]
theorem step93 (p : Nat → Bool) (h : Constraints p) : clause p c93 = true := by
  simpa only [c93,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause93
def c94 : List Lit := [(143, false), (27, false), (91, false)]
theorem step94 (p : Nat → Bool) (h : Constraints p) : clause p c94 = true := by
  simpa only [c94,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause94
def c95 : List Lit := [(25, false), (143, true), (24, true), (27, true), (91, true)]
theorem step95 (p : Nat → Bool) (h : Constraints p) : clause p c95 = true := by
  simpa only [c95,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause95
def c96 : List Lit := [(25, false), (143, true), (15, true), (27, true), (91, true)]
theorem step96 (p : Nat → Bool) (h : Constraints p) : clause p c96 = true := by
  simpa only [c96,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause96
def c97 : List Lit := [(25, false), (143, true), (15, true), (24, true), (91, true)]
theorem step97 (p : Nat → Bool) (h : Constraints p) : clause p c97 = true := by
  simpa only [c97,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause97
def c98 : List Lit := [(25, false), (143, true), (15, true), (24, true), (27, true)]
theorem step98 (p : Nat → Bool) (h : Constraints p) : clause p c98 = true := by
  simpa only [c98,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause98
def c99 : List Lit := [(26, false), (6, true), (16, true), (24, true), (27, true), (29, true), (41, true)]
theorem step99 (p : Nat → Bool) (h : Constraints p) : clause p c99 = true := by
  simpa only [c99,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause99
def c100 : List Lit := [(26, false), (144, true), (6, true), (16, true), (24, true), (29, true), (41, true)]
theorem step100 (p : Nat → Bool) (h : Constraints p) : clause p c100 = true := by
  simpa only [c100,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause100
def c101 : List Lit := [(26, false), (144, true), (6, true), (16, true), (24, true), (27, true), (41, true)]
theorem step101 (p : Nat → Bool) (h : Constraints p) : clause p c101 = true := by
  simpa only [c101,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause101
def c102 : List Lit := [(26, false), (144, true), (6, true), (16, true), (24, true), (27, true), (29, true)]
theorem step102 (p : Nat → Bool) (h : Constraints p) : clause p c102 = true := by
  simpa only [c102,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause102
def c103 : List Lit := [(27, false), (17, false), (25, false), (26, false)]
theorem step103 (p : Nat → Bool) (h : Constraints p) : clause p c103 = true := by
  simpa only [c103,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause103
def c104 : List Lit := [(27, false), (17, false), (26, false), (92, false)]
theorem step104 (p : Nat → Bool) (h : Constraints p) : clause p c104 = true := by
  simpa only [c104,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause104
def c105 : List Lit := [(27, false), (25, false), (26, false), (92, false)]
theorem step105 (p : Nat → Bool) (h : Constraints p) : clause p c105 = true := by
  simpa only [c105,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause105
def c106 : List Lit := [(146, false), (28, true)]
theorem step106 (p : Nat → Bool) (h : Constraints p) : clause p c106 = true := by
  simpa only [c106,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause106
def c107 : List Lit := [(28, false), (146, true), (24, true), (30, true)]
theorem step107 (p : Nat → Bool) (h : Constraints p) : clause p c107 = true := by
  simpa only [c107,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause107
def c108 : List Lit := [(28, false), (146, true), (18, true), (30, true)]
theorem step108 (p : Nat → Bool) (h : Constraints p) : clause p c108 = true := by
  simpa only [c108,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause108
def c109 : List Lit := [(28, false), (146, true), (18, true), (24, true)]
theorem step109 (p : Nat → Bool) (h : Constraints p) : clause p c109 = true := by
  simpa only [c109,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause109
def c110 : List Lit := [(29, false), (21, false), (26, false), (31, false)]
theorem step110 (p : Nat → Bool) (h : Constraints p) : clause p c110 = true := by
  simpa only [c110,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause110
def c111 : List Lit := [(29, false), (21, false), (26, false), (47, false)]
theorem step111 (p : Nat → Bool) (h : Constraints p) : clause p c111 = true := by
  simpa only [c111,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause111
def c112 : List Lit := [(29, false), (21, false), (26, false), (98, false)]
theorem step112 (p : Nat → Bool) (h : Constraints p) : clause p c112 = true := by
  simpa only [c112,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause112
def c113 : List Lit := [(29, false), (21, false), (31, false), (47, false)]
theorem step113 (p : Nat → Bool) (h : Constraints p) : clause p c113 = true := by
  simpa only [c113,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause113
def c114 : List Lit := [(29, false), (21, false), (31, false), (98, false)]
theorem step114 (p : Nat → Bool) (h : Constraints p) : clause p c114 = true := by
  simpa only [c114,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause114
def c115 : List Lit := [(29, false), (21, false), (47, false), (98, false)]
theorem step115 (p : Nat → Bool) (h : Constraints p) : clause p c115 = true := by
  simpa only [c115,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause115
def c116 : List Lit := [(29, false), (26, false), (31, false), (47, false)]
theorem step116 (p : Nat → Bool) (h : Constraints p) : clause p c116 = true := by
  simpa only [c116,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause116
def c117 : List Lit := [(29, false), (26, false), (31, false), (98, false)]
theorem step117 (p : Nat → Bool) (h : Constraints p) : clause p c117 = true := by
  simpa only [c117,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause117
def c118 : List Lit := [(29, false), (26, false), (47, false), (98, false)]
theorem step118 (p : Nat → Bool) (h : Constraints p) : clause p c118 = true := by
  simpa only [c118,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause118
def c119 : List Lit := [(29, false), (31, false), (47, false), (98, false)]
theorem step119 (p : Nat → Bool) (h : Constraints p) : clause p c119 = true := by
  simpa only [c119,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause119
def c120 : List Lit := [(30, false), (148, true), (31, true)]
theorem step120 (p : Nat → Bool) (h : Constraints p) : clause p c120 = true := by
  simpa only [c120,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause120
def c121 : List Lit := [(32, false), (150, true), (31, true)]
theorem step121 (p : Nat → Bool) (h : Constraints p) : clause p c121 = true := by
  simpa only [c121,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause121
def c122 : List Lit := [(33, false), (14, false), (34, false), (37, false)]
theorem step122 (p : Nat → Bool) (h : Constraints p) : clause p c122 = true := by
  simpa only [c122,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause122
def c123 : List Lit := [(34, false), (8, false), (15, false), (33, false)]
theorem step123 (p : Nat → Bool) (h : Constraints p) : clause p c123 = true := by
  simpa only [c123,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause123
def c124 : List Lit := [(152, false), (8, false), (38, false)]
theorem step124 (p : Nat → Bool) (h : Constraints p) : clause p c124 = true := by
  simpa only [c124,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause124
def c125 : List Lit := [(34, false), (152, true), (15, true), (33, true), (38, true)]
theorem step125 (p : Nat → Bool) (h : Constraints p) : clause p c125 = true := by
  simpa only [c125,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause125
def c126 : List Lit := [(34, false), (152, true), (8, true), (33, true), (38, true)]
theorem step126 (p : Nat → Bool) (h : Constraints p) : clause p c126 = true := by
  simpa only [c126,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause126
def c127 : List Lit := [(35, false), (36, false), (40, false), (43, false)]
theorem step127 (p : Nat → Bool) (h : Constraints p) : clause p c127 = true := by
  simpa only [c127,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause127
def c128 : List Lit := [(35, false), (153, true), (40, true), (43, true)]
theorem step128 (p : Nat → Bool) (h : Constraints p) : clause p c128 = true := by
  simpa only [c128,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause128
def c129 : List Lit := [(35, false), (153, true), (36, true), (43, true)]
theorem step129 (p : Nat → Bool) (h : Constraints p) : clause p c129 = true := by
  simpa only [c129,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause129
def c130 : List Lit := [(36, false), (19, false), (35, false), (44, false)]
theorem step130 (p : Nat → Bool) (h : Constraints p) : clause p c130 = true := by
  simpa only [c130,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause130
def c131 : List Lit := [(36, false), (154, true), (35, true), (44, true)]
theorem step131 (p : Nat → Bool) (h : Constraints p) : clause p c131 = true := by
  simpa only [c131,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause131
def c132 : List Lit := [(37, false), (10, false), (33, false), (39, false)]
theorem step132 (p : Nat → Bool) (h : Constraints p) : clause p c132 = true := by
  simpa only [c132,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause132
def c133 : List Lit := [(37, false), (10, false), (33, false), (45, false)]
theorem step133 (p : Nat → Bool) (h : Constraints p) : clause p c133 = true := by
  simpa only [c133,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause133
def c134 : List Lit := [(37, false), (10, false), (39, false), (45, false)]
theorem step134 (p : Nat → Bool) (h : Constraints p) : clause p c134 = true := by
  simpa only [c134,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause134
def c135 : List Lit := [(37, false), (33, false), (39, false), (45, false)]
theorem step135 (p : Nat → Bool) (h : Constraints p) : clause p c135 = true := by
  simpa only [c135,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause135
def c136 : List Lit := [(37, false), (38, false), (39, false), (45, false)]
theorem step136 (p : Nat → Bool) (h : Constraints p) : clause p c136 = true := by
  simpa only [c136,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause136
def c137 : List Lit := [(37, false), (155, true), (10, true), (33, true), (38, true), (45, true)]
theorem step137 (p : Nat → Bool) (h : Constraints p) : clause p c137 = true := by
  simpa only [c137,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause137
def c138 : List Lit := [(38, false), (20, false), (34, false), (37, false)]
theorem step138 (p : Nat → Bool) (h : Constraints p) : clause p c138 = true := by
  simpa only [c138,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause138
def c139 : List Lit := [(38, false), (20, false), (37, false), (46, false)]
theorem step139 (p : Nat → Bool) (h : Constraints p) : clause p c139 = true := by
  simpa only [c139,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause139
def c140 : List Lit := [(38, false), (34, false), (37, false), (46, false)]
theorem step140 (p : Nat → Bool) (h : Constraints p) : clause p c140 = true := by
  simpa only [c140,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause140
def c141 : List Lit := [(38, false), (34, false), (37, false), (105, false)]
theorem step141 (p : Nat → Bool) (h : Constraints p) : clause p c141 = true := by
  simpa only [c141,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause141
def c142 : List Lit := [(38, false), (37, false), (46, false), (105, false)]
theorem step142 (p : Nat → Bool) (h : Constraints p) : clause p c142 = true := by
  simpa only [c142,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause142
def c143 : List Lit := [(39, false), (157, true), (40, true)]
theorem step143 (p : Nat → Bool) (h : Constraints p) : clause p c143 = true := by
  simpa only [c143,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause143
def c144 : List Lit := [(39, false), (157, true), (37, true)]
theorem step144 (p : Nat → Bool) (h : Constraints p) : clause p c144 = true := by
  simpa only [c144,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause144
def c145 : List Lit := [(40, false), (158, true), (39, true)]
theorem step145 (p : Nat → Bool) (h : Constraints p) : clause p c145 = true := by
  simpa only [c145,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause145
def c146 : List Lit := [(40, false), (158, true), (35, true)]
theorem step146 (p : Nat → Bool) (h : Constraints p) : clause p c146 = true := by
  simpa only [c146,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause146
def c147 : List Lit := [(41, false), (12, false), (26, false), (43, false)]
theorem step147 (p : Nat → Bool) (h : Constraints p) : clause p c147 = true := by
  simpa only [c147,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause147
def c148 : List Lit := [(41, false), (12, false), (26, false), (47, false)]
theorem step148 (p : Nat → Bool) (h : Constraints p) : clause p c148 = true := by
  simpa only [c148,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause148
def c149 : List Lit := [(41, false), (12, false), (43, false), (47, false)]
theorem step149 (p : Nat → Bool) (h : Constraints p) : clause p c149 = true := by
  simpa only [c149,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause149
def c150 : List Lit := [(41, false), (159, true), (12, true), (26, true), (43, true)]
theorem step150 (p : Nat → Bool) (h : Constraints p) : clause p c150 = true := by
  simpa only [c150,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause150
def c151 : List Lit := [(42, false), (160, true), (49, true)]
theorem step151 (p : Nat → Bool) (h : Constraints p) : clause p c151 = true := by
  simpa only [c151,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause151
def c152 : List Lit := [(42, false), (160, true), (44, true)]
theorem step152 (p : Nat → Bool) (h : Constraints p) : clause p c152 = true := by
  simpa only [c152,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause152
def c153 : List Lit := [(43, false), (35, false), (41, false), (44, false)]
theorem step153 (p : Nat → Bool) (h : Constraints p) : clause p c153 = true := by
  simpa only [c153,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause153
def c154 : List Lit := [(43, false), (35, false), (44, false), (114, false)]
theorem step154 (p : Nat → Bool) (h : Constraints p) : clause p c154 = true := by
  simpa only [c154,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause154
def c155 : List Lit := [(44, false), (36, false), (42, false), (43, false)]
theorem step155 (p : Nat → Bool) (h : Constraints p) : clause p c155 = true := by
  simpa only [c155,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause155
def c156 : List Lit := [(44, false), (162, true), (42, true), (43, true)]
theorem step156 (p : Nat → Bool) (h : Constraints p) : clause p c156 = true := by
  simpa only [c156,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause156
def c157 : List Lit := [(44, false), (162, true), (36, true), (43, true)]
theorem step157 (p : Nat → Bool) (h : Constraints p) : clause p c157 = true := by
  simpa only [c157,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause157
def c158 : List Lit := [(45, false), (37, false), (46, false), (47, false)]
theorem step158 (p : Nat → Bool) (h : Constraints p) : clause p c158 = true := by
  simpa only [c158,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause158
def c159 : List Lit := [(45, false), (37, false), (46, false), (115, false)]
theorem step159 (p : Nat → Bool) (h : Constraints p) : clause p c159 = true := by
  simpa only [c159,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause159
def c160 : List Lit := [(45, false), (37, false), (47, false), (115, false)]
theorem step160 (p : Nat → Bool) (h : Constraints p) : clause p c160 = true := by
  simpa only [c160,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause160
def c161 : List Lit := [(45, false), (46, false), (47, false), (115, false)]
theorem step161 (p : Nat → Bool) (h : Constraints p) : clause p c161 = true := by
  simpa only [c161,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause161
def c162 : List Lit := [(46, false), (164, true), (45, true), (48, true), (49, true)]
theorem step162 (p : Nat → Bool) (h : Constraints p) : clause p c162 = true := by
  simpa only [c162,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause162
def c163 : List Lit := [(46, false), (164, true), (38, true), (45, true), (48, true)]
theorem step163 (p : Nat → Bool) (h : Constraints p) : clause p c163 = true := by
  simpa only [c163,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause163
def c164 : List Lit := [(165, false), (29, false), (48, false)]
theorem step164 (p : Nat → Bool) (h : Constraints p) : clause p c164 = true := by
  simpa only [c164,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause164
def c165 : List Lit := [(47, false), (165, true), (41, true), (45, true), (48, true)]
theorem step165 (p : Nat → Bool) (h : Constraints p) : clause p c165 = true := by
  simpa only [c165,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause165
def c166 : List Lit := [(47, false), (165, true), (29, true), (41, true), (48, true)]
theorem step166 (p : Nat → Bool) (h : Constraints p) : clause p c166 = true := by
  simpa only [c166,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause166
def c167 : List Lit := [(47, false), (165, true), (29, true), (41, true), (45, true)]
theorem step167 (p : Nat → Bool) (h : Constraints p) : clause p c167 = true := by
  simpa only [c167,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause167
def c168 : List Lit := [(48, false), (166, true), (47, true)]
theorem step168 (p : Nat → Bool) (h : Constraints p) : clause p c168 = true := by
  simpa only [c168,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause168
def c169 : List Lit := [(48, false), (166, true), (46, true)]
theorem step169 (p : Nat → Bool) (h : Constraints p) : clause p c169 = true := by
  simpa only [c169,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause169
def c170 : List Lit := [(49, false), (167, true), (46, true)]
theorem step170 (p : Nat → Bool) (h : Constraints p) : clause p c170 = true := by
  simpa only [c170,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause170
def c171 : List Lit := [(49, false), (167, true), (42, true)]
theorem step171 (p : Nat → Bool) (h : Constraints p) : clause p c171 = true := by
  simpa only [c171,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause171
def c172 : List Lit := [(50, false), (51, false), (52, false), (55, false)]
theorem step172 (p : Nat → Bool) (h : Constraints p) : clause p c172 = true := by
  simpa only [c172,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause172
def c173 : List Lit := [(50, false), (51, false), (52, false), (65, false)]
theorem step173 (p : Nat → Bool) (h : Constraints p) : clause p c173 = true := by
  simpa only [c173,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause173
def c174 : List Lit := [(50, false), (51, false), (52, false), (81, false)]
theorem step174 (p : Nat → Bool) (h : Constraints p) : clause p c174 = true := by
  simpa only [c174,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause174
def c175 : List Lit := [(50, false), (51, false), (55, false), (65, false)]
theorem step175 (p : Nat → Bool) (h : Constraints p) : clause p c175 = true := by
  simpa only [c175,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause175
def c176 : List Lit := [(50, false), (51, false), (55, false), (81, false)]
theorem step176 (p : Nat → Bool) (h : Constraints p) : clause p c176 = true := by
  simpa only [c176,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause176
def c177 : List Lit := [(50, false), (51, false), (65, false), (81, false)]
theorem step177 (p : Nat → Bool) (h : Constraints p) : clause p c177 = true := by
  simpa only [c177,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause177
def c178 : List Lit := [(50, false), (52, false), (55, false), (65, false)]
theorem step178 (p : Nat → Bool) (h : Constraints p) : clause p c178 = true := by
  simpa only [c178,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause178
def c179 : List Lit := [(50, false), (52, false), (55, false), (81, false)]
theorem step179 (p : Nat → Bool) (h : Constraints p) : clause p c179 = true := by
  simpa only [c179,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause179
def c180 : List Lit := [(50, false), (52, false), (65, false), (81, false)]
theorem step180 (p : Nat → Bool) (h : Constraints p) : clause p c180 = true := by
  simpa only [c180,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause180
def c181 : List Lit := [(50, false), (55, false), (65, false), (81, false)]
theorem step181 (p : Nat → Bool) (h : Constraints p) : clause p c181 = true := by
  simpa only [c181,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause181
def c182 : List Lit := [(50, false), (168, true), (52, true), (55, true), (65, true), (81, true)]
theorem step182 (p : Nat → Bool) (h : Constraints p) : clause p c182 = true := by
  simpa only [c182,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause182
def c183 : List Lit := [(50, false), (168, true), (51, true), (55, true), (65, true), (81, true)]
theorem step183 (p : Nat → Bool) (h : Constraints p) : clause p c183 = true := by
  simpa only [c183,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause183
def c184 : List Lit := [(50, false), (168, true), (51, true), (52, true), (55, true), (65, true)]
theorem step184 (p : Nat → Bool) (h : Constraints p) : clause p c184 = true := by
  simpa only [c184,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause184
def c185 : List Lit := [(51, false), (50, true), (56, true), (82, true)]
theorem step185 (p : Nat → Bool) (h : Constraints p) : clause p c185 = true := by
  simpa only [c185,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause185
def c186 : List Lit := [(51, false), (169, true), (56, true), (82, true)]
theorem step186 (p : Nat → Bool) (h : Constraints p) : clause p c186 = true := by
  simpa only [c186,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause186
def c187 : List Lit := [(51, false), (169, true), (50, true), (82, true)]
theorem step187 (p : Nat → Bool) (h : Constraints p) : clause p c187 = true := by
  simpa only [c187,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause187
def c188 : List Lit := [(51, false), (169, true), (50, true), (56, true)]
theorem step188 (p : Nat → Bool) (h : Constraints p) : clause p c188 = true := by
  simpa only [c188,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause188
def c189 : List Lit := [(170, false), (52, true)]
theorem step189 (p : Nat → Bool) (h : Constraints p) : clause p c189 = true := by
  simpa only [c189,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause189
def c190 : List Lit := [(52, false), (50, true), (70, true), (88, true)]
theorem step190 (p : Nat → Bool) (h : Constraints p) : clause p c190 = true := by
  simpa only [c190,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause190
def c191 : List Lit := [(52, false), (170, true), (70, true), (88, true)]
theorem step191 (p : Nat → Bool) (h : Constraints p) : clause p c191 = true := by
  simpa only [c191,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause191
def c192 : List Lit := [(52, false), (170, true), (50, true), (88, true)]
theorem step192 (p : Nat → Bool) (h : Constraints p) : clause p c192 = true := by
  simpa only [c192,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause192
def c193 : List Lit := [(52, false), (170, true), (50, true), (70, true)]
theorem step193 (p : Nat → Bool) (h : Constraints p) : clause p c193 = true := by
  simpa only [c193,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause193
def c194 : List Lit := [(53, false), (54, false), (55, false), (57, false)]
theorem step194 (p : Nat → Bool) (h : Constraints p) : clause p c194 = true := by
  simpa only [c194,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause194
def c195 : List Lit := [(53, false), (54, false), (55, false), (59, false)]
theorem step195 (p : Nat → Bool) (h : Constraints p) : clause p c195 = true := by
  simpa only [c195,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause195
def c196 : List Lit := [(53, false), (54, false), (57, false), (59, false)]
theorem step196 (p : Nat → Bool) (h : Constraints p) : clause p c196 = true := by
  simpa only [c196,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause196
def c197 : List Lit := [(53, false), (55, false), (57, false), (59, false)]
theorem step197 (p : Nat → Bool) (h : Constraints p) : clause p c197 = true := by
  simpa only [c197,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause197
def c198 : List Lit := [(53, false), (171, true), (54, true), (55, true), (59, true)]
theorem step198 (p : Nat → Bool) (h : Constraints p) : clause p c198 = true := by
  simpa only [c198,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause198
def c199 : List Lit := [(53, false), (171, true), (54, true), (55, true), (57, true)]
theorem step199 (p : Nat → Bool) (h : Constraints p) : clause p c199 = true := by
  simpa only [c199,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause199
def c200 : List Lit := [(172, false), (54, true)]
theorem step200 (p : Nat → Bool) (h : Constraints p) : clause p c200 = true := by
  simpa only [c200,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause200
def c201 : List Lit := [(54, false), (53, true), (56, true), (91, true)]
theorem step201 (p : Nat → Bool) (h : Constraints p) : clause p c201 = true := by
  simpa only [c201,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause201
def c202 : List Lit := [(172, false), (53, false), (91, false)]
theorem step202 (p : Nat → Bool) (h : Constraints p) : clause p c202 = true := by
  simpa only [c202,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause202
def c203 : List Lit := [(172, false), (56, false), (91, false)]
theorem step203 (p : Nat → Bool) (h : Constraints p) : clause p c203 = true := by
  simpa only [c203,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause203
def c204 : List Lit := [(54, false), (172, true), (56, true), (91, true)]
theorem step204 (p : Nat → Bool) (h : Constraints p) : clause p c204 = true := by
  simpa only [c204,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause204
def c205 : List Lit := [(54, false), (172, true), (53, true), (91, true)]
theorem step205 (p : Nat → Bool) (h : Constraints p) : clause p c205 = true := by
  simpa only [c205,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause205
def c206 : List Lit := [(54, false), (172, true), (53, true), (56, true)]
theorem step206 (p : Nat → Bool) (h : Constraints p) : clause p c206 = true := by
  simpa only [c206,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause206
def c207 : List Lit := [(56, false), (51, false), (54, false), (55, false)]
theorem step207 (p : Nat → Bool) (h : Constraints p) : clause p c207 = true := by
  simpa only [c207,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause207
def c208 : List Lit := [(56, false), (51, false), (54, false), (92, false)]
theorem step208 (p : Nat → Bool) (h : Constraints p) : clause p c208 = true := by
  simpa only [c208,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause208
def c209 : List Lit := [(56, false), (51, false), (55, false), (92, false)]
theorem step209 (p : Nat → Bool) (h : Constraints p) : clause p c209 = true := by
  simpa only [c209,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause209
def c210 : List Lit := [(56, false), (54, false), (55, false), (92, false)]
theorem step210 (p : Nat → Bool) (h : Constraints p) : clause p c210 = true := by
  simpa only [c210,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause210
def c211 : List Lit := [(56, false), (174, true), (54, true), (55, true), (92, true)]
theorem step211 (p : Nat → Bool) (h : Constraints p) : clause p c211 = true := by
  simpa only [c211,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause211
def c212 : List Lit := [(56, false), (174, true), (51, true), (55, true), (92, true)]
theorem step212 (p : Nat → Bool) (h : Constraints p) : clause p c212 = true := by
  simpa only [c212,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause212
def c213 : List Lit := [(57, false), (53, true), (58, true), (60, true)]
theorem step213 (p : Nat → Bool) (h : Constraints p) : clause p c213 = true := by
  simpa only [c213,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause213
def c214 : List Lit := [(57, false), (175, true), (58, true), (60, true)]
theorem step214 (p : Nat → Bool) (h : Constraints p) : clause p c214 = true := by
  simpa only [c214,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause214
def c215 : List Lit := [(57, false), (175, true), (53, true), (60, true)]
theorem step215 (p : Nat → Bool) (h : Constraints p) : clause p c215 = true := by
  simpa only [c215,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause215
def c216 : List Lit := [(57, false), (175, true), (53, true), (58, true)]
theorem step216 (p : Nat → Bool) (h : Constraints p) : clause p c216 = true := by
  simpa only [c216,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause216
def c217 : List Lit := [(58, false), (7, false), (55, false), (61, false)]
theorem step217 (p : Nat → Bool) (h : Constraints p) : clause p c217 = true := by
  simpa only [c217,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause217
def c218 : List Lit := [(58, false), (7, false), (57, false), (61, false)]
theorem step218 (p : Nat → Bool) (h : Constraints p) : clause p c218 = true := by
  simpa only [c218,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause218
def c219 : List Lit := [(58, false), (7, false), (61, false), (94, false)]
theorem step219 (p : Nat → Bool) (h : Constraints p) : clause p c219 = true := by
  simpa only [c219,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause219
def c220 : List Lit := [(58, false), (55, false), (57, false), (61, false)]
theorem step220 (p : Nat → Bool) (h : Constraints p) : clause p c220 = true := by
  simpa only [c220,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause220
def c221 : List Lit := [(58, false), (55, false), (61, false), (94, false)]
theorem step221 (p : Nat → Bool) (h : Constraints p) : clause p c221 = true := by
  simpa only [c221,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause221
def c222 : List Lit := [(58, false), (57, false), (61, false), (94, false)]
theorem step222 (p : Nat → Bool) (h : Constraints p) : clause p c222 = true := by
  simpa only [c222,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause222
def c223 : List Lit := [(177, false), (59, true)]
theorem step223 (p : Nat → Bool) (h : Constraints p) : clause p c223 = true := by
  simpa only [c223,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause223
def c224 : List Lit := [(59, false), (53, true), (60, true), (96, true)]
theorem step224 (p : Nat → Bool) (h : Constraints p) : clause p c224 = true := by
  simpa only [c224,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause224
def c225 : List Lit := [(59, false), (177, true), (60, true), (96, true)]
theorem step225 (p : Nat → Bool) (h : Constraints p) : clause p c225 = true := by
  simpa only [c225,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause225
def c226 : List Lit := [(59, false), (177, true), (53, true), (96, true)]
theorem step226 (p : Nat → Bool) (h : Constraints p) : clause p c226 = true := by
  simpa only [c226,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause226
def c227 : List Lit := [(59, false), (177, true), (53, true), (60, true)]
theorem step227 (p : Nat → Bool) (h : Constraints p) : clause p c227 = true := by
  simpa only [c227,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause227
def c228 : List Lit := [(60, false), (57, false), (59, false), (61, false)]
theorem step228 (p : Nat → Bool) (h : Constraints p) : clause p c228 = true := by
  simpa only [c228,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause228
def c229 : List Lit := [(61, false), (58, false), (60, false), (62, false)]
theorem step229 (p : Nat → Bool) (h : Constraints p) : clause p c229 = true := by
  simpa only [c229,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause229
def c230 : List Lit := [(179, false), (58, false), (62, false)]
theorem step230 (p : Nat → Bool) (h : Constraints p) : clause p c230 = true := by
  simpa only [c230,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause230
def c231 : List Lit := [(61, false), (179, true), (58, true), (60, true)]
theorem step231 (p : Nat → Bool) (h : Constraints p) : clause p c231 = true := by
  simpa only [c231,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause231
def c232 : List Lit := [(62, false), (61, true)]
theorem step232 (p : Nat → Bool) (h : Constraints p) : clause p c232 = true := by
  simpa only [c232,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause232
def c233 : List Lit := [(62, true)]
theorem step233 (p : Nat → Bool) (h : Constraints p) : clause p c233 = true := by
  simpa only [c233,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause233
def c234 : List Lit := [(63, false), (64, false), (65, false), (68, false)]
theorem step234 (p : Nat → Bool) (h : Constraints p) : clause p c234 = true := by
  simpa only [c234,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause234
def c235 : List Lit := [(63, false), (181, true), (65, true), (68, true)]
theorem step235 (p : Nat → Bool) (h : Constraints p) : clause p c235 = true := by
  simpa only [c235,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause235
def c236 : List Lit := [(63, false), (181, true), (64, true), (65, true)]
theorem step236 (p : Nat → Bool) (h : Constraints p) : clause p c236 = true := by
  simpa only [c236,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause236
def c237 : List Lit := [(64, false), (182, true), (63, true), (69, true)]
theorem step237 (p : Nat → Bool) (h : Constraints p) : clause p c237 = true := by
  simpa only [c237,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause237
def c238 : List Lit := [(64, false), (182, true), (8, true), (69, true)]
theorem step238 (p : Nat → Bool) (h : Constraints p) : clause p c238 = true := by
  simpa only [c238,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause238
def c239 : List Lit := [(64, false), (182, true), (8, true), (63, true)]
theorem step239 (p : Nat → Bool) (h : Constraints p) : clause p c239 = true := by
  simpa only [c239,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause239
def c240 : List Lit := [(65, false), (50, false), (66, false), (70, false)]
theorem step240 (p : Nat → Bool) (h : Constraints p) : clause p c240 = true := by
  simpa only [c240,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause240
def c241 : List Lit := [(65, false), (50, false), (66, false), (73, false)]
theorem step241 (p : Nat → Bool) (h : Constraints p) : clause p c241 = true := by
  simpa only [c241,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause241
def c242 : List Lit := [(65, false), (50, false), (66, false), (101, false)]
theorem step242 (p : Nat → Bool) (h : Constraints p) : clause p c242 = true := by
  simpa only [c242,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause242
def c243 : List Lit := [(65, false), (50, false), (73, false), (101, false)]
theorem step243 (p : Nat → Bool) (h : Constraints p) : clause p c243 = true := by
  simpa only [c243,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause243
def c244 : List Lit := [(65, false), (63, false), (66, false), (70, false)]
theorem step244 (p : Nat → Bool) (h : Constraints p) : clause p c244 = true := by
  simpa only [c244,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause244
def c245 : List Lit := [(65, false), (63, false), (66, false), (73, false)]
theorem step245 (p : Nat → Bool) (h : Constraints p) : clause p c245 = true := by
  simpa only [c245,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause245
def c246 : List Lit := [(65, false), (66, false), (70, false), (101, false)]
theorem step246 (p : Nat → Bool) (h : Constraints p) : clause p c246 = true := by
  simpa only [c246,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause246
def c247 : List Lit := [(65, false), (66, false), (73, false), (101, false)]
theorem step247 (p : Nat → Bool) (h : Constraints p) : clause p c247 = true := by
  simpa only [c247,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause247
def c248 : List Lit := [(66, false), (65, false), (67, false), (72, false)]
theorem step248 (p : Nat → Bool) (h : Constraints p) : clause p c248 = true := by
  simpa only [c248,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause248
def c249 : List Lit := [(66, false), (184, true), (65, true), (72, true)]
theorem step249 (p : Nat → Bool) (h : Constraints p) : clause p c249 = true := by
  simpa only [c249,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause249
def c250 : List Lit := [(66, false), (184, true), (65, true), (67, true)]
theorem step250 (p : Nat → Bool) (h : Constraints p) : clause p c250 = true := by
  simpa only [c250,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause250
def c251 : List Lit := [(67, false), (185, true), (75, true)]
theorem step251 (p : Nat → Bool) (h : Constraints p) : clause p c251 = true := by
  simpa only [c251,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause251
def c252 : List Lit := [(67, false), (185, true), (66, true)]
theorem step252 (p : Nat → Bool) (h : Constraints p) : clause p c252 = true := by
  simpa only [c252,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause252
def c253 : List Lit := [(68, false), (10, false), (63, false), (71, false)]
theorem step253 (p : Nat → Bool) (h : Constraints p) : clause p c253 = true := by
  simpa only [c253,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause253
def c254 : List Lit := [(68, false), (10, false), (69, false), (71, false)]
theorem step254 (p : Nat → Bool) (h : Constraints p) : clause p c254 = true := by
  simpa only [c254,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause254
def c255 : List Lit := [(68, false), (186, true), (63, true), (69, true), (70, true), (71, true)]
theorem step255 (p : Nat → Bool) (h : Constraints p) : clause p c255 = true := by
  simpa only [c255,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause255
def c256 : List Lit := [(68, false), (186, true), (10, true), (63, true), (69, true), (70, true)]
theorem step256 (p : Nat → Bool) (h : Constraints p) : clause p c256 = true := by
  simpa only [c256,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause256
def c257 : List Lit := [(69, false), (64, false), (68, false), (76, false)]
theorem step257 (p : Nat → Bool) (h : Constraints p) : clause p c257 = true := by
  simpa only [c257,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause257
def c258 : List Lit := [(69, false), (64, false), (76, false), (105, false)]
theorem step258 (p : Nat → Bool) (h : Constraints p) : clause p c258 = true := by
  simpa only [c258,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause258
def c259 : List Lit := [(69, false), (68, false), (76, false), (105, false)]
theorem step259 (p : Nat → Bool) (h : Constraints p) : clause p c259 = true := by
  simpa only [c259,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause259
def c260 : List Lit := [(70, false), (52, false), (65, false), (68, false)]
theorem step260 (p : Nat → Bool) (h : Constraints p) : clause p c260 = true := by
  simpa only [c260,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause260
def c261 : List Lit := [(70, false), (52, false), (65, false), (72, false)]
theorem step261 (p : Nat → Bool) (h : Constraints p) : clause p c261 = true := by
  simpa only [c261,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause261
def c262 : List Lit := [(70, false), (52, false), (65, false), (77, false)]
theorem step262 (p : Nat → Bool) (h : Constraints p) : clause p c262 = true := by
  simpa only [c262,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause262
def c263 : List Lit := [(70, false), (52, false), (65, false), (106, false)]
theorem step263 (p : Nat → Bool) (h : Constraints p) : clause p c263 = true := by
  simpa only [c263,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause263
def c264 : List Lit := [(70, false), (52, false), (68, false), (72, false)]
theorem step264 (p : Nat → Bool) (h : Constraints p) : clause p c264 = true := by
  simpa only [c264,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause264
def c265 : List Lit := [(70, false), (52, false), (68, false), (77, false)]
theorem step265 (p : Nat → Bool) (h : Constraints p) : clause p c265 = true := by
  simpa only [c265,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause265
def c266 : List Lit := [(70, false), (52, false), (68, false), (106, false)]
theorem step266 (p : Nat → Bool) (h : Constraints p) : clause p c266 = true := by
  simpa only [c266,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause266
def c267 : List Lit := [(70, false), (52, false), (72, false), (77, false)]
theorem step267 (p : Nat → Bool) (h : Constraints p) : clause p c267 = true := by
  simpa only [c267,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause267
def c268 : List Lit := [(70, false), (52, false), (72, false), (106, false)]
theorem step268 (p : Nat → Bool) (h : Constraints p) : clause p c268 = true := by
  simpa only [c268,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause268
def c269 : List Lit := [(70, false), (52, false), (77, false), (106, false)]
theorem step269 (p : Nat → Bool) (h : Constraints p) : clause p c269 = true := by
  simpa only [c269,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause269
def c270 : List Lit := [(70, false), (65, false), (68, false), (72, false)]
theorem step270 (p : Nat → Bool) (h : Constraints p) : clause p c270 = true := by
  simpa only [c270,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause270
def c271 : List Lit := [(70, false), (65, false), (68, false), (77, false)]
theorem step271 (p : Nat → Bool) (h : Constraints p) : clause p c271 = true := by
  simpa only [c271,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause271
def c272 : List Lit := [(70, false), (65, false), (68, false), (106, false)]
theorem step272 (p : Nat → Bool) (h : Constraints p) : clause p c272 = true := by
  simpa only [c272,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause272
def c273 : List Lit := [(70, false), (65, false), (72, false), (77, false)]
theorem step273 (p : Nat → Bool) (h : Constraints p) : clause p c273 = true := by
  simpa only [c273,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause273
def c274 : List Lit := [(70, false), (65, false), (72, false), (106, false)]
theorem step274 (p : Nat → Bool) (h : Constraints p) : clause p c274 = true := by
  simpa only [c274,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause274
def c275 : List Lit := [(70, false), (65, false), (77, false), (106, false)]
theorem step275 (p : Nat → Bool) (h : Constraints p) : clause p c275 = true := by
  simpa only [c275,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause275
def c276 : List Lit := [(70, false), (68, false), (72, false), (77, false)]
theorem step276 (p : Nat → Bool) (h : Constraints p) : clause p c276 = true := by
  simpa only [c276,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause276
def c277 : List Lit := [(70, false), (68, false), (72, false), (106, false)]
theorem step277 (p : Nat → Bool) (h : Constraints p) : clause p c277 = true := by
  simpa only [c277,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause277
def c278 : List Lit := [(70, false), (68, false), (77, false), (106, false)]
theorem step278 (p : Nat → Bool) (h : Constraints p) : clause p c278 = true := by
  simpa only [c278,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause278
def c279 : List Lit := [(70, false), (72, false), (77, false), (106, false)]
theorem step279 (p : Nat → Bool) (h : Constraints p) : clause p c279 = true := by
  simpa only [c279,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause279
def c280 : List Lit := [(70, false), (188, true), (52, true), (68, true), (72, true), (77, true), (106, true)]
theorem step280 (p : Nat → Bool) (h : Constraints p) : clause p c280 = true := by
  simpa only [c280,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause280
def c281 : List Lit := [(70, false), (188, true), (52, true), (65, true), (68, true), (77, true), (106, true)]
theorem step281 (p : Nat → Bool) (h : Constraints p) : clause p c281 = true := by
  simpa only [c281,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause281
def c282 : List Lit := [(71, false), (189, true), (72, true)]
theorem step282 (p : Nat → Bool) (h : Constraints p) : clause p c282 = true := by
  simpa only [c282,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause282
def c283 : List Lit := [(71, false), (189, true), (68, true)]
theorem step283 (p : Nat → Bool) (h : Constraints p) : clause p c283 = true := by
  simpa only [c283,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause283
def c284 : List Lit := [(72, false), (66, true), (70, true), (71, true)]
theorem step284 (p : Nat → Bool) (h : Constraints p) : clause p c284 = true := by
  simpa only [c284,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause284
def c285 : List Lit := [(72, false), (190, true), (70, true), (71, true)]
theorem step285 (p : Nat → Bool) (h : Constraints p) : clause p c285 = true := by
  simpa only [c285,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause285
def c286 : List Lit := [(72, false), (190, true), (66, true), (71, true)]
theorem step286 (p : Nat → Bool) (h : Constraints p) : clause p c286 = true := by
  simpa only [c286,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause286
def c287 : List Lit := [(72, false), (190, true), (66, true), (70, true)]
theorem step287 (p : Nat → Bool) (h : Constraints p) : clause p c287 = true := by
  simpa only [c287,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause287
def c288 : List Lit := [(73, false), (12, false), (55, false), (77, false)]
theorem step288 (p : Nat → Bool) (h : Constraints p) : clause p c288 = true := by
  simpa only [c288,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause288
def c289 : List Lit := [(73, false), (12, false), (65, false), (77, false)]
theorem step289 (p : Nat → Bool) (h : Constraints p) : clause p c289 = true := by
  simpa only [c289,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause289
def c290 : List Lit := [(73, false), (55, false), (65, false), (77, false)]
theorem step290 (p : Nat → Bool) (h : Constraints p) : clause p c290 = true := by
  simpa only [c290,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause290
def c291 : List Lit := [(73, false), (191, true), (55, true), (65, true), (77, true)]
theorem step291 (p : Nat → Bool) (h : Constraints p) : clause p c291 = true := by
  simpa only [c291,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause291
def c292 : List Lit := [(73, false), (191, true), (12, true), (55, true), (65, true)]
theorem step292 (p : Nat → Bool) (h : Constraints p) : clause p c292 = true := by
  simpa only [c292,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause292
def c293 : List Lit := [(74, false), (192, true), (79, true)]
theorem step293 (p : Nat → Bool) (h : Constraints p) : clause p c293 = true := by
  simpa only [c293,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause293
def c294 : List Lit := [(74, false), (192, true), (75, true)]
theorem step294 (p : Nat → Bool) (h : Constraints p) : clause p c294 = true := by
  simpa only [c294,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause294
def c295 : List Lit := [(75, false), (193, true), (74, true)]
theorem step295 (p : Nat → Bool) (h : Constraints p) : clause p c295 = true := by
  simpa only [c295,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause295
def c296 : List Lit := [(75, false), (193, true), (67, true)]
theorem step296 (p : Nat → Bool) (h : Constraints p) : clause p c296 = true := by
  simpa only [c296,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause296
def c297 : List Lit := [(76, false), (69, false), (78, false), (79, false)]
theorem step297 (p : Nat → Bool) (h : Constraints p) : clause p c297 = true := by
  simpa only [c297,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause297
def c298 : List Lit := [(76, false), (194, true), (78, true), (79, true)]
theorem step298 (p : Nat → Bool) (h : Constraints p) : clause p c298 = true := by
  simpa only [c298,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause298
def c299 : List Lit := [(76, false), (194, true), (69, true), (79, true)]
theorem step299 (p : Nat → Bool) (h : Constraints p) : clause p c299 = true := by
  simpa only [c299,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause299
def c300 : List Lit := [(76, false), (194, true), (69, true), (78, true)]
theorem step300 (p : Nat → Bool) (h : Constraints p) : clause p c300 = true := by
  simpa only [c300,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause300
def c301 : List Lit := [(77, false), (70, false), (73, false), (78, false)]
theorem step301 (p : Nat → Bool) (h : Constraints p) : clause p c301 = true := by
  simpa only [c301,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause301
def c302 : List Lit := [(77, false), (195, true), (73, true), (78, true)]
theorem step302 (p : Nat → Bool) (h : Constraints p) : clause p c302 = true := by
  simpa only [c302,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause302
def c303 : List Lit := [(77, false), (195, true), (70, true), (78, true)]
theorem step303 (p : Nat → Bool) (h : Constraints p) : clause p c303 = true := by
  simpa only [c303,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause303
def c304 : List Lit := [(77, false), (195, true), (70, true), (73, true)]
theorem step304 (p : Nat → Bool) (h : Constraints p) : clause p c304 = true := by
  simpa only [c304,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause304
def c305 : List Lit := [(78, false), (196, true), (77, true)]
theorem step305 (p : Nat → Bool) (h : Constraints p) : clause p c305 = true := by
  simpa only [c305,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause305
def c306 : List Lit := [(78, false), (196, true), (76, true)]
theorem step306 (p : Nat → Bool) (h : Constraints p) : clause p c306 = true := by
  simpa only [c306,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause306
def c307 : List Lit := [(79, false), (197, true), (76, true)]
theorem step307 (p : Nat → Bool) (h : Constraints p) : clause p c307 = true := by
  simpa only [c307,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause307
def c308 : List Lit := [(79, false), (197, true), (74, true)]
theorem step308 (p : Nat → Bool) (h : Constraints p) : clause p c308 = true := by
  simpa only [c308,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause308
def c309 : List Lit := [(80, false), (14, false), (81, false), (83, false)]
theorem step309 (p : Nat → Bool) (h : Constraints p) : clause p c309 = true := by
  simpa only [c309,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause309
def c310 : List Lit := [(80, false), (14, false), (81, false), (86, false)]
theorem step310 (p : Nat → Bool) (h : Constraints p) : clause p c310 = true := by
  simpa only [c310,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause310
def c311 : List Lit := [(80, false), (81, false), (83, false), (86, false)]
theorem step311 (p : Nat → Bool) (h : Constraints p) : clause p c311 = true := by
  simpa only [c311,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause311
def c312 : List Lit := [(81, false), (16, false), (50, false), (84, false)]
theorem step312 (p : Nat → Bool) (h : Constraints p) : clause p c312 = true := by
  simpa only [c312,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause312
def c313 : List Lit := [(81, false), (16, false), (50, false), (88, false)]
theorem step313 (p : Nat → Bool) (h : Constraints p) : clause p c313 = true := by
  simpa only [c313,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause313
def c314 : List Lit := [(81, false), (16, false), (50, false), (101, false)]
theorem step314 (p : Nat → Bool) (h : Constraints p) : clause p c314 = true := by
  simpa only [c314,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause314
def c315 : List Lit := [(81, false), (16, false), (82, false), (101, false)]
theorem step315 (p : Nat → Bool) (h : Constraints p) : clause p c315 = true := by
  simpa only [c315,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause315
def c316 : List Lit := [(81, false), (50, false), (80, false), (88, false)]
theorem step316 (p : Nat → Bool) (h : Constraints p) : clause p c316 = true := by
  simpa only [c316,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause316
def c317 : List Lit := [(81, false), (50, false), (80, false), (101, false)]
theorem step317 (p : Nat → Bool) (h : Constraints p) : clause p c317 = true := by
  simpa only [c317,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause317
def c318 : List Lit := [(81, false), (50, false), (82, false), (101, false)]
theorem step318 (p : Nat → Bool) (h : Constraints p) : clause p c318 = true := by
  simpa only [c318,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause318
def c319 : List Lit := [(81, false), (50, false), (84, false), (88, false)]
theorem step319 (p : Nat → Bool) (h : Constraints p) : clause p c319 = true := by
  simpa only [c319,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause319
def c320 : List Lit := [(81, false), (50, false), (84, false), (101, false)]
theorem step320 (p : Nat → Bool) (h : Constraints p) : clause p c320 = true := by
  simpa only [c320,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause320
def c321 : List Lit := [(81, false), (50, false), (88, false), (101, false)]
theorem step321 (p : Nat → Bool) (h : Constraints p) : clause p c321 = true := by
  simpa only [c321,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause321
def c322 : List Lit := [(81, false), (80, false), (82, false), (88, false)]
theorem step322 (p : Nat → Bool) (h : Constraints p) : clause p c322 = true := by
  simpa only [c322,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause322
def c323 : List Lit := [(81, false), (82, false), (84, false), (88, false)]
theorem step323 (p : Nat → Bool) (h : Constraints p) : clause p c323 = true := by
  simpa only [c323,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause323
def c324 : List Lit := [(81, false), (199, true), (50, true), (80, true), (82, true), (84, true), (88, true), (101, true)]
theorem step324 (p : Nat → Bool) (h : Constraints p) : clause p c324 = true := by
  simpa only [c324,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause324
def c325 : List Lit := [(81, false), (199, true), (16, true), (80, true), (82, true), (84, true), (88, true), (101, true)]
theorem step325 (p : Nat → Bool) (h : Constraints p) : clause p c325 = true := by
  simpa only [c325,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause325
def c326 : List Lit := [(81, false), (199, true), (16, true), (50, true), (80, true), (84, true), (88, true), (101, true)]
theorem step326 (p : Nat → Bool) (h : Constraints p) : clause p c326 = true := by
  simpa only [c326,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause326
def c327 : List Lit := [(81, false), (199, true), (16, true), (50, true), (80, true), (82, true), (88, true), (101, true)]
theorem step327 (p : Nat → Bool) (h : Constraints p) : clause p c327 = true := by
  simpa only [c327,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause327
def c328 : List Lit := [(81, false), (199, true), (16, true), (50, true), (80, true), (82, true), (84, true), (101, true)]
theorem step328 (p : Nat → Bool) (h : Constraints p) : clause p c328 = true := by
  simpa only [c328,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause328
def c329 : List Lit := [(82, false), (17, false), (51, false), (81, false)]
theorem step329 (p : Nat → Bool) (h : Constraints p) : clause p c329 = true := by
  simpa only [c329,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause329
def c330 : List Lit := [(82, false), (17, false), (51, false), (85, false)]
theorem step330 (p : Nat → Bool) (h : Constraints p) : clause p c330 = true := by
  simpa only [c330,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause330
def c331 : List Lit := [(82, false), (17, false), (51, false), (92, false)]
theorem step331 (p : Nat → Bool) (h : Constraints p) : clause p c331 = true := by
  simpa only [c331,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause331
def c332 : List Lit := [(82, false), (17, false), (51, false), (102, false)]
theorem step332 (p : Nat → Bool) (h : Constraints p) : clause p c332 = true := by
  simpa only [c332,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause332
def c333 : List Lit := [(82, false), (17, false), (81, false), (85, false)]
theorem step333 (p : Nat → Bool) (h : Constraints p) : clause p c333 = true := by
  simpa only [c333,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause333
def c334 : List Lit := [(82, false), (17, false), (81, false), (92, false)]
theorem step334 (p : Nat → Bool) (h : Constraints p) : clause p c334 = true := by
  simpa only [c334,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause334
def c335 : List Lit := [(82, false), (17, false), (85, false), (92, false)]
theorem step335 (p : Nat → Bool) (h : Constraints p) : clause p c335 = true := by
  simpa only [c335,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause335
def c336 : List Lit := [(82, false), (17, false), (85, false), (102, false)]
theorem step336 (p : Nat → Bool) (h : Constraints p) : clause p c336 = true := by
  simpa only [c336,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause336
def c337 : List Lit := [(82, false), (51, false), (81, false), (85, false)]
theorem step337 (p : Nat → Bool) (h : Constraints p) : clause p c337 = true := by
  simpa only [c337,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause337
def c338 : List Lit := [(82, false), (51, false), (81, false), (92, false)]
theorem step338 (p : Nat → Bool) (h : Constraints p) : clause p c338 = true := by
  simpa only [c338,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause338
def c339 : List Lit := [(82, false), (51, false), (81, false), (102, false)]
theorem step339 (p : Nat → Bool) (h : Constraints p) : clause p c339 = true := by
  simpa only [c339,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause339
def c340 : List Lit := [(82, false), (51, false), (85, false), (92, false)]
theorem step340 (p : Nat → Bool) (h : Constraints p) : clause p c340 = true := by
  simpa only [c340,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause340
def c341 : List Lit := [(82, false), (51, false), (85, false), (102, false)]
theorem step341 (p : Nat → Bool) (h : Constraints p) : clause p c341 = true := by
  simpa only [c341,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause341
def c342 : List Lit := [(82, false), (51, false), (92, false), (102, false)]
theorem step342 (p : Nat → Bool) (h : Constraints p) : clause p c342 = true := by
  simpa only [c342,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause342
def c343 : List Lit := [(82, false), (81, false), (85, false), (92, false)]
theorem step343 (p : Nat → Bool) (h : Constraints p) : clause p c343 = true := by
  simpa only [c343,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause343
def c344 : List Lit := [(82, false), (81, false), (85, false), (102, false)]
theorem step344 (p : Nat → Bool) (h : Constraints p) : clause p c344 = true := by
  simpa only [c344,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause344
def c345 : List Lit := [(82, false), (81, false), (92, false), (102, false)]
theorem step345 (p : Nat → Bool) (h : Constraints p) : clause p c345 = true := by
  simpa only [c345,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause345
def c346 : List Lit := [(82, false), (85, false), (92, false), (102, false)]
theorem step346 (p : Nat → Bool) (h : Constraints p) : clause p c346 = true := by
  simpa only [c346,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause346
def c347 : List Lit := [(83, false), (201, true), (18, true), (80, true), (84, true), (89, true)]
theorem step347 (p : Nat → Bool) (h : Constraints p) : clause p c347 = true := by
  simpa only [c347,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause347
def c348 : List Lit := [(84, false), (81, false), (83, false), (85, false)]
theorem step348 (p : Nat → Bool) (h : Constraints p) : clause p c348 = true := by
  simpa only [c348,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause348
def c349 : List Lit := [(84, false), (81, false), (83, false), (90, false)]
theorem step349 (p : Nat → Bool) (h : Constraints p) : clause p c349 = true := by
  simpa only [c349,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause349
def c350 : List Lit := [(84, false), (81, false), (83, false), (94, false)]
theorem step350 (p : Nat → Bool) (h : Constraints p) : clause p c350 = true := by
  simpa only [c350,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause350
def c351 : List Lit := [(84, false), (81, false), (85, false), (90, false)]
theorem step351 (p : Nat → Bool) (h : Constraints p) : clause p c351 = true := by
  simpa only [c351,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause351
def c352 : List Lit := [(84, false), (81, false), (85, false), (94, false)]
theorem step352 (p : Nat → Bool) (h : Constraints p) : clause p c352 = true := by
  simpa only [c352,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause352
def c353 : List Lit := [(84, false), (81, false), (90, false), (94, false)]
theorem step353 (p : Nat → Bool) (h : Constraints p) : clause p c353 = true := by
  simpa only [c353,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause353
def c354 : List Lit := [(84, false), (83, false), (85, false), (90, false)]
theorem step354 (p : Nat → Bool) (h : Constraints p) : clause p c354 = true := by
  simpa only [c354,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause354
def c355 : List Lit := [(84, false), (83, false), (85, false), (94, false)]
theorem step355 (p : Nat → Bool) (h : Constraints p) : clause p c355 = true := by
  simpa only [c355,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause355
def c356 : List Lit := [(84, false), (83, false), (90, false), (94, false)]
theorem step356 (p : Nat → Bool) (h : Constraints p) : clause p c356 = true := by
  simpa only [c356,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause356
def c357 : List Lit := [(84, false), (85, false), (90, false), (94, false)]
theorem step357 (p : Nat → Bool) (h : Constraints p) : clause p c357 = true := by
  simpa only [c357,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause357
def c358 : List Lit := [(85, false), (19, true), (82, true), (84, true), (95, true)]
theorem step358 (p : Nat → Bool) (h : Constraints p) : clause p c358 = true := by
  simpa only [c358,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause358
def c359 : List Lit := [(85, false), (203, true), (82, true), (84, true), (95, true)]
theorem step359 (p : Nat → Bool) (h : Constraints p) : clause p c359 = true := by
  simpa only [c359,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause359
def c360 : List Lit := [(85, false), (203, true), (19, true), (84, true), (95, true)]
theorem step360 (p : Nat → Bool) (h : Constraints p) : clause p c360 = true := by
  simpa only [c360,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause360
def c361 : List Lit := [(85, false), (203, true), (19, true), (82, true), (95, true)]
theorem step361 (p : Nat → Bool) (h : Constraints p) : clause p c361 = true := by
  simpa only [c361,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause361
def c362 : List Lit := [(85, false), (203, true), (19, true), (82, true), (84, true)]
theorem step362 (p : Nat → Bool) (h : Constraints p) : clause p c362 = true := by
  simpa only [c362,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause362
def c363 : List Lit := [(86, false), (204, true), (87, true), (88, true), (89, true), (96, true)]
theorem step363 (p : Nat → Bool) (h : Constraints p) : clause p c363 = true := by
  simpa only [c363,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause363
def c364 : List Lit := [(86, false), (204, true), (80, true), (87, true), (88, true), (96, true)]
theorem step364 (p : Nat → Bool) (h : Constraints p) : clause p c364 = true := by
  simpa only [c364,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause364
def c365 : List Lit := [(87, false), (20, false), (86, false), (97, false)]
theorem step365 (p : Nat → Bool) (h : Constraints p) : clause p c365 = true := by
  simpa only [c365,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause365
def c366 : List Lit := [(87, false), (20, false), (86, false), (105, false)]
theorem step366 (p : Nat → Bool) (h : Constraints p) : clause p c366 = true := by
  simpa only [c366,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause366
def c367 : List Lit := [(87, false), (86, false), (97, false), (105, false)]
theorem step367 (p : Nat → Bool) (h : Constraints p) : clause p c367 = true := by
  simpa only [c367,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause367
def c368 : List Lit := [(88, false), (21, false), (52, false), (81, false)]
theorem step368 (p : Nat → Bool) (h : Constraints p) : clause p c368 = true := by
  simpa only [c368,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause368
def c369 : List Lit := [(88, false), (21, false), (52, false), (86, false)]
theorem step369 (p : Nat → Bool) (h : Constraints p) : clause p c369 = true := by
  simpa only [c369,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause369
def c370 : List Lit := [(88, false), (21, false), (52, false), (90, false)]
theorem step370 (p : Nat → Bool) (h : Constraints p) : clause p c370 = true := by
  simpa only [c370,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause370
def c371 : List Lit := [(88, false), (21, false), (52, false), (98, false)]
theorem step371 (p : Nat → Bool) (h : Constraints p) : clause p c371 = true := by
  simpa only [c371,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause371
def c372 : List Lit := [(88, false), (21, false), (52, false), (106, false)]
theorem step372 (p : Nat → Bool) (h : Constraints p) : clause p c372 = true := by
  simpa only [c372,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause372
def c373 : List Lit := [(88, false), (21, false), (81, false), (86, false)]
theorem step373 (p : Nat → Bool) (h : Constraints p) : clause p c373 = true := by
  simpa only [c373,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause373
def c374 : List Lit := [(88, false), (21, false), (81, false), (90, false)]
theorem step374 (p : Nat → Bool) (h : Constraints p) : clause p c374 = true := by
  simpa only [c374,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause374
def c375 : List Lit := [(88, false), (21, false), (81, false), (98, false)]
theorem step375 (p : Nat → Bool) (h : Constraints p) : clause p c375 = true := by
  simpa only [c375,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause375
def c376 : List Lit := [(88, false), (21, false), (81, false), (106, false)]
theorem step376 (p : Nat → Bool) (h : Constraints p) : clause p c376 = true := by
  simpa only [c376,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause376
def c377 : List Lit := [(88, false), (21, false), (86, false), (90, false)]
theorem step377 (p : Nat → Bool) (h : Constraints p) : clause p c377 = true := by
  simpa only [c377,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause377
def c378 : List Lit := [(88, false), (21, false), (86, false), (98, false)]
theorem step378 (p : Nat → Bool) (h : Constraints p) : clause p c378 = true := by
  simpa only [c378,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause378
def c379 : List Lit := [(88, false), (21, false), (86, false), (106, false)]
theorem step379 (p : Nat → Bool) (h : Constraints p) : clause p c379 = true := by
  simpa only [c379,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause379
def c380 : List Lit := [(88, false), (21, false), (90, false), (98, false)]
theorem step380 (p : Nat → Bool) (h : Constraints p) : clause p c380 = true := by
  simpa only [c380,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause380
def c381 : List Lit := [(88, false), (21, false), (90, false), (106, false)]
theorem step381 (p : Nat → Bool) (h : Constraints p) : clause p c381 = true := by
  simpa only [c381,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause381
def c382 : List Lit := [(88, false), (21, false), (98, false), (106, false)]
theorem step382 (p : Nat → Bool) (h : Constraints p) : clause p c382 = true := by
  simpa only [c382,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause382
def c383 : List Lit := [(88, false), (52, false), (81, false), (86, false)]
theorem step383 (p : Nat → Bool) (h : Constraints p) : clause p c383 = true := by
  simpa only [c383,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause383
def c384 : List Lit := [(88, false), (52, false), (81, false), (90, false)]
theorem step384 (p : Nat → Bool) (h : Constraints p) : clause p c384 = true := by
  simpa only [c384,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause384
def c385 : List Lit := [(88, false), (52, false), (81, false), (98, false)]
theorem step385 (p : Nat → Bool) (h : Constraints p) : clause p c385 = true := by
  simpa only [c385,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause385
def c386 : List Lit := [(88, false), (52, false), (81, false), (106, false)]
theorem step386 (p : Nat → Bool) (h : Constraints p) : clause p c386 = true := by
  simpa only [c386,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause386
def c387 : List Lit := [(88, false), (52, false), (86, false), (90, false)]
theorem step387 (p : Nat → Bool) (h : Constraints p) : clause p c387 = true := by
  simpa only [c387,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause387
def c388 : List Lit := [(88, false), (52, false), (86, false), (98, false)]
theorem step388 (p : Nat → Bool) (h : Constraints p) : clause p c388 = true := by
  simpa only [c388,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause388
def c389 : List Lit := [(88, false), (52, false), (86, false), (106, false)]
theorem step389 (p : Nat → Bool) (h : Constraints p) : clause p c389 = true := by
  simpa only [c389,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause389
def c390 : List Lit := [(88, false), (52, false), (90, false), (98, false)]
theorem step390 (p : Nat → Bool) (h : Constraints p) : clause p c390 = true := by
  simpa only [c390,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause390
def c391 : List Lit := [(88, false), (52, false), (90, false), (106, false)]
theorem step391 (p : Nat → Bool) (h : Constraints p) : clause p c391 = true := by
  simpa only [c391,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause391
def c392 : List Lit := [(88, false), (52, false), (98, false), (106, false)]
theorem step392 (p : Nat → Bool) (h : Constraints p) : clause p c392 = true := by
  simpa only [c392,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause392
def c393 : List Lit := [(88, false), (81, false), (86, false), (90, false)]
theorem step393 (p : Nat → Bool) (h : Constraints p) : clause p c393 = true := by
  simpa only [c393,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause393
def c394 : List Lit := [(88, false), (81, false), (86, false), (98, false)]
theorem step394 (p : Nat → Bool) (h : Constraints p) : clause p c394 = true := by
  simpa only [c394,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause394
def c395 : List Lit := [(88, false), (81, false), (86, false), (106, false)]
theorem step395 (p : Nat → Bool) (h : Constraints p) : clause p c395 = true := by
  simpa only [c395,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause395
def c396 : List Lit := [(88, false), (81, false), (90, false), (98, false)]
theorem step396 (p : Nat → Bool) (h : Constraints p) : clause p c396 = true := by
  simpa only [c396,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause396
def c397 : List Lit := [(88, false), (81, false), (90, false), (106, false)]
theorem step397 (p : Nat → Bool) (h : Constraints p) : clause p c397 = true := by
  simpa only [c397,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause397
def c398 : List Lit := [(88, false), (81, false), (98, false), (106, false)]
theorem step398 (p : Nat → Bool) (h : Constraints p) : clause p c398 = true := by
  simpa only [c398,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause398
def c399 : List Lit := [(88, false), (86, false), (90, false), (98, false)]
theorem step399 (p : Nat → Bool) (h : Constraints p) : clause p c399 = true := by
  simpa only [c399,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause399
def c400 : List Lit := [(88, false), (86, false), (90, false), (106, false)]
theorem step400 (p : Nat → Bool) (h : Constraints p) : clause p c400 = true := by
  simpa only [c400,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause400
def c401 : List Lit := [(88, false), (86, false), (98, false), (106, false)]
theorem step401 (p : Nat → Bool) (h : Constraints p) : clause p c401 = true := by
  simpa only [c401,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause401
def c402 : List Lit := [(88, false), (90, false), (98, false), (106, false)]
theorem step402 (p : Nat → Bool) (h : Constraints p) : clause p c402 = true := by
  simpa only [c402,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause402
def c403 : List Lit := [(88, false), (206, true), (21, true), (81, true), (86, true), (90, true), (98, true), (106, true)]
theorem step403 (p : Nat → Bool) (h : Constraints p) : clause p c403 = true := by
  simpa only [c403,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause403
def c404 : List Lit := [(88, false), (206, true), (21, true), (52, true), (81, true), (86, true), (98, true), (106, true)]
theorem step404 (p : Nat → Bool) (h : Constraints p) : clause p c404 = true := by
  simpa only [c404,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause404
def c405 : List Lit := [(89, false), (83, false), (86, false), (90, false)]
theorem step405 (p : Nat → Bool) (h : Constraints p) : clause p c405 = true := by
  simpa only [c405,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause405
def c406 : List Lit := [(89, false), (207, true), (86, true), (90, true)]
theorem step406 (p : Nat → Bool) (h : Constraints p) : clause p c406 = true := by
  simpa only [c406,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause406
def c407 : List Lit := [(89, false), (207, true), (83, true), (86, true)]
theorem step407 (p : Nat → Bool) (h : Constraints p) : clause p c407 = true := by
  simpa only [c407,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause407
def c408 : List Lit := [(208, false), (90, true)]
theorem step408 (p : Nat → Bool) (h : Constraints p) : clause p c408 = true := by
  simpa only [c408,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause408
def c409 : List Lit := [(90, false), (84, true), (88, true), (89, true)]
theorem step409 (p : Nat → Bool) (h : Constraints p) : clause p c409 = true := by
  simpa only [c409,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause409
def c410 : List Lit := [(208, false), (84, false), (88, false)]
theorem step410 (p : Nat → Bool) (h : Constraints p) : clause p c410 = true := by
  simpa only [c410,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause410
def c411 : List Lit := [(90, false), (208, true), (88, true), (89, true)]
theorem step411 (p : Nat → Bool) (h : Constraints p) : clause p c411 = true := by
  simpa only [c411,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause411
def c412 : List Lit := [(90, false), (208, true), (84, true), (89, true)]
theorem step412 (p : Nat → Bool) (h : Constraints p) : clause p c412 = true := by
  simpa only [c412,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause412
def c413 : List Lit := [(90, false), (208, true), (84, true), (88, true)]
theorem step413 (p : Nat → Bool) (h : Constraints p) : clause p c413 = true := by
  simpa only [c413,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause413
def c414 : List Lit := [(91, false), (25, false), (54, false), (92, false)]
theorem step414 (p : Nat → Bool) (h : Constraints p) : clause p c414 = true := by
  simpa only [c414,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause414
def c415 : List Lit := [(91, false), (25, false), (54, false), (93, false)]
theorem step415 (p : Nat → Bool) (h : Constraints p) : clause p c415 = true := by
  simpa only [c415,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause415
def c416 : List Lit := [(91, false), (25, false), (54, false), (97, false)]
theorem step416 (p : Nat → Bool) (h : Constraints p) : clause p c416 = true := by
  simpa only [c416,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause416
def c417 : List Lit := [(91, false), (25, false), (54, false), (111, false)]
theorem step417 (p : Nat → Bool) (h : Constraints p) : clause p c417 = true := by
  simpa only [c417,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause417
def c418 : List Lit := [(91, false), (25, false), (92, false), (93, false)]
theorem step418 (p : Nat → Bool) (h : Constraints p) : clause p c418 = true := by
  simpa only [c418,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause418
def c419 : List Lit := [(91, false), (25, false), (92, false), (97, false)]
theorem step419 (p : Nat → Bool) (h : Constraints p) : clause p c419 = true := by
  simpa only [c419,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause419
def c420 : List Lit := [(91, false), (25, false), (92, false), (111, false)]
theorem step420 (p : Nat → Bool) (h : Constraints p) : clause p c420 = true := by
  simpa only [c420,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause420
def c421 : List Lit := [(91, false), (25, false), (93, false), (97, false)]
theorem step421 (p : Nat → Bool) (h : Constraints p) : clause p c421 = true := by
  simpa only [c421,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause421
def c422 : List Lit := [(91, false), (25, false), (93, false), (111, false)]
theorem step422 (p : Nat → Bool) (h : Constraints p) : clause p c422 = true := by
  simpa only [c422,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause422
def c423 : List Lit := [(91, false), (25, false), (97, false), (111, false)]
theorem step423 (p : Nat → Bool) (h : Constraints p) : clause p c423 = true := by
  simpa only [c423,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause423
def c424 : List Lit := [(91, false), (54, false), (92, false), (93, false)]
theorem step424 (p : Nat → Bool) (h : Constraints p) : clause p c424 = true := by
  simpa only [c424,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause424
def c425 : List Lit := [(91, false), (54, false), (92, false), (97, false)]
theorem step425 (p : Nat → Bool) (h : Constraints p) : clause p c425 = true := by
  simpa only [c425,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause425
def c426 : List Lit := [(91, false), (54, false), (92, false), (111, false)]
theorem step426 (p : Nat → Bool) (h : Constraints p) : clause p c426 = true := by
  simpa only [c426,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause426
def c427 : List Lit := [(91, false), (54, false), (93, false), (97, false)]
theorem step427 (p : Nat → Bool) (h : Constraints p) : clause p c427 = true := by
  simpa only [c427,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause427
def c428 : List Lit := [(91, false), (54, false), (93, false), (111, false)]
theorem step428 (p : Nat → Bool) (h : Constraints p) : clause p c428 = true := by
  simpa only [c428,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause428
def c429 : List Lit := [(91, false), (54, false), (97, false), (111, false)]
theorem step429 (p : Nat → Bool) (h : Constraints p) : clause p c429 = true := by
  simpa only [c429,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause429
def c430 : List Lit := [(91, false), (92, false), (93, false), (97, false)]
theorem step430 (p : Nat → Bool) (h : Constraints p) : clause p c430 = true := by
  simpa only [c430,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause430
def c431 : List Lit := [(91, false), (92, false), (93, false), (111, false)]
theorem step431 (p : Nat → Bool) (h : Constraints p) : clause p c431 = true := by
  simpa only [c431,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause431
def c432 : List Lit := [(91, false), (92, false), (97, false), (111, false)]
theorem step432 (p : Nat → Bool) (h : Constraints p) : clause p c432 = true := by
  simpa only [c432,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause432
def c433 : List Lit := [(91, false), (93, false), (97, false), (111, false)]
theorem step433 (p : Nat → Bool) (h : Constraints p) : clause p c433 = true := by
  simpa only [c433,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause433
def c434 : List Lit := [(92, false), (27, false), (56, false), (95, false)]
theorem step434 (p : Nat → Bool) (h : Constraints p) : clause p c434 = true := by
  simpa only [c434,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause434
def c435 : List Lit := [(92, false), (56, false), (91, false), (95, false)]
theorem step435 (p : Nat → Bool) (h : Constraints p) : clause p c435 = true := by
  simpa only [c435,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause435
def c436 : List Lit := [(92, false), (56, false), (91, false), (99, false)]
theorem step436 (p : Nat → Bool) (h : Constraints p) : clause p c436 = true := by
  simpa only [c436,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause436
def c437 : List Lit := [(92, false), (56, false), (91, false), (112, false)]
theorem step437 (p : Nat → Bool) (h : Constraints p) : clause p c437 = true := by
  simpa only [c437,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause437
def c438 : List Lit := [(92, false), (56, false), (95, false), (99, false)]
theorem step438 (p : Nat → Bool) (h : Constraints p) : clause p c438 = true := by
  simpa only [c438,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause438
def c439 : List Lit := [(92, false), (56, false), (95, false), (112, false)]
theorem step439 (p : Nat → Bool) (h : Constraints p) : clause p c439 = true := by
  simpa only [c439,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause439
def c440 : List Lit := [(92, false), (82, false), (91, false), (99, false)]
theorem step440 (p : Nat → Bool) (h : Constraints p) : clause p c440 = true := by
  simpa only [c440,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause440
def c441 : List Lit := [(92, false), (91, false), (95, false), (99, false)]
theorem step441 (p : Nat → Bool) (h : Constraints p) : clause p c441 = true := by
  simpa only [c441,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause441
def c442 : List Lit := [(92, false), (91, false), (95, false), (112, false)]
theorem step442 (p : Nat → Bool) (h : Constraints p) : clause p c442 = true := by
  simpa only [c442,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause442
def c443 : List Lit := [(92, false), (91, false), (99, false), (112, false)]
theorem step443 (p : Nat → Bool) (h : Constraints p) : clause p c443 = true := by
  simpa only [c443,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause443
def c444 : List Lit := [(211, false), (93, true)]
theorem step444 (p : Nat → Bool) (h : Constraints p) : clause p c444 = true := by
  simpa only [c444,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause444
def c445 : List Lit := [(93, false), (91, true), (95, true), (100, true)]
theorem step445 (p : Nat → Bool) (h : Constraints p) : clause p c445 = true := by
  simpa only [c445,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause445
def c446 : List Lit := [(93, false), (211, true), (95, true), (100, true)]
theorem step446 (p : Nat → Bool) (h : Constraints p) : clause p c446 = true := by
  simpa only [c446,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause446
def c447 : List Lit := [(93, false), (211, true), (91, true), (100, true)]
theorem step447 (p : Nat → Bool) (h : Constraints p) : clause p c447 = true := by
  simpa only [c447,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause447
def c448 : List Lit := [(93, false), (211, true), (91, true), (95, true)]
theorem step448 (p : Nat → Bool) (h : Constraints p) : clause p c448 = true := by
  simpa only [c448,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause448
def c449 : List Lit := [(94, false), (212, true), (84, true), (95, true), (114, true)]
theorem step449 (p : Nat → Bool) (h : Constraints p) : clause p c449 = true := by
  simpa only [c449,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause449
def c450 : List Lit := [(94, false), (212, true), (58, true), (84, true), (95, true)]
theorem step450 (p : Nat → Bool) (h : Constraints p) : clause p c450 = true := by
  simpa only [c450,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause450
def c451 : List Lit := [(95, false), (85, false), (92, false), (93, false)]
theorem step451 (p : Nat → Bool) (h : Constraints p) : clause p c451 = true := by
  simpa only [c451,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause451
def c452 : List Lit := [(95, false), (85, false), (92, false), (94, false)]
theorem step452 (p : Nat → Bool) (h : Constraints p) : clause p c452 = true := by
  simpa only [c452,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause452
def c453 : List Lit := [(95, false), (85, false), (93, false), (94, false)]
theorem step453 (p : Nat → Bool) (h : Constraints p) : clause p c453 = true := by
  simpa only [c453,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause453
def c454 : List Lit := [(95, false), (92, false), (93, false), (94, false)]
theorem step454 (p : Nat → Bool) (h : Constraints p) : clause p c454 = true := by
  simpa only [c454,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause454
def c455 : List Lit := [(95, false), (213, true), (92, true), (93, true), (94, true)]
theorem step455 (p : Nat → Bool) (h : Constraints p) : clause p c455 = true := by
  simpa only [c455,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause455
def c456 : List Lit := [(95, false), (213, true), (85, true), (92, true), (94, true)]
theorem step456 (p : Nat → Bool) (h : Constraints p) : clause p c456 = true := by
  simpa only [c456,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause456
def c457 : List Lit := [(96, false), (59, false), (86, false), (97, false)]
theorem step457 (p : Nat → Bool) (h : Constraints p) : clause p c457 = true := by
  simpa only [c457,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause457
def c458 : List Lit := [(96, false), (59, false), (86, false), (98, false)]
theorem step458 (p : Nat → Bool) (h : Constraints p) : clause p c458 = true := by
  simpa only [c458,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause458
def c459 : List Lit := [(96, false), (59, false), (86, false), (115, false)]
theorem step459 (p : Nat → Bool) (h : Constraints p) : clause p c459 = true := by
  simpa only [c459,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause459
def c460 : List Lit := [(96, false), (59, false), (97, false), (98, false)]
theorem step460 (p : Nat → Bool) (h : Constraints p) : clause p c460 = true := by
  simpa only [c460,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause460
def c461 : List Lit := [(96, false), (59, false), (97, false), (115, false)]
theorem step461 (p : Nat → Bool) (h : Constraints p) : clause p c461 = true := by
  simpa only [c461,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause461
def c462 : List Lit := [(96, false), (59, false), (98, false), (115, false)]
theorem step462 (p : Nat → Bool) (h : Constraints p) : clause p c462 = true := by
  simpa only [c462,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause462
def c463 : List Lit := [(96, false), (86, false), (97, false), (98, false)]
theorem step463 (p : Nat → Bool) (h : Constraints p) : clause p c463 = true := by
  simpa only [c463,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause463
def c464 : List Lit := [(96, false), (86, false), (97, false), (115, false)]
theorem step464 (p : Nat → Bool) (h : Constraints p) : clause p c464 = true := by
  simpa only [c464,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause464
def c465 : List Lit := [(96, false), (86, false), (98, false), (115, false)]
theorem step465 (p : Nat → Bool) (h : Constraints p) : clause p c465 = true := by
  simpa only [c465,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause465
def c466 : List Lit := [(96, false), (97, false), (98, false), (115, false)]
theorem step466 (p : Nat → Bool) (h : Constraints p) : clause p c466 = true := by
  simpa only [c466,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause466
def c467 : List Lit := [(96, false), (214, true), (86, true), (97, true), (98, true), (115, true)]
theorem step467 (p : Nat → Bool) (h : Constraints p) : clause p c467 = true := by
  simpa only [c467,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause467
def c468 : List Lit := [(97, false), (87, false), (91, false), (99, false)]
theorem step468 (p : Nat → Bool) (h : Constraints p) : clause p c468 = true := by
  simpa only [c468,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause468
def c469 : List Lit := [(97, false), (87, false), (96, false), (100, false)]
theorem step469 (p : Nat → Bool) (h : Constraints p) : clause p c469 = true := by
  simpa only [c469,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause469
def c470 : List Lit := [(97, false), (87, false), (99, false), (100, false)]
theorem step470 (p : Nat → Bool) (h : Constraints p) : clause p c470 = true := by
  simpa only [c470,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause470
def c471 : List Lit := [(97, false), (215, true), (91, true), (96, true), (99, true), (100, true)]
theorem step471 (p : Nat → Bool) (h : Constraints p) : clause p c471 = true := by
  simpa only [c471,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause471
def c472 : List Lit := [(97, false), (215, true), (87, true), (96, true), (99, true), (100, true)]
theorem step472 (p : Nat → Bool) (h : Constraints p) : clause p c472 = true := by
  simpa only [c472,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause472
def c473 : List Lit := [(97, false), (215, true), (87, true), (91, true), (99, true), (100, true)]
theorem step473 (p : Nat → Bool) (h : Constraints p) : clause p c473 = true := by
  simpa only [c473,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause473
def c474 : List Lit := [(98, false), (29, true), (88, true), (96, true), (99, true)]
theorem step474 (p : Nat → Bool) (h : Constraints p) : clause p c474 = true := by
  simpa only [c474,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause474
def c475 : List Lit := [(98, false), (29, false), (88, false), (96, false)]
theorem step475 (p : Nat → Bool) (h : Constraints p) : clause p c475 = true := by
  simpa only [c475,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause475
def c476 : List Lit := [(98, false), (216, true), (88, true), (96, true), (99, true)]
theorem step476 (p : Nat → Bool) (h : Constraints p) : clause p c476 = true := by
  simpa only [c476,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause476
def c477 : List Lit := [(98, false), (216, true), (29, true), (96, true), (99, true)]
theorem step477 (p : Nat → Bool) (h : Constraints p) : clause p c477 = true := by
  simpa only [c477,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause477
def c478 : List Lit := [(98, false), (216, true), (29, true), (88, true), (99, true)]
theorem step478 (p : Nat → Bool) (h : Constraints p) : clause p c478 = true := by
  simpa only [c478,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause478
def c479 : List Lit := [(98, false), (216, true), (29, true), (88, true), (96, true)]
theorem step479 (p : Nat → Bool) (h : Constraints p) : clause p c479 = true := by
  simpa only [c479,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause479
def c480 : List Lit := [(99, false), (92, false), (97, false), (98, false)]
theorem step480 (p : Nat → Bool) (h : Constraints p) : clause p c480 = true := by
  simpa only [c480,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause480
def c481 : List Lit := [(99, false), (217, true), (92, true), (97, true)]
theorem step481 (p : Nat → Bool) (h : Constraints p) : clause p c481 = true := by
  simpa only [c481,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause481
def c482 : List Lit := [(100, false), (218, true), (97, true)]
theorem step482 (p : Nat → Bool) (h : Constraints p) : clause p c482 = true := by
  simpa only [c482,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause482
def c483 : List Lit := [(100, false), (218, true), (93, true)]
theorem step483 (p : Nat → Bool) (h : Constraints p) : clause p c483 = true := by
  simpa only [c483,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause483
def c484 : List Lit := [(101, false), (65, false), (81, false), (102, false)]
theorem step484 (p : Nat → Bool) (h : Constraints p) : clause p c484 = true := by
  simpa only [c484,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause484
def c485 : List Lit := [(101, false), (65, false), (81, false), (106, false)]
theorem step485 (p : Nat → Bool) (h : Constraints p) : clause p c485 = true := by
  simpa only [c485,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause485
def c486 : List Lit := [(101, false), (65, false), (102, false), (106, false)]
theorem step486 (p : Nat → Bool) (h : Constraints p) : clause p c486 = true := by
  simpa only [c486,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause486
def c487 : List Lit := [(101, false), (81, false), (102, false), (106, false)]
theorem step487 (p : Nat → Bool) (h : Constraints p) : clause p c487 = true := by
  simpa only [c487,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause487
def c488 : List Lit := [(101, false), (219, true), (65, true), (102, true), (106, true)]
theorem step488 (p : Nat → Bool) (h : Constraints p) : clause p c488 = true := by
  simpa only [c488,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause488
def c489 : List Lit := [(101, false), (219, true), (65, true), (81, true), (106, true)]
theorem step489 (p : Nat → Bool) (h : Constraints p) : clause p c489 = true := by
  simpa only [c489,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause489
def c490 : List Lit := [(101, false), (219, true), (65, true), (81, true), (102, true)]
theorem step490 (p : Nat → Bool) (h : Constraints p) : clause p c490 = true := by
  simpa only [c490,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause490
def c491 : List Lit := [(102, false), (82, false), (101, false), (112, false)]
theorem step491 (p : Nat → Bool) (h : Constraints p) : clause p c491 = true := by
  simpa only [c491,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause491
def c492 : List Lit := [(102, false), (82, false), (107, false), (112, false)]
theorem step492 (p : Nat → Bool) (h : Constraints p) : clause p c492 = true := by
  simpa only [c492,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause492
def c493 : List Lit := [(102, false), (220, true), (101, true), (107, true), (112, true)]
theorem step493 (p : Nat → Bool) (h : Constraints p) : clause p c493 = true := by
  simpa only [c493,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause493
def c494 : List Lit := [(102, false), (220, true), (82, true), (107, true), (112, true)]
theorem step494 (p : Nat → Bool) (h : Constraints p) : clause p c494 = true := by
  simpa only [c494,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause494
def c495 : List Lit := [(102, false), (220, true), (82, true), (101, true), (112, true)]
theorem step495 (p : Nat → Bool) (h : Constraints p) : clause p c495 = true := by
  simpa only [c495,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause495
def c496 : List Lit := [(102, false), (220, true), (82, true), (101, true), (107, true)]
theorem step496 (p : Nat → Bool) (h : Constraints p) : clause p c496 = true := by
  simpa only [c496,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause496
def c497 : List Lit := [(103, false), (83, false), (104, false), (113, false)]
theorem step497 (p : Nat → Bool) (h : Constraints p) : clause p c497 = true := by
  simpa only [c497,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause497
def c498 : List Lit := [(104, false), (103, true), (108, true)]
theorem step498 (p : Nat → Bool) (h : Constraints p) : clause p c498 = true := by
  simpa only [c498,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause498
def c499 : List Lit := [(104, false), (222, true), (108, true)]
theorem step499 (p : Nat → Bool) (h : Constraints p) : clause p c499 = true := by
  simpa only [c499,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause499
def c500 : List Lit := [(104, false), (222, true), (103, true)]
theorem step500 (p : Nat → Bool) (h : Constraints p) : clause p c500 = true := by
  simpa only [c500,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause500
def c501 : List Lit := [(105, false), (223, true), (38, true), (87, true), (107, true), (108, true)]
theorem step501 (p : Nat → Bool) (h : Constraints p) : clause p c501 = true := by
  simpa only [c501,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause501
def c502 : List Lit := [(105, false), (223, true), (38, true), (69, true), (107, true), (108, true)]
theorem step502 (p : Nat → Bool) (h : Constraints p) : clause p c502 = true := by
  simpa only [c502,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause502
def c503 : List Lit := [(106, false), (70, true), (88, true), (101, true), (107, true)]
theorem step503 (p : Nat → Bool) (h : Constraints p) : clause p c503 = true := by
  simpa only [c503,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause503
def c504 : List Lit := [(106, false), (70, false), (88, false), (107, false)]
theorem step504 (p : Nat → Bool) (h : Constraints p) : clause p c504 = true := by
  simpa only [c504,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause504
def c505 : List Lit := [(106, false), (224, true), (88, true), (101, true), (107, true)]
theorem step505 (p : Nat → Bool) (h : Constraints p) : clause p c505 = true := by
  simpa only [c505,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause505
def c506 : List Lit := [(106, false), (224, true), (70, true), (101, true), (107, true)]
theorem step506 (p : Nat → Bool) (h : Constraints p) : clause p c506 = true := by
  simpa only [c506,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause506
def c507 : List Lit := [(106, false), (224, true), (70, true), (88, true), (107, true)]
theorem step507 (p : Nat → Bool) (h : Constraints p) : clause p c507 = true := by
  simpa only [c507,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause507
def c508 : List Lit := [(106, false), (224, true), (70, true), (88, true), (101, true)]
theorem step508 (p : Nat → Bool) (h : Constraints p) : clause p c508 = true := by
  simpa only [c508,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause508
def c509 : List Lit := [(107, false), (102, false), (105, false), (106, false)]
theorem step509 (p : Nat → Bool) (h : Constraints p) : clause p c509 = true := by
  simpa only [c509,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause509
def c510 : List Lit := [(107, false), (102, false), (105, false), (109, false)]
theorem step510 (p : Nat → Bool) (h : Constraints p) : clause p c510 = true := by
  simpa only [c510,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause510
def c511 : List Lit := [(107, false), (102, false), (106, false), (109, false)]
theorem step511 (p : Nat → Bool) (h : Constraints p) : clause p c511 = true := by
  simpa only [c511,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause511
def c512 : List Lit := [(107, false), (105, false), (106, false), (109, false)]
theorem step512 (p : Nat → Bool) (h : Constraints p) : clause p c512 = true := by
  simpa only [c512,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause512
def c513 : List Lit := [(108, false), (104, false), (105, false), (109, false)]
theorem step513 (p : Nat → Bool) (h : Constraints p) : clause p c513 = true := by
  simpa only [c513,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause513
def c514 : List Lit := [(108, false), (226, true), (105, true), (109, true)]
theorem step514 (p : Nat → Bool) (h : Constraints p) : clause p c514 = true := by
  simpa only [c514,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause514
def c515 : List Lit := [(108, false), (226, true), (104, true), (105, true)]
theorem step515 (p : Nat → Bool) (h : Constraints p) : clause p c515 = true := by
  simpa only [c515,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause515
def c516 : List Lit := [(227, false), (109, true)]
theorem step516 (p : Nat → Bool) (h : Constraints p) : clause p c516 = true := by
  simpa only [c516,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause516
def c517 : List Lit := [(109, false), (107, false), (108, false), (118, false)]
theorem step517 (p : Nat → Bool) (h : Constraints p) : clause p c517 = true := by
  simpa only [c517,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause517
def c518 : List Lit := [(109, false), (227, true), (107, true), (108, true)]
theorem step518 (p : Nat → Bool) (h : Constraints p) : clause p c518 = true := by
  simpa only [c518,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause518
def c519 : List Lit := [(110, false), (111, false), (113, false), (115, false)]
theorem step519 (p : Nat → Bool) (h : Constraints p) : clause p c519 = true := by
  simpa only [c519,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause519
def c520 : List Lit := [(110, false), (228, true), (113, true), (115, true)]
theorem step520 (p : Nat → Bool) (h : Constraints p) : clause p c520 = true := by
  simpa only [c520,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause520
def c521 : List Lit := [(111, false), (91, true), (110, true), (112, true)]
theorem step521 (p : Nat → Bool) (h : Constraints p) : clause p c521 = true := by
  simpa only [c521,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause521
def c522 : List Lit := [(111, false), (229, true), (110, true), (112, true)]
theorem step522 (p : Nat → Bool) (h : Constraints p) : clause p c522 = true := by
  simpa only [c522,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause522
def c523 : List Lit := [(111, false), (229, true), (91, true), (112, true)]
theorem step523 (p : Nat → Bool) (h : Constraints p) : clause p c523 = true := by
  simpa only [c523,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause523
def c524 : List Lit := [(111, false), (229, true), (91, true), (110, true)]
theorem step524 (p : Nat → Bool) (h : Constraints p) : clause p c524 = true := by
  simpa only [c524,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause524
def c525 : List Lit := [(112, false), (92, false), (102, false), (111, false)]
theorem step525 (p : Nat → Bool) (h : Constraints p) : clause p c525 = true := by
  simpa only [c525,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause525
def c526 : List Lit := [(112, false), (230, true), (92, true), (111, true)]
theorem step526 (p : Nat → Bool) (h : Constraints p) : clause p c526 = true := by
  simpa only [c526,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause526
def c527 : List Lit := [(112, false), (230, true), (92, true), (102, true)]
theorem step527 (p : Nat → Bool) (h : Constraints p) : clause p c527 = true := by
  simpa only [c527,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause527
def c528 : List Lit := [(113, false), (103, false), (110, false), (114, false)]
theorem step528 (p : Nat → Bool) (h : Constraints p) : clause p c528 = true := by
  simpa only [c528,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause528
def c529 : List Lit := [(113, false), (231, true), (110, true), (114, true), (116, true)]
theorem step529 (p : Nat → Bool) (h : Constraints p) : clause p c529 = true := by
  simpa only [c529,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause529
def c530 : List Lit := [(113, false), (231, true), (103, true), (110, true), (116, true)]
theorem step530 (p : Nat → Bool) (h : Constraints p) : clause p c530 = true := by
  simpa only [c530,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause530
def c531 : List Lit := [(114, false), (43, false), (113, false), (117, false)]
theorem step531 (p : Nat → Bool) (h : Constraints p) : clause p c531 = true := by
  simpa only [c531,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause531
def c532 : List Lit := [(114, false), (94, false), (113, false), (117, false)]
theorem step532 (p : Nat → Bool) (h : Constraints p) : clause p c532 = true := by
  simpa only [c532,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause532
def c533 : List Lit := [(115, false), (45, true), (96, true), (110, true), (116, true)]
theorem step533 (p : Nat → Bool) (h : Constraints p) : clause p c533 = true := by
  simpa only [c533,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause533
def c534 : List Lit := [(115, false), (45, false), (96, false), (110, false)]
theorem step534 (p : Nat → Bool) (h : Constraints p) : clause p c534 = true := by
  simpa only [c534,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause534
def c535 : List Lit := [(115, false), (45, false), (96, false), (116, false)]
theorem step535 (p : Nat → Bool) (h : Constraints p) : clause p c535 = true := by
  simpa only [c535,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause535
def c536 : List Lit := [(115, false), (233, true), (96, true), (110, true), (116, true)]
theorem step536 (p : Nat → Bool) (h : Constraints p) : clause p c536 = true := by
  simpa only [c536,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause536
def c537 : List Lit := [(115, false), (233, true), (45, true), (110, true), (116, true)]
theorem step537 (p : Nat → Bool) (h : Constraints p) : clause p c537 = true := by
  simpa only [c537,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause537
def c538 : List Lit := [(115, false), (233, true), (45, true), (96, true), (116, true)]
theorem step538 (p : Nat → Bool) (h : Constraints p) : clause p c538 = true := by
  simpa only [c538,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause538
def c539 : List Lit := [(116, false), (113, false), (115, false), (117, false)]
theorem step539 (p : Nat → Bool) (h : Constraints p) : clause p c539 = true := by
  simpa only [c539,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause539
def c540 : List Lit := [(117, false), (235, true), (116, true), (118, true)]
theorem step540 (p : Nat → Bool) (h : Constraints p) : clause p c540 = true := by
  simpa only [c540,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause540
def c541 : List Lit := [(117, false), (235, true), (114, true), (118, true)]
theorem step541 (p : Nat → Bool) (h : Constraints p) : clause p c541 = true := by
  simpa only [c541,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause541
def c542 : List Lit := [(117, false), (235, true), (114, true), (116, true)]
theorem step542 (p : Nat → Bool) (h : Constraints p) : clause p c542 = true := by
  simpa only [c542,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause542
def c543 : List Lit := [(118, false), (236, true), (109, true)]
theorem step543 (p : Nat → Bool) (h : Constraints p) : clause p c543 = true := by
  simpa only [c543,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause543
def c544 : List Lit := [(119, false)]
theorem step544 (p : Nat → Bool) (h : Constraints p) : clause p c544 = true := by
  simpa only [c544,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause544
def c545 : List Lit := [(120, false)]
theorem step545 (p : Nat → Bool) (h : Constraints p) : clause p c545 = true := by
  simpa only [c545,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause545
def c546 : List Lit := [(122, false)]
theorem step546 (p : Nat → Bool) (h : Constraints p) : clause p c546 = true := by
  simpa only [c546,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause546
def c547 : List Lit := [(124, false)]
theorem step547 (p : Nat → Bool) (h : Constraints p) : clause p c547 = true := by
  simpa only [c547,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause547
def c548 : List Lit := [(126, false)]
theorem step548 (p : Nat → Bool) (h : Constraints p) : clause p c548 = true := by
  simpa only [c548,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause548
def c549 : List Lit := [(127, false)]
theorem step549 (p : Nat → Bool) (h : Constraints p) : clause p c549 = true := by
  simpa only [c549,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause549
def c550 : List Lit := [(128, false)]
theorem step550 (p : Nat → Bool) (h : Constraints p) : clause p c550 = true := by
  simpa only [c550,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause550
def c551 : List Lit := [(131, false)]
theorem step551 (p : Nat → Bool) (h : Constraints p) : clause p c551 = true := by
  simpa only [c551,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause551
def c552 : List Lit := [(133, false)]
theorem step552 (p : Nat → Bool) (h : Constraints p) : clause p c552 = true := by
  simpa only [c552,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause552
def c553 : List Lit := [(134, false)]
theorem step553 (p : Nat → Bool) (h : Constraints p) : clause p c553 = true := by
  simpa only [c553,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause553
def c554 : List Lit := [(136, false)]
theorem step554 (p : Nat → Bool) (h : Constraints p) : clause p c554 = true := by
  simpa only [c554,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause554
def c555 : List Lit := [(137, false)]
theorem step555 (p : Nat → Bool) (h : Constraints p) : clause p c555 = true := by
  simpa only [c555,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause555
def c556 : List Lit := [(140, false)]
theorem step556 (p : Nat → Bool) (h : Constraints p) : clause p c556 = true := by
  simpa only [c556,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause556
def c557 : List Lit := [(142, false)]
theorem step557 (p : Nat → Bool) (h : Constraints p) : clause p c557 = true := by
  simpa only [c557,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause557
def c558 : List Lit := [(145, false)]
theorem step558 (p : Nat → Bool) (h : Constraints p) : clause p c558 = true := by
  simpa only [c558,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause558
def c559 : List Lit := [(147, false)]
theorem step559 (p : Nat → Bool) (h : Constraints p) : clause p c559 = true := by
  simpa only [c559,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause559
def c560 : List Lit := [(148, false)]
theorem step560 (p : Nat → Bool) (h : Constraints p) : clause p c560 = true := by
  simpa only [c560,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause560
def c561 : List Lit := [(150, false)]
theorem step561 (p : Nat → Bool) (h : Constraints p) : clause p c561 = true := by
  simpa only [c561,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause561
def c562 : List Lit := [(151, false)]
theorem step562 (p : Nat → Bool) (h : Constraints p) : clause p c562 = true := by
  simpa only [c562,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause562
def c563 : List Lit := [(153, false)]
theorem step563 (p : Nat → Bool) (h : Constraints p) : clause p c563 = true := by
  simpa only [c563,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause563
def c564 : List Lit := [(156, false)]
theorem step564 (p : Nat → Bool) (h : Constraints p) : clause p c564 = true := by
  simpa only [c564,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause564
def c565 : List Lit := [(157, false)]
theorem step565 (p : Nat → Bool) (h : Constraints p) : clause p c565 = true := by
  simpa only [c565,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause565
def c566 : List Lit := [(159, false)]
theorem step566 (p : Nat → Bool) (h : Constraints p) : clause p c566 = true := by
  simpa only [c566,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause566
def c567 : List Lit := [(162, false)]
theorem step567 (p : Nat → Bool) (h : Constraints p) : clause p c567 = true := by
  simpa only [c567,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause567
def c568 : List Lit := [(163, false)]
theorem step568 (p : Nat → Bool) (h : Constraints p) : clause p c568 = true := by
  simpa only [c568,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause568
def c569 : List Lit := [(166, false)]
theorem step569 (p : Nat → Bool) (h : Constraints p) : clause p c569 = true := by
  simpa only [c569,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause569
def c570 : List Lit := [(167, false)]
theorem step570 (p : Nat → Bool) (h : Constraints p) : clause p c570 = true := by
  simpa only [c570,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause570
def c571 : List Lit := [(168, false)]
theorem step571 (p : Nat → Bool) (h : Constraints p) : clause p c571 = true := by
  simpa only [c571,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause571
def c572 : List Lit := [(171, false)]
theorem step572 (p : Nat → Bool) (h : Constraints p) : clause p c572 = true := by
  simpa only [c572,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause572
def c573 : List Lit := [(174, false)]
theorem step573 (p : Nat → Bool) (h : Constraints p) : clause p c573 = true := by
  simpa only [c573,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause573
def c574 : List Lit := [(176, false)]
theorem step574 (p : Nat → Bool) (h : Constraints p) : clause p c574 = true := by
  simpa only [c574,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause574
def c575 : List Lit := [(178, false)]
theorem step575 (p : Nat → Bool) (h : Constraints p) : clause p c575 = true := by
  simpa only [c575,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause575
def c576 : List Lit := [(181, false)]
theorem step576 (p : Nat → Bool) (h : Constraints p) : clause p c576 = true := by
  simpa only [c576,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause576
def c577 : List Lit := [(184, false)]
theorem step577 (p : Nat → Bool) (h : Constraints p) : clause p c577 = true := by
  simpa only [c577,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause577
def c578 : List Lit := [(187, false)]
theorem step578 (p : Nat → Bool) (h : Constraints p) : clause p c578 = true := by
  simpa only [c578,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause578
def c579 : List Lit := [(188, false)]
theorem step579 (p : Nat → Bool) (h : Constraints p) : clause p c579 = true := by
  simpa only [c579,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause579
def c580 : List Lit := [(189, false)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true := by
  simpa only [c580,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause580
def c581 : List Lit := [(191, false)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true := by
  simpa only [c581,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause581
def c582 : List Lit := [(193, false)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true := by
  simpa only [c582,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause582
def c583 : List Lit := [(196, false)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true := by
  simpa only [c583,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause583
def c584 : List Lit := [(197, false)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true := by
  simpa only [c584,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause584
def c585 : List Lit := [(198, false)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true := by
  simpa only [c585,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause585
def c586 : List Lit := [(200, false)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true := by
  simpa only [c586,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause586
def c587 : List Lit := [(202, false)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true := by
  simpa only [c587,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause587
def c588 : List Lit := [(205, false)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true := by
  simpa only [c588,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause588
def c589 : List Lit := [(206, false)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true := by
  simpa only [c589,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause589
def c590 : List Lit := [(207, false)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true := by
  simpa only [c590,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause590
def c591 : List Lit := [(209, false)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true := by
  simpa only [c591,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause591
def c592 : List Lit := [(213, false)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true := by
  simpa only [c592,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause592
def c593 : List Lit := [(214, false)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true := by
  simpa only [c593,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause593
def c594 : List Lit := [(217, false)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true := by
  simpa only [c594,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause594
def c595 : List Lit := [(218, false)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true := by
  simpa only [c595,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause595
def c596 : List Lit := [(219, false)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true := by
  simpa only [c596,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause596
def c597 : List Lit := [(221, false)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true := by
  simpa only [c597,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause597
def c598 : List Lit := [(225, false)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true := by
  simpa only [c598,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause598
def c599 : List Lit := [(226, false)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true := by
  simpa only [c599,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause599
def c600 : List Lit := [(228, false)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true := by
  simpa only [c600,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause600
def c601 : List Lit := [(230, false)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true := by
  simpa only [c601,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause601
def c602 : List Lit := [(232, false)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true := by
  simpa only [c602,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause602
def c603 : List Lit := [(234, false)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true := by
  simpa only [c603,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause603
def c604 : List Lit := [(236, false)]
theorem step604 (p : Nat → Bool) (h : Constraints p) : clause p c604 = true := by
  simpa only [c604,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause604
def c605 : List Lit := [(121, false), (237, true)]
theorem step605 (p : Nat → Bool) (h : Constraints p) : clause p c605 = true := by
  simpa only [c605,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause605
def c606 : List Lit := [(237, false), (239, true)]
theorem step606 (p : Nat → Bool) (h : Constraints p) : clause p c606 = true := by
  simpa only [c606,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause606
def c607 : List Lit := [(123, false), (241, true)]
theorem step607 (p : Nat → Bool) (h : Constraints p) : clause p c607 = true := by
  simpa only [c607,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause607
def c608 : List Lit := [(125, false), (243, true)]
theorem step608 (p : Nat → Bool) (h : Constraints p) : clause p c608 = true := by
  simpa only [c608,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause608
def c609 : List Lit := [(243, false), (245, true)]
theorem step609 (p : Nat → Bool) (h : Constraints p) : clause p c609 = true := by
  simpa only [c609,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause609
def c610 : List Lit := [(241, false), (245, true)]
theorem step610 (p : Nat → Bool) (h : Constraints p) : clause p c610 = true := by
  simpa only [c610,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause610
def c611 : List Lit := [(245, false), (247, true)]
theorem step611 (p : Nat → Bool) (h : Constraints p) : clause p c611 = true := by
  simpa only [c611,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause611
def c612 : List Lit := [(239, false), (247, true)]
theorem step612 (p : Nat → Bool) (h : Constraints p) : clause p c612 = true := by
  simpa only [c612,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause612
def c613 : List Lit := [(130, false), (253, true)]
theorem step613 (p : Nat → Bool) (h : Constraints p) : clause p c613 = true := by
  simpa only [c613,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause613
def c614 : List Lit := [(129, false), (253, true)]
theorem step614 (p : Nat → Bool) (h : Constraints p) : clause p c614 = true := by
  simpa only [c614,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause614
def c615 : List Lit := [(132, false), (255, true)]
theorem step615 (p : Nat → Bool) (h : Constraints p) : clause p c615 = true := by
  simpa only [c615,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause615
def c616 : List Lit := [(255, false), (257, true)]
theorem step616 (p : Nat → Bool) (h : Constraints p) : clause p c616 = true := by
  simpa only [c616,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause616
def c617 : List Lit := [(253, false), (257, true)]
theorem step617 (p : Nat → Bool) (h : Constraints p) : clause p c617 = true := by
  simpa only [c617,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause617
def c618 : List Lit := [(257, false), (259, true)]
theorem step618 (p : Nat → Bool) (h : Constraints p) : clause p c618 = true := by
  simpa only [c618,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause618
def c619 : List Lit := [(259, false), (261, true)]
theorem step619 (p : Nat → Bool) (h : Constraints p) : clause p c619 = true := by
  simpa only [c619,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause619
def c620 : List Lit := [(247, false), (261, true)]
theorem step620 (p : Nat → Bool) (h : Constraints p) : clause p c620 = true := by
  simpa only [c620,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause620
def c621 : List Lit := [(135, false), (263, true)]
theorem step621 (p : Nat → Bool) (h : Constraints p) : clause p c621 = true := by
  simpa only [c621,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause621
def c622 : List Lit := [(263, false), (265, true)]
theorem step622 (p : Nat → Bool) (h : Constraints p) : clause p c622 = true := by
  simpa only [c622,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause622
def c623 : List Lit := [(139, false), (269, true)]
theorem step623 (p : Nat → Bool) (h : Constraints p) : clause p c623 = true := by
  simpa only [c623,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause623
def c624 : List Lit := [(138, false), (269, true)]
theorem step624 (p : Nat → Bool) (h : Constraints p) : clause p c624 = true := by
  simpa only [c624,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause624
def c625 : List Lit := [(138, false), (139, false), (270, true)]
theorem step625 (p : Nat → Bool) (h : Constraints p) : clause p c625 = true := by
  simpa only [c625,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause625
def c626 : List Lit := [(269, false), (271, true)]
theorem step626 (p : Nat → Bool) (h : Constraints p) : clause p c626 = true := by
  simpa only [c626,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause626
def c627 : List Lit := [(270, false), (272, true)]
theorem step627 (p : Nat → Bool) (h : Constraints p) : clause p c627 = true := by
  simpa only [c627,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause627
def c628 : List Lit := [(271, false), (273, true)]
theorem step628 (p : Nat → Bool) (h : Constraints p) : clause p c628 = true := by
  simpa only [c628,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause628
def c629 : List Lit := [(272, false), (274, true)]
theorem step629 (p : Nat → Bool) (h : Constraints p) : clause p c629 = true := by
  simpa only [c629,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause629
def c630 : List Lit := [(265, false), (273, true)]
theorem step630 (p : Nat → Bool) (h : Constraints p) : clause p c630 = true := by
  simpa only [c630,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause630
def c631 : List Lit := [(265, false), (271, false), (274, true)]
theorem step631 (p : Nat → Bool) (h : Constraints p) : clause p c631 = true := by
  simpa only [c631,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause631
def c632 : List Lit := [(141, false), (275, true)]
theorem step632 (p : Nat → Bool) (h : Constraints p) : clause p c632 = true := by
  simpa only [c632,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause632
def c633 : List Lit := [(143, false), (277, true)]
theorem step633 (p : Nat → Bool) (h : Constraints p) : clause p c633 = true := by
  simpa only [c633,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause633
def c634 : List Lit := [(277, false), (279, true)]
theorem step634 (p : Nat → Bool) (h : Constraints p) : clause p c634 = true := by
  simpa only [c634,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause634
def c635 : List Lit := [(275, false), (279, true)]
theorem step635 (p : Nat → Bool) (h : Constraints p) : clause p c635 = true := by
  simpa only [c635,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause635
def c636 : List Lit := [(144, false), (281, true)]
theorem step636 (p : Nat → Bool) (h : Constraints p) : clause p c636 = true := by
  simpa only [c636,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause636
def c637 : List Lit := [(146, false), (283, true)]
theorem step637 (p : Nat → Bool) (h : Constraints p) : clause p c637 = true := by
  simpa only [c637,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause637
def c638 : List Lit := [(283, false), (285, true)]
theorem step638 (p : Nat → Bool) (h : Constraints p) : clause p c638 = true := by
  simpa only [c638,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause638
def c639 : List Lit := [(281, false), (285, true)]
theorem step639 (p : Nat → Bool) (h : Constraints p) : clause p c639 = true := by
  simpa only [c639,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause639
def c640 : List Lit := [(281, false), (283, false), (286, true)]
theorem step640 (p : Nat → Bool) (h : Constraints p) : clause p c640 = true := by
  simpa only [c640,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause640
def c641 : List Lit := [(285, false), (287, true)]
theorem step641 (p : Nat → Bool) (h : Constraints p) : clause p c641 = true := by
  simpa only [c641,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause641
def c642 : List Lit := [(286, false), (288, true)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true := by
  simpa only [c642,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause642
def c643 : List Lit := [(279, false), (287, true)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true := by
  simpa only [c643,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause643
def c644 : List Lit := [(279, false), (285, false), (288, true)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true := by
  simpa only [c644,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause644
def c645 : List Lit := [(287, false), (289, true)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true := by
  simpa only [c645,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause645
def c646 : List Lit := [(288, false), (290, true)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true := by
  simpa only [c646,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause646
def c647 : List Lit := [(273, false), (289, true)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true := by
  simpa only [c647,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause647
def c648 : List Lit := [(273, false), (287, false), (290, true)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true := by
  simpa only [c648,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause648
def c649 : List Lit := [(274, false), (290, true)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true := by
  simpa only [c649,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause649
def c650 : List Lit := [(289, false), (291, true)]
theorem step650 (p : Nat → Bool) (h : Constraints p) : clause p c650 = true := by
  simpa only [c650,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause650
def c651 : List Lit := [(290, false), (292, true)]
theorem step651 (p : Nat → Bool) (h : Constraints p) : clause p c651 = true := by
  simpa only [c651,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause651
def c652 : List Lit := [(261, false), (291, true)]
theorem step652 (p : Nat → Bool) (h : Constraints p) : clause p c652 = true := by
  simpa only [c652,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause652
def c653 : List Lit := [(261, false), (289, false), (292, true)]
theorem step653 (p : Nat → Bool) (h : Constraints p) : clause p c653 = true := by
  simpa only [c653,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause653
def c654 : List Lit := [(149, false), (293, true)]
theorem step654 (p : Nat → Bool) (h : Constraints p) : clause p c654 = true := by
  simpa only [c654,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause654
def c655 : List Lit := [(293, false), (295, true)]
theorem step655 (p : Nat → Bool) (h : Constraints p) : clause p c655 = true := by
  simpa only [c655,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause655
def c656 : List Lit := [(152, false), (297, true)]
theorem step656 (p : Nat → Bool) (h : Constraints p) : clause p c656 = true := by
  simpa only [c656,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause656
def c657 : List Lit := [(154, false), (299, true)]
theorem step657 (p : Nat → Bool) (h : Constraints p) : clause p c657 = true := by
  simpa only [c657,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause657
def c658 : List Lit := [(299, false), (301, true)]
theorem step658 (p : Nat → Bool) (h : Constraints p) : clause p c658 = true := by
  simpa only [c658,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause658
def c659 : List Lit := [(297, false), (301, true)]
theorem step659 (p : Nat → Bool) (h : Constraints p) : clause p c659 = true := by
  simpa only [c659,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause659
def c660 : List Lit := [(301, false), (303, true)]
theorem step660 (p : Nat → Bool) (h : Constraints p) : clause p c660 = true := by
  simpa only [c660,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause660
def c661 : List Lit := [(295, false), (303, true)]
theorem step661 (p : Nat → Bool) (h : Constraints p) : clause p c661 = true := by
  simpa only [c661,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause661
def c662 : List Lit := [(155, false), (307, true)]
theorem step662 (p : Nat → Bool) (h : Constraints p) : clause p c662 = true := by
  simpa only [c662,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause662
def c663 : List Lit := [(158, false), (309, true)]
theorem step663 (p : Nat → Bool) (h : Constraints p) : clause p c663 = true := by
  simpa only [c663,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause663
def c664 : List Lit := [(161, false), (311, true)]
theorem step664 (p : Nat → Bool) (h : Constraints p) : clause p c664 = true := by
  simpa only [c664,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause664
def c665 : List Lit := [(160, false), (311, true)]
theorem step665 (p : Nat → Bool) (h : Constraints p) : clause p c665 = true := by
  simpa only [c665,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause665
def c666 : List Lit := [(311, false), (313, true)]
theorem step666 (p : Nat → Bool) (h : Constraints p) : clause p c666 = true := by
  simpa only [c666,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause666
def c667 : List Lit := [(309, false), (313, true)]
theorem step667 (p : Nat → Bool) (h : Constraints p) : clause p c667 = true := by
  simpa only [c667,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause667
def c668 : List Lit := [(309, false), (311, false), (314, true)]
theorem step668 (p : Nat → Bool) (h : Constraints p) : clause p c668 = true := by
  simpa only [c668,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause668
def c669 : List Lit := [(313, false), (315, true)]
theorem step669 (p : Nat → Bool) (h : Constraints p) : clause p c669 = true := by
  simpa only [c669,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause669
def c670 : List Lit := [(314, false), (316, true)]
theorem step670 (p : Nat → Bool) (h : Constraints p) : clause p c670 = true := by
  simpa only [c670,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause670
def c671 : List Lit := [(307, false), (315, true)]
theorem step671 (p : Nat → Bool) (h : Constraints p) : clause p c671 = true := by
  simpa only [c671,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause671
def c672 : List Lit := [(315, false), (317, true)]
theorem step672 (p : Nat → Bool) (h : Constraints p) : clause p c672 = true := by
  simpa only [c672,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause672
def c673 : List Lit := [(316, false), (318, true)]
theorem step673 (p : Nat → Bool) (h : Constraints p) : clause p c673 = true := by
  simpa only [c673,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause673
def c674 : List Lit := [(303, false), (317, true)]
theorem step674 (p : Nat → Bool) (h : Constraints p) : clause p c674 = true := by
  simpa only [c674,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause674
def c675 : List Lit := [(303, false), (315, false), (318, true)]
theorem step675 (p : Nat → Bool) (h : Constraints p) : clause p c675 = true := by
  simpa only [c675,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause675
def c676 : List Lit := [(164, false), (319, true)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true := by
  simpa only [c676,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause676
def c677 : List Lit := [(319, false), (321, true)]
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true := by
  simpa only [c677,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause677
def c678 : List Lit := [(165, false), (323, true)]
theorem step678 (p : Nat → Bool) (h : Constraints p) : clause p c678 = true := by
  simpa only [c678,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause678
def c679 : List Lit := [(323, false), (327, true)]
theorem step679 (p : Nat → Bool) (h : Constraints p) : clause p c679 = true := by
  simpa only [c679,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause679
def c680 : List Lit := [(327, false), (329, true)]
theorem step680 (p : Nat → Bool) (h : Constraints p) : clause p c680 = true := by
  simpa only [c680,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause680
def c681 : List Lit := [(321, false), (329, true)]
theorem step681 (p : Nat → Bool) (h : Constraints p) : clause p c681 = true := by
  simpa only [c681,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause681
def c682 : List Lit := [(321, false), (327, false), (330, true)]
theorem step682 (p : Nat → Bool) (h : Constraints p) : clause p c682 = true := by
  simpa only [c682,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause682
def c683 : List Lit := [(170, false), (331, true)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true := by
  simpa only [c683,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause683
def c684 : List Lit := [(169, false), (331, true)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true := by
  simpa only [c684,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause684
def c685 : List Lit := [(169, false), (170, false), (332, true)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true := by
  simpa only [c685,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause685
def c686 : List Lit := [(172, false), (333, true)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true := by
  simpa only [c686,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause686
def c687 : List Lit := [(333, false), (335, true)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true := by
  simpa only [c687,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause687
def c688 : List Lit := [(331, false), (335, true)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true := by
  simpa only [c688,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause688
def c689 : List Lit := [(331, false), (333, false), (336, true)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true := by
  simpa only [c689,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause689
def c690 : List Lit := [(332, false), (336, true)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true := by
  simpa only [c690,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause690
def c691 : List Lit := [(173, false), (337, true)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true := by
  simpa only [c691,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause691
def c692 : List Lit := [(175, false), (339, true)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true := by
  simpa only [c692,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause692
def c693 : List Lit := [(339, false), (341, true)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true := by
  simpa only [c693,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause693
def c694 : List Lit := [(337, false), (341, true)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true := by
  simpa only [c694,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause694
def c695 : List Lit := [(341, false), (343, true)]
theorem step695 (p : Nat → Bool) (h : Constraints p) : clause p c695 = true := by
  simpa only [c695,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause695
def c696 : List Lit := [(335, false), (343, true)]
theorem step696 (p : Nat → Bool) (h : Constraints p) : clause p c696 = true := by
  simpa only [c696,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause696
def c697 : List Lit := [(335, false), (341, false), (344, true)]
theorem step697 (p : Nat → Bool) (h : Constraints p) : clause p c697 = true := by
  simpa only [c697,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause697
def c698 : List Lit := [(336, false), (344, true)]
theorem step698 (p : Nat → Bool) (h : Constraints p) : clause p c698 = true := by
  simpa only [c698,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause698
def c699 : List Lit := [(343, false), (345, true)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true := by
  simpa only [c699,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause699
def c700 : List Lit := [(344, false), (346, true)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true := by
  simpa only [c700,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause700
def c701 : List Lit := [(329, false), (345, true)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true := by
  simpa only [c701,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause701
def c702 : List Lit := [(329, false), (343, false), (346, true)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true := by
  simpa only [c702,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause702
def c703 : List Lit := [(330, false), (346, true)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true := by
  simpa only [c703,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause703
def c704 : List Lit := [(345, false), (347, true)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true := by
  simpa only [c704,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause704
def c705 : List Lit := [(346, false), (348, true)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true := by
  simpa only [c705,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause705
def c706 : List Lit := [(317, false), (347, true)]
theorem step706 (p : Nat → Bool) (h : Constraints p) : clause p c706 = true := by
  simpa only [c706,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause706
def c707 : List Lit := [(317, false), (345, false), (348, true)]
theorem step707 (p : Nat → Bool) (h : Constraints p) : clause p c707 = true := by
  simpa only [c707,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause707
def c708 : List Lit := [(318, false), (348, true)]
theorem step708 (p : Nat → Bool) (h : Constraints p) : clause p c708 = true := by
  simpa only [c708,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause708
def c709 : List Lit := [(347, false), (349, true)]
theorem step709 (p : Nat → Bool) (h : Constraints p) : clause p c709 = true := by
  simpa only [c709,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause709
def c710 : List Lit := [(348, false), (350, true)]
theorem step710 (p : Nat → Bool) (h : Constraints p) : clause p c710 = true := by
  simpa only [c710,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause710
def c711 : List Lit := [(291, false), (349, true)]
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true := by
  simpa only [c711,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause711
def c712 : List Lit := [(291, false), (347, false), (350, true)]
theorem step712 (p : Nat → Bool) (h : Constraints p) : clause p c712 = true := by
  simpa only [c712,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause712
def c713 : List Lit := [(292, false), (350, true)]
theorem step713 (p : Nat → Bool) (h : Constraints p) : clause p c713 = true := by
  simpa only [c713,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause713
def c714 : List Lit := [(179, false), (351, true)]
theorem step714 (p : Nat → Bool) (h : Constraints p) : clause p c714 = true := by
  simpa only [c714,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause714
def c715 : List Lit := [(351, false), (353, true)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true := by
  simpa only [c715,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause715
def c716 : List Lit := [(177, false), (353, true)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true := by
  simpa only [c716,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause716
def c717 : List Lit := [(177, false), (351, false), (354, true)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true := by
  simpa only [c717,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause717
def c718 : List Lit := [(182, false), (355, true)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true := by
  simpa only [c718,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause718
def c719 : List Lit := [(183, false), (357, true)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true := by
  simpa only [c719,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause719
def c720 : List Lit := [(357, false), (359, true)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true := by
  simpa only [c720,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause720
def c721 : List Lit := [(355, false), (359, true)]
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true := by
  simpa only [c721,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause721
def c722 : List Lit := [(359, false), (361, true)]
theorem step722 (p : Nat → Bool) (h : Constraints p) : clause p c722 = true := by
  simpa only [c722,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause722
def c723 : List Lit := [(353, false), (361, true)]
theorem step723 (p : Nat → Bool) (h : Constraints p) : clause p c723 = true := by
  simpa only [c723,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause723
def c724 : List Lit := [(354, false), (362, true)]
theorem step724 (p : Nat → Bool) (h : Constraints p) : clause p c724 = true := by
  simpa only [c724,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause724
def c725 : List Lit := [(186, false), (363, true)]
theorem step725 (p : Nat → Bool) (h : Constraints p) : clause p c725 = true := by
  simpa only [c725,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause725
def c726 : List Lit := [(363, false), (365, true)]
theorem step726 (p : Nat → Bool) (h : Constraints p) : clause p c726 = true := by
  simpa only [c726,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause726
def c727 : List Lit := [(185, false), (365, true)]
theorem step727 (p : Nat → Bool) (h : Constraints p) : clause p c727 = true := by
  simpa only [c727,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause727
def c728 : List Lit := [(190, false), (369, true)]
theorem step728 (p : Nat → Bool) (h : Constraints p) : clause p c728 = true := by
  simpa only [c728,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause728
def c729 : List Lit := [(369, false), (371, true)]
theorem step729 (p : Nat → Bool) (h : Constraints p) : clause p c729 = true := by
  simpa only [c729,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause729
def c730 : List Lit := [(371, false), (373, true)]
theorem step730 (p : Nat → Bool) (h : Constraints p) : clause p c730 = true := by
  simpa only [c730,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause730
def c731 : List Lit := [(365, false), (373, true)]
theorem step731 (p : Nat → Bool) (h : Constraints p) : clause p c731 = true := by
  simpa only [c731,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause731
def c732 : List Lit := [(365, false), (371, false), (374, true)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true := by
  simpa only [c732,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause732
def c733 : List Lit := [(373, false), (375, true)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true := by
  simpa only [c733,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause733
def c734 : List Lit := [(374, false), (376, true)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true := by
  simpa only [c734,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause734
def c735 : List Lit := [(361, false), (375, true)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true := by
  simpa only [c735,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause735
def c736 : List Lit := [(361, false), (373, false), (376, true)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true := by
  simpa only [c736,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause736
def c737 : List Lit := [(362, false), (376, true)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true := by
  simpa only [c737,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause737
def c738 : List Lit := [(194, false), (377, true)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true := by
  simpa only [c738,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause738
def c739 : List Lit := [(377, false), (379, true)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true := by
  simpa only [c739,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause739
def c740 : List Lit := [(192, false), (379, true)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true := by
  simpa only [c740,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause740
def c741 : List Lit := [(195, false), (381, true)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true := by
  simpa only [c741,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause741
def c742 : List Lit := [(381, false), (385, true)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true := by
  simpa only [c742,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause742
def c743 : List Lit := [(385, false), (387, true)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true := by
  simpa only [c743,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause743
def c744 : List Lit := [(379, false), (387, true)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true := by
  simpa only [c744,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause744
def c745 : List Lit := [(199, false), (389, true)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true := by
  simpa only [c745,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause745
def c746 : List Lit := [(201, false), (391, true)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true := by
  simpa only [c746,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause746
def c747 : List Lit := [(391, false), (393, true)]
theorem step747 (p : Nat → Bool) (h : Constraints p) : clause p c747 = true := by
  simpa only [c747,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause747
def c748 : List Lit := [(389, false), (393, true)]
theorem step748 (p : Nat → Bool) (h : Constraints p) : clause p c748 = true := by
  simpa only [c748,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause748
def c749 : List Lit := [(204, false), (395, true)]
theorem step749 (p : Nat → Bool) (h : Constraints p) : clause p c749 = true := by
  simpa only [c749,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause749
def c750 : List Lit := [(203, false), (395, true)]
theorem step750 (p : Nat → Bool) (h : Constraints p) : clause p c750 = true := by
  simpa only [c750,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause750
def c751 : List Lit := [(395, false), (399, true)]
theorem step751 (p : Nat → Bool) (h : Constraints p) : clause p c751 = true := by
  simpa only [c751,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause751
def c752 : List Lit := [(399, false), (401, true)]
theorem step752 (p : Nat → Bool) (h : Constraints p) : clause p c752 = true := by
  simpa only [c752,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause752
def c753 : List Lit := [(393, false), (401, true)]
theorem step753 (p : Nat → Bool) (h : Constraints p) : clause p c753 = true := by
  simpa only [c753,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause753
def c754 : List Lit := [(401, false), (403, true)]
theorem step754 (p : Nat → Bool) (h : Constraints p) : clause p c754 = true := by
  simpa only [c754,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause754
def c755 : List Lit := [(387, false), (403, true)]
theorem step755 (p : Nat → Bool) (h : Constraints p) : clause p c755 = true := by
  simpa only [c755,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause755
def c756 : List Lit := [(387, false), (401, false), (404, true)]
theorem step756 (p : Nat → Bool) (h : Constraints p) : clause p c756 = true := by
  simpa only [c756,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause756
def c757 : List Lit := [(403, false), (405, true)]
theorem step757 (p : Nat → Bool) (h : Constraints p) : clause p c757 = true := by
  simpa only [c757,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause757
def c758 : List Lit := [(404, false), (406, true)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true := by
  simpa only [c758,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause758
def c759 : List Lit := [(375, false), (405, true)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true := by
  simpa only [c759,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause759
def c760 : List Lit := [(375, false), (403, false), (406, true)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true := by
  simpa only [c760,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause760
def c761 : List Lit := [(376, false), (406, true)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true := by
  simpa only [c761,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause761
def c762 : List Lit := [(208, false), (407, true)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true := by
  simpa only [c762,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause762
def c763 : List Lit := [(407, false), (409, true)]
theorem step763 (p : Nat → Bool) (h : Constraints p) : clause p c763 = true := by
  simpa only [c763,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause763
def c764 : List Lit := [(211, false), (411, true)]
theorem step764 (p : Nat → Bool) (h : Constraints p) : clause p c764 = true := by
  simpa only [c764,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause764
def c765 : List Lit := [(210, false), (411, true)]
theorem step765 (p : Nat → Bool) (h : Constraints p) : clause p c765 = true := by
  simpa only [c765,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause765
def c766 : List Lit := [(212, false), (413, true)]
theorem step766 (p : Nat → Bool) (h : Constraints p) : clause p c766 = true := by
  simpa only [c766,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause766
def c767 : List Lit := [(413, false), (415, true)]
theorem step767 (p : Nat → Bool) (h : Constraints p) : clause p c767 = true := by
  simpa only [c767,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause767
def c768 : List Lit := [(411, false), (415, true)]
theorem step768 (p : Nat → Bool) (h : Constraints p) : clause p c768 = true := by
  simpa only [c768,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause768
def c769 : List Lit := [(411, false), (413, false), (416, true)]
theorem step769 (p : Nat → Bool) (h : Constraints p) : clause p c769 = true := by
  simpa only [c769,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause769
def c770 : List Lit := [(415, false), (417, true)]
theorem step770 (p : Nat → Bool) (h : Constraints p) : clause p c770 = true := by
  simpa only [c770,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause770
def c771 : List Lit := [(416, false), (418, true)]
theorem step771 (p : Nat → Bool) (h : Constraints p) : clause p c771 = true := by
  simpa only [c771,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause771
def c772 : List Lit := [(409, false), (417, true)]
theorem step772 (p : Nat → Bool) (h : Constraints p) : clause p c772 = true := by
  simpa only [c772,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause772
def c773 : List Lit := [(409, false), (415, false), (418, true)]
theorem step773 (p : Nat → Bool) (h : Constraints p) : clause p c773 = true := by
  simpa only [c773,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause773
def c774 : List Lit := [(215, false), (419, true)]
theorem step774 (p : Nat → Bool) (h : Constraints p) : clause p c774 = true := by
  simpa only [c774,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause774
def c775 : List Lit := [(216, false), (421, true)]
theorem step775 (p : Nat → Bool) (h : Constraints p) : clause p c775 = true := by
  simpa only [c775,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause775
def c776 : List Lit := [(421, false), (423, true)]
theorem step776 (p : Nat → Bool) (h : Constraints p) : clause p c776 = true := by
  simpa only [c776,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause776
def c777 : List Lit := [(419, false), (423, true)]
theorem step777 (p : Nat → Bool) (h : Constraints p) : clause p c777 = true := by
  simpa only [c777,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause777
def c778 : List Lit := [(220, false), (427, true)]
theorem step778 (p : Nat → Bool) (h : Constraints p) : clause p c778 = true := by
  simpa only [c778,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause778
def c779 : List Lit := [(427, false), (429, true)]
theorem step779 (p : Nat → Bool) (h : Constraints p) : clause p c779 = true := by
  simpa only [c779,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause779
def c780 : List Lit := [(429, false), (431, true)]
theorem step780 (p : Nat → Bool) (h : Constraints p) : clause p c780 = true := by
  simpa only [c780,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause780
def c781 : List Lit := [(423, false), (431, true)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true := by
  simpa only [c781,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause781
def c782 : List Lit := [(431, false), (433, true)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true := by
  simpa only [c782,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause782
def c783 : List Lit := [(417, false), (433, true)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true := by
  simpa only [c783,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause783
def c784 : List Lit := [(417, false), (431, false), (434, true)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true := by
  simpa only [c784,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause784
def c785 : List Lit := [(418, false), (434, true)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true := by
  simpa only [c785,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause785
def c786 : List Lit := [(224, false), (435, true)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true := by
  simpa only [c786,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause786
def c787 : List Lit := [(223, false), (435, true)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true := by
  simpa only [c787,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause787
def c788 : List Lit := [(435, false), (437, true)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true := by
  simpa only [c788,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause788
def c789 : List Lit := [(222, false), (437, true)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true := by
  simpa only [c789,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause789
def c790 : List Lit := [(227, false), (441, true)]
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true := by
  simpa only [c790,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause790
def c791 : List Lit := [(441, false), (443, true)]
theorem step791 (p : Nat → Bool) (h : Constraints p) : clause p c791 = true := by
  simpa only [c791,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause791
def c792 : List Lit := [(443, false), (445, true)]
theorem step792 (p : Nat → Bool) (h : Constraints p) : clause p c792 = true := by
  simpa only [c792,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause792
def c793 : List Lit := [(437, false), (445, true)]
theorem step793 (p : Nat → Bool) (h : Constraints p) : clause p c793 = true := by
  simpa only [c793,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause793
def c794 : List Lit := [(437, false), (443, false), (446, true)]
theorem step794 (p : Nat → Bool) (h : Constraints p) : clause p c794 = true := by
  simpa only [c794,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause794
def c795 : List Lit := [(229, false), (447, true)]
theorem step795 (p : Nat → Bool) (h : Constraints p) : clause p c795 = true := by
  simpa only [c795,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause795
def c796 : List Lit := [(231, false), (449, true)]
theorem step796 (p : Nat → Bool) (h : Constraints p) : clause p c796 = true := by
  simpa only [c796,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause796
def c797 : List Lit := [(449, false), (451, true)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true := by
  simpa only [c797,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause797
def c798 : List Lit := [(447, false), (451, true)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true := by
  simpa only [c798,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause798
def c799 : List Lit := [(447, false), (449, false), (452, true)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true := by
  simpa only [c799,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause799
def c800 : List Lit := [(233, false), (453, true)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true := by
  simpa only [c800,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause800
def c801 : List Lit := [(235, false), (455, true)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true := by
  simpa only [c801,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause801
def c802 : List Lit := [(455, false), (457, true)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true := by
  simpa only [c802,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause802
def c803 : List Lit := [(453, false), (457, true)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true := by
  simpa only [c803,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause803
def c804 : List Lit := [(453, false), (455, false), (458, true)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true := by
  simpa only [c804,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause804
def c805 : List Lit := [(457, false), (459, true)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true := by
  simpa only [c805,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause805
def c806 : List Lit := [(458, false), (460, true)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true := by
  simpa only [c806,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause806
def c807 : List Lit := [(451, false), (459, true)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true := by
  simpa only [c807,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause807
def c808 : List Lit := [(451, false), (457, false), (460, true)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true := by
  simpa only [c808,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause808
def c809 : List Lit := [(452, false), (460, true)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true := by
  simpa only [c809,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause809
def c810 : List Lit := [(459, false), (461, true)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true := by
  simpa only [c810,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause810
def c811 : List Lit := [(460, false), (462, true)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true := by
  simpa only [c811,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause811
def c812 : List Lit := [(445, false), (461, true)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true := by
  simpa only [c812,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause812
def c813 : List Lit := [(445, false), (459, false), (462, true)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true := by
  simpa only [c813,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause813
def c814 : List Lit := [(446, false), (462, true)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true := by
  simpa only [c814,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause814
def c815 : List Lit := [(461, false), (463, true)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true := by
  simpa only [c815,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause815
def c816 : List Lit := [(462, false), (464, true)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true := by
  simpa only [c816,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause816
def c817 : List Lit := [(433, false), (463, true)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true := by
  simpa only [c817,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause817
def c818 : List Lit := [(433, false), (461, false), (464, true)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true := by
  simpa only [c818,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause818
def c819 : List Lit := [(434, false), (464, true)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true := by
  simpa only [c819,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause819
def c820 : List Lit := [(463, false), (465, true)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true := by
  simpa only [c820,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause820
def c821 : List Lit := [(464, false), (466, true)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true := by
  simpa only [c821,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause821
def c822 : List Lit := [(405, false), (465, true)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true := by
  simpa only [c822,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause822
def c823 : List Lit := [(405, false), (463, false), (466, true)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true := by
  simpa only [c823,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause823
def c824 : List Lit := [(406, false), (466, true)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true := by
  simpa only [c824,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause824
def c825 : List Lit := [(466, false), (468, true)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true := by
  simpa only [c825,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause825
def c826 : List Lit := [(349, false), (465, false), (468, true)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true := by
  simpa only [c826,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause826
def c827 : List Lit := [(350, false), (468, true)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true := by
  simpa only [c827,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause827
def c828 : List Lit := [(468, false)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true := by
  simpa only [c828,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause828
def c829 : List Lit := [(119, true), (120, true), (121, true), (122, true), (123, true), (124, true), (125, true), (126, true), (127, true), (128, true), (129, true), (130, true), (131, true), (132, true), (133, true), (134, true), (135, true), (136, true), (137, true), (138, true), (139, true), (140, true), (141, true), (142, true), (143, true), (144, true), (145, true), (146, true), (147, true), (148, true), (149, true), (150, true), (151, true), (152, true), (153, true), (154, true), (155, true), (156, true), (157, true), (158, true), (159, true), (160, true), (161, true), (162, true), (163, true), (164, true), (165, true), (166, true), (167, true), (168, true), (169, true), (170, true), (171, true), (172, true), (173, true), (174, true), (175, true), (176, true), (177, true), (178, true), (179, true), (181, true), (182, true), (183, true), (184, true), (185, true), (186, true), (187, true), (188, true), (189, true), (190, true), (191, true), (192, true), (193, true), (194, true), (195, true), (196, true), (197, true), (198, true), (199, true), (200, true), (201, true), (202, true), (203, true), (204, true), (205, true), (206, true), (207, true), (208, true), (209, true), (210, true), (211, true), (212, true), (213, true), (214, true), (215, true), (216, true), (217, true), (218, true), (219, true), (220, true), (221, true), (222, true), (223, true), (224, true), (225, true), (226, true), (227, true), (228, true), (229, true), (230, true), (231, true), (232, true), (233, true), (234, true), (235, true), (236, true)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true := by
  simpa only [c829,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause829
def c830 : List Lit := [(7, true), (1445, true)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true := by
  simpa only [c830,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause830
def c831 : List Lit := [(5, true), (1445, true)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true := by
  simpa only [c831,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause831
def c832 : List Lit := [(5, true), (7, true), (1446, true)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true := by
  simpa only [c832,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause832
def c833 : List Lit := [(1445, false), (1447, true)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true := by
  simpa only [c833,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause833
def c834 : List Lit := [(1446, false), (1448, true)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true := by
  simpa only [c834,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause834
def c835 : List Lit := [(3, true), (1447, true)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true := by
  simpa only [c835,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause835
def c836 : List Lit := [(3, true), (1445, false), (1448, true)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true := by
  simpa only [c836,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause836
def c837 : List Lit := [(3, true), (1446, false), (1449, true)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true := by
  simpa only [c837,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause837
def c838 : List Lit := [(12, true), (1450, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true := by
  simpa only [c838,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause838
def c839 : List Lit := [(11, true), (1450, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true := by
  simpa only [c839,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause839
def c840 : List Lit := [(11, true), (12, true), (1451, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true := by
  simpa only [c840,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause840
def c841 : List Lit := [(17, true), (1452, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true := by
  simpa only [c841,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause841
def c842 : List Lit := [(14, true), (1452, true)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true := by
  simpa only [c842,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause842
def c843 : List Lit := [(14, true), (17, true), (1453, true)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true := by
  simpa only [c843,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause843
def c844 : List Lit := [(1452, false), (1454, true)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true := by
  simpa only [c844,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause844
def c845 : List Lit := [(1453, false), (1455, true)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true := by
  simpa only [c845,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause845
def c846 : List Lit := [(1450, false), (1454, true)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true := by
  simpa only [c846,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause846
def c847 : List Lit := [(1450, false), (1452, false), (1455, true)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true := by
  simpa only [c847,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause847
def c848 : List Lit := [(1450, false), (1453, false), (1456, true)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true := by
  simpa only [c848,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause848
def c849 : List Lit := [(1451, false), (1455, true)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true := by
  simpa only [c849,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause849
def c850 : List Lit := [(1451, false), (1452, false), (1456, true)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true := by
  simpa only [c850,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause850
def c851 : List Lit := [(1451, false), (1453, false), (1457, true)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true := by
  simpa only [c851,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause851
def c852 : List Lit := [(1454, false), (1458, true)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true := by
  simpa only [c852,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause852
def c853 : List Lit := [(1455, false), (1459, true)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true := by
  simpa only [c853,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause853
def c854 : List Lit := [(1456, false), (1460, true)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true := by
  simpa only [c854,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause854
def c855 : List Lit := [(1457, false), (1461, true)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true := by
  simpa only [c855,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause855
def c856 : List Lit := [(1447, false), (1458, true)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true := by
  simpa only [c856,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause856
def c857 : List Lit := [(1447, false), (1454, false), (1459, true)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true := by
  simpa only [c857,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause857
def c858 : List Lit := [(1447, false), (1455, false), (1460, true)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true := by
  simpa only [c858,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause858
def c859 : List Lit := [(1448, false), (1459, true)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true := by
  simpa only [c859,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause859
def c860 : List Lit := [(1448, false), (1454, false), (1460, true)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true := by
  simpa only [c860,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause860
def c861 : List Lit := [(1448, false), (1455, false), (1461, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true := by
  simpa only [c861,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause861
def c862 : List Lit := [(1448, false), (1456, false), (1462, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true := by
  simpa only [c862,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause862
def c863 : List Lit := [(1449, false), (1460, true)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true := by
  simpa only [c863,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause863
def c864 : List Lit := [(1449, false), (1454, false), (1461, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true := by
  simpa only [c864,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause864
def c865 : List Lit := [(1449, false), (1455, false), (1462, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true := by
  simpa only [c865,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause865
def c866 : List Lit := [(23, true), (1465, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true := by
  simpa only [c866,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause866
def c867 : List Lit := [(21, true), (1465, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true := by
  simpa only [c867,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause867
def c868 : List Lit := [(21, true), (23, true), (1466, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true := by
  simpa only [c868,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause868
def c869 : List Lit := [(1465, false), (1467, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true := by
  simpa only [c869,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause869
def c870 : List Lit := [(1466, false), (1468, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true := by
  simpa only [c870,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause870
def c871 : List Lit := [(20, true), (1467, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true := by
  simpa only [c871,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause871
def c872 : List Lit := [(20, true), (1465, false), (1468, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true := by
  simpa only [c872,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause872
def c873 : List Lit := [(20, true), (1466, false), (1469, true)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true := by
  simpa only [c873,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause873
def c874 : List Lit := [(26, true), (1470, true)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true := by
  simpa only [c874,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause874
def c875 : List Lit := [(25, true), (1470, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true := by
  simpa only [c875,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause875
def c876 : List Lit := [(25, true), (26, true), (1471, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true := by
  simpa only [c876,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause876
def c877 : List Lit := [(31, true), (1472, true)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true := by
  simpa only [c877,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause877
def c878 : List Lit := [(28, true), (1472, true)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true := by
  simpa only [c878,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause878
def c879 : List Lit := [(28, true), (31, true), (1473, true)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true := by
  simpa only [c879,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause879
def c880 : List Lit := [(1472, false), (1474, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true := by
  simpa only [c880,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause880
def c881 : List Lit := [(1473, false), (1475, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true := by
  simpa only [c881,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause881
def c882 : List Lit := [(1470, false), (1474, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true := by
  simpa only [c882,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause882
def c883 : List Lit := [(1470, false), (1472, false), (1475, true)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true := by
  simpa only [c883,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause883
def c884 : List Lit := [(1470, false), (1473, false), (1476, true)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true := by
  simpa only [c884,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause884
def c885 : List Lit := [(1471, false), (1475, true)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true := by
  simpa only [c885,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause885
def c886 : List Lit := [(1471, false), (1472, false), (1476, true)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true := by
  simpa only [c886,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause886
def c887 : List Lit := [(1474, false), (1478, true)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true := by
  simpa only [c887,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause887
def c888 : List Lit := [(1475, false), (1479, true)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true := by
  simpa only [c888,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause888
def c889 : List Lit := [(1476, false), (1480, true)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true := by
  simpa only [c889,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause889
def c890 : List Lit := [(1467, false), (1478, true)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true := by
  simpa only [c890,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause890
def c891 : List Lit := [(1467, false), (1474, false), (1479, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true := by
  simpa only [c891,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause891
def c892 : List Lit := [(1467, false), (1475, false), (1480, true)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true := by
  simpa only [c892,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause892
def c893 : List Lit := [(1467, false), (1476, false), (1481, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true := by
  simpa only [c893,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause893
def c894 : List Lit := [(1468, false), (1479, true)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true := by
  simpa only [c894,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause894
def c895 : List Lit := [(1468, false), (1474, false), (1480, true)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true := by
  simpa only [c895,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause895
def c896 : List Lit := [(1468, false), (1475, false), (1481, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true := by
  simpa only [c896,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause896
def c897 : List Lit := [(1468, false), (1476, false), (1482, true)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true := by
  simpa only [c897,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause897
def c898 : List Lit := [(1469, false), (1480, true)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true := by
  simpa only [c898,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause898
def c899 : List Lit := [(1469, false), (1474, false), (1481, true)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true := by
  simpa only [c899,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause899
def c900 : List Lit := [(1469, false), (1475, false), (1482, true)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true := by
  simpa only [c900,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause900
def c901 : List Lit := [(1478, false), (1485, true)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true := by
  simpa only [c901,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause901
def c902 : List Lit := [(1479, false), (1486, true)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true := by
  simpa only [c902,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause902
def c903 : List Lit := [(1480, false), (1487, true)]
theorem step903 (p : Nat → Bool) (h : Constraints p) : clause p c903 = true := by
  simpa only [c903,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause903
def c904 : List Lit := [(1481, false), (1488, true)]
theorem step904 (p : Nat → Bool) (h : Constraints p) : clause p c904 = true := by
  simpa only [c904,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause904
def c905 : List Lit := [(1482, false), (1489, true)]
theorem step905 (p : Nat → Bool) (h : Constraints p) : clause p c905 = true := by
  simpa only [c905,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause905
def c906 : List Lit := [(1458, false), (1485, true)]
theorem step906 (p : Nat → Bool) (h : Constraints p) : clause p c906 = true := by
  simpa only [c906,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause906
def c907 : List Lit := [(1458, false), (1478, false), (1486, true)]
theorem step907 (p : Nat → Bool) (h : Constraints p) : clause p c907 = true := by
  simpa only [c907,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause907
def c908 : List Lit := [(1458, false), (1479, false), (1487, true)]
theorem step908 (p : Nat → Bool) (h : Constraints p) : clause p c908 = true := by
  simpa only [c908,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause908
def c909 : List Lit := [(1458, false), (1480, false), (1488, true)]
theorem step909 (p : Nat → Bool) (h : Constraints p) : clause p c909 = true := by
  simpa only [c909,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause909
def c910 : List Lit := [(1458, false), (1481, false), (1489, true)]
theorem step910 (p : Nat → Bool) (h : Constraints p) : clause p c910 = true := by
  simpa only [c910,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause910
def c911 : List Lit := [(1459, false), (1486, true)]
theorem step911 (p : Nat → Bool) (h : Constraints p) : clause p c911 = true := by
  simpa only [c911,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause911
def c912 : List Lit := [(1459, false), (1478, false), (1487, true)]
theorem step912 (p : Nat → Bool) (h : Constraints p) : clause p c912 = true := by
  simpa only [c912,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause912
def c913 : List Lit := [(1459, false), (1479, false), (1488, true)]
theorem step913 (p : Nat → Bool) (h : Constraints p) : clause p c913 = true := by
  simpa only [c913,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause913
def c914 : List Lit := [(1459, false), (1480, false), (1489, true)]
theorem step914 (p : Nat → Bool) (h : Constraints p) : clause p c914 = true := by
  simpa only [c914,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause914
def c915 : List Lit := [(1459, false), (1481, false), (1490, true)]
theorem step915 (p : Nat → Bool) (h : Constraints p) : clause p c915 = true := by
  simpa only [c915,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause915
def c916 : List Lit := [(1460, false), (1487, true)]
theorem step916 (p : Nat → Bool) (h : Constraints p) : clause p c916 = true := by
  simpa only [c916,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause916
def c917 : List Lit := [(1460, false), (1478, false), (1488, true)]
theorem step917 (p : Nat → Bool) (h : Constraints p) : clause p c917 = true := by
  simpa only [c917,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause917
def c918 : List Lit := [(1460, false), (1479, false), (1489, true)]
theorem step918 (p : Nat → Bool) (h : Constraints p) : clause p c918 = true := by
  simpa only [c918,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause918
def c919 : List Lit := [(1460, false), (1480, false), (1490, true)]
theorem step919 (p : Nat → Bool) (h : Constraints p) : clause p c919 = true := by
  simpa only [c919,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause919
def c920 : List Lit := [(1461, false), (1488, true)]
theorem step920 (p : Nat → Bool) (h : Constraints p) : clause p c920 = true := by
  simpa only [c920,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause920
def c921 : List Lit := [(1461, false), (1478, false), (1489, true)]
theorem step921 (p : Nat → Bool) (h : Constraints p) : clause p c921 = true := by
  simpa only [c921,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause921
def c922 : List Lit := [(1461, false), (1479, false), (1490, true)]
theorem step922 (p : Nat → Bool) (h : Constraints p) : clause p c922 = true := by
  simpa only [c922,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause922
def c923 : List Lit := [(1462, false), (1478, false), (1490, true)]
theorem step923 (p : Nat → Bool) (h : Constraints p) : clause p c923 = true := by
  simpa only [c923,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause923
def c924 : List Lit := [(37, true), (1499, true)]
theorem step924 (p : Nat → Bool) (h : Constraints p) : clause p c924 = true := by
  simpa only [c924,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause924
def c925 : List Lit := [(36, true), (1499, true)]
theorem step925 (p : Nat → Bool) (h : Constraints p) : clause p c925 = true := by
  simpa only [c925,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause925
def c926 : List Lit := [(36, true), (37, true), (1500, true)]
theorem step926 (p : Nat → Bool) (h : Constraints p) : clause p c926 = true := by
  simpa only [c926,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause926
def c927 : List Lit := [(1499, false), (1501, true)]
theorem step927 (p : Nat → Bool) (h : Constraints p) : clause p c927 = true := by
  simpa only [c927,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause927
def c928 : List Lit := [(1500, false), (1502, true)]
theorem step928 (p : Nat → Bool) (h : Constraints p) : clause p c928 = true := by
  simpa only [c928,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause928
def c929 : List Lit := [(34, true), (1501, true)]
theorem step929 (p : Nat → Bool) (h : Constraints p) : clause p c929 = true := by
  simpa only [c929,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause929
def c930 : List Lit := [(34, true), (1499, false), (1502, true)]
theorem step930 (p : Nat → Bool) (h : Constraints p) : clause p c930 = true := by
  simpa only [c930,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause930
def c931 : List Lit := [(42, true), (1504, true)]
theorem step931 (p : Nat → Bool) (h : Constraints p) : clause p c931 = true := by
  simpa only [c931,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause931
def c932 : List Lit := [(40, true), (1504, true)]
theorem step932 (p : Nat → Bool) (h : Constraints p) : clause p c932 = true := by
  simpa only [c932,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause932
def c933 : List Lit := [(40, true), (42, true), (1505, true)]
theorem step933 (p : Nat → Bool) (h : Constraints p) : clause p c933 = true := by
  simpa only [c933,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause933
def c934 : List Lit := [(46, true), (1506, true)]
theorem step934 (p : Nat → Bool) (h : Constraints p) : clause p c934 = true := by
  simpa only [c934,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause934
def c935 : List Lit := [(43, true), (1506, true)]
theorem step935 (p : Nat → Bool) (h : Constraints p) : clause p c935 = true := by
  simpa only [c935,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause935
def c936 : List Lit := [(43, true), (46, true), (1507, true)]
theorem step936 (p : Nat → Bool) (h : Constraints p) : clause p c936 = true := by
  simpa only [c936,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause936
def c937 : List Lit := [(1506, false), (1508, true)]
theorem step937 (p : Nat → Bool) (h : Constraints p) : clause p c937 = true := by
  simpa only [c937,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause937
def c938 : List Lit := [(1507, false), (1509, true)]
theorem step938 (p : Nat → Bool) (h : Constraints p) : clause p c938 = true := by
  simpa only [c938,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause938
def c939 : List Lit := [(1504, false), (1508, true)]
theorem step939 (p : Nat → Bool) (h : Constraints p) : clause p c939 = true := by
  simpa only [c939,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause939
def c940 : List Lit := [(1504, false), (1506, false), (1509, true)]
theorem step940 (p : Nat → Bool) (h : Constraints p) : clause p c940 = true := by
  simpa only [c940,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause940
def c941 : List Lit := [(1504, false), (1507, false), (1510, true)]
theorem step941 (p : Nat → Bool) (h : Constraints p) : clause p c941 = true := by
  simpa only [c941,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause941
def c942 : List Lit := [(1505, false), (1509, true)]
theorem step942 (p : Nat → Bool) (h : Constraints p) : clause p c942 = true := by
  simpa only [c942,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause942
def c943 : List Lit := [(1505, false), (1506, false), (1510, true)]
theorem step943 (p : Nat → Bool) (h : Constraints p) : clause p c943 = true := by
  simpa only [c943,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause943
def c944 : List Lit := [(1505, false), (1507, false), (1511, true)]
theorem step944 (p : Nat → Bool) (h : Constraints p) : clause p c944 = true := by
  simpa only [c944,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause944
def c945 : List Lit := [(1508, false), (1512, true)]
theorem step945 (p : Nat → Bool) (h : Constraints p) : clause p c945 = true := by
  simpa only [c945,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause945
def c946 : List Lit := [(1509, false), (1513, true)]
theorem step946 (p : Nat → Bool) (h : Constraints p) : clause p c946 = true := by
  simpa only [c946,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause946
def c947 : List Lit := [(1510, false), (1514, true)]
theorem step947 (p : Nat → Bool) (h : Constraints p) : clause p c947 = true := by
  simpa only [c947,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause947
def c948 : List Lit := [(1511, false), (1515, true)]
theorem step948 (p : Nat → Bool) (h : Constraints p) : clause p c948 = true := by
  simpa only [c948,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause948
def c949 : List Lit := [(1501, false), (1512, true)]
theorem step949 (p : Nat → Bool) (h : Constraints p) : clause p c949 = true := by
  simpa only [c949,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause949
def c950 : List Lit := [(1501, false), (1508, false), (1513, true)]
theorem step950 (p : Nat → Bool) (h : Constraints p) : clause p c950 = true := by
  simpa only [c950,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause950
def c951 : List Lit := [(1501, false), (1509, false), (1514, true)]
theorem step951 (p : Nat → Bool) (h : Constraints p) : clause p c951 = true := by
  simpa only [c951,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause951
def c952 : List Lit := [(1501, false), (1510, false), (1515, true)]
theorem step952 (p : Nat → Bool) (h : Constraints p) : clause p c952 = true := by
  simpa only [c952,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause952
def c953 : List Lit := [(1501, false), (1511, false), (1516, true)]
theorem step953 (p : Nat → Bool) (h : Constraints p) : clause p c953 = true := by
  simpa only [c953,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause953
def c954 : List Lit := [(1502, false), (1513, true)]
theorem step954 (p : Nat → Bool) (h : Constraints p) : clause p c954 = true := by
  simpa only [c954,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause954
def c955 : List Lit := [(1502, false), (1508, false), (1514, true)]
theorem step955 (p : Nat → Bool) (h : Constraints p) : clause p c955 = true := by
  simpa only [c955,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause955
def c956 : List Lit := [(1502, false), (1511, false), (1517, true)]
theorem step956 (p : Nat → Bool) (h : Constraints p) : clause p c956 = true := by
  simpa only [c956,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause956
def c957 : List Lit := [(52, true), (1519, true)]
theorem step957 (p : Nat → Bool) (h : Constraints p) : clause p c957 = true := by
  simpa only [c957,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause957
def c958 : List Lit := [(51, true), (1519, true)]
theorem step958 (p : Nat → Bool) (h : Constraints p) : clause p c958 = true := by
  simpa only [c958,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause958
def c959 : List Lit := [(51, true), (52, true), (1520, true)]
theorem step959 (p : Nat → Bool) (h : Constraints p) : clause p c959 = true := by
  simpa only [c959,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause959
def c960 : List Lit := [(1519, false), (1521, true)]
theorem step960 (p : Nat → Bool) (h : Constraints p) : clause p c960 = true := by
  simpa only [c960,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause960
def c961 : List Lit := [(1520, false), (1522, true)]
theorem step961 (p : Nat → Bool) (h : Constraints p) : clause p c961 = true := by
  simpa only [c961,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause961
def c962 : List Lit := [(47, true), (1521, true)]
theorem step962 (p : Nat → Bool) (h : Constraints p) : clause p c962 = true := by
  simpa only [c962,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause962
def c963 : List Lit := [(47, true), (1519, false), (1522, true)]
theorem step963 (p : Nat → Bool) (h : Constraints p) : clause p c963 = true := by
  simpa only [c963,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause963
def c964 : List Lit := [(47, true), (1520, false), (1523, true)]
theorem step964 (p : Nat → Bool) (h : Constraints p) : clause p c964 = true := by
  simpa only [c964,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause964
def c965 : List Lit := [(55, true), (1524, true)]
theorem step965 (p : Nat → Bool) (h : Constraints p) : clause p c965 = true := by
  simpa only [c965,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause965
def c966 : List Lit := [(54, true), (1524, true)]
theorem step966 (p : Nat → Bool) (h : Constraints p) : clause p c966 = true := by
  simpa only [c966,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause966
def c967 : List Lit := [(54, true), (55, true), (1525, true)]
theorem step967 (p : Nat → Bool) (h : Constraints p) : clause p c967 = true := by
  simpa only [c967,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause967
def c968 : List Lit := [(59, true), (1526, true)]
theorem step968 (p : Nat → Bool) (h : Constraints p) : clause p c968 = true := by
  simpa only [c968,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause968
def c969 : List Lit := [(57, true), (1526, true)]
theorem step969 (p : Nat → Bool) (h : Constraints p) : clause p c969 = true := by
  simpa only [c969,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause969
def c970 : List Lit := [(57, true), (59, true), (1527, true)]
theorem step970 (p : Nat → Bool) (h : Constraints p) : clause p c970 = true := by
  simpa only [c970,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause970
def c971 : List Lit := [(1526, false), (1528, true)]
theorem step971 (p : Nat → Bool) (h : Constraints p) : clause p c971 = true := by
  simpa only [c971,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause971
def c972 : List Lit := [(1527, false), (1529, true)]
theorem step972 (p : Nat → Bool) (h : Constraints p) : clause p c972 = true := by
  simpa only [c972,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause972
def c973 : List Lit := [(1524, false), (1528, true)]
theorem step973 (p : Nat → Bool) (h : Constraints p) : clause p c973 = true := by
  simpa only [c973,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause973
def c974 : List Lit := [(1524, false), (1526, false), (1529, true)]
theorem step974 (p : Nat → Bool) (h : Constraints p) : clause p c974 = true := by
  simpa only [c974,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause974
def c975 : List Lit := [(1524, false), (1527, false), (1530, true)]
theorem step975 (p : Nat → Bool) (h : Constraints p) : clause p c975 = true := by
  simpa only [c975,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause975
def c976 : List Lit := [(1525, false), (1529, true)]
theorem step976 (p : Nat → Bool) (h : Constraints p) : clause p c976 = true := by
  simpa only [c976,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause976
def c977 : List Lit := [(1525, false), (1526, false), (1530, true)]
theorem step977 (p : Nat → Bool) (h : Constraints p) : clause p c977 = true := by
  simpa only [c977,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause977
def c978 : List Lit := [(1525, false), (1527, false), (1531, true)]
theorem step978 (p : Nat → Bool) (h : Constraints p) : clause p c978 = true := by
  simpa only [c978,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause978
def c979 : List Lit := [(1528, false), (1532, true)]
theorem step979 (p : Nat → Bool) (h : Constraints p) : clause p c979 = true := by
  simpa only [c979,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause979
def c980 : List Lit := [(1529, false), (1533, true)]
theorem step980 (p : Nat → Bool) (h : Constraints p) : clause p c980 = true := by
  simpa only [c980,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause980
def c981 : List Lit := [(1530, false), (1534, true)]
theorem step981 (p : Nat → Bool) (h : Constraints p) : clause p c981 = true := by
  simpa only [c981,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause981
def c982 : List Lit := [(1531, false), (1535, true)]
theorem step982 (p : Nat → Bool) (h : Constraints p) : clause p c982 = true := by
  simpa only [c982,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause982
def c983 : List Lit := [(1521, false), (1528, false), (1533, true)]
theorem step983 (p : Nat → Bool) (h : Constraints p) : clause p c983 = true := by
  simpa only [c983,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause983
def c984 : List Lit := [(1521, false), (1529, false), (1534, true)]
theorem step984 (p : Nat → Bool) (h : Constraints p) : clause p c984 = true := by
  simpa only [c984,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause984
def c985 : List Lit := [(1521, false), (1530, false), (1535, true)]
theorem step985 (p : Nat → Bool) (h : Constraints p) : clause p c985 = true := by
  simpa only [c985,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause985
def c986 : List Lit := [(1521, false), (1531, false), (1536, true)]
theorem step986 (p : Nat → Bool) (h : Constraints p) : clause p c986 = true := by
  simpa only [c986,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause986
def c987 : List Lit := [(1522, false), (1528, false), (1534, true)]
theorem step987 (p : Nat → Bool) (h : Constraints p) : clause p c987 = true := by
  simpa only [c987,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause987
def c988 : List Lit := [(1522, false), (1529, false), (1535, true)]
theorem step988 (p : Nat → Bool) (h : Constraints p) : clause p c988 = true := by
  simpa only [c988,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause988
def c989 : List Lit := [(1522, false), (1530, false), (1536, true)]
theorem step989 (p : Nat → Bool) (h : Constraints p) : clause p c989 = true := by
  simpa only [c989,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause989
def c990 : List Lit := [(1523, false), (1528, false), (1535, true)]
theorem step990 (p : Nat → Bool) (h : Constraints p) : clause p c990 = true := by
  simpa only [c990,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause990
def c991 : List Lit := [(1523, false), (1529, false), (1536, true)]
theorem step991 (p : Nat → Bool) (h : Constraints p) : clause p c991 = true := by
  simpa only [c991,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause991
def c992 : List Lit := [(1535, false), (1542, true)]
theorem step992 (p : Nat → Bool) (h : Constraints p) : clause p c992 = true := by
  simpa only [c992,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause992
def c993 : List Lit := [(1512, false), (1532, false), (1540, true)]
theorem step993 (p : Nat → Bool) (h : Constraints p) : clause p c993 = true := by
  simpa only [c993,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause993
def c994 : List Lit := [(1512, false), (1533, false), (1541, true)]
theorem step994 (p : Nat → Bool) (h : Constraints p) : clause p c994 = true := by
  simpa only [c994,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause994
def c995 : List Lit := [(1512, false), (1534, false), (1542, true)]
theorem step995 (p : Nat → Bool) (h : Constraints p) : clause p c995 = true := by
  simpa only [c995,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause995
def c996 : List Lit := [(1512, false), (1535, false), (1543, true)]
theorem step996 (p : Nat → Bool) (h : Constraints p) : clause p c996 = true := by
  simpa only [c996,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause996
def c997 : List Lit := [(1512, false), (1536, false), (1544, true)]
theorem step997 (p : Nat → Bool) (h : Constraints p) : clause p c997 = true := by
  simpa only [c997,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause997
def c998 : List Lit := [(1513, false), (1533, false), (1542, true)]
theorem step998 (p : Nat → Bool) (h : Constraints p) : clause p c998 = true := by
  simpa only [c998,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause998
def c999 : List Lit := [(1513, false), (1534, false), (1543, true)]
theorem step999 (p : Nat → Bool) (h : Constraints p) : clause p c999 = true := by
  simpa only [c999,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause999
def c1000 : List Lit := [(1513, false), (1535, false), (1544, true)]
theorem step1000 (p : Nat → Bool) (h : Constraints p) : clause p c1000 = true := by
  simpa only [c1000,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1000
def c1001 : List Lit := [(1513, false), (1536, false), (1545, true)]
theorem step1001 (p : Nat → Bool) (h : Constraints p) : clause p c1001 = true := by
  simpa only [c1001,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1001
def c1002 : List Lit := [(1514, false), (1532, false), (1542, true)]
theorem step1002 (p : Nat → Bool) (h : Constraints p) : clause p c1002 = true := by
  simpa only [c1002,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1002
def c1003 : List Lit := [(1514, false), (1533, false), (1543, true)]
theorem step1003 (p : Nat → Bool) (h : Constraints p) : clause p c1003 = true := by
  simpa only [c1003,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1003
def c1004 : List Lit := [(1514, false), (1534, false), (1544, true)]
theorem step1004 (p : Nat → Bool) (h : Constraints p) : clause p c1004 = true := by
  simpa only [c1004,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1004
def c1005 : List Lit := [(1514, false), (1535, false), (1545, true)]
theorem step1005 (p : Nat → Bool) (h : Constraints p) : clause p c1005 = true := by
  simpa only [c1005,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1005
def c1006 : List Lit := [(1514, false), (1536, false), (1546, true)]
theorem step1006 (p : Nat → Bool) (h : Constraints p) : clause p c1006 = true := by
  simpa only [c1006,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1006
def c1007 : List Lit := [(1515, false), (1533, false), (1544, true)]
theorem step1007 (p : Nat → Bool) (h : Constraints p) : clause p c1007 = true := by
  simpa only [c1007,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1007
def c1008 : List Lit := [(1515, false), (1534, false), (1545, true)]
theorem step1008 (p : Nat → Bool) (h : Constraints p) : clause p c1008 = true := by
  simpa only [c1008,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1008
def c1009 : List Lit := [(1516, false), (1533, false), (1545, true)]
theorem step1009 (p : Nat → Bool) (h : Constraints p) : clause p c1009 = true := by
  simpa only [c1009,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1009
def c1010 : List Lit := [(1517, false), (1533, false), (1546, true)]
theorem step1010 (p : Nat → Bool) (h : Constraints p) : clause p c1010 = true := by
  simpa only [c1010,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1010
def c1011 : List Lit := [(1545, false), (1559, true)]
theorem step1011 (p : Nat → Bool) (h : Constraints p) : clause p c1011 = true := by
  simpa only [c1011,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1011
def c1012 : List Lit := [(1485, false), (1541, false), (1556, true)]
theorem step1012 (p : Nat → Bool) (h : Constraints p) : clause p c1012 = true := by
  simpa only [c1012,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1012
def c1013 : List Lit := [(1485, false), (1542, false), (1557, true)]
theorem step1013 (p : Nat → Bool) (h : Constraints p) : clause p c1013 = true := by
  simpa only [c1013,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1013
def c1014 : List Lit := [(1485, false), (1543, false), (1558, true)]
theorem step1014 (p : Nat → Bool) (h : Constraints p) : clause p c1014 = true := by
  simpa only [c1014,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1014
def c1015 : List Lit := [(1485, false), (1544, false), (1559, true)]
theorem step1015 (p : Nat → Bool) (h : Constraints p) : clause p c1015 = true := by
  simpa only [c1015,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1015
def c1016 : List Lit := [(1485, false), (1545, false), (1560, true)]
theorem step1016 (p : Nat → Bool) (h : Constraints p) : clause p c1016 = true := by
  simpa only [c1016,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1016
def c1017 : List Lit := [(1485, false), (1546, false), (1561, true)]
theorem step1017 (p : Nat → Bool) (h : Constraints p) : clause p c1017 = true := by
  simpa only [c1017,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1017
def c1018 : List Lit := [(1486, false), (1541, false), (1557, true)]
theorem step1018 (p : Nat → Bool) (h : Constraints p) : clause p c1018 = true := by
  simpa only [c1018,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1018
def c1019 : List Lit := [(1486, false), (1542, false), (1558, true)]
theorem step1019 (p : Nat → Bool) (h : Constraints p) : clause p c1019 = true := by
  simpa only [c1019,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1019
def c1020 : List Lit := [(1486, false), (1543, false), (1559, true)]
theorem step1020 (p : Nat → Bool) (h : Constraints p) : clause p c1020 = true := by
  simpa only [c1020,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1020
def c1021 : List Lit := [(1486, false), (1544, false), (1560, true)]
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true := by
  simpa only [c1021,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1021
def c1022 : List Lit := [(1486, false), (1545, false), (1561, true)]
theorem step1022 (p : Nat → Bool) (h : Constraints p) : clause p c1022 = true := by
  simpa only [c1022,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1022
def c1023 : List Lit := [(1487, false), (1541, false), (1558, true)]
theorem step1023 (p : Nat → Bool) (h : Constraints p) : clause p c1023 = true := by
  simpa only [c1023,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1023
def c1024 : List Lit := [(1487, false), (1542, false), (1559, true)]
theorem step1024 (p : Nat → Bool) (h : Constraints p) : clause p c1024 = true := by
  simpa only [c1024,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1024
def c1025 : List Lit := [(1487, false), (1543, false), (1560, true)]
theorem step1025 (p : Nat → Bool) (h : Constraints p) : clause p c1025 = true := by
  simpa only [c1025,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1025
def c1026 : List Lit := [(1487, false), (1544, false), (1561, true)]
theorem step1026 (p : Nat → Bool) (h : Constraints p) : clause p c1026 = true := by
  simpa only [c1026,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1026
def c1027 : List Lit := [(1487, false), (1545, false), (1562, true)]
theorem step1027 (p : Nat → Bool) (h : Constraints p) : clause p c1027 = true := by
  simpa only [c1027,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1027
def c1028 : List Lit := [(1488, false), (1540, false), (1558, true)]
theorem step1028 (p : Nat → Bool) (h : Constraints p) : clause p c1028 = true := by
  simpa only [c1028,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1028
def c1029 : List Lit := [(1488, false), (1541, false), (1559, true)]
theorem step1029 (p : Nat → Bool) (h : Constraints p) : clause p c1029 = true := by
  simpa only [c1029,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1029
def c1030 : List Lit := [(1488, false), (1542, false), (1560, true)]
theorem step1030 (p : Nat → Bool) (h : Constraints p) : clause p c1030 = true := by
  simpa only [c1030,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1030
def c1031 : List Lit := [(1488, false), (1543, false), (1561, true)]
theorem step1031 (p : Nat → Bool) (h : Constraints p) : clause p c1031 = true := by
  simpa only [c1031,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1031
def c1032 : List Lit := [(1488, false), (1544, false), (1562, true)]
theorem step1032 (p : Nat → Bool) (h : Constraints p) : clause p c1032 = true := by
  simpa only [c1032,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1032
def c1033 : List Lit := [(1488, false), (1545, false), (1563, true)]
theorem step1033 (p : Nat → Bool) (h : Constraints p) : clause p c1033 = true := by
  simpa only [c1033,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1033
def c1034 : List Lit := [(1489, false), (1540, false), (1559, true)]
theorem step1034 (p : Nat → Bool) (h : Constraints p) : clause p c1034 = true := by
  simpa only [c1034,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1034
def c1035 : List Lit := [(1489, false), (1541, false), (1560, true)]
theorem step1035 (p : Nat → Bool) (h : Constraints p) : clause p c1035 = true := by
  simpa only [c1035,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1035
def c1036 : List Lit := [(1489, false), (1542, false), (1561, true)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true := by
  simpa only [c1036,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1036
def c1037 : List Lit := [(1489, false), (1543, false), (1562, true)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true := by
  simpa only [c1037,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1037
def c1038 : List Lit := [(1490, false), (1541, false), (1561, true)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true := by
  simpa only [c1038,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1038
def c1039 : List Lit := [(1490, false), (1542, false), (1562, true)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true := by
  simpa only [c1039,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1039
def c1040 : List Lit := [(1490, false), (1543, false), (1563, true)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true := by
  simpa only [c1040,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1040
def c1041 : List Lit := [(65, true), (1569, true)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true := by
  simpa only [c1041,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1041
def c1042 : List Lit := [(64, true), (1569, true)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true := by
  simpa only [c1042,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1042
def c1043 : List Lit := [(64, true), (65, true), (1570, true)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true := by
  simpa only [c1043,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1043
def c1044 : List Lit := [(1569, false), (1571, true)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true := by
  simpa only [c1044,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1044
def c1045 : List Lit := [(1570, false), (1572, true)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true := by
  simpa only [c1045,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1045
def c1046 : List Lit := [(68, true), (1574, true)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true := by
  simpa only [c1046,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1046
def c1047 : List Lit := [(67, true), (1574, true)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true := by
  simpa only [c1047,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1047
def c1048 : List Lit := [(67, true), (68, true), (1575, true)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true := by
  simpa only [c1048,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1048
def c1049 : List Lit := [(74, true), (1576, true)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true := by
  simpa only [c1049,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1049
def c1050 : List Lit := [(72, true), (1576, true)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true := by
  simpa only [c1050,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1050
def c1051 : List Lit := [(72, true), (74, true), (1577, true)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true := by
  simpa only [c1051,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1051
def c1052 : List Lit := [(1576, false), (1578, true)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true := by
  simpa only [c1052,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1052
def c1053 : List Lit := [(1577, false), (1579, true)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true := by
  simpa only [c1053,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1053
def c1054 : List Lit := [(1574, false), (1578, true)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true := by
  simpa only [c1054,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1054
def c1055 : List Lit := [(1574, false), (1576, false), (1579, true)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true := by
  simpa only [c1055,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1055
def c1056 : List Lit := [(1574, false), (1577, false), (1580, true)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true := by
  simpa only [c1056,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1056
def c1057 : List Lit := [(1575, false), (1576, false), (1580, true)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true := by
  simpa only [c1057,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1057
def c1058 : List Lit := [(1575, false), (1577, false), (1581, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true := by
  simpa only [c1058,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1058
def c1059 : List Lit := [(1578, false), (1582, true)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true := by
  simpa only [c1059,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1059
def c1060 : List Lit := [(1579, false), (1583, true)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true := by
  simpa only [c1060,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1060
def c1061 : List Lit := [(1580, false), (1584, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true := by
  simpa only [c1061,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1061
def c1062 : List Lit := [(1571, false), (1582, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true := by
  simpa only [c1062,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1062
def c1063 : List Lit := [(1571, false), (1578, false), (1583, true)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true := by
  simpa only [c1063,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1063
def c1064 : List Lit := [(1571, false), (1579, false), (1584, true)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true := by
  simpa only [c1064,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1064
def c1065 : List Lit := [(1571, false), (1580, false), (1585, true)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true := by
  simpa only [c1065,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1065
def c1066 : List Lit := [(1571, false), (1581, false), (1586, true)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true := by
  simpa only [c1066,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1066
def c1067 : List Lit := [(1572, false), (1583, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true := by
  simpa only [c1067,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1067
def c1068 : List Lit := [(1572, false), (1578, false), (1584, true)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true := by
  simpa only [c1068,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1068
def c1069 : List Lit := [(1572, false), (1579, false), (1585, true)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true := by
  simpa only [c1069,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1069
def c1070 : List Lit := [(81, true), (1589, true)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true := by
  simpa only [c1070,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1070
def c1071 : List Lit := [(77, true), (1589, true)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true := by
  simpa only [c1071,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1071
def c1072 : List Lit := [(77, true), (81, true), (1590, true)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true := by
  simpa only [c1072,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1072
def c1073 : List Lit := [(1589, false), (1591, true)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true := by
  simpa only [c1073,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1073
def c1074 : List Lit := [(1590, false), (1592, true)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true := by
  simpa only [c1074,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1074
def c1075 : List Lit := [(76, true), (1591, true)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true := by
  simpa only [c1075,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1075
def c1076 : List Lit := [(76, true), (1589, false), (1592, true)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true := by
  simpa only [c1076,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1076
def c1077 : List Lit := [(76, true), (1590, false), (1593, true)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true := by
  simpa only [c1077,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1077
def c1078 : List Lit := [(85, true), (1594, true)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true := by
  simpa only [c1078,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1078
def c1079 : List Lit := [(83, true), (1594, true)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true := by
  simpa only [c1079,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1079
def c1080 : List Lit := [(83, true), (85, true), (1595, true)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true := by
  simpa only [c1080,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1080
def c1081 : List Lit := [(90, true), (1596, true)]
theorem step1081 (p : Nat → Bool) (h : Constraints p) : clause p c1081 = true := by
  simpa only [c1081,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1081
def c1082 : List Lit := [(86, true), (1596, true)]
theorem step1082 (p : Nat → Bool) (h : Constraints p) : clause p c1082 = true := by
  simpa only [c1082,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1082
def c1083 : List Lit := [(86, true), (90, true), (1597, true)]
theorem step1083 (p : Nat → Bool) (h : Constraints p) : clause p c1083 = true := by
  simpa only [c1083,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1083
def c1084 : List Lit := [(1596, false), (1598, true)]
theorem step1084 (p : Nat → Bool) (h : Constraints p) : clause p c1084 = true := by
  simpa only [c1084,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1084
def c1085 : List Lit := [(1597, false), (1599, true)]
theorem step1085 (p : Nat → Bool) (h : Constraints p) : clause p c1085 = true := by
  simpa only [c1085,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1085
def c1086 : List Lit := [(1594, false), (1598, true)]
theorem step1086 (p : Nat → Bool) (h : Constraints p) : clause p c1086 = true := by
  simpa only [c1086,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1086
def c1087 : List Lit := [(1594, false), (1596, false), (1599, true)]
theorem step1087 (p : Nat → Bool) (h : Constraints p) : clause p c1087 = true := by
  simpa only [c1087,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1087
def c1088 : List Lit := [(1594, false), (1597, false), (1600, true)]
theorem step1088 (p : Nat → Bool) (h : Constraints p) : clause p c1088 = true := by
  simpa only [c1088,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1088
def c1089 : List Lit := [(1595, false), (1599, true)]
theorem step1089 (p : Nat → Bool) (h : Constraints p) : clause p c1089 = true := by
  simpa only [c1089,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1089
def c1090 : List Lit := [(1595, false), (1596, false), (1600, true)]
theorem step1090 (p : Nat → Bool) (h : Constraints p) : clause p c1090 = true := by
  simpa only [c1090,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1090
def c1091 : List Lit := [(1595, false), (1597, false), (1601, true)]
theorem step1091 (p : Nat → Bool) (h : Constraints p) : clause p c1091 = true := by
  simpa only [c1091,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1091
def c1092 : List Lit := [(1598, false), (1602, true)]
theorem step1092 (p : Nat → Bool) (h : Constraints p) : clause p c1092 = true := by
  simpa only [c1092,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1092
def c1093 : List Lit := [(1599, false), (1603, true)]
theorem step1093 (p : Nat → Bool) (h : Constraints p) : clause p c1093 = true := by
  simpa only [c1093,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1093
def c1094 : List Lit := [(1600, false), (1604, true)]
theorem step1094 (p : Nat → Bool) (h : Constraints p) : clause p c1094 = true := by
  simpa only [c1094,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1094
def c1095 : List Lit := [(1601, false), (1605, true)]
theorem step1095 (p : Nat → Bool) (h : Constraints p) : clause p c1095 = true := by
  simpa only [c1095,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1095
def c1096 : List Lit := [(1591, false), (1602, true)]
theorem step1096 (p : Nat → Bool) (h : Constraints p) : clause p c1096 = true := by
  simpa only [c1096,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1096
def c1097 : List Lit := [(1591, false), (1598, false), (1603, true)]
theorem step1097 (p : Nat → Bool) (h : Constraints p) : clause p c1097 = true := by
  simpa only [c1097,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1097
def c1098 : List Lit := [(1591, false), (1599, false), (1604, true)]
theorem step1098 (p : Nat → Bool) (h : Constraints p) : clause p c1098 = true := by
  simpa only [c1098,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1098
def c1099 : List Lit := [(1591, false), (1600, false), (1605, true)]
theorem step1099 (p : Nat → Bool) (h : Constraints p) : clause p c1099 = true := by
  simpa only [c1099,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1099
def c1100 : List Lit := [(1591, false), (1601, false), (1606, true)]
theorem step1100 (p : Nat → Bool) (h : Constraints p) : clause p c1100 = true := by
  simpa only [c1100,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1100
def c1101 : List Lit := [(1592, false), (1603, true)]
theorem step1101 (p : Nat → Bool) (h : Constraints p) : clause p c1101 = true := by
  simpa only [c1101,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1101
def c1102 : List Lit := [(1592, false), (1598, false), (1604, true)]
theorem step1102 (p : Nat → Bool) (h : Constraints p) : clause p c1102 = true := by
  simpa only [c1102,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1102
def c1103 : List Lit := [(1592, false), (1599, false), (1605, true)]
theorem step1103 (p : Nat → Bool) (h : Constraints p) : clause p c1103 = true := by
  simpa only [c1103,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1103
def c1104 : List Lit := [(1592, false), (1600, false), (1606, true)]
theorem step1104 (p : Nat → Bool) (h : Constraints p) : clause p c1104 = true := by
  simpa only [c1104,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1104
def c1105 : List Lit := [(1593, false), (1598, false), (1605, true)]
theorem step1105 (p : Nat → Bool) (h : Constraints p) : clause p c1105 = true := by
  simpa only [c1105,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1105
def c1106 : List Lit := [(1593, false), (1599, false), (1606, true)]
theorem step1106 (p : Nat → Bool) (h : Constraints p) : clause p c1106 = true := by
  simpa only [c1106,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1106
def c1107 : List Lit := [(1602, false), (1609, true)]
theorem step1107 (p : Nat → Bool) (h : Constraints p) : clause p c1107 = true := by
  simpa only [c1107,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1107
def c1108 : List Lit := [(1604, false), (1611, true)]
theorem step1108 (p : Nat → Bool) (h : Constraints p) : clause p c1108 = true := by
  simpa only [c1108,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1108
def c1109 : List Lit := [(1605, false), (1612, true)]
theorem step1109 (p : Nat → Bool) (h : Constraints p) : clause p c1109 = true := by
  simpa only [c1109,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1109
def c1110 : List Lit := [(1582, false), (1602, false), (1610, true)]
theorem step1110 (p : Nat → Bool) (h : Constraints p) : clause p c1110 = true := by
  simpa only [c1110,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1110
def c1111 : List Lit := [(1582, false), (1603, false), (1611, true)]
theorem step1111 (p : Nat → Bool) (h : Constraints p) : clause p c1111 = true := by
  simpa only [c1111,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1111
def c1112 : List Lit := [(1582, false), (1604, false), (1612, true)]
theorem step1112 (p : Nat → Bool) (h : Constraints p) : clause p c1112 = true := by
  simpa only [c1112,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1112
def c1113 : List Lit := [(1582, false), (1605, false), (1613, true)]
theorem step1113 (p : Nat → Bool) (h : Constraints p) : clause p c1113 = true := by
  simpa only [c1113,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1113
def c1114 : List Lit := [(1582, false), (1606, false), (1614, true)]
theorem step1114 (p : Nat → Bool) (h : Constraints p) : clause p c1114 = true := by
  simpa only [c1114,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1114
def c1115 : List Lit := [(1583, false), (1602, false), (1611, true)]
theorem step1115 (p : Nat → Bool) (h : Constraints p) : clause p c1115 = true := by
  simpa only [c1115,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1115
def c1116 : List Lit := [(1583, false), (1603, false), (1612, true)]
theorem step1116 (p : Nat → Bool) (h : Constraints p) : clause p c1116 = true := by
  simpa only [c1116,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1116
def c1117 : List Lit := [(1583, false), (1604, false), (1613, true)]
theorem step1117 (p : Nat → Bool) (h : Constraints p) : clause p c1117 = true := by
  simpa only [c1117,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1117
def c1118 : List Lit := [(1583, false), (1605, false), (1614, true)]
theorem step1118 (p : Nat → Bool) (h : Constraints p) : clause p c1118 = true := by
  simpa only [c1118,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1118
def c1119 : List Lit := [(1583, false), (1606, false), (1615, true)]
theorem step1119 (p : Nat → Bool) (h : Constraints p) : clause p c1119 = true := by
  simpa only [c1119,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1119
def c1120 : List Lit := [(1584, false), (1602, false), (1612, true)]
theorem step1120 (p : Nat → Bool) (h : Constraints p) : clause p c1120 = true := by
  simpa only [c1120,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1120
def c1121 : List Lit := [(1584, false), (1603, false), (1613, true)]
theorem step1121 (p : Nat → Bool) (h : Constraints p) : clause p c1121 = true := by
  simpa only [c1121,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1121
def c1122 : List Lit := [(1584, false), (1604, false), (1614, true)]
theorem step1122 (p : Nat → Bool) (h : Constraints p) : clause p c1122 = true := by
  simpa only [c1122,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1122
def c1123 : List Lit := [(1584, false), (1605, false), (1615, true)]
theorem step1123 (p : Nat → Bool) (h : Constraints p) : clause p c1123 = true := by
  simpa only [c1123,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1123
def c1124 : List Lit := [(1584, false), (1606, false), (1616, true)]
theorem step1124 (p : Nat → Bool) (h : Constraints p) : clause p c1124 = true := by
  simpa only [c1124,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1124
def c1125 : List Lit := [(1585, false), (1612, true)]
theorem step1125 (p : Nat → Bool) (h : Constraints p) : clause p c1125 = true := by
  simpa only [c1125,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1125
def c1126 : List Lit := [(1585, false), (1602, false), (1613, true)]
theorem step1126 (p : Nat → Bool) (h : Constraints p) : clause p c1126 = true := by
  simpa only [c1126,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1126
def c1127 : List Lit := [(1585, false), (1603, false), (1614, true)]
theorem step1127 (p : Nat → Bool) (h : Constraints p) : clause p c1127 = true := by
  simpa only [c1127,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1127
def c1128 : List Lit := [(1585, false), (1604, false), (1615, true)]
theorem step1128 (p : Nat → Bool) (h : Constraints p) : clause p c1128 = true := by
  simpa only [c1128,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1128
def c1129 : List Lit := [(1585, false), (1605, false), (1616, true)]
theorem step1129 (p : Nat → Bool) (h : Constraints p) : clause p c1129 = true := by
  simpa only [c1129,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1129
def c1130 : List Lit := [(1586, false), (1613, true)]
theorem step1130 (p : Nat → Bool) (h : Constraints p) : clause p c1130 = true := by
  simpa only [c1130,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1130
def c1131 : List Lit := [(1586, false), (1602, false), (1614, true)]
theorem step1131 (p : Nat → Bool) (h : Constraints p) : clause p c1131 = true := by
  simpa only [c1131,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1131
def c1132 : List Lit := [(1586, false), (1603, false), (1615, true)]
theorem step1132 (p : Nat → Bool) (h : Constraints p) : clause p c1132 = true := by
  simpa only [c1132,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1132
def c1133 : List Lit := [(1586, false), (1604, false), (1616, true)]
theorem step1133 (p : Nat → Bool) (h : Constraints p) : clause p c1133 = true := by
  simpa only [c1133,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1133
def c1134 : List Lit := [(1586, false), (1605, false), (1617, true)]
theorem step1134 (p : Nat → Bool) (h : Constraints p) : clause p c1134 = true := by
  simpa only [c1134,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1134
def c1135 : List Lit := [(94, true), (1623, true)]
theorem step1135 (p : Nat → Bool) (h : Constraints p) : clause p c1135 = true := by
  simpa only [c1135,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1135
def c1136 : List Lit := [(93, true), (1623, true)]
theorem step1136 (p : Nat → Bool) (h : Constraints p) : clause p c1136 = true := by
  simpa only [c1136,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1136
def c1137 : List Lit := [(93, true), (94, true), (1624, true)]
theorem step1137 (p : Nat → Bool) (h : Constraints p) : clause p c1137 = true := by
  simpa only [c1137,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1137
def c1138 : List Lit := [(1623, false), (1625, true)]
theorem step1138 (p : Nat → Bool) (h : Constraints p) : clause p c1138 = true := by
  simpa only [c1138,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1138
def c1139 : List Lit := [(1624, false), (1626, true)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true := by
  simpa only [c1139,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1139
def c1140 : List Lit := [(92, true), (1625, true)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true := by
  simpa only [c1140,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1140
def c1141 : List Lit := [(92, true), (1623, false), (1626, true)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true := by
  simpa only [c1141,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1141
def c1142 : List Lit := [(92, true), (1624, false), (1627, true)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true := by
  simpa only [c1142,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1142
def c1143 : List Lit := [(98, true), (1628, true)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true := by
  simpa only [c1143,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1143
def c1144 : List Lit := [(97, true), (1628, true)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true := by
  simpa only [c1144,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1144
def c1145 : List Lit := [(97, true), (98, true), (1629, true)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true := by
  simpa only [c1145,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1145
def c1146 : List Lit := [(104, true), (1630, true)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true := by
  simpa only [c1146,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1146
def c1147 : List Lit := [(102, true), (1630, true)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true := by
  simpa only [c1147,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1147
def c1148 : List Lit := [(102, true), (104, true), (1631, true)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true := by
  simpa only [c1148,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1148
def c1149 : List Lit := [(1630, false), (1632, true)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true := by
  simpa only [c1149,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1149
def c1150 : List Lit := [(1631, false), (1633, true)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true := by
  simpa only [c1150,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1150
def c1151 : List Lit := [(1628, false), (1632, true)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true := by
  simpa only [c1151,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1151
def c1152 : List Lit := [(1628, false), (1630, false), (1633, true)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true := by
  simpa only [c1152,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1152
def c1153 : List Lit := [(1628, false), (1631, false), (1634, true)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true := by
  simpa only [c1153,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1153
def c1154 : List Lit := [(1629, false), (1633, true)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true := by
  simpa only [c1154,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1154
def c1155 : List Lit := [(1629, false), (1630, false), (1634, true)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true := by
  simpa only [c1155,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1155
def c1156 : List Lit := [(1629, false), (1631, false), (1635, true)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true := by
  simpa only [c1156,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1156
def c1157 : List Lit := [(1632, false), (1636, true)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true := by
  simpa only [c1157,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1157
def c1158 : List Lit := [(1633, false), (1637, true)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true := by
  simpa only [c1158,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1158
def c1159 : List Lit := [(1634, false), (1638, true)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true := by
  simpa only [c1159,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1159
def c1160 : List Lit := [(1625, false), (1636, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true := by
  simpa only [c1160,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1160
def c1161 : List Lit := [(1625, false), (1632, false), (1637, true)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true := by
  simpa only [c1161,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1161
def c1162 : List Lit := [(1625, false), (1633, false), (1638, true)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true := by
  simpa only [c1162,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1162
def c1163 : List Lit := [(1625, false), (1634, false), (1639, true)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true := by
  simpa only [c1163,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1163
def c1164 : List Lit := [(1625, false), (1635, false), (1640, true)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true := by
  simpa only [c1164,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1164
def c1165 : List Lit := [(1626, false), (1637, true)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true := by
  simpa only [c1165,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1165
def c1166 : List Lit := [(1626, false), (1632, false), (1638, true)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true := by
  simpa only [c1166,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1166
def c1167 : List Lit := [(1626, false), (1633, false), (1639, true)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true := by
  simpa only [c1167,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1167
def c1168 : List Lit := [(1626, false), (1634, false), (1640, true)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true := by
  simpa only [c1168,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1168
def c1169 : List Lit := [(1627, false), (1638, true)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true := by
  simpa only [c1169,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1169
def c1170 : List Lit := [(1627, false), (1632, false), (1639, true)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true := by
  simpa only [c1170,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1170
def c1171 : List Lit := [(1627, false), (1633, false), (1640, true)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true := by
  simpa only [c1171,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1171
def c1172 : List Lit := [(1627, false), (1634, false), (1641, true)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true := by
  simpa only [c1172,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1172
def c1173 : List Lit := [(109, true), (1643, true)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true := by
  simpa only [c1173,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1173
def c1174 : List Lit := [(106, true), (1643, true)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true := by
  simpa only [c1174,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1174
def c1175 : List Lit := [(106, true), (109, true), (1644, true)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true := by
  simpa only [c1175,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1175
def c1176 : List Lit := [(1643, false), (1645, true)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true := by
  simpa only [c1176,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1176
def c1177 : List Lit := [(1644, false), (1646, true)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true := by
  simpa only [c1177,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1177
def c1178 : List Lit := [(105, true), (1645, true)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true := by
  simpa only [c1178,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1178
def c1179 : List Lit := [(105, true), (1643, false), (1646, true)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true := by
  simpa only [c1179,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1179
def c1180 : List Lit := [(113, true), (1648, true)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true := by
  simpa only [c1180,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1180
def c1181 : List Lit := [(111, true), (1648, true)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true := by
  simpa only [c1181,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1181
def c1182 : List Lit := [(111, true), (113, true), (1649, true)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true := by
  simpa only [c1182,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1182
def c1183 : List Lit := [(117, true), (1650, true)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true := by
  simpa only [c1183,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1183
def c1184 : List Lit := [(115, true), (1650, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true := by
  simpa only [c1184,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1184
def c1185 : List Lit := [(115, true), (117, true), (1651, true)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true := by
  simpa only [c1185,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1185
def c1186 : List Lit := [(1650, false), (1652, true)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true := by
  simpa only [c1186,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1186
def c1187 : List Lit := [(1651, false), (1653, true)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true := by
  simpa only [c1187,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1187
def c1188 : List Lit := [(1648, false), (1652, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true := by
  simpa only [c1188,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1188
def c1189 : List Lit := [(1648, false), (1650, false), (1653, true)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true := by
  simpa only [c1189,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1189
def c1190 : List Lit := [(1649, false), (1653, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true := by
  simpa only [c1190,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1190
def c1191 : List Lit := [(1652, false), (1656, true)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true := by
  simpa only [c1191,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1191
def c1192 : List Lit := [(1653, false), (1657, true)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true := by
  simpa only [c1192,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1192
def c1193 : List Lit := [(1645, false), (1656, true)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true := by
  simpa only [c1193,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1193
def c1194 : List Lit := [(1645, false), (1652, false), (1657, true)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true := by
  simpa only [c1194,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1194
def c1195 : List Lit := [(1645, false), (1653, false), (1658, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true := by
  simpa only [c1195,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1195
def c1196 : List Lit := [(1646, false), (1657, true)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true := by
  simpa only [c1196,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1196
def c1197 : List Lit := [(1646, false), (1652, false), (1658, true)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true := by
  simpa only [c1197,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1197
def c1198 : List Lit := [(1646, false), (1653, false), (1659, true)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true := by
  simpa only [c1198,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1198
def c1199 : List Lit := [(1657, false), (1664, true)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true := by
  simpa only [c1199,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1199
def c1200 : List Lit := [(1658, false), (1665, true)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true := by
  simpa only [c1200,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1200
def c1201 : List Lit := [(1659, false), (1666, true)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true := by
  simpa only [c1201,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1201
def c1202 : List Lit := [(1636, false), (1656, false), (1664, true)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true := by
  simpa only [c1202,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1202
def c1203 : List Lit := [(1636, false), (1657, false), (1665, true)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true := by
  simpa only [c1203,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1203
def c1204 : List Lit := [(1636, false), (1658, false), (1666, true)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true := by
  simpa only [c1204,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1204
def c1205 : List Lit := [(1636, false), (1659, false), (1667, true)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true := by
  simpa only [c1205,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1205
def c1206 : List Lit := [(1637, false), (1664, true)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true := by
  simpa only [c1206,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1206
def c1207 : List Lit := [(1637, false), (1656, false), (1665, true)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true := by
  simpa only [c1207,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1207
def c1208 : List Lit := [(1637, false), (1657, false), (1666, true)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true := by
  simpa only [c1208,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1208
def c1209 : List Lit := [(1637, false), (1658, false), (1667, true)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true := by
  simpa only [c1209,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1209
def c1210 : List Lit := [(1637, false), (1659, false), (1668, true)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true := by
  simpa only [c1210,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1210
def c1211 : List Lit := [(1638, false), (1665, true)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true := by
  simpa only [c1211,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1211
def c1212 : List Lit := [(1638, false), (1656, false), (1666, true)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true := by
  simpa only [c1212,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1212
def c1213 : List Lit := [(1638, false), (1657, false), (1667, true)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true := by
  simpa only [c1213,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1213
def c1214 : List Lit := [(1638, false), (1658, false), (1668, true)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true := by
  simpa only [c1214,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1214
def c1215 : List Lit := [(1638, false), (1659, false), (1669, true)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true := by
  simpa only [c1215,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1215
def c1216 : List Lit := [(1639, false), (1666, true)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true := by
  simpa only [c1216,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1216
def c1217 : List Lit := [(1639, false), (1656, false), (1667, true)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true := by
  simpa only [c1217,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1217
def c1218 : List Lit := [(1639, false), (1657, false), (1668, true)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true := by
  simpa only [c1218,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1218
def c1219 : List Lit := [(1639, false), (1658, false), (1669, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true := by
  simpa only [c1219,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1219
def c1220 : List Lit := [(1640, false), (1667, true)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true := by
  simpa only [c1220,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1220
def c1221 : List Lit := [(1640, false), (1656, false), (1668, true)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true := by
  simpa only [c1221,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1221
def c1222 : List Lit := [(1640, false), (1657, false), (1669, true)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true := by
  simpa only [c1222,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1222
def c1223 : List Lit := [(1641, false), (1668, true)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true := by
  simpa only [c1223,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1223
def c1224 : List Lit := [(1641, false), (1656, false), (1669, true)]
theorem step1224 (p : Nat → Bool) (h : Constraints p) : clause p c1224 = true := by
  simpa only [c1224,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1224
def c1225 : List Lit := [(1609, false), (1667, false), (1682, true)]
theorem step1225 (p : Nat → Bool) (h : Constraints p) : clause p c1225 = true := by
  simpa only [c1225,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1225
def c1226 : List Lit := [(1609, false), (1668, false), (1683, true)]
theorem step1226 (p : Nat → Bool) (h : Constraints p) : clause p c1226 = true := by
  simpa only [c1226,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1226
def c1227 : List Lit := [(1610, false), (1665, false), (1681, true)]
theorem step1227 (p : Nat → Bool) (h : Constraints p) : clause p c1227 = true := by
  simpa only [c1227,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1227
def c1228 : List Lit := [(1610, false), (1666, false), (1682, true)]
theorem step1228 (p : Nat → Bool) (h : Constraints p) : clause p c1228 = true := by
  simpa only [c1228,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1228
def c1229 : List Lit := [(1610, false), (1667, false), (1683, true)]
theorem step1229 (p : Nat → Bool) (h : Constraints p) : clause p c1229 = true := by
  simpa only [c1229,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1229
def c1230 : List Lit := [(1610, false), (1668, false), (1684, true)]
theorem step1230 (p : Nat → Bool) (h : Constraints p) : clause p c1230 = true := by
  simpa only [c1230,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1230
def c1231 : List Lit := [(1610, false), (1669, false), (1685, true)]
theorem step1231 (p : Nat → Bool) (h : Constraints p) : clause p c1231 = true := by
  simpa only [c1231,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1231
def c1232 : List Lit := [(1611, false), (1665, false), (1682, true)]
theorem step1232 (p : Nat → Bool) (h : Constraints p) : clause p c1232 = true := by
  simpa only [c1232,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1232
def c1233 : List Lit := [(1611, false), (1666, false), (1683, true)]
theorem step1233 (p : Nat → Bool) (h : Constraints p) : clause p c1233 = true := by
  simpa only [c1233,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1233
def c1234 : List Lit := [(1611, false), (1667, false), (1684, true)]
theorem step1234 (p : Nat → Bool) (h : Constraints p) : clause p c1234 = true := by
  simpa only [c1234,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1234
def c1235 : List Lit := [(1611, false), (1668, false), (1685, true)]
theorem step1235 (p : Nat → Bool) (h : Constraints p) : clause p c1235 = true := by
  simpa only [c1235,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1235
def c1236 : List Lit := [(1611, false), (1669, false), (1686, true)]
theorem step1236 (p : Nat → Bool) (h : Constraints p) : clause p c1236 = true := by
  simpa only [c1236,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1236
def c1237 : List Lit := [(1612, false), (1664, false), (1682, true)]
theorem step1237 (p : Nat → Bool) (h : Constraints p) : clause p c1237 = true := by
  simpa only [c1237,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1237
def c1238 : List Lit := [(1612, false), (1665, false), (1683, true)]
theorem step1238 (p : Nat → Bool) (h : Constraints p) : clause p c1238 = true := by
  simpa only [c1238,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1238
def c1239 : List Lit := [(1612, false), (1666, false), (1684, true)]
theorem step1239 (p : Nat → Bool) (h : Constraints p) : clause p c1239 = true := by
  simpa only [c1239,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1239
def c1240 : List Lit := [(1612, false), (1667, false), (1685, true)]
theorem step1240 (p : Nat → Bool) (h : Constraints p) : clause p c1240 = true := by
  simpa only [c1240,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1240
def c1241 : List Lit := [(1612, false), (1668, false), (1686, true)]
theorem step1241 (p : Nat → Bool) (h : Constraints p) : clause p c1241 = true := by
  simpa only [c1241,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1241
def c1242 : List Lit := [(1612, false), (1669, false), (1687, true)]
theorem step1242 (p : Nat → Bool) (h : Constraints p) : clause p c1242 = true := by
  simpa only [c1242,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1242
def c1243 : List Lit := [(1613, false), (1664, false), (1683, true)]
theorem step1243 (p : Nat → Bool) (h : Constraints p) : clause p c1243 = true := by
  simpa only [c1243,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1243
def c1244 : List Lit := [(1613, false), (1665, false), (1684, true)]
theorem step1244 (p : Nat → Bool) (h : Constraints p) : clause p c1244 = true := by
  simpa only [c1244,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1244
def c1245 : List Lit := [(1613, false), (1666, false), (1685, true)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true := by
  simpa only [c1245,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1245
def c1246 : List Lit := [(1613, false), (1667, false), (1686, true)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true := by
  simpa only [c1246,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1246
def c1247 : List Lit := [(1613, false), (1668, false), (1687, true)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true := by
  simpa only [c1247,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1247
def c1248 : List Lit := [(1613, false), (1669, false), (1688, true)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true := by
  simpa only [c1248,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1248
def c1249 : List Lit := [(1614, false), (1664, false), (1684, true)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true := by
  simpa only [c1249,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1249
def c1250 : List Lit := [(1614, false), (1665, false), (1685, true)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true := by
  simpa only [c1250,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1250
def c1251 : List Lit := [(1614, false), (1666, false), (1686, true)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true := by
  simpa only [c1251,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1251
def c1252 : List Lit := [(1614, false), (1667, false), (1687, true)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true := by
  simpa only [c1252,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1252
def c1253 : List Lit := [(1614, false), (1668, false), (1688, true)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true := by
  simpa only [c1253,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1253
def c1254 : List Lit := [(1615, false), (1665, false), (1686, true)]
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true := by
  simpa only [c1254,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1254
def c1255 : List Lit := [(1615, false), (1666, false), (1687, true)]
theorem step1255 (p : Nat → Bool) (h : Constraints p) : clause p c1255 = true := by
  simpa only [c1255,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1255
def c1256 : List Lit := [(1615, false), (1667, false), (1688, true)]
theorem step1256 (p : Nat → Bool) (h : Constraints p) : clause p c1256 = true := by
  simpa only [c1256,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1256
def c1257 : List Lit := [(1616, false), (1665, false), (1687, true)]
theorem step1257 (p : Nat → Bool) (h : Constraints p) : clause p c1257 = true := by
  simpa only [c1257,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1257
def c1258 : List Lit := [(1616, false), (1666, false), (1688, true)]
theorem step1258 (p : Nat → Bool) (h : Constraints p) : clause p c1258 = true := by
  simpa only [c1258,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1258
def c1259 : List Lit := [(1617, false), (1665, false), (1688, true)]
theorem step1259 (p : Nat → Bool) (h : Constraints p) : clause p c1259 = true := by
  simpa only [c1259,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1259
def c1260 : List Lit := [(1556, false), (1688, false), (1708, true)]
theorem step1260 (p : Nat → Bool) (h : Constraints p) : clause p c1260 = true := by
  simpa only [c1260,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1260
def c1261 : List Lit := [(1557, false), (1687, false), (1708, true)]
theorem step1261 (p : Nat → Bool) (h : Constraints p) : clause p c1261 = true := by
  simpa only [c1261,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1261
def c1262 : List Lit := [(1558, false), (1686, false), (1708, true)]
theorem step1262 (p : Nat → Bool) (h : Constraints p) : clause p c1262 = true := by
  simpa only [c1262,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1262
def c1263 : List Lit := [(1559, false), (1685, false), (1708, true)]
theorem step1263 (p : Nat → Bool) (h : Constraints p) : clause p c1263 = true := by
  simpa only [c1263,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1263
def c1264 : List Lit := [(1560, false), (1684, false), (1708, true)]
theorem step1264 (p : Nat → Bool) (h : Constraints p) : clause p c1264 = true := by
  simpa only [c1264,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1264
def c1265 : List Lit := [(1561, false), (1683, false), (1708, true)]
theorem step1265 (p : Nat → Bool) (h : Constraints p) : clause p c1265 = true := by
  simpa only [c1265,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1265
def c1266 : List Lit := [(1562, false), (1682, false), (1708, true)]
theorem step1266 (p : Nat → Bool) (h : Constraints p) : clause p c1266 = true := by
  simpa only [c1266,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1266
def c1267 : List Lit := [(1563, false), (1681, false), (1708, true)]
theorem step1267 (p : Nat → Bool) (h : Constraints p) : clause p c1267 = true := by
  simpa only [c1267,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1267
def c1268 : List Lit := [(1708, false)]
theorem step1268 (p : Nat → Bool) (h : Constraints p) : clause p c1268 = true := by
  simpa only [c1268,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1268
def c1269 : List Lit := [(6, false), (12, false), (55, false), (73, false)]
theorem step1269 (p : Nat → Bool) (h : Constraints p) : clause p c1269 = true := by
  simpa only [c1269,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1269
def c1270 : List Lit := [(14, false), (18, false), (24, false), (28, false)]
theorem step1270 (p : Nat → Bool) (h : Constraints p) : clause p c1270 = true := by
  simpa only [c1270,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1270
def c1271 : List Lit := [(16, false), (21, false), (26, false), (29, false)]
theorem step1271 (p : Nat → Bool) (h : Constraints p) : clause p c1271 = true := by
  simpa only [c1271,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1271
def c1272 : List Lit := [(16, false), (21, false), (81, false), (88, false)]
theorem step1272 (p : Nat → Bool) (h : Constraints p) : clause p c1272 = true := by
  simpa only [c1272,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1272
def c1273 : List Lit := [(17, false), (19, false), (82, false), (85, false)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true := by
  simpa only [c1273,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1273
def c1274 : List Lit := [(21, false), (29, false), (88, false), (98, false)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true := by
  simpa only [c1274,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1274
def c1275 : List Lit := [(45, false), (46, false), (47, false), (48, false)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true := by
  simpa only [c1275,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1275
def c1276 : List Lit := [(50, false), (51, false), (55, false), (56, false)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true := by
  simpa only [c1276,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1276
def c1277 : List Lit := [(50, false), (51, false), (81, false), (82, false)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true := by
  simpa only [c1277,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1277
def c1278 : List Lit := [(50, false), (52, false), (65, false), (70, false)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true := by
  simpa only [c1278,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1278
def c1279 : List Lit := [(50, false), (52, false), (81, false), (88, false)]
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true := by
  simpa only [c1279,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1279
def c1280 : List Lit := [(51, false), (56, false), (82, false), (92, false)]
theorem step1280 (p : Nat → Bool) (h : Constraints p) : clause p c1280 = true := by
  simpa only [c1280,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1280
def c1281 : List Lit := [(52, false), (70, false), (88, false), (106, false)]
theorem step1281 (p : Nat → Bool) (h : Constraints p) : clause p c1281 = true := by
  simpa only [c1281,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1281
def c1282 : List Lit := [(53, false), (54, false), (55, false), (56, false)]
theorem step1282 (p : Nat → Bool) (h : Constraints p) : clause p c1282 = true := by
  simpa only [c1282,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1282
def c1283 : List Lit := [(54, false), (56, false), (91, false), (92, false)]
theorem step1283 (p : Nat → Bool) (h : Constraints p) : clause p c1283 = true := by
  simpa only [c1283,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1283
def c1284 : List Lit := [(65, false), (66, false), (70, false), (72, false)]
theorem step1284 (p : Nat → Bool) (h : Constraints p) : clause p c1284 = true := by
  simpa only [c1284,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1284
def c1285 : List Lit := [(65, false), (70, false), (73, false), (77, false)]
theorem step1285 (p : Nat → Bool) (h : Constraints p) : clause p c1285 = true := by
  simpa only [c1285,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1285
def c1286 : List Lit := [(65, false), (70, false), (101, false), (106, false)]
theorem step1286 (p : Nat → Bool) (h : Constraints p) : clause p c1286 = true := by
  simpa only [c1286,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1286
def c1287 : List Lit := [(81, false), (84, false), (88, false), (90, false)]
theorem step1287 (p : Nat → Bool) (h : Constraints p) : clause p c1287 = true := by
  simpa only [c1287,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1287
def c1288 : List Lit := [(81, false), (88, false), (101, false), (106, false)]
theorem step1288 (p : Nat → Bool) (h : Constraints p) : clause p c1288 = true := by
  simpa only [c1288,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1288
def c1289 : List Lit := [(82, false), (92, false), (102, false), (112, false)]
theorem step1289 (p : Nat → Bool) (h : Constraints p) : clause p c1289 = true := by
  simpa only [c1289,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1289
def c1290 : List Lit := [(83, false), (84, false), (89, false), (90, false)]
theorem step1290 (p : Nat → Bool) (h : Constraints p) : clause p c1290 = true := by
  simpa only [c1290,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1290
def c1291 : List Lit := [(86, false), (87, false), (96, false), (97, false)]
theorem step1291 (p : Nat → Bool) (h : Constraints p) : clause p c1291 = true := by
  simpa only [c1291,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1291
def c1292 : List Lit := [(86, false), (88, false), (89, false), (90, false)]
theorem step1292 (p : Nat → Bool) (h : Constraints p) : clause p c1292 = true := by
  simpa only [c1292,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1292
def c1293 : List Lit := [(86, false), (88, false), (96, false), (98, false)]
theorem step1293 (p : Nat → Bool) (h : Constraints p) : clause p c1293 = true := by
  simpa only [c1293,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1293
def c1294 : List Lit := [(91, false), (92, false), (93, false), (95, false)]
theorem step1294 (p : Nat → Bool) (h : Constraints p) : clause p c1294 = true := by
  simpa only [c1294,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1294
def c1295 : List Lit := [(91, false), (92, false), (111, false), (112, false)]
theorem step1295 (p : Nat → Bool) (h : Constraints p) : clause p c1295 = true := by
  simpa only [c1295,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1295
def c1296 : List Lit := [(91, false), (93, false), (97, false), (100, false)]
theorem step1296 (p : Nat → Bool) (h : Constraints p) : clause p c1296 = true := by
  simpa only [c1296,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1296
def c1297 : List Lit := [(96, false), (97, false), (98, false), (99, false)]
theorem step1297 (p : Nat → Bool) (h : Constraints p) : clause p c1297 = true := by
  simpa only [c1297,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1297
def c1298 : List Lit := [(101, false), (102, false), (106, false), (107, false)]
theorem step1298 (p : Nat → Bool) (h : Constraints p) : clause p c1298 = true := by
  simpa only [c1298,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1298
def c1299 : List Lit := [(113, false), (114, false), (116, false), (117, false)]
theorem step1299 (p : Nat → Bool) (h : Constraints p) : clause p c1299 = true := by
  simpa only [c1299,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1299
end B112E007
