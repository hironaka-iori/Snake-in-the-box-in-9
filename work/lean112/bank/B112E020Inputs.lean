import TreeRup
namespace B112E020
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
structure Block0 (p : Nat → Bool) : Prop where
  clause1 : p 1 = false ∨ p 2 = false ∨ p 3 = false ∨ p 9 = false
  clause2 : p 125 = false ∨ p 2 = false ∨ p 9 = false
  clause3 : p 1 = false ∨ p 125 = true ∨ p 3 = true ∨ p 9 = true
  clause4 : p 2 = false ∨ p 1 = true
  clause5 : p 2 = true
  clause6 : p 3 = false ∨ p 127 = true ∨ p 7 = true
  clause7 : p 4 = false ∨ p 128 = true ∨ p 6 = true
  clause8 : p 4 = false ∨ p 128 = true ∨ p 5 = true
  clause9 : p 5 = false ∨ p 4 = false ∨ p 10 = false ∨ p 19 = false
  clause10 : p 5 = false ∨ p 129 = true ∨ p 10 = true ∨ p 19 = true
  clause11 : p 5 = false ∨ p 129 = true ∨ p 4 = true ∨ p 19 = true
  clause12 : p 5 = false ∨ p 129 = true ∨ p 4 = true ∨ p 10 = true
  clause13 : p 6 = false ∨ p 4 = false ∨ p 7 = false ∨ p 11 = false
  clause14 : p 6 = false ∨ p 130 = true ∨ p 7 = true ∨ p 11 = true
  clause15 : p 6 = false ∨ p 130 = true ∨ p 4 = true ∨ p 11 = true
  clause16 : p 6 = false ∨ p 130 = true ∨ p 4 = true ∨ p 7 = true
  clause17 : p 7 = false ∨ p 3 = false ∨ p 6 = false ∨ p 22 = false
  clause18 : p 7 = false ∨ p 131 = true ∨ p 6 = true ∨ p 22 = true
  clause19 : p 7 = false ∨ p 131 = true ∨ p 3 = true ∨ p 22 = true
  clause20 : p 8 = false ∨ p 10 = false ∨ p 25 = false ∨ p 43 = false
  clause21 : p 8 = false ∨ p 132 = true ∨ p 25 = true ∨ p 43 = true
  clause22 : p 8 = false ∨ p 132 = true ∨ p 10 = true ∨ p 43 = true
  clause23 : p 8 = false ∨ p 132 = true ∨ p 10 = true ∨ p 25 = true
  clause24 : p 9 = false ∨ p 1 = false ∨ p 28 = false ∨ p 44 = false
  clause25 : p 9 = false ∨ p 133 = true ∨ p 28 = true ∨ p 44 = true
  clause26 : p 10 = false ∨ p 5 = true ∨ p 8 = true ∨ p 12 = true ∨ p 13 = true ∨ p 29 = true ∨ p 47 = true
  clause27 : p 10 = false ∨ p 5 = false ∨ p 8 = false ∨ p 12 = false
  clause28 : p 10 = false ∨ p 5 = false ∨ p 8 = false ∨ p 29 = false
  clause29 : p 10 = false ∨ p 5 = false ∨ p 8 = false ∨ p 47 = false
  clause30 : p 10 = false ∨ p 5 = false ∨ p 12 = false ∨ p 29 = false
  clause31 : p 10 = false ∨ p 5 = false ∨ p 12 = false ∨ p 47 = false
  clause32 : p 10 = false ∨ p 5 = false ∨ p 29 = false ∨ p 47 = false
structure Block1 (p : Nat → Bool) : Prop where
  clause33 : p 10 = false ∨ p 8 = false ∨ p 12 = false ∨ p 29 = false
  clause34 : p 10 = false ∨ p 8 = false ∨ p 12 = false ∨ p 47 = false
  clause35 : p 10 = false ∨ p 8 = false ∨ p 29 = false ∨ p 47 = false
  clause36 : p 10 = false ∨ p 12 = false ∨ p 29 = false ∨ p 47 = false
  clause37 : p 10 = false ∨ p 134 = true ∨ p 8 = true ∨ p 12 = true ∨ p 13 = true ∨ p 29 = true ∨ p 47 = true
  clause38 : p 10 = false ∨ p 134 = true ∨ p 5 = true ∨ p 8 = true ∨ p 13 = true ∨ p 29 = true ∨ p 47 = true
  clause39 : p 10 = false ∨ p 134 = true ∨ p 5 = true ∨ p 8 = true ∨ p 12 = true ∨ p 13 = true ∨ p 47 = true
  clause40 : p 10 = false ∨ p 134 = true ∨ p 5 = true ∨ p 8 = true ∨ p 12 = true ∨ p 13 = true ∨ p 29 = true
  clause41 : p 11 = false ∨ p 6 = false ∨ p 12 = false ∨ p 30 = false
  clause42 : p 11 = false ∨ p 6 = false ∨ p 12 = false ∨ p 48 = false
  clause43 : p 11 = false ∨ p 6 = false ∨ p 30 = false ∨ p 48 = false
  clause44 : p 11 = false ∨ p 12 = false ∨ p 30 = false ∨ p 48 = false
  clause45 : p 11 = false ∨ p 135 = true ∨ p 12 = true ∨ p 30 = true ∨ p 48 = true
  clause46 : p 11 = false ∨ p 135 = true ∨ p 6 = true ∨ p 12 = true ∨ p 48 = true
  clause47 : p 12 = false ∨ p 136 = true ∨ p 11 = true
  clause48 : p 12 = false ∨ p 136 = true ∨ p 10 = true
  clause49 : p 13 = false ∨ p 137 = true
  clause50 : p 14 = false ∨ p 15 = false ∨ p 16 = false ∨ p 24 = false
  clause51 : p 14 = false ∨ p 138 = true ∨ p 15 = true ∨ p 24 = true
  clause52 : p 14 = false ∨ p 138 = true ∨ p 15 = true ∨ p 16 = true
  clause53 : p 15 = false ∨ p 14 = false ∨ p 17 = false ∨ p 51 = false
  clause54 : p 15 = false ∨ p 14 = false ∨ p 17 = false ∨ p 71 = false
  clause55 : p 15 = false ∨ p 14 = false ∨ p 19 = false ∨ p 25 = false
  clause56 : p 15 = false ∨ p 17 = false ∨ p 19 = false ∨ p 25 = false
  clause57 : p 15 = false ∨ p 17 = false ∨ p 25 = false ∨ p 51 = false
  clause58 : p 15 = false ∨ p 17 = false ∨ p 25 = false ∨ p 71 = false
  clause59 : p 16 = false ∨ p 140 = true ∨ p 17 = true ∨ p 26 = true
  clause60 : p 16 = false ∨ p 140 = true ∨ p 14 = true ∨ p 26 = true
  clause61 : p 16 = false ∨ p 140 = true ∨ p 14 = true ∨ p 17 = true
  clause62 : p 17 = false ∨ p 15 = false ∨ p 16 = false ∨ p 18 = false
  clause63 : p 17 = false ∨ p 15 = false ∨ p 16 = false ∨ p 27 = false
  clause64 : p 17 = false ∨ p 15 = false ∨ p 18 = false ∨ p 27 = false
structure Block2 (p : Nat → Bool) : Prop where
  clause65 : p 17 = false ∨ p 16 = false ∨ p 18 = false ∨ p 27 = false
  clause66 : p 17 = false ∨ p 141 = true ∨ p 15 = true ∨ p 18 = true ∨ p 27 = true
  clause67 : p 17 = false ∨ p 141 = true ∨ p 15 = true ∨ p 16 = true ∨ p 27 = true
  clause68 : p 18 = false ∨ p 142 = true ∨ p 23 = true
  clause69 : p 18 = false ∨ p 142 = true ∨ p 17 = true
  clause70 : p 19 = false ∨ p 5 = false ∨ p 15 = false ∨ p 21 = false
  clause71 : p 19 = false ∨ p 5 = false ∨ p 15 = false ∨ p 29 = false
  clause72 : p 19 = false ∨ p 5 = false ∨ p 15 = false ∨ p 75 = false
  clause73 : p 19 = false ∨ p 5 = false ∨ p 21 = false ∨ p 29 = false
  clause74 : p 19 = false ∨ p 5 = false ∨ p 21 = false ∨ p 75 = false
  clause75 : p 19 = false ∨ p 5 = false ∨ p 29 = false ∨ p 75 = false
  clause76 : p 19 = false ∨ p 15 = false ∨ p 21 = false ∨ p 29 = false
  clause77 : p 19 = false ∨ p 15 = false ∨ p 21 = false ∨ p 75 = false
  clause78 : p 19 = false ∨ p 15 = false ∨ p 29 = false ∨ p 75 = false
  clause79 : p 19 = false ∨ p 21 = false ∨ p 29 = false ∨ p 75 = false
  clause80 : p 20 = false ∨ p 21 = false ∨ p 22 = false ∨ p 31 = false
  clause81 : p 20 = false ∨ p 21 = false ∨ p 22 = false ∨ p 58 = false
  clause82 : p 20 = false ∨ p 21 = false ∨ p 31 = false ∨ p 58 = false
  clause83 : p 20 = false ∨ p 22 = false ∨ p 31 = false ∨ p 58 = false
  clause84 : p 144 = false ∨ p 31 = false ∨ p 58 = false
  clause85 : p 20 = false ∨ p 144 = true ∨ p 22 = true ∨ p 31 = true ∨ p 58 = true
  clause86 : p 20 = false ∨ p 144 = true ∨ p 21 = true ∨ p 22 = true ∨ p 58 = true
  clause87 : p 21 = false ∨ p 19 = false ∨ p 20 = false ∨ p 23 = false
  clause88 : p 21 = false ∨ p 145 = true ∨ p 20 = true ∨ p 23 = true
  clause89 : p 21 = false ∨ p 145 = true ∨ p 19 = true ∨ p 23 = true
  clause90 : p 21 = false ∨ p 145 = true ∨ p 19 = true ∨ p 20 = true
  clause91 : p 22 = false ∨ p 7 = false ∨ p 20 = false ∨ p 23 = false
  clause92 : p 22 = false ∨ p 7 = false ∨ p 20 = false ∨ p 32 = false
  clause93 : p 22 = false ∨ p 7 = false ∨ p 20 = false ∨ p 77 = false
  clause94 : p 22 = false ∨ p 7 = false ∨ p 23 = false ∨ p 32 = false
  clause95 : p 22 = false ∨ p 7 = false ∨ p 23 = false ∨ p 77 = false
  clause96 : p 22 = false ∨ p 7 = false ∨ p 32 = false ∨ p 59 = false
structure Block3 (p : Nat → Bool) : Prop where
  clause97 : p 22 = false ∨ p 7 = false ∨ p 32 = false ∨ p 77 = false
  clause98 : p 22 = false ∨ p 20 = false ∨ p 23 = false ∨ p 32 = false
  clause99 : p 22 = false ∨ p 20 = false ∨ p 23 = false ∨ p 77 = false
  clause100 : p 22 = false ∨ p 20 = false ∨ p 32 = false ∨ p 59 = false
  clause101 : p 22 = false ∨ p 20 = false ∨ p 32 = false ∨ p 77 = false
  clause102 : p 22 = false ∨ p 20 = false ∨ p 59 = false ∨ p 77 = false
  clause103 : p 22 = false ∨ p 23 = false ∨ p 32 = false ∨ p 59 = false
  clause104 : p 22 = false ∨ p 23 = false ∨ p 32 = false ∨ p 77 = false
  clause105 : p 22 = false ∨ p 23 = false ∨ p 59 = false ∨ p 77 = false
  clause106 : p 22 = false ∨ p 32 = false ∨ p 59 = false ∨ p 77 = false
  clause107 : p 23 = false ∨ p 18 = false ∨ p 21 = false ∨ p 22 = false
  clause108 : p 23 = false ∨ p 147 = true ∨ p 21 = true ∨ p 22 = true
  clause109 : p 23 = false ∨ p 147 = true ∨ p 18 = true ∨ p 22 = true
  clause110 : p 24 = false ∨ p 14 = false ∨ p 25 = false ∨ p 28 = false
  clause111 : p 24 = false ∨ p 25 = false ∨ p 26 = false ∨ p 28 = false
  clause112 : p 24 = false ∨ p 148 = true ∨ p 25 = true ∨ p 26 = true ∨ p 28 = true
  clause113 : p 24 = false ∨ p 148 = true ∨ p 14 = true ∨ p 26 = true ∨ p 28 = true
  clause114 : p 24 = false ∨ p 148 = true ∨ p 14 = true ∨ p 25 = true ∨ p 28 = true
  clause115 : p 25 = false ∨ p 8 = false ∨ p 15 = false ∨ p 24 = false
  clause116 : p 25 = false ∨ p 8 = false ∨ p 15 = false ∨ p 29 = false
  clause117 : p 25 = false ∨ p 8 = false ∨ p 15 = false ∨ p 60 = false
  clause118 : p 25 = false ∨ p 8 = false ∨ p 24 = false ∨ p 27 = false
  clause119 : p 25 = false ∨ p 8 = false ∨ p 24 = false ∨ p 29 = false
  clause120 : p 25 = false ∨ p 8 = false ∨ p 24 = false ∨ p 60 = false
  clause121 : p 25 = false ∨ p 8 = false ∨ p 27 = false ∨ p 29 = false
  clause122 : p 25 = false ∨ p 8 = false ∨ p 27 = false ∨ p 60 = false
  clause123 : p 25 = false ∨ p 8 = false ∨ p 29 = false ∨ p 60 = false
  clause124 : p 25 = false ∨ p 15 = false ∨ p 24 = false ∨ p 27 = false
  clause125 : p 25 = false ∨ p 15 = false ∨ p 24 = false ∨ p 29 = false
  clause126 : p 25 = false ∨ p 15 = false ∨ p 24 = false ∨ p 60 = false
  clause127 : p 25 = false ∨ p 15 = false ∨ p 27 = false ∨ p 60 = false
  clause128 : p 25 = false ∨ p 15 = false ∨ p 29 = false ∨ p 60 = false
structure Block4 (p : Nat → Bool) : Prop where
  clause129 : p 25 = false ∨ p 24 = false ∨ p 27 = false ∨ p 29 = false
  clause130 : p 25 = false ∨ p 24 = false ∨ p 27 = false ∨ p 60 = false
  clause131 : p 25 = false ∨ p 24 = false ∨ p 29 = false ∨ p 60 = false
  clause132 : p 25 = false ∨ p 27 = false ∨ p 29 = false ∨ p 60 = false
  clause133 : p 25 = false ∨ p 149 = true ∨ p 8 = true ∨ p 15 = true ∨ p 27 = true ∨ p 29 = true ∨ p 60 = true
  clause134 : p 26 = false ∨ p 16 = false ∨ p 24 = false ∨ p 27 = false
  clause135 : p 26 = false ∨ p 16 = false ∨ p 24 = false ∨ p 30 = false
  clause136 : p 26 = false ∨ p 16 = false ∨ p 24 = false ∨ p 61 = false
  clause137 : p 26 = false ∨ p 16 = false ∨ p 24 = false ∨ p 78 = false
  clause138 : p 26 = false ∨ p 16 = false ∨ p 27 = false ∨ p 30 = false
  clause139 : p 26 = false ∨ p 16 = false ∨ p 27 = false ∨ p 61 = false
  clause140 : p 26 = false ∨ p 16 = false ∨ p 27 = false ∨ p 78 = false
  clause141 : p 26 = false ∨ p 16 = false ∨ p 30 = false ∨ p 61 = false
  clause142 : p 26 = false ∨ p 16 = false ∨ p 30 = false ∨ p 78 = false
  clause143 : p 26 = false ∨ p 16 = false ∨ p 61 = false ∨ p 78 = false
  clause144 : p 26 = false ∨ p 24 = false ∨ p 27 = false ∨ p 30 = false
  clause145 : p 26 = false ∨ p 24 = false ∨ p 27 = false ∨ p 61 = false
  clause146 : p 26 = false ∨ p 24 = false ∨ p 27 = false ∨ p 78 = false
  clause147 : p 26 = false ∨ p 24 = false ∨ p 30 = false ∨ p 61 = false
  clause148 : p 26 = false ∨ p 24 = false ∨ p 30 = false ∨ p 78 = false
  clause149 : p 26 = false ∨ p 24 = false ∨ p 61 = false ∨ p 78 = false
  clause150 : p 26 = false ∨ p 27 = false ∨ p 30 = false ∨ p 61 = false
  clause151 : p 26 = false ∨ p 27 = false ∨ p 30 = false ∨ p 78 = false
  clause152 : p 26 = false ∨ p 27 = false ∨ p 61 = false ∨ p 78 = false
  clause153 : p 26 = false ∨ p 30 = false ∨ p 61 = false ∨ p 78 = false
  clause154 : p 27 = false ∨ p 17 = false ∨ p 25 = false ∨ p 79 = false
  clause155 : p 27 = false ∨ p 151 = true ∨ p 25 = true ∨ p 26 = true ∨ p 62 = true ∨ p 79 = true
  clause156 : p 28 = false ∨ p 9 = false ∨ p 24 = false ∨ p 31 = false
  clause157 : p 28 = false ∨ p 9 = false ∨ p 24 = false ∨ p 80 = false
  clause158 : p 28 = false ∨ p 9 = false ∨ p 31 = false ∨ p 80 = false
  clause159 : p 28 = false ∨ p 24 = false ∨ p 31 = false ∨ p 80 = false
  clause160 : p 29 = false ∨ p 10 = false ∨ p 19 = false ∨ p 25 = false
structure Block5 (p : Nat → Bool) : Prop where
  clause161 : p 29 = false ∨ p 10 = false ∨ p 19 = false ∨ p 67 = false
  clause162 : p 29 = false ∨ p 10 = false ∨ p 25 = false ∨ p 67 = false
  clause163 : p 29 = false ∨ p 19 = false ∨ p 25 = false ∨ p 67 = false
  clause164 : p 29 = false ∨ p 153 = true ∨ p 19 = true ∨ p 25 = true ∨ p 67 = true
  clause165 : p 29 = false ∨ p 153 = true ∨ p 10 = true ∨ p 25 = true ∨ p 67 = true
  clause166 : p 29 = false ∨ p 153 = true ∨ p 10 = true ∨ p 19 = true ∨ p 67 = true
  clause167 : p 29 = false ∨ p 153 = true ∨ p 10 = true ∨ p 19 = true ∨ p 25 = true
  clause168 : p 30 = false ∨ p 11 = false ∨ p 26 = false ∨ p 32 = false
  clause169 : p 30 = false ∨ p 11 = false ∨ p 32 = false ∨ p 82 = false
  clause170 : p 30 = false ∨ p 26 = false ∨ p 32 = false ∨ p 82 = false
  clause171 : p 30 = false ∨ p 154 = true ∨ p 26 = true ∨ p 32 = true ∨ p 82 = true
  clause172 : p 30 = false ∨ p 154 = true ∨ p 11 = true ∨ p 32 = true ∨ p 82 = true
  clause173 : p 30 = false ∨ p 154 = true ∨ p 11 = true ∨ p 26 = true ∨ p 82 = true
  clause174 : p 30 = false ∨ p 154 = true ∨ p 11 = true ∨ p 26 = true ∨ p 32 = true
  clause175 : p 31 = false ∨ p 20 = false ∨ p 28 = false ∨ p 32 = false
  clause176 : p 31 = false ∨ p 155 = true ∨ p 28 = true ∨ p 32 = true
  clause177 : p 31 = false ∨ p 155 = true ∨ p 20 = true ∨ p 32 = true
  clause178 : p 31 = false ∨ p 155 = true ∨ p 20 = true ∨ p 28 = true
  clause179 : p 32 = false ∨ p 22 = false ∨ p 30 = false ∨ p 31 = false
  clause180 : p 32 = false ∨ p 156 = true ∨ p 22 = true ∨ p 31 = true
  clause181 : p 32 = false ∨ p 156 = true ∨ p 22 = true ∨ p 30 = true
  clause182 : p 33 = false ∨ p 157 = true ∨ p 35 = true ∨ p 42 = true
  clause183 : p 33 = false ∨ p 157 = true ∨ p 34 = true ∨ p 42 = true
  clause184 : p 34 = false ∨ p 158 = true ∨ p 33 = true ∨ p 36 = true ∨ p 43 = true ∨ p 86 = true
  clause185 : p 34 = false ∨ p 158 = true ∨ p 33 = true ∨ p 36 = true ∨ p 43 = true ∨ p 51 = true
  clause186 : p 35 = false ∨ p 159 = true ∨ p 36 = true
  clause187 : p 35 = false ∨ p 159 = true ∨ p 33 = true
  clause188 : p 36 = false ∨ p 34 = false ∨ p 35 = false ∨ p 38 = false
  clause189 : p 36 = false ∨ p 34 = false ∨ p 37 = false ∨ p 38 = false
  clause190 : p 36 = false ∨ p 35 = false ∨ p 37 = false ∨ p 38 = false
  clause191 : p 36 = false ∨ p 160 = true ∨ p 34 = true ∨ p 37 = true ∨ p 38 = true
  clause192 : p 37 = false ∨ p 36 = false ∨ p 41 = false ∨ p 89 = false
structure Block6 (p : Nat → Bool) : Prop where
  clause193 : p 37 = false ∨ p 161 = true ∨ p 36 = true ∨ p 89 = true
  clause194 : p 37 = false ∨ p 161 = true ∨ p 36 = true ∨ p 41 = true
  clause195 : p 38 = false ∨ p 36 = false ∨ p 41 = false ∨ p 57 = false
  clause196 : p 38 = false ∨ p 162 = true ∨ p 36 = true ∨ p 57 = true
  clause197 : p 39 = false ∨ p 40 = false ∨ p 49 = false ∨ p 58 = false
  clause198 : p 39 = false ∨ p 163 = true ∨ p 49 = true ∨ p 58 = true
  clause199 : p 40 = false ∨ p 164 = true ∨ p 41 = true
  clause200 : p 40 = false ∨ p 164 = true ∨ p 39 = true
  clause201 : p 41 = false ∨ p 37 = false ∨ p 38 = false ∨ p 40 = false
  clause202 : p 41 = false ∨ p 165 = true ∨ p 37 = true ∨ p 38 = true
  clause203 : p 42 = false ∨ p 33 = false ∨ p 43 = false ∨ p 44 = false
  clause204 : p 42 = false ∨ p 33 = false ∨ p 43 = false ∨ p 46 = false
  clause205 : p 42 = false ∨ p 33 = false ∨ p 44 = false ∨ p 46 = false
  clause206 : p 42 = false ∨ p 166 = true ∨ p 43 = true ∨ p 44 = true ∨ p 46 = true
  clause207 : p 42 = false ∨ p 166 = true ∨ p 33 = true ∨ p 44 = true ∨ p 46 = true
  clause208 : p 43 = false ∨ p 8 = false ∨ p 34 = false ∨ p 42 = false
  clause209 : p 43 = false ∨ p 8 = false ∨ p 34 = false ∨ p 47 = false
  clause210 : p 43 = false ∨ p 8 = false ∨ p 34 = false ∨ p 60 = false
  clause211 : p 43 = false ∨ p 8 = false ∨ p 42 = false ∨ p 47 = false
  clause212 : p 43 = false ∨ p 8 = false ∨ p 42 = false ∨ p 60 = false
  clause213 : p 43 = false ∨ p 8 = false ∨ p 47 = false ∨ p 60 = false
  clause214 : p 43 = false ∨ p 34 = false ∨ p 42 = false ∨ p 47 = false
  clause215 : p 43 = false ∨ p 34 = false ∨ p 42 = false ∨ p 60 = false
  clause216 : p 43 = false ∨ p 34 = false ∨ p 47 = false ∨ p 60 = false
  clause217 : p 43 = false ∨ p 42 = false ∨ p 47 = false ∨ p 60 = false
  clause218 : p 44 = false ∨ p 9 = false ∨ p 42 = false ∨ p 45 = false
  clause219 : p 44 = false ∨ p 9 = false ∨ p 42 = false ∨ p 49 = false
  clause220 : p 44 = false ∨ p 9 = false ∨ p 45 = false ∨ p 49 = false
  clause221 : p 44 = false ∨ p 9 = false ∨ p 45 = false ∨ p 96 = false
  clause222 : p 44 = false ∨ p 9 = false ∨ p 49 = false ∨ p 96 = false
  clause223 : p 44 = false ∨ p 42 = false ∨ p 45 = false ∨ p 49 = false
  clause224 : p 44 = false ∨ p 42 = false ∨ p 45 = false ∨ p 96 = false
structure Block7 (p : Nat → Bool) : Prop where
  clause225 : p 44 = false ∨ p 42 = false ∨ p 49 = false ∨ p 96 = false
  clause226 : p 44 = false ∨ p 45 = false ∨ p 49 = false ∨ p 96 = false
  clause227 : p 44 = false ∨ p 168 = true ∨ p 9 = true ∨ p 42 = true ∨ p 49 = true ∨ p 96 = true
  clause228 : p 45 = false ∨ p 44 = false ∨ p 50 = false ∨ p 64 = false
  clause229 : p 45 = false ∨ p 169 = true ∨ p 50 = true ∨ p 64 = true
  clause230 : p 45 = false ∨ p 169 = true ∨ p 44 = true ∨ p 64 = true
  clause231 : p 45 = false ∨ p 169 = true ∨ p 44 = true ∨ p 50 = true
  clause232 : p 46 = false ∨ p 42 = false ∨ p 47 = false ∨ p 48 = false
  clause233 : p 46 = false ∨ p 42 = false ∨ p 47 = false ∨ p 49 = false
  clause234 : p 46 = false ∨ p 42 = false ∨ p 47 = false ∨ p 66 = false
  clause235 : p 46 = false ∨ p 42 = false ∨ p 48 = false ∨ p 49 = false
  clause236 : p 46 = false ∨ p 42 = false ∨ p 48 = false ∨ p 66 = false
  clause237 : p 46 = false ∨ p 42 = false ∨ p 49 = false ∨ p 66 = false
  clause238 : p 46 = false ∨ p 47 = false ∨ p 48 = false ∨ p 49 = false
  clause239 : p 46 = false ∨ p 47 = false ∨ p 48 = false ∨ p 66 = false
  clause240 : p 46 = false ∨ p 47 = false ∨ p 49 = false ∨ p 66 = false
  clause241 : p 46 = false ∨ p 48 = false ∨ p 49 = false ∨ p 66 = false
  clause242 : p 46 = false ∨ p 170 = true ∨ p 42 = true ∨ p 47 = true ∨ p 49 = true ∨ p 66 = true
  clause243 : p 47 = false ∨ p 10 = false ∨ p 43 = false ∨ p 46 = false
  clause244 : p 47 = false ∨ p 10 = false ∨ p 46 = false ∨ p 67 = false
  clause245 : p 47 = false ∨ p 43 = false ∨ p 46 = false ∨ p 67 = false
  clause246 : p 47 = false ∨ p 171 = true ∨ p 43 = true ∨ p 46 = true ∨ p 67 = true
  clause247 : p 47 = false ∨ p 171 = true ∨ p 10 = true ∨ p 46 = true ∨ p 67 = true
  clause248 : p 47 = false ∨ p 171 = true ∨ p 10 = true ∨ p 43 = true ∨ p 67 = true
  clause249 : p 47 = false ∨ p 171 = true ∨ p 10 = true ∨ p 43 = true ∨ p 46 = true
  clause250 : p 48 = false ∨ p 11 = false ∨ p 46 = false ∨ p 50 = false
  clause251 : p 48 = false ∨ p 172 = true ∨ p 46 = true ∨ p 50 = true ∨ p 98 = true
  clause252 : p 48 = false ∨ p 172 = true ∨ p 11 = true ∨ p 46 = true ∨ p 98 = true
  clause253 : p 48 = false ∨ p 172 = true ∨ p 11 = true ∨ p 46 = true ∨ p 50 = true
  clause254 : p 49 = false ∨ p 39 = false ∨ p 44 = false ∨ p 46 = false
  clause255 : p 49 = false ∨ p 39 = false ∨ p 44 = false ∨ p 50 = false
  clause256 : p 49 = false ∨ p 39 = false ∨ p 46 = false ∨ p 50 = false
structure Block8 (p : Nat → Bool) : Prop where
  clause257 : p 49 = false ∨ p 44 = false ∨ p 46 = false ∨ p 50 = false
  clause258 : p 49 = false ∨ p 173 = true ∨ p 44 = true ∨ p 46 = true ∨ p 50 = true
  clause259 : p 49 = false ∨ p 173 = true ∨ p 39 = true ∨ p 46 = true ∨ p 50 = true
  clause260 : p 49 = false ∨ p 173 = true ∨ p 39 = true ∨ p 44 = true ∨ p 50 = true
  clause261 : p 49 = false ∨ p 173 = true ∨ p 39 = true ∨ p 44 = true ∨ p 46 = true
  clause262 : p 50 = false ∨ p 45 = false ∨ p 48 = false ∨ p 49 = false
  clause263 : p 174 = false ∨ p 45 = false ∨ p 48 = false
  clause264 : p 50 = false ∨ p 174 = true ∨ p 48 = true ∨ p 49 = true
  clause265 : p 51 = false ∨ p 15 = false ∨ p 34 = false ∨ p 53 = false
  clause266 : p 51 = false ∨ p 15 = false ∨ p 53 = false ∨ p 60 = false
  clause267 : p 51 = false ∨ p 34 = false ∨ p 53 = false ∨ p 60 = false
  clause268 : p 51 = false ∨ p 34 = false ∨ p 53 = false ∨ p 103 = false
  clause269 : p 51 = false ∨ p 53 = false ∨ p 60 = false ∨ p 103 = false
  clause270 : p 52 = false ∨ p 53 = false ∨ p 54 = false ∨ p 58 = false
  clause271 : p 52 = false ∨ p 176 = true ∨ p 54 = true ∨ p 58 = true
  clause272 : p 52 = false ∨ p 176 = true ∨ p 53 = true ∨ p 58 = true
  clause273 : p 53 = false ∨ p 51 = false ∨ p 52 = false ∨ p 63 = false
  clause274 : p 53 = false ∨ p 177 = true ∨ p 52 = true ∨ p 63 = true
  clause275 : p 53 = false ∨ p 177 = true ∨ p 51 = true ∨ p 63 = true
  clause276 : p 53 = false ∨ p 177 = true ∨ p 51 = true ∨ p 52 = true
  clause277 : p 54 = false ∨ p 52 = false ∨ p 59 = false ∨ p 64 = false
  clause278 : p 54 = false ∨ p 178 = true ∨ p 59 = true ∨ p 64 = true
  clause279 : p 54 = false ∨ p 178 = true ∨ p 52 = true ∨ p 64 = true
  clause280 : p 54 = false ∨ p 178 = true ∨ p 52 = true ∨ p 59 = true
  clause281 : p 55 = false ∨ p 56 = false ∨ p 58 = false ∨ p 66 = false
  clause282 : p 55 = false ∨ p 56 = false ∨ p 58 = false ∨ p 107 = false
  clause283 : p 55 = false ∨ p 56 = false ∨ p 66 = false ∨ p 107 = false
  clause284 : p 55 = false ∨ p 58 = false ∨ p 66 = false ∨ p 107 = false
  clause285 : p 55 = false ∨ p 179 = true ∨ p 58 = true ∨ p 66 = true ∨ p 107 = true
  clause286 : p 55 = false ∨ p 179 = true ∨ p 56 = true ∨ p 58 = true ∨ p 107 = true
  clause287 : p 56 = false ∨ p 55 = false ∨ p 57 = false ∨ p 59 = false
  clause288 : p 56 = false ∨ p 180 = true ∨ p 57 = true ∨ p 59 = true
structure Block9 (p : Nat → Bool) : Prop where
  clause289 : p 56 = false ∨ p 180 = true ∨ p 55 = true ∨ p 59 = true
  clause290 : p 56 = false ∨ p 180 = true ∨ p 55 = true ∨ p 57 = true
  clause291 : p 57 = false ∨ p 38 = false ∨ p 56 = false ∨ p 68 = false
  clause292 : p 57 = false ∨ p 38 = false ∨ p 56 = false ∨ p 109 = false
  clause293 : p 57 = false ∨ p 38 = false ∨ p 68 = false ∨ p 109 = false
  clause294 : p 57 = false ∨ p 56 = false ∨ p 68 = false ∨ p 109 = false
  clause295 : p 58 = false ∨ p 20 = false ∨ p 39 = false ∨ p 55 = false
  clause296 : p 58 = false ∨ p 20 = false ∨ p 39 = false ∨ p 59 = false
  clause297 : p 58 = false ∨ p 20 = false ∨ p 52 = false ∨ p 55 = false
  clause298 : p 58 = false ∨ p 20 = false ∨ p 52 = false ∨ p 59 = false
  clause299 : p 58 = false ∨ p 20 = false ∨ p 55 = false ∨ p 59 = false
  clause300 : p 58 = false ∨ p 20 = false ∨ p 55 = false ∨ p 110 = false
  clause301 : p 58 = false ∨ p 39 = false ∨ p 52 = false ∨ p 55 = false
  clause302 : p 58 = false ∨ p 39 = false ∨ p 52 = false ∨ p 59 = false
  clause303 : p 58 = false ∨ p 39 = false ∨ p 55 = false ∨ p 59 = false
  clause304 : p 58 = false ∨ p 39 = false ∨ p 55 = false ∨ p 110 = false
  clause305 : p 58 = false ∨ p 52 = false ∨ p 55 = false ∨ p 59 = false
  clause306 : p 58 = false ∨ p 52 = false ∨ p 55 = false ∨ p 110 = false
  clause307 : p 58 = false ∨ p 52 = false ∨ p 59 = false ∨ p 110 = false
  clause308 : p 59 = false ∨ p 22 = false ∨ p 54 = false ∨ p 56 = false
  clause309 : p 59 = false ∨ p 22 = false ∨ p 54 = false ∨ p 58 = false
  clause310 : p 59 = false ∨ p 22 = false ∨ p 56 = false ∨ p 58 = false
  clause311 : p 59 = false ∨ p 54 = false ∨ p 56 = false ∨ p 58 = false
  clause312 : p 59 = false ∨ p 183 = true ∨ p 22 = true ∨ p 56 = true ∨ p 58 = true
  clause313 : p 59 = false ∨ p 183 = true ∨ p 22 = true ∨ p 54 = true ∨ p 58 = true
  clause314 : p 60 = false ∨ p 25 = false ∨ p 43 = false ∨ p 51 = false
  clause315 : p 60 = false ∨ p 25 = false ∨ p 43 = false ∨ p 62 = false
  clause316 : p 60 = false ∨ p 25 = false ∨ p 43 = false ∨ p 63 = false
  clause317 : p 60 = false ∨ p 25 = false ∨ p 43 = false ∨ p 67 = false
  clause318 : p 60 = false ∨ p 25 = false ∨ p 51 = false ∨ p 62 = false
  clause319 : p 60 = false ∨ p 25 = false ∨ p 51 = false ∨ p 63 = false
  clause320 : p 60 = false ∨ p 25 = false ∨ p 51 = false ∨ p 67 = false
structure Block10 (p : Nat → Bool) : Prop where
  clause321 : p 60 = false ∨ p 25 = false ∨ p 62 = false ∨ p 63 = false
  clause322 : p 60 = false ∨ p 25 = false ∨ p 63 = false ∨ p 67 = false
  clause323 : p 60 = false ∨ p 43 = false ∨ p 51 = false ∨ p 62 = false
  clause324 : p 60 = false ∨ p 43 = false ∨ p 51 = false ∨ p 63 = false
  clause325 : p 60 = false ∨ p 43 = false ∨ p 51 = false ∨ p 67 = false
  clause326 : p 60 = false ∨ p 43 = false ∨ p 62 = false ∨ p 63 = false
  clause327 : p 60 = false ∨ p 43 = false ∨ p 62 = false ∨ p 67 = false
  clause328 : p 60 = false ∨ p 43 = false ∨ p 63 = false ∨ p 67 = false
  clause329 : p 60 = false ∨ p 43 = false ∨ p 67 = false ∨ p 114 = false
  clause330 : p 60 = false ∨ p 51 = false ∨ p 62 = false ∨ p 67 = false
  clause331 : p 60 = false ∨ p 62 = false ∨ p 63 = false ∨ p 67 = false
  clause332 : p 60 = false ∨ p 184 = true ∨ p 43 = true ∨ p 51 = true ∨ p 62 = true ∨ p 63 = true ∨ p 67 = true ∨ p 114 = true
  clause333 : p 60 = false ∨ p 184 = true ∨ p 25 = true ∨ p 43 = true ∨ p 51 = true ∨ p 62 = true ∨ p 67 = true ∨ p 114 = true
  clause334 : p 61 = false ∨ p 26 = false ∨ p 62 = false ∨ p 64 = false
  clause335 : p 61 = false ∨ p 26 = false ∨ p 64 = false ∨ p 115 = false
  clause336 : p 61 = false ∨ p 62 = false ∨ p 64 = false ∨ p 115 = false
  clause337 : p 61 = false ∨ p 185 = true ∨ p 62 = true ∨ p 64 = true ∨ p 115 = true
  clause338 : p 61 = false ∨ p 185 = true ∨ p 26 = true ∨ p 64 = true ∨ p 115 = true
  clause339 : p 61 = false ∨ p 185 = true ∨ p 26 = true ∨ p 62 = true ∨ p 115 = true
  clause340 : p 61 = false ∨ p 185 = true ∨ p 26 = true ∨ p 62 = true ∨ p 64 = true
  clause341 : p 62 = false ∨ p 27 = false ∨ p 60 = false ∨ p 61 = false
  clause342 : p 62 = false ∨ p 27 = false ∨ p 60 = false ∨ p 65 = false
  clause343 : p 62 = false ∨ p 27 = false ∨ p 60 = false ∨ p 116 = false
  clause344 : p 62 = false ∨ p 27 = false ∨ p 61 = false ∨ p 65 = false
  clause345 : p 62 = false ∨ p 27 = false ∨ p 61 = false ∨ p 68 = false
  clause346 : p 62 = false ∨ p 27 = false ∨ p 61 = false ∨ p 116 = false
  clause347 : p 62 = false ∨ p 27 = false ∨ p 65 = false ∨ p 68 = false
  clause348 : p 62 = false ∨ p 27 = false ∨ p 68 = false ∨ p 116 = false
  clause349 : p 62 = false ∨ p 60 = false ∨ p 61 = false ∨ p 65 = false
  clause350 : p 62 = false ∨ p 60 = false ∨ p 61 = false ∨ p 68 = false
  clause351 : p 62 = false ∨ p 60 = false ∨ p 61 = false ∨ p 116 = false
  clause352 : p 62 = false ∨ p 60 = false ∨ p 65 = false ∨ p 68 = false
structure Block11 (p : Nat → Bool) : Prop where
  clause353 : p 62 = false ∨ p 60 = false ∨ p 65 = false ∨ p 116 = false
  clause354 : p 62 = false ∨ p 60 = false ∨ p 68 = false ∨ p 116 = false
  clause355 : p 62 = false ∨ p 61 = false ∨ p 65 = false ∨ p 68 = false
  clause356 : p 62 = false ∨ p 61 = false ∨ p 65 = false ∨ p 116 = false
  clause357 : p 62 = false ∨ p 61 = false ∨ p 68 = false ∨ p 116 = false
  clause358 : p 62 = false ∨ p 65 = false ∨ p 68 = false ∨ p 116 = false
  clause359 : p 62 = false ∨ p 186 = true ∨ p 27 = true ∨ p 60 = true ∨ p 65 = true ∨ p 68 = true ∨ p 116 = true
  clause360 : p 62 = false ∨ p 186 = true ∨ p 27 = true ∨ p 60 = true ∨ p 61 = true ∨ p 68 = true ∨ p 116 = true
  clause361 : p 62 = false ∨ p 186 = true ∨ p 27 = true ∨ p 60 = true ∨ p 61 = true ∨ p 65 = true ∨ p 116 = true
  clause362 : p 63 = false ∨ p 53 = false ∨ p 60 = false ∨ p 65 = false
  clause363 : p 63 = false ∨ p 53 = false ∨ p 60 = false ∨ p 69 = false
  clause364 : p 63 = false ∨ p 53 = false ∨ p 65 = false ∨ p 69 = false
  clause365 : p 63 = false ∨ p 60 = false ∨ p 65 = false ∨ p 69 = false
  clause366 : p 64 = false ∨ p 45 = false ∨ p 54 = false ∨ p 61 = false
  clause367 : p 64 = false ∨ p 45 = false ∨ p 54 = false ∨ p 65 = false
  clause368 : p 64 = false ∨ p 45 = false ∨ p 54 = false ∨ p 118 = false
  clause369 : p 64 = false ∨ p 45 = false ∨ p 61 = false ∨ p 65 = false
  clause370 : p 64 = false ∨ p 45 = false ∨ p 61 = false ∨ p 118 = false
  clause371 : p 64 = false ∨ p 45 = false ∨ p 65 = false ∨ p 118 = false
  clause372 : p 64 = false ∨ p 54 = false ∨ p 61 = false ∨ p 65 = false
  clause373 : p 64 = false ∨ p 54 = false ∨ p 61 = false ∨ p 118 = false
  clause374 : p 64 = false ∨ p 54 = false ∨ p 65 = false ∨ p 118 = false
  clause375 : p 64 = false ∨ p 61 = false ∨ p 65 = false ∨ p 118 = false
  clause376 : p 64 = false ∨ p 188 = true ∨ p 45 = true ∨ p 54 = true ∨ p 61 = true ∨ p 65 = true
  clause377 : p 65 = false ∨ p 62 = false ∨ p 63 = false ∨ p 64 = false
  clause378 : p 65 = false ∨ p 63 = false ∨ p 64 = false ∨ p 70 = false
  clause379 : p 65 = false ∨ p 189 = true ∨ p 63 = true ∨ p 64 = true ∨ p 70 = true
  clause380 : p 65 = false ∨ p 189 = true ∨ p 62 = true ∨ p 64 = true ∨ p 70 = true
  clause381 : p 65 = false ∨ p 189 = true ∨ p 62 = true ∨ p 63 = true ∨ p 70 = true
  clause382 : p 65 = false ∨ p 189 = true ∨ p 62 = true ∨ p 63 = true ∨ p 64 = true
  clause383 : p 66 = false ∨ p 46 = false ∨ p 55 = false ∨ p 119 = false
  clause384 : p 66 = false ∨ p 190 = true ∨ p 55 = true ∨ p 67 = true ∨ p 119 = true
structure Block12 (p : Nat → Bool) : Prop where
  clause385 : p 66 = false ∨ p 190 = true ∨ p 46 = true ∨ p 67 = true ∨ p 119 = true
  clause386 : p 66 = false ∨ p 190 = true ∨ p 46 = true ∨ p 55 = true ∨ p 119 = true
  clause387 : p 66 = false ∨ p 190 = true ∨ p 46 = true ∨ p 55 = true ∨ p 67 = true
  clause388 : p 67 = false ∨ p 29 = false ∨ p 47 = false ∨ p 60 = false
  clause389 : p 67 = false ∨ p 29 = false ∨ p 47 = false ∨ p 66 = false
  clause390 : p 67 = false ∨ p 29 = false ∨ p 47 = false ∨ p 68 = false
  clause391 : p 67 = false ∨ p 29 = false ∨ p 47 = false ∨ p 69 = false
  clause392 : p 67 = false ∨ p 29 = false ∨ p 60 = false ∨ p 66 = false
  clause393 : p 67 = false ∨ p 29 = false ∨ p 60 = false ∨ p 68 = false
  clause394 : p 67 = false ∨ p 29 = false ∨ p 60 = false ∨ p 69 = false
  clause395 : p 67 = false ∨ p 29 = false ∨ p 66 = false ∨ p 68 = false
  clause396 : p 67 = false ∨ p 29 = false ∨ p 66 = false ∨ p 69 = false
  clause397 : p 67 = false ∨ p 29 = false ∨ p 68 = false ∨ p 69 = false
  clause398 : p 67 = false ∨ p 47 = false ∨ p 60 = false ∨ p 66 = false
  clause399 : p 67 = false ∨ p 47 = false ∨ p 60 = false ∨ p 68 = false
  clause400 : p 67 = false ∨ p 47 = false ∨ p 60 = false ∨ p 69 = false
  clause401 : p 67 = false ∨ p 47 = false ∨ p 66 = false ∨ p 68 = false
  clause402 : p 67 = false ∨ p 47 = false ∨ p 66 = false ∨ p 69 = false
  clause403 : p 67 = false ∨ p 47 = false ∨ p 68 = false ∨ p 69 = false
  clause404 : p 67 = false ∨ p 60 = false ∨ p 66 = false ∨ p 68 = false
  clause405 : p 67 = false ∨ p 60 = false ∨ p 66 = false ∨ p 69 = false
  clause406 : p 67 = false ∨ p 60 = false ∨ p 68 = false ∨ p 69 = false
  clause407 : p 67 = false ∨ p 66 = false ∨ p 68 = false ∨ p 69 = false
  clause408 : p 68 = false ∨ p 57 = false ∨ p 62 = false ∨ p 67 = false
  clause409 : p 68 = false ∨ p 57 = false ∨ p 62 = false ∨ p 70 = false
  clause410 : p 68 = false ∨ p 57 = false ∨ p 67 = false ∨ p 70 = false
  clause411 : p 68 = false ∨ p 57 = false ∨ p 70 = false ∨ p 120 = false
  clause412 : p 68 = false ∨ p 62 = false ∨ p 70 = false ∨ p 120 = false
  clause413 : p 68 = false ∨ p 192 = true ∨ p 62 = true ∨ p 67 = true ∨ p 70 = true ∨ p 120 = true
  clause414 : p 68 = false ∨ p 192 = true ∨ p 57 = true ∨ p 67 = true ∨ p 70 = true ∨ p 120 = true
  clause415 : p 68 = false ∨ p 192 = true ∨ p 57 = true ∨ p 62 = true ∨ p 67 = true ∨ p 120 = true
  clause416 : p 68 = false ∨ p 192 = true ∨ p 57 = true ∨ p 62 = true ∨ p 67 = true ∨ p 70 = true
structure Block13 (p : Nat → Bool) : Prop where
  clause417 : p 69 = false ∨ p 63 = false ∨ p 67 = false ∨ p 70 = false
  clause418 : p 69 = false ∨ p 63 = false ∨ p 67 = false ∨ p 122 = false
  clause419 : p 69 = false ∨ p 193 = true ∨ p 67 = true ∨ p 70 = true ∨ p 122 = true
  clause420 : p 69 = false ∨ p 193 = true ∨ p 63 = true ∨ p 70 = true ∨ p 122 = true
  clause421 : p 69 = false ∨ p 193 = true ∨ p 63 = true ∨ p 67 = true ∨ p 122 = true
  clause422 : p 69 = false ∨ p 193 = true ∨ p 63 = true ∨ p 67 = true ∨ p 70 = true
  clause423 : p 70 = false ∨ p 65 = true ∨ p 68 = true ∨ p 69 = true ∨ p 124 = true
  clause424 : p 70 = false ∨ p 65 = false ∨ p 68 = false ∨ p 69 = false
  clause425 : p 70 = false ∨ p 65 = false ∨ p 68 = false ∨ p 124 = false
  clause426 : p 70 = false ∨ p 65 = false ∨ p 69 = false ∨ p 124 = false
  clause427 : p 70 = false ∨ p 68 = false ∨ p 69 = false ∨ p 124 = false
  clause428 : p 70 = false ∨ p 194 = true ∨ p 65 = true ∨ p 69 = true ∨ p 124 = true
  clause429 : p 70 = false ∨ p 194 = true ∨ p 65 = true ∨ p 68 = true ∨ p 124 = true
  clause430 : p 71 = false ∨ p 15 = false ∨ p 75 = false ∨ p 103 = false
  clause431 : p 71 = false ∨ p 195 = true ∨ p 15 = true ∨ p 103 = true
  clause432 : p 72 = false ∨ p 196 = true ∨ p 80 = true
  clause433 : p 73 = false ∨ p 197 = true ∨ p 77 = true
  clause434 : p 73 = false ∨ p 197 = true ∨ p 72 = true
  clause435 : p 74 = false ∨ p 75 = false ∨ p 76 = false ∨ p 107 = false
  clause436 : p 74 = false ∨ p 198 = true ∨ p 75 = true ∨ p 107 = true
  clause437 : p 75 = false ∨ p 19 = false ∨ p 74 = false ∨ p 108 = false
  clause438 : p 75 = false ∨ p 199 = true ∨ p 71 = true ∨ p 74 = true ∨ p 108 = true
  clause439 : p 75 = false ∨ p 199 = true ∨ p 19 = true ∨ p 74 = true ∨ p 108 = true
  clause440 : p 75 = false ∨ p 199 = true ∨ p 19 = true ∨ p 71 = true ∨ p 108 = true
  clause441 : p 76 = false ∨ p 74 = false ∨ p 77 = false ∨ p 82 = false
  clause442 : p 76 = false ∨ p 200 = true ∨ p 77 = true ∨ p 82 = true
  clause443 : p 76 = false ∨ p 200 = true ∨ p 74 = true ∨ p 82 = true
  clause444 : p 76 = false ∨ p 200 = true ∨ p 74 = true ∨ p 77 = true
  clause445 : p 77 = false ∨ p 22 = false ∨ p 73 = false ∨ p 76 = false
  clause446 : p 77 = false ∨ p 201 = true ∨ p 22 = true ∨ p 76 = true
  clause447 : p 77 = false ∨ p 201 = true ∨ p 22 = true ∨ p 73 = true
  clause448 : p 78 = false ∨ p 26 = false ∨ p 79 = false ∨ p 115 = false
structure Block14 (p : Nat → Bool) : Prop where
  clause449 : p 78 = false ∨ p 202 = true ∨ p 79 = true ∨ p 82 = true ∨ p 115 = true
  clause450 : p 78 = false ∨ p 202 = true ∨ p 26 = true ∨ p 82 = true ∨ p 115 = true
  clause451 : p 78 = false ∨ p 202 = true ∨ p 26 = true ∨ p 79 = true ∨ p 115 = true
  clause452 : p 78 = false ∨ p 202 = true ∨ p 26 = true ∨ p 79 = true ∨ p 82 = true
  clause453 : p 79 = false ∨ p 27 = false ∨ p 78 = false ∨ p 83 = false
  clause454 : p 79 = false ∨ p 27 = false ∨ p 78 = false ∨ p 116 = false
  clause455 : p 79 = false ∨ p 78 = false ∨ p 83 = false ∨ p 116 = false
  clause456 : p 79 = false ∨ p 203 = true ∨ p 27 = true ∨ p 83 = true ∨ p 116 = true
  clause457 : p 79 = false ∨ p 203 = true ∨ p 27 = true ∨ p 78 = true ∨ p 116 = true
  clause458 : p 80 = false ∨ p 28 = false ∨ p 72 = false ∨ p 81 = false
  clause459 : p 80 = false ∨ p 72 = false ∨ p 81 = false ∨ p 117 = false
  clause460 : p 81 = false ∨ p 205 = true ∨ p 80 = true
  clause461 : p 82 = false ∨ p 30 = false ∨ p 76 = false ∨ p 78 = false
  clause462 : p 82 = false ∨ p 30 = false ∨ p 76 = false ∨ p 83 = false
  clause463 : p 82 = false ∨ p 30 = false ∨ p 78 = false ∨ p 83 = false
  clause464 : p 82 = false ∨ p 76 = false ∨ p 78 = false ∨ p 83 = false
  clause465 : p 83 = false ∨ p 79 = false ∨ p 82 = false ∨ p 85 = false
  clause466 : p 83 = false ∨ p 79 = false ∨ p 85 = false ∨ p 120 = false
  clause467 : p 83 = false ∨ p 82 = false ∨ p 85 = false ∨ p 120 = false
  clause468 : p 83 = false ∨ p 207 = true ∨ p 82 = true ∨ p 85 = true ∨ p 120 = true
  clause469 : p 83 = false ∨ p 207 = true ∨ p 79 = true ∨ p 85 = true ∨ p 120 = true
  clause470 : p 83 = false ∨ p 207 = true ∨ p 79 = true ∨ p 82 = true ∨ p 120 = true
  clause471 : p 83 = false ∨ p 207 = true ∨ p 79 = true ∨ p 82 = true ∨ p 85 = true
  clause472 : p 84 = false ∨ p 81 = false ∨ p 85 = false ∨ p 122 = false
  clause473 : p 84 = false ∨ p 208 = true ∨ p 85 = true ∨ p 122 = true
  clause474 : p 84 = false ∨ p 208 = true ∨ p 81 = true ∨ p 122 = true
  clause475 : p 84 = false ∨ p 208 = true ∨ p 81 = true ∨ p 85 = true
  clause476 : p 85 = false ∨ p 83 = true ∨ p 84 = true ∨ p 124 = true
  clause477 : p 85 = false ∨ p 83 = false ∨ p 84 = false ∨ p 124 = false
  clause478 : p 85 = false ∨ p 209 = true ∨ p 83 = true ∨ p 124 = true
  clause479 : p 86 = false ∨ p 34 = false ∨ p 91 = false ∨ p 103 = false
  clause480 : p 210 = false ∨ p 34 = false ∨ p 91 = false
structure Block15 (p : Nat → Bool) : Prop where
  clause481 : p 210 = false ∨ p 91 = false ∨ p 103 = false
  clause482 : p 86 = false ∨ p 210 = true ∨ p 34 = true ∨ p 103 = true
  clause483 : p 87 = false ∨ p 211 = true ∨ p 96 = true
  clause484 : p 87 = false ∨ p 211 = true ∨ p 88 = true
  clause485 : p 88 = false ∨ p 87 = false ∨ p 89 = false ∨ p 93 = false
  clause486 : p 88 = false ∨ p 212 = true ∨ p 89 = true ∨ p 93 = true
  clause487 : p 88 = false ∨ p 212 = true ∨ p 87 = true ∨ p 89 = true
  clause488 : p 89 = false ∨ p 37 = false ∨ p 88 = false ∨ p 106 = false
  clause489 : p 90 = false ∨ p 91 = false ∨ p 92 = false ∨ p 107 = false
  clause490 : p 90 = false ∨ p 214 = true ∨ p 91 = true ∨ p 107 = true
  clause491 : p 91 = false ∨ p 215 = true ∨ p 90 = true ∨ p 108 = true
  clause492 : p 91 = false ∨ p 215 = true ∨ p 86 = true ∨ p 108 = true
  clause493 : p 92 = false ∨ p 90 = false ∨ p 93 = false ∨ p 98 = false
  clause494 : p 92 = false ∨ p 216 = true ∨ p 93 = true ∨ p 98 = true
  clause495 : p 92 = false ∨ p 216 = true ∨ p 90 = true ∨ p 98 = true
  clause496 : p 92 = false ∨ p 216 = true ∨ p 90 = true ∨ p 93 = true
  clause497 : p 93 = false ∨ p 217 = true ∨ p 88 = true
  clause498 : p 94 = false ∨ p 218 = true ∨ p 98 = true ∨ p 115 = true
  clause499 : p 94 = false ∨ p 218 = true ∨ p 95 = true ∨ p 115 = true
  clause500 : p 94 = false ∨ p 218 = true ∨ p 95 = true ∨ p 98 = true
  clause501 : p 95 = false ∨ p 94 = false ∨ p 99 = false ∨ p 116 = false
  clause502 : p 95 = false ∨ p 219 = true ∨ p 99 = true ∨ p 116 = true
  clause503 : p 95 = false ∨ p 219 = true ∨ p 94 = true ∨ p 116 = true
  clause504 : p 96 = false ∨ p 44 = false ∨ p 97 = false ∨ p 117 = false
  clause505 : p 96 = false ∨ p 220 = true ∨ p 87 = true ∨ p 97 = true ∨ p 117 = true
  clause506 : p 96 = false ∨ p 220 = true ∨ p 44 = true ∨ p 87 = true ∨ p 117 = true
  clause507 : p 96 = false ∨ p 220 = true ∨ p 44 = true ∨ p 87 = true ∨ p 97 = true
  clause508 : p 97 = false ∨ p 221 = true ∨ p 100 = true
  clause509 : p 97 = false ∨ p 221 = true ∨ p 96 = true
  clause510 : p 98 = false ∨ p 48 = false ∨ p 92 = false ∨ p 94 = false
  clause511 : p 98 = false ∨ p 48 = false ∨ p 92 = false ∨ p 99 = false
  clause512 : p 98 = false ∨ p 48 = false ∨ p 94 = false ∨ p 99 = false
structure Block16 (p : Nat → Bool) : Prop where
  clause513 : p 98 = false ∨ p 92 = false ∨ p 94 = false ∨ p 99 = false
  clause514 : p 99 = false ∨ p 95 = false ∨ p 98 = false ∨ p 101 = false
  clause515 : p 99 = false ∨ p 95 = false ∨ p 101 = false ∨ p 120 = false
  clause516 : p 99 = false ∨ p 223 = true ∨ p 98 = true ∨ p 101 = true ∨ p 120 = true
  clause517 : p 99 = false ∨ p 223 = true ∨ p 95 = true ∨ p 98 = true ∨ p 120 = true
  clause518 : p 100 = false ∨ p 97 = false ∨ p 101 = false ∨ p 122 = false
  clause519 : p 100 = false ∨ p 224 = true ∨ p 101 = true ∨ p 122 = true
  clause520 : p 100 = false ∨ p 224 = true ∨ p 97 = true ∨ p 122 = true
  clause521 : p 101 = false ∨ p 99 = false ∨ p 100 = false ∨ p 124 = false
  clause522 : p 101 = false ∨ p 225 = true ∨ p 99 = true ∨ p 124 = true
  clause523 : p 102 = false ∨ p 103 = false ∨ p 104 = false ∨ p 107 = false
  clause524 : p 102 = false ∨ p 103 = false ∨ p 104 = false ∨ p 113 = false
  clause525 : p 102 = false ∨ p 103 = false ∨ p 107 = false ∨ p 113 = false
  clause526 : p 102 = false ∨ p 104 = false ∨ p 107 = false ∨ p 113 = false
  clause527 : p 102 = false ∨ p 226 = true ∨ p 103 = true ∨ p 107 = true ∨ p 113 = true
  clause528 : p 103 = false ∨ p 51 = false ∨ p 71 = false ∨ p 86 = false
  clause529 : p 103 = false ∨ p 51 = false ∨ p 86 = false ∨ p 102 = false
  clause530 : p 103 = false ∨ p 51 = false ∨ p 102 = false ∨ p 108 = false
  clause531 : p 103 = false ∨ p 71 = false ∨ p 86 = false ∨ p 102 = false
  clause532 : p 103 = false ∨ p 71 = false ∨ p 86 = false ∨ p 105 = false
  clause533 : p 103 = false ∨ p 71 = false ∨ p 86 = false ∨ p 114 = false
  clause534 : p 103 = false ∨ p 86 = false ∨ p 102 = false ∨ p 114 = false
  clause535 : p 103 = false ∨ p 102 = false ∨ p 105 = false ∨ p 108 = false
  clause536 : p 103 = false ∨ p 105 = false ∨ p 108 = false ∨ p 114 = false
  clause537 : p 104 = false ∨ p 228 = true ∨ p 105 = true ∨ p 115 = true
  clause538 : p 104 = false ∨ p 228 = true ∨ p 102 = true ∨ p 115 = true
  clause539 : p 104 = false ∨ p 228 = true ∨ p 102 = true ∨ p 105 = true
  clause540 : p 105 = false ∨ p 103 = false ∨ p 104 = false ∨ p 106 = false
  clause541 : p 105 = false ∨ p 103 = false ∨ p 104 = false ∨ p 109 = false
  clause542 : p 105 = false ∨ p 103 = false ∨ p 104 = false ∨ p 116 = false
  clause543 : p 105 = false ∨ p 103 = false ∨ p 106 = false ∨ p 109 = false
  clause544 : p 105 = false ∨ p 103 = false ∨ p 106 = false ∨ p 116 = false
structure Block17 (p : Nat → Bool) : Prop where
  clause545 : p 105 = false ∨ p 103 = false ∨ p 109 = false ∨ p 116 = false
  clause546 : p 105 = false ∨ p 104 = false ∨ p 106 = false ∨ p 109 = false
  clause547 : p 105 = false ∨ p 104 = false ∨ p 106 = false ∨ p 116 = false
  clause548 : p 105 = false ∨ p 104 = false ∨ p 109 = false ∨ p 116 = false
  clause549 : p 105 = false ∨ p 106 = false ∨ p 109 = false ∨ p 116 = false
  clause550 : p 105 = false ∨ p 229 = true ∨ p 103 = true ∨ p 104 = true ∨ p 109 = true ∨ p 116 = true
  clause551 : p 106 = false ∨ p 89 = false ∨ p 105 = false ∨ p 112 = false
  clause552 : p 106 = false ∨ p 230 = true ∨ p 105 = true ∨ p 112 = true
  clause553 : p 106 = false ∨ p 230 = true ∨ p 89 = true ∨ p 112 = true
  clause554 : p 106 = false ∨ p 230 = true ∨ p 89 = true ∨ p 105 = true
  clause555 : p 107 = false ∨ p 55 = false ∨ p 74 = false ∨ p 90 = false
  clause556 : p 107 = false ∨ p 55 = false ∨ p 90 = false ∨ p 102 = false
  clause557 : p 107 = false ∨ p 55 = false ∨ p 90 = false ∨ p 110 = false
  clause558 : p 107 = false ∨ p 55 = false ∨ p 90 = false ∨ p 119 = false
  clause559 : p 107 = false ∨ p 55 = false ∨ p 102 = false ∨ p 108 = false
  clause560 : p 107 = false ∨ p 55 = false ∨ p 102 = false ∨ p 110 = false
  clause561 : p 107 = false ∨ p 55 = false ∨ p 108 = false ∨ p 110 = false
  clause562 : p 107 = false ∨ p 74 = false ∨ p 90 = false ∨ p 119 = false
  clause563 : p 107 = false ∨ p 74 = false ∨ p 102 = false ∨ p 110 = false
  clause564 : p 107 = false ∨ p 74 = false ∨ p 108 = false ∨ p 119 = false
  clause565 : p 107 = false ∨ p 90 = false ∨ p 102 = false ∨ p 110 = false
  clause566 : p 107 = false ∨ p 90 = false ∨ p 108 = false ∨ p 119 = false
  clause567 : p 107 = false ∨ p 90 = false ∨ p 110 = false ∨ p 119 = false
  clause568 : p 107 = false ∨ p 102 = false ∨ p 108 = false ∨ p 110 = false
  clause569 : p 107 = false ∨ p 102 = false ∨ p 108 = false ∨ p 119 = false
  clause570 : p 107 = false ∨ p 108 = false ∨ p 110 = false ∨ p 119 = false
  clause571 : p 108 = false ∨ p 75 = false ∨ p 91 = false ∨ p 103 = false
  clause572 : p 108 = false ∨ p 75 = false ∨ p 91 = false ∨ p 107 = false
  clause573 : p 108 = false ∨ p 75 = false ∨ p 91 = false ∨ p 109 = false
  clause574 : p 108 = false ∨ p 75 = false ∨ p 91 = false ∨ p 111 = false
  clause575 : p 108 = false ∨ p 75 = false ∨ p 103 = false ∨ p 107 = false
  clause576 : p 108 = false ∨ p 75 = false ∨ p 103 = false ∨ p 109 = false
structure Block18 (p : Nat → Bool) : Prop where
  clause577 : p 108 = false ∨ p 75 = false ∨ p 103 = false ∨ p 111 = false
  clause578 : p 108 = false ∨ p 75 = false ∨ p 107 = false ∨ p 109 = false
  clause579 : p 108 = false ∨ p 75 = false ∨ p 107 = false ∨ p 111 = false
  clause580 : p 108 = false ∨ p 75 = false ∨ p 109 = false ∨ p 111 = false
  clause581 : p 108 = false ∨ p 91 = false ∨ p 103 = false ∨ p 107 = false
  clause582 : p 108 = false ∨ p 91 = false ∨ p 103 = false ∨ p 109 = false
  clause583 : p 108 = false ∨ p 91 = false ∨ p 103 = false ∨ p 111 = false
  clause584 : p 108 = false ∨ p 91 = false ∨ p 107 = false ∨ p 109 = false
  clause585 : p 108 = false ∨ p 91 = false ∨ p 107 = false ∨ p 111 = false
  clause586 : p 108 = false ∨ p 91 = false ∨ p 109 = false ∨ p 111 = false
  clause587 : p 108 = false ∨ p 103 = false ∨ p 107 = false ∨ p 109 = false
  clause588 : p 108 = false ∨ p 103 = false ∨ p 107 = false ∨ p 111 = false
  clause589 : p 108 = false ∨ p 103 = false ∨ p 109 = false ∨ p 111 = false
  clause590 : p 108 = false ∨ p 107 = false ∨ p 109 = false ∨ p 111 = false
  clause591 : p 109 = false ∨ p 57 = false ∨ p 105 = false ∨ p 112 = false
  clause592 : p 109 = false ∨ p 57 = false ∨ p 108 = false ∨ p 112 = false
  clause593 : p 109 = false ∨ p 105 = false ∨ p 112 = false ∨ p 120 = false
  clause594 : p 109 = false ∨ p 108 = false ∨ p 112 = false ∨ p 120 = false
  clause595 : p 109 = false ∨ p 233 = true ∨ p 105 = true ∨ p 108 = true ∨ p 112 = true ∨ p 120 = true
  clause596 : p 109 = false ∨ p 233 = true ∨ p 57 = true ∨ p 105 = true ∨ p 108 = true ∨ p 120 = true
  clause597 : p 110 = false ∨ p 58 = true ∨ p 107 = true ∨ p 111 = true ∨ p 121 = true
  clause598 : p 110 = false ∨ p 58 = false ∨ p 107 = false ∨ p 111 = false
  clause599 : p 110 = false ∨ p 58 = false ∨ p 107 = false ∨ p 121 = false
  clause600 : p 110 = false ∨ p 58 = false ∨ p 111 = false ∨ p 121 = false
  clause601 : p 110 = false ∨ p 107 = false ∨ p 111 = false ∨ p 121 = false
  clause602 : p 110 = false ∨ p 234 = true ∨ p 58 = true ∨ p 107 = true ∨ p 121 = true
  clause603 : p 110 = false ∨ p 234 = true ∨ p 58 = true ∨ p 107 = true ∨ p 111 = true
  clause604 : p 111 = false ∨ p 108 = false ∨ p 112 = false ∨ p 122 = false
  clause605 : p 111 = false ∨ p 235 = true ∨ p 110 = true ∨ p 112 = true ∨ p 122 = true
  clause606 : p 111 = false ∨ p 235 = true ∨ p 108 = true ∨ p 112 = true ∨ p 122 = true
  clause607 : p 111 = false ∨ p 235 = true ∨ p 108 = true ∨ p 110 = true ∨ p 122 = true
  clause608 : p 111 = false ∨ p 235 = true ∨ p 108 = true ∨ p 110 = true ∨ p 112 = true
structure Block19 (p : Nat → Bool) : Prop where
  clause609 : p 112 = false ∨ p 106 = false ∨ p 109 = false ∨ p 111 = false
  clause610 : p 112 = false ∨ p 106 = false ∨ p 109 = false ∨ p 124 = false
  clause611 : p 112 = false ∨ p 106 = false ∨ p 111 = false ∨ p 124 = false
  clause612 : p 112 = false ∨ p 109 = false ∨ p 111 = false ∨ p 124 = false
  clause613 : p 236 = false ∨ p 106 = false ∨ p 109 = false
  clause614 : p 236 = false ∨ p 106 = false ∨ p 111 = false
  clause615 : p 112 = false ∨ p 236 = true ∨ p 109 = true ∨ p 111 = true ∨ p 124 = true
  clause616 : p 113 = false ∨ p 237 = true ∨ p 114 = true ∨ p 115 = true ∨ p 117 = true ∨ p 119 = true
  clause617 : p 113 = false ∨ p 237 = true ∨ p 102 = true ∨ p 115 = true ∨ p 117 = true ∨ p 119 = true
  clause618 : p 113 = false ∨ p 237 = true ∨ p 102 = true ∨ p 114 = true ∨ p 117 = true ∨ p 119 = true
  clause619 : p 113 = false ∨ p 237 = true ∨ p 102 = true ∨ p 114 = true ∨ p 115 = true ∨ p 119 = true
  clause620 : p 113 = false ∨ p 237 = true ∨ p 102 = true ∨ p 114 = true ∨ p 115 = true ∨ p 117 = true
  clause621 : p 114 = false ∨ p 60 = false ∨ p 103 = false ∨ p 113 = false
  clause622 : p 114 = false ∨ p 60 = false ∨ p 103 = false ∨ p 116 = false
  clause623 : p 114 = false ∨ p 60 = false ∨ p 113 = false ∨ p 116 = false
  clause624 : p 114 = false ∨ p 103 = false ∨ p 113 = false ∨ p 116 = false
  clause625 : p 114 = false ∨ p 238 = true ∨ p 60 = true ∨ p 103 = true ∨ p 116 = true
  clause626 : p 115 = false ∨ p 61 = false ∨ p 78 = false ∨ p 94 = false
  clause627 : p 115 = false ∨ p 61 = false ∨ p 78 = false ∨ p 104 = false
  clause628 : p 115 = false ∨ p 61 = false ∨ p 78 = false ∨ p 113 = false
  clause629 : p 115 = false ∨ p 61 = false ∨ p 78 = false ∨ p 116 = false
  clause630 : p 115 = false ∨ p 61 = false ∨ p 78 = false ∨ p 118 = false
  clause631 : p 115 = false ∨ p 61 = false ∨ p 94 = false ∨ p 104 = false
  clause632 : p 115 = false ∨ p 61 = false ∨ p 94 = false ∨ p 113 = false
  clause633 : p 115 = false ∨ p 61 = false ∨ p 94 = false ∨ p 116 = false
  clause634 : p 115 = false ∨ p 61 = false ∨ p 94 = false ∨ p 118 = false
  clause635 : p 115 = false ∨ p 61 = false ∨ p 104 = false ∨ p 113 = false
  clause636 : p 115 = false ∨ p 61 = false ∨ p 104 = false ∨ p 116 = false
  clause637 : p 115 = false ∨ p 61 = false ∨ p 104 = false ∨ p 118 = false
  clause638 : p 115 = false ∨ p 61 = false ∨ p 113 = false ∨ p 116 = false
  clause639 : p 115 = false ∨ p 61 = false ∨ p 113 = false ∨ p 118 = false
  clause640 : p 115 = false ∨ p 61 = false ∨ p 116 = false ∨ p 118 = false
structure Block20 (p : Nat → Bool) : Prop where
  clause641 : p 115 = false ∨ p 78 = false ∨ p 94 = false ∨ p 104 = false
  clause642 : p 115 = false ∨ p 78 = false ∨ p 94 = false ∨ p 113 = false
  clause643 : p 115 = false ∨ p 78 = false ∨ p 94 = false ∨ p 116 = false
  clause644 : p 115 = false ∨ p 78 = false ∨ p 94 = false ∨ p 118 = false
  clause645 : p 115 = false ∨ p 78 = false ∨ p 104 = false ∨ p 113 = false
  clause646 : p 115 = false ∨ p 78 = false ∨ p 104 = false ∨ p 116 = false
  clause647 : p 115 = false ∨ p 78 = false ∨ p 104 = false ∨ p 118 = false
  clause648 : p 115 = false ∨ p 78 = false ∨ p 113 = false ∨ p 116 = false
  clause649 : p 115 = false ∨ p 78 = false ∨ p 113 = false ∨ p 118 = false
  clause650 : p 115 = false ∨ p 78 = false ∨ p 116 = false ∨ p 118 = false
  clause651 : p 115 = false ∨ p 94 = false ∨ p 104 = false ∨ p 113 = false
  clause652 : p 115 = false ∨ p 94 = false ∨ p 104 = false ∨ p 116 = false
  clause653 : p 115 = false ∨ p 94 = false ∨ p 104 = false ∨ p 118 = false
  clause654 : p 115 = false ∨ p 94 = false ∨ p 113 = false ∨ p 116 = false
  clause655 : p 115 = false ∨ p 94 = false ∨ p 113 = false ∨ p 118 = false
  clause656 : p 115 = false ∨ p 94 = false ∨ p 116 = false ∨ p 118 = false
  clause657 : p 115 = false ∨ p 104 = false ∨ p 113 = false ∨ p 116 = false
  clause658 : p 115 = false ∨ p 104 = false ∨ p 113 = false ∨ p 118 = false
  clause659 : p 115 = false ∨ p 104 = false ∨ p 116 = false ∨ p 118 = false
  clause660 : p 115 = false ∨ p 113 = false ∨ p 116 = false ∨ p 118 = false
  clause661 : p 115 = false ∨ p 239 = true ∨ p 61 = true ∨ p 94 = true ∨ p 104 = true ∨ p 113 = true ∨ p 116 = true ∨ p 118 = true
  clause662 : p 116 = false ∨ p 62 = false ∨ p 79 = false ∨ p 105 = false
  clause663 : p 116 = false ∨ p 62 = false ∨ p 95 = false ∨ p 105 = false
  clause664 : p 116 = false ∨ p 79 = false ∨ p 95 = false ∨ p 105 = false
  clause665 : p 116 = false ∨ p 79 = false ∨ p 95 = false ∨ p 115 = false
  clause666 : p 116 = false ∨ p 79 = false ∨ p 115 = false ∨ p 120 = false
  clause667 : p 116 = false ∨ p 95 = false ∨ p 105 = false ∨ p 114 = false
  clause668 : p 116 = false ∨ p 95 = false ∨ p 105 = false ∨ p 120 = false
  clause669 : p 116 = false ∨ p 240 = true ∨ p 62 = true ∨ p 95 = true ∨ p 105 = true ∨ p 114 = true ∨ p 115 = true ∨ p 120 = true
  clause670 : p 116 = false ∨ p 240 = true ∨ p 62 = true ∨ p 79 = true ∨ p 105 = true ∨ p 114 = true ∨ p 115 = true ∨ p 120 = true
  clause671 : p 116 = false ∨ p 240 = true ∨ p 62 = true ∨ p 79 = true ∨ p 95 = true ∨ p 105 = true ∨ p 114 = true ∨ p 120 = true
  clause672 : p 117 = false ∨ p 80 = false ∨ p 96 = false ∨ p 113 = false
structure Block21 (p : Nat → Bool) : Prop where
  clause673 : p 117 = false ∨ p 80 = false ∨ p 96 = false ∨ p 118 = false
  clause674 : p 117 = false ∨ p 80 = false ∨ p 96 = false ∨ p 121 = false
  clause675 : p 117 = false ∨ p 80 = false ∨ p 113 = false ∨ p 118 = false
  clause676 : p 117 = false ∨ p 80 = false ∨ p 113 = false ∨ p 121 = false
  clause677 : p 117 = false ∨ p 80 = false ∨ p 118 = false ∨ p 121 = false
  clause678 : p 117 = false ∨ p 96 = false ∨ p 113 = false ∨ p 118 = false
  clause679 : p 117 = false ∨ p 96 = false ∨ p 113 = false ∨ p 121 = false
  clause680 : p 117 = false ∨ p 96 = false ∨ p 118 = false ∨ p 121 = false
  clause681 : p 117 = false ∨ p 113 = false ∨ p 118 = false ∨ p 121 = false
  clause682 : p 118 = false ∨ p 64 = false ∨ p 115 = false ∨ p 117 = false
  clause683 : p 118 = false ∨ p 64 = false ∨ p 115 = false ∨ p 123 = false
  clause684 : p 118 = false ∨ p 242 = true ∨ p 115 = true ∨ p 117 = true ∨ p 123 = true
  clause685 : p 118 = false ∨ p 242 = true ∨ p 64 = true ∨ p 117 = true ∨ p 123 = true
  clause686 : p 118 = false ∨ p 242 = true ∨ p 64 = true ∨ p 115 = true ∨ p 123 = true
  clause687 : p 118 = false ∨ p 242 = true ∨ p 64 = true ∨ p 115 = true ∨ p 117 = true
  clause688 : p 119 = false ∨ p 66 = false ∨ p 107 = false ∨ p 113 = false
  clause689 : p 119 = false ∨ p 66 = false ∨ p 107 = false ∨ p 121 = false
  clause690 : p 119 = false ∨ p 66 = false ∨ p 113 = false ∨ p 121 = false
  clause691 : p 119 = false ∨ p 107 = false ∨ p 113 = false ∨ p 121 = false
  clause692 : p 243 = false ∨ p 66 = false ∨ p 113 = false
  clause693 : p 243 = false ∨ p 66 = false ∨ p 121 = false
  clause694 : p 119 = false ∨ p 243 = true ∨ p 107 = true ∨ p 113 = true ∨ p 121 = true
  clause695 : p 119 = false ∨ p 243 = true ∨ p 66 = true ∨ p 107 = true ∨ p 121 = true
  clause696 : p 119 = false ∨ p 243 = true ∨ p 66 = true ∨ p 107 = true ∨ p 113 = true
  clause697 : p 120 = false ∨ p 68 = false ∨ p 83 = false ∨ p 99 = false
  clause698 : p 120 = false ∨ p 68 = false ∨ p 83 = false ∨ p 109 = false
  clause699 : p 120 = false ∨ p 68 = false ∨ p 83 = false ∨ p 116 = false
  clause700 : p 120 = false ∨ p 68 = false ∨ p 83 = false ∨ p 124 = false
  clause701 : p 120 = false ∨ p 68 = false ∨ p 99 = false ∨ p 109 = false
  clause702 : p 120 = false ∨ p 68 = false ∨ p 99 = false ∨ p 116 = false
  clause703 : p 120 = false ∨ p 68 = false ∨ p 99 = false ∨ p 124 = false
  clause704 : p 120 = false ∨ p 68 = false ∨ p 109 = false ∨ p 116 = false
structure Block22 (p : Nat → Bool) : Prop where
  clause705 : p 120 = false ∨ p 68 = false ∨ p 109 = false ∨ p 124 = false
  clause706 : p 120 = false ∨ p 68 = false ∨ p 116 = false ∨ p 124 = false
  clause707 : p 120 = false ∨ p 83 = false ∨ p 99 = false ∨ p 109 = false
  clause708 : p 120 = false ∨ p 83 = false ∨ p 99 = false ∨ p 116 = false
  clause709 : p 120 = false ∨ p 83 = false ∨ p 99 = false ∨ p 124 = false
  clause710 : p 120 = false ∨ p 83 = false ∨ p 109 = false ∨ p 116 = false
  clause711 : p 120 = false ∨ p 83 = false ∨ p 109 = false ∨ p 124 = false
  clause712 : p 120 = false ∨ p 83 = false ∨ p 116 = false ∨ p 124 = false
  clause713 : p 120 = false ∨ p 99 = false ∨ p 109 = false ∨ p 116 = false
  clause714 : p 120 = false ∨ p 99 = false ∨ p 109 = false ∨ p 124 = false
  clause715 : p 120 = false ∨ p 109 = false ∨ p 116 = false ∨ p 124 = false
  clause716 : p 121 = false ∨ p 110 = false ∨ p 117 = false ∨ p 119 = false
  clause717 : p 121 = false ∨ p 110 = false ∨ p 119 = false ∨ p 123 = false
  clause718 : p 121 = false ∨ p 110 = false ∨ p 122 = false ∨ p 123 = false
  clause719 : p 121 = false ∨ p 117 = false ∨ p 119 = false ∨ p 122 = false
  clause720 : p 121 = false ∨ p 119 = false ∨ p 122 = false ∨ p 123 = false
  clause721 : p 121 = false ∨ p 245 = true ∨ p 117 = true ∨ p 119 = true ∨ p 122 = true ∨ p 123 = true
  clause722 : p 121 = false ∨ p 245 = true ∨ p 110 = true ∨ p 119 = true ∨ p 122 = true ∨ p 123 = true
  clause723 : p 121 = false ∨ p 245 = true ∨ p 110 = true ∨ p 117 = true ∨ p 122 = true ∨ p 123 = true
  clause724 : p 121 = false ∨ p 245 = true ∨ p 110 = true ∨ p 117 = true ∨ p 119 = true ∨ p 123 = true
  clause725 : p 121 = false ∨ p 245 = true ∨ p 110 = true ∨ p 117 = true ∨ p 119 = true ∨ p 122 = true
  clause726 : p 122 = false ∨ p 69 = false ∨ p 84 = false ∨ p 100 = false
  clause727 : p 122 = false ∨ p 69 = false ∨ p 84 = false ∨ p 111 = false
  clause728 : p 122 = false ∨ p 69 = false ∨ p 84 = false ∨ p 121 = false
  clause729 : p 122 = false ∨ p 69 = false ∨ p 84 = false ∨ p 124 = false
  clause730 : p 122 = false ∨ p 69 = false ∨ p 100 = false ∨ p 111 = false
  clause731 : p 122 = false ∨ p 69 = false ∨ p 100 = false ∨ p 121 = false
  clause732 : p 122 = false ∨ p 69 = false ∨ p 100 = false ∨ p 124 = false
  clause733 : p 122 = false ∨ p 69 = false ∨ p 111 = false ∨ p 121 = false
  clause734 : p 122 = false ∨ p 69 = false ∨ p 111 = false ∨ p 124 = false
  clause735 : p 122 = false ∨ p 69 = false ∨ p 121 = false ∨ p 124 = false
  clause736 : p 122 = false ∨ p 84 = false ∨ p 100 = false ∨ p 111 = false
structure Block23 (p : Nat → Bool) : Prop where
  clause737 : p 122 = false ∨ p 84 = false ∨ p 100 = false ∨ p 121 = false
  clause738 : p 122 = false ∨ p 84 = false ∨ p 100 = false ∨ p 124 = false
  clause739 : p 122 = false ∨ p 84 = false ∨ p 111 = false ∨ p 121 = false
  clause740 : p 122 = false ∨ p 84 = false ∨ p 111 = false ∨ p 124 = false
  clause741 : p 122 = false ∨ p 84 = false ∨ p 121 = false ∨ p 124 = false
  clause742 : p 122 = false ∨ p 100 = false ∨ p 111 = false ∨ p 121 = false
  clause743 : p 122 = false ∨ p 100 = false ∨ p 111 = false ∨ p 124 = false
  clause744 : p 122 = false ∨ p 100 = false ∨ p 121 = false ∨ p 124 = false
  clause745 : p 122 = false ∨ p 111 = false ∨ p 121 = false ∨ p 124 = false
  clause746 : p 123 = false ∨ p 118 = false ∨ p 121 = false ∨ p 124 = false
  clause747 : p 123 = false ∨ p 247 = true ∨ p 121 = true ∨ p 124 = true
  clause748 : p 123 = false ∨ p 247 = true ∨ p 118 = true ∨ p 124 = true
  clause749 : p 124 = false ∨ p 70 = false ∨ p 101 = false ∨ p 112 = false
  clause750 : p 124 = false ∨ p 70 = false ∨ p 101 = false ∨ p 123 = false
  clause751 : p 124 = false ∨ p 70 = false ∨ p 112 = false ∨ p 120 = false
  clause752 : p 124 = false ∨ p 70 = false ∨ p 112 = false ∨ p 122 = false
  clause753 : p 124 = false ∨ p 70 = false ∨ p 112 = false ∨ p 123 = false
  clause754 : p 124 = false ∨ p 70 = false ∨ p 120 = false ∨ p 123 = false
  clause755 : p 124 = false ∨ p 70 = false ∨ p 122 = false ∨ p 123 = false
  clause756 : p 124 = false ∨ p 85 = false ∨ p 101 = false ∨ p 112 = false
  clause757 : p 124 = false ∨ p 85 = false ∨ p 101 = false ∨ p 123 = false
  clause758 : p 124 = false ∨ p 85 = false ∨ p 112 = false ∨ p 122 = false
  clause759 : p 124 = false ∨ p 85 = false ∨ p 112 = false ∨ p 123 = false
  clause760 : p 124 = false ∨ p 85 = false ∨ p 122 = false ∨ p 123 = false
  clause761 : p 124 = false ∨ p 101 = false ∨ p 112 = false ∨ p 120 = false
  clause762 : p 124 = false ∨ p 101 = false ∨ p 112 = false ∨ p 122 = false
  clause763 : p 124 = false ∨ p 101 = false ∨ p 112 = false ∨ p 123 = false
  clause764 : p 124 = false ∨ p 101 = false ∨ p 120 = false ∨ p 123 = false
  clause765 : p 124 = false ∨ p 112 = false ∨ p 120 = false ∨ p 122 = false
  clause766 : p 124 = false ∨ p 112 = false ∨ p 120 = false ∨ p 123 = false
  clause767 : p 124 = false ∨ p 112 = false ∨ p 122 = false ∨ p 123 = false
  clause768 : p 124 = false ∨ p 120 = false ∨ p 122 = false ∨ p 123 = false
structure Block24 (p : Nat → Bool) : Prop where
  clause769 : p 127 = false
  clause770 : p 129 = false
  clause771 : p 130 = false
  clause772 : p 132 = false
  clause773 : p 133 = false
  clause774 : p 136 = false
  clause775 : p 137 = false
  clause776 : p 140 = false
  clause777 : p 142 = false
  clause778 : p 145 = false
  clause779 : p 148 = false
  clause780 : p 151 = false
  clause781 : p 153 = false
  clause782 : p 154 = false
  clause783 : p 155 = false
  clause784 : p 158 = false
  clause785 : p 159 = false
  clause786 : p 161 = false
  clause787 : p 162 = false
  clause788 : p 164 = false
  clause789 : p 166 = false
  clause790 : p 169 = false
  clause791 : p 171 = false
  clause792 : p 172 = false
  clause793 : p 173 = false
  clause794 : p 177 = false
  clause795 : p 178 = false
  clause796 : p 180 = false
  clause797 : p 184 = false
  clause798 : p 185 = false
  clause799 : p 189 = false
  clause800 : p 190 = false
structure Block25 (p : Nat → Bool) : Prop where
  clause801 : p 192 = false
  clause802 : p 193 = false
  clause803 : p 197 = false
  clause804 : p 199 = false
  clause805 : p 200 = false
  clause806 : p 202 = false
  clause807 : p 207 = false
  clause808 : p 208 = false
  clause809 : p 212 = false
  clause810 : p 215 = false
  clause811 : p 216 = false
  clause812 : p 218 = false
  clause813 : p 220 = false
  clause814 : p 223 = false
  clause815 : p 224 = false
  clause816 : p 228 = false
  clause817 : p 230 = false
  clause818 : p 233 = false
  clause819 : p 235 = false
  clause820 : p 237 = false
  clause821 : p 240 = false
  clause822 : p 242 = false
  clause823 : p 245 = false
  clause824 : p 128 = false ∨ p 249 = true
  clause825 : p 249 = false ∨ p 251 = true
  clause826 : p 125 = false ∨ p 251 = true
  clause827 : p 125 = false ∨ p 249 = false ∨ p 252 = true
  clause828 : p 131 = false ∨ p 255 = true
  clause829 : p 255 = false ∨ p 257 = true
  clause830 : p 257 = false ∨ p 259 = true
  clause831 : p 251 = false ∨ p 259 = true
  clause832 : p 252 = false ∨ p 260 = true
structure Block26 (p : Nat → Bool) : Prop where
  clause833 : p 134 = false ∨ p 261 = true
  clause834 : p 135 = false ∨ p 263 = true
  clause835 : p 263 = false ∨ p 265 = true
  clause836 : p 261 = false ∨ p 265 = true
  clause837 : p 138 = false ∨ p 267 = true
  clause838 : p 267 = false ∨ p 271 = true
  clause839 : p 271 = false ∨ p 273 = true
  clause840 : p 265 = false ∨ p 273 = true
  clause841 : p 273 = false ∨ p 275 = true
  clause842 : p 259 = false ∨ p 275 = true
  clause843 : p 259 = false ∨ p 273 = false ∨ p 276 = true
  clause844 : p 260 = false ∨ p 276 = true
  clause845 : p 141 = false ∨ p 279 = true
  clause846 : p 144 = false ∨ p 281 = true
  clause847 : p 147 = false ∨ p 283 = true
  clause848 : p 283 = false ∨ p 285 = true
  clause849 : p 281 = false ∨ p 285 = true
  clause850 : p 281 = false ∨ p 283 = false ∨ p 286 = true
  clause851 : p 285 = false ∨ p 287 = true
  clause852 : p 286 = false ∨ p 288 = true
  clause853 : p 279 = false ∨ p 287 = true
  clause854 : p 279 = false ∨ p 285 = false ∨ p 288 = true
  clause855 : p 149 = false ∨ p 289 = true
  clause856 : p 289 = false ∨ p 293 = true
  clause857 : p 293 = false ∨ p 301 = true
  clause858 : p 301 = false ∨ p 303 = true
  clause859 : p 287 = false ∨ p 303 = true
  clause860 : p 288 = false ∨ p 304 = true
  clause861 : p 303 = false ∨ p 305 = true
  clause862 : p 304 = false ∨ p 306 = true
  clause863 : p 275 = false ∨ p 305 = true
  clause864 : p 275 = false ∨ p 303 = false ∨ p 306 = true
structure Block27 (p : Nat → Bool) : Prop where
  clause865 : p 276 = false ∨ p 306 = true
  clause866 : p 157 = false ∨ p 307 = true
  clause867 : p 307 = false ∨ p 309 = true
  clause868 : p 156 = false ∨ p 309 = true
  clause869 : p 156 = false ∨ p 307 = false ∨ p 310 = true
  clause870 : p 160 = false ∨ p 311 = true
  clause871 : p 311 = false ∨ p 315 = true
  clause872 : p 315 = false ∨ p 317 = true
  clause873 : p 309 = false ∨ p 317 = true
  clause874 : p 310 = false ∨ p 318 = true
  clause875 : p 163 = false ∨ p 319 = true
  clause876 : p 165 = false ∨ p 321 = true
  clause877 : p 321 = false ∨ p 323 = true
  clause878 : p 319 = false ∨ p 323 = true
  clause879 : p 168 = false ∨ p 325 = true
  clause880 : p 170 = false ∨ p 327 = true
  clause881 : p 327 = false ∨ p 329 = true
  clause882 : p 325 = false ∨ p 329 = true
  clause883 : p 329 = false ∨ p 331 = true
  clause884 : p 323 = false ∨ p 331 = true
  clause885 : p 331 = false ∨ p 333 = true
  clause886 : p 317 = false ∨ p 333 = true
  clause887 : p 317 = false ∨ p 331 = false ∨ p 334 = true
  clause888 : p 318 = false ∨ p 334 = true
  clause889 : p 174 = false ∨ p 337 = true
  clause890 : p 337 = false ∨ p 339 = true
  clause891 : p 176 = false ∨ p 341 = true
  clause892 : p 341 = false ∨ p 345 = true
  clause893 : p 345 = false ∨ p 347 = true
  clause894 : p 339 = false ∨ p 347 = true
  clause895 : p 339 = false ∨ p 345 = false ∨ p 348 = true
  clause896 : p 179 = false ∨ p 349 = true
structure Block28 (p : Nat → Bool) : Prop where
  clause897 : p 349 = false ∨ p 353 = true
  clause898 : p 183 = false ∨ p 355 = true
  clause899 : p 186 = false ∨ p 357 = true
  clause900 : p 357 = false ∨ p 359 = true
  clause901 : p 355 = false ∨ p 359 = true
  clause902 : p 359 = false ∨ p 361 = true
  clause903 : p 353 = false ∨ p 361 = true
  clause904 : p 353 = false ∨ p 359 = false ∨ p 362 = true
  clause905 : p 361 = false ∨ p 363 = true
  clause906 : p 362 = false ∨ p 364 = true
  clause907 : p 347 = false ∨ p 363 = true
  clause908 : p 347 = false ∨ p 361 = false ∨ p 364 = true
  clause909 : p 348 = false ∨ p 364 = true
  clause910 : p 363 = false ∨ p 365 = true
  clause911 : p 364 = false ∨ p 366 = true
  clause912 : p 333 = false ∨ p 365 = true
  clause913 : p 333 = false ∨ p 363 = false ∨ p 366 = true
  clause914 : p 334 = false ∨ p 366 = true
  clause915 : p 365 = false ∨ p 367 = true
  clause916 : p 366 = false ∨ p 368 = true
  clause917 : p 305 = false ∨ p 367 = true
  clause918 : p 305 = false ∨ p 365 = false ∨ p 368 = true
  clause919 : p 306 = false ∨ p 368 = true
  clause920 : p 188 = false ∨ p 369 = true
  clause921 : p 369 = false ∨ p 371 = true
  clause922 : p 371 = false ∨ p 379 = true
  clause923 : p 195 = false ∨ p 381 = true
  clause924 : p 194 = false ∨ p 381 = true
  clause925 : p 196 = false ∨ p 383 = true
  clause926 : p 383 = false ∨ p 385 = true
  clause927 : p 381 = false ∨ p 385 = true
  clause928 : p 198 = false ∨ p 387 = true
structure Block29 (p : Nat → Bool) : Prop where
  clause929 : p 201 = false ∨ p 389 = true
  clause930 : p 389 = false ∨ p 391 = true
  clause931 : p 387 = false ∨ p 391 = true
  clause932 : p 391 = false ∨ p 393 = true
  clause933 : p 385 = false ∨ p 393 = true
  clause934 : p 393 = false ∨ p 395 = true
  clause935 : p 379 = false ∨ p 395 = true
  clause936 : p 203 = false ∨ p 397 = true
  clause937 : p 205 = false ∨ p 399 = true
  clause938 : p 399 = false ∨ p 401 = true
  clause939 : p 397 = false ∨ p 401 = true
  clause940 : p 209 = false ∨ p 405 = true
  clause941 : p 405 = false ∨ p 407 = true
  clause942 : p 407 = false ∨ p 409 = true
  clause943 : p 401 = false ∨ p 409 = true
  clause944 : p 211 = false ∨ p 411 = true
  clause945 : p 210 = false ∨ p 411 = true
  clause946 : p 411 = false ∨ p 415 = true
  clause947 : p 214 = false ∨ p 417 = true
  clause948 : p 217 = false ∨ p 419 = true
  clause949 : p 419 = false ∨ p 421 = true
  clause950 : p 417 = false ∨ p 421 = true
  clause951 : p 421 = false ∨ p 423 = true
  clause952 : p 415 = false ∨ p 423 = true
  clause953 : p 415 = false ∨ p 421 = false ∨ p 424 = true
  clause954 : p 423 = false ∨ p 425 = true
  clause955 : p 424 = false ∨ p 426 = true
  clause956 : p 409 = false ∨ p 425 = true
  clause957 : p 425 = false ∨ p 427 = true
  clause958 : p 426 = false ∨ p 428 = true
  clause959 : p 395 = false ∨ p 427 = true
  clause960 : p 395 = false ∨ p 425 = false ∨ p 428 = true
structure Block30 (p : Nat → Bool) : Prop where
  clause961 : p 219 = false ∨ p 429 = true
  clause962 : p 429 = false ∨ p 431 = true
  clause963 : p 221 = false ∨ p 433 = true
  clause964 : p 433 = false ∨ p 437 = true
  clause965 : p 437 = false ∨ p 439 = true
  clause966 : p 431 = false ∨ p 439 = true
  clause967 : p 226 = false ∨ p 441 = true
  clause968 : p 225 = false ∨ p 441 = true
  clause969 : p 225 = false ∨ p 226 = false ∨ p 442 = true
  clause970 : p 441 = false ∨ p 445 = true
  clause971 : p 442 = false ∨ p 446 = true
  clause972 : p 229 = false ∨ p 447 = true
  clause973 : p 447 = false ∨ p 451 = true
  clause974 : p 451 = false ∨ p 453 = true
  clause975 : p 445 = false ∨ p 453 = true
  clause976 : p 446 = false ∨ p 454 = true
  clause977 : p 453 = false ∨ p 455 = true
  clause978 : p 454 = false ∨ p 456 = true
  clause979 : p 439 = false ∨ p 455 = true
  clause980 : p 439 = false ∨ p 453 = false ∨ p 456 = true
  clause981 : p 234 = false ∨ p 457 = true
  clause982 : p 236 = false ∨ p 459 = true
  clause983 : p 459 = false ∨ p 461 = true
  clause984 : p 457 = false ∨ p 461 = true
  clause985 : p 238 = false ∨ p 463 = true
  clause986 : p 239 = false ∨ p 465 = true
  clause987 : p 465 = false ∨ p 467 = true
  clause988 : p 463 = false ∨ p 467 = true
  clause989 : p 467 = false ∨ p 469 = true
  clause990 : p 461 = false ∨ p 469 = true
  clause991 : p 243 = false ∨ p 473 = true
  clause992 : p 473 = false ∨ p 475 = true
structure Block31 (p : Nat → Bool) : Prop where
  clause993 : p 247 = false ∨ p 479 = true
  clause994 : p 479 = false ∨ p 481 = true
  clause995 : p 481 = false ∨ p 483 = true
  clause996 : p 475 = false ∨ p 483 = true
  clause997 : p 475 = false ∨ p 481 = false ∨ p 484 = true
  clause998 : p 483 = false ∨ p 485 = true
  clause999 : p 484 = false ∨ p 486 = true
  clause1000 : p 469 = false ∨ p 485 = true
  clause1001 : p 469 = false ∨ p 483 = false ∨ p 486 = true
  clause1002 : p 485 = false ∨ p 487 = true
  clause1003 : p 486 = false ∨ p 488 = true
  clause1004 : p 455 = false ∨ p 487 = true
  clause1005 : p 455 = false ∨ p 485 = false ∨ p 488 = true
  clause1006 : p 456 = false ∨ p 488 = true
  clause1007 : p 487 = false ∨ p 489 = true
  clause1008 : p 488 = false ∨ p 490 = true
  clause1009 : p 427 = false ∨ p 489 = true
  clause1010 : p 427 = false ∨ p 487 = false ∨ p 490 = true
  clause1011 : p 428 = false ∨ p 490 = true
  clause1012 : p 490 = false ∨ p 492 = true
  clause1013 : p 367 = false ∨ p 489 = false ∨ p 492 = true
  clause1014 : p 368 = false ∨ p 492 = true
  clause1015 : p 492 = false
  clause1016 : p 5 = true ∨ p 1497 = true
  clause1017 : p 3 = true ∨ p 1497 = true
  clause1018 : p 3 = true ∨ p 5 = true ∨ p 1498 = true
  clause1019 : p 1497 = false ∨ p 1499 = true
  clause1020 : p 1498 = false ∨ p 1500 = true
  clause1021 : p 8 = true ∨ p 1502 = true
  clause1022 : p 6 = true ∨ p 1502 = true
  clause1023 : p 6 = true ∨ p 8 = true ∨ p 1503 = true
  clause1024 : p 12 = true ∨ p 1504 = true
structure Block32 (p : Nat → Bool) : Prop where
  clause1025 : p 9 = true ∨ p 1504 = true
  clause1026 : p 9 = true ∨ p 12 = true ∨ p 1505 = true
  clause1027 : p 1504 = false ∨ p 1506 = true
  clause1028 : p 1505 = false ∨ p 1507 = true
  clause1029 : p 1502 = false ∨ p 1506 = true
  clause1030 : p 1502 = false ∨ p 1504 = false ∨ p 1507 = true
  clause1031 : p 1502 = false ∨ p 1505 = false ∨ p 1508 = true
  clause1032 : p 1503 = false ∨ p 1507 = true
  clause1033 : p 1503 = false ∨ p 1504 = false ∨ p 1508 = true
  clause1034 : p 1503 = false ∨ p 1505 = false ∨ p 1509 = true
  clause1035 : p 1507 = false ∨ p 1511 = true
  clause1036 : p 1508 = false ∨ p 1512 = true
  clause1037 : p 1509 = false ∨ p 1513 = true
  clause1038 : p 1499 = false ∨ p 1506 = false ∨ p 1511 = true
  clause1039 : p 1499 = false ∨ p 1507 = false ∨ p 1512 = true
  clause1040 : p 1499 = false ∨ p 1508 = false ∨ p 1513 = true
  clause1041 : p 1499 = false ∨ p 1509 = false ∨ p 1514 = true
  clause1042 : p 1500 = false ∨ p 1511 = true
  clause1043 : p 1500 = false ∨ p 1506 = false ∨ p 1512 = true
  clause1044 : p 1500 = false ∨ p 1507 = false ∨ p 1513 = true
  clause1045 : p 1500 = false ∨ p 1508 = false ∨ p 1514 = true
  clause1046 : p 1500 = false ∨ p 1509 = false ∨ p 1515 = true
  clause1047 : p 13 = true ∨ p 1517 = true
  clause1048 : p 13 = true ∨ p 15 = true ∨ p 1518 = true
  clause1049 : p 18 = true ∨ p 1519 = true
  clause1050 : p 16 = true ∨ p 1519 = true
  clause1051 : p 16 = true ∨ p 18 = true ∨ p 1520 = true
  clause1052 : p 1517 = false ∨ p 1521 = true
  clause1053 : p 1517 = false ∨ p 1519 = false ∨ p 1522 = true
  clause1054 : p 1517 = false ∨ p 1520 = false ∨ p 1523 = true
  clause1055 : p 1518 = false ∨ p 1522 = true
  clause1056 : p 1518 = false ∨ p 1519 = false ∨ p 1523 = true
structure Block33 (p : Nat → Bool) : Prop where
  clause1057 : p 1518 = false ∨ p 1520 = false ∨ p 1524 = true
  clause1058 : p 22 = true ∨ p 1525 = true
  clause1059 : p 21 = true ∨ p 1525 = true
  clause1060 : p 21 = true ∨ p 22 = true ∨ p 1526 = true
  clause1061 : p 27 = true ∨ p 1527 = true
  clause1062 : p 24 = true ∨ p 1527 = true
  clause1063 : p 24 = true ∨ p 27 = true ∨ p 1528 = true
  clause1064 : p 1527 = false ∨ p 1529 = true
  clause1065 : p 1528 = false ∨ p 1530 = true
  clause1066 : p 1525 = false ∨ p 1529 = true
  clause1067 : p 1525 = false ∨ p 1527 = false ∨ p 1530 = true
  clause1068 : p 1525 = false ∨ p 1528 = false ∨ p 1531 = true
  clause1069 : p 1526 = false ∨ p 1530 = true
  clause1070 : p 1526 = false ∨ p 1527 = false ∨ p 1531 = true
  clause1071 : p 1526 = false ∨ p 1528 = false ∨ p 1532 = true
  clause1072 : p 1521 = false ∨ p 1530 = false ∨ p 1535 = true
  clause1073 : p 1521 = false ∨ p 1531 = false ∨ p 1536 = true
  clause1074 : p 1522 = false ∨ p 1534 = true
  clause1075 : p 1522 = false ∨ p 1529 = false ∨ p 1535 = true
  clause1076 : p 1522 = false ∨ p 1530 = false ∨ p 1536 = true
  clause1077 : p 1522 = false ∨ p 1531 = false ∨ p 1537 = true
  clause1078 : p 1522 = false ∨ p 1532 = false ∨ p 1538 = true
  clause1079 : p 1523 = false ∨ p 1535 = true
  clause1080 : p 1523 = false ∨ p 1529 = false ∨ p 1536 = true
  clause1081 : p 1523 = false ∨ p 1530 = false ∨ p 1537 = true
  clause1082 : p 1523 = false ∨ p 1531 = false ∨ p 1538 = true
  clause1083 : p 1523 = false ∨ p 1532 = false ∨ p 1539 = true
  clause1084 : p 1524 = false ∨ p 1536 = true
  clause1085 : p 1524 = false ∨ p 1529 = false ∨ p 1537 = true
  clause1086 : p 1524 = false ∨ p 1530 = false ∨ p 1538 = true
  clause1087 : p 1524 = false ∨ p 1531 = false ∨ p 1539 = true
  clause1088 : p 1524 = false ∨ p 1532 = false ∨ p 1540 = true
structure Block34 (p : Nat → Bool) : Prop where
  clause1089 : p 1511 = false ∨ p 1535 = false ∨ p 1545 = true
  clause1090 : p 1511 = false ∨ p 1536 = false ∨ p 1546 = true
  clause1091 : p 1511 = false ∨ p 1537 = false ∨ p 1547 = true
  clause1092 : p 1511 = false ∨ p 1538 = false ∨ p 1548 = true
  clause1093 : p 1511 = false ∨ p 1539 = false ∨ p 1549 = true
  clause1094 : p 1511 = false ∨ p 1540 = false ∨ p 1550 = true
  clause1095 : p 1512 = false ∨ p 1535 = false ∨ p 1546 = true
  clause1096 : p 1512 = false ∨ p 1536 = false ∨ p 1547 = true
  clause1097 : p 1512 = false ∨ p 1537 = false ∨ p 1548 = true
  clause1098 : p 1512 = false ∨ p 1538 = false ∨ p 1549 = true
  clause1099 : p 1512 = false ∨ p 1540 = false ∨ p 1551 = true
  clause1100 : p 1513 = false ∨ p 1535 = false ∨ p 1547 = true
  clause1101 : p 1513 = false ∨ p 1536 = false ∨ p 1548 = true
  clause1102 : p 1513 = false ∨ p 1537 = false ∨ p 1549 = true
  clause1103 : p 1513 = false ∨ p 1538 = false ∨ p 1550 = true
  clause1104 : p 1514 = false ∨ p 1534 = false ∨ p 1547 = true
  clause1105 : p 1514 = false ∨ p 1535 = false ∨ p 1548 = true
  clause1106 : p 1514 = false ∨ p 1536 = false ∨ p 1549 = true
  clause1107 : p 1515 = false ∨ p 1535 = false ∨ p 1549 = true
  clause1108 : p 1515 = false ∨ p 1536 = false ∨ p 1550 = true
  clause1109 : p 30 = true ∨ p 1556 = true
  clause1110 : p 29 = true ∨ p 1556 = true
  clause1111 : p 29 = true ∨ p 30 = true ∨ p 1557 = true
  clause1112 : p 34 = true ∨ p 1558 = true
  clause1113 : p 31 = true ∨ p 1558 = true
  clause1114 : p 31 = true ∨ p 34 = true ∨ p 1559 = true
  clause1115 : p 1558 = false ∨ p 1560 = true
  clause1116 : p 1559 = false ∨ p 1561 = true
  clause1117 : p 1556 = false ∨ p 1560 = true
  clause1118 : p 1556 = false ∨ p 1558 = false ∨ p 1561 = true
  clause1119 : p 1556 = false ∨ p 1559 = false ∨ p 1562 = true
  clause1120 : p 1557 = false ∨ p 1561 = true
structure Block35 (p : Nat → Bool) : Prop where
  clause1121 : p 1557 = false ∨ p 1558 = false ∨ p 1562 = true
  clause1122 : p 1557 = false ∨ p 1559 = false ∨ p 1563 = true
  clause1123 : p 37 = true ∨ p 1564 = true
  clause1124 : p 35 = true ∨ p 1564 = true
  clause1125 : p 35 = true ∨ p 37 = true ∨ p 1565 = true
  clause1126 : p 40 = true ∨ p 1566 = true
  clause1127 : p 38 = true ∨ p 1566 = true
  clause1128 : p 38 = true ∨ p 40 = true ∨ p 1567 = true
  clause1129 : p 1566 = false ∨ p 1568 = true
  clause1130 : p 1567 = false ∨ p 1569 = true
  clause1131 : p 1564 = false ∨ p 1568 = true
  clause1132 : p 1564 = false ∨ p 1566 = false ∨ p 1569 = true
  clause1133 : p 1564 = false ∨ p 1567 = false ∨ p 1570 = true
  clause1134 : p 1565 = false ∨ p 1569 = true
  clause1135 : p 1565 = false ∨ p 1566 = false ∨ p 1570 = true
  clause1136 : p 1565 = false ∨ p 1567 = false ∨ p 1571 = true
  clause1137 : p 1569 = false ∨ p 1573 = true
  clause1138 : p 1570 = false ∨ p 1574 = true
  clause1139 : p 1571 = false ∨ p 1575 = true
  clause1140 : p 1560 = false ∨ p 1568 = false ∨ p 1573 = true
  clause1141 : p 1560 = false ∨ p 1569 = false ∨ p 1574 = true
  clause1142 : p 1560 = false ∨ p 1570 = false ∨ p 1575 = true
  clause1143 : p 1560 = false ∨ p 1571 = false ∨ p 1576 = true
  clause1144 : p 1561 = false ∨ p 1568 = false ∨ p 1574 = true
  clause1145 : p 1561 = false ∨ p 1569 = false ∨ p 1575 = true
  clause1146 : p 1561 = false ∨ p 1570 = false ∨ p 1576 = true
  clause1147 : p 1562 = false ∨ p 1568 = false ∨ p 1575 = true
  clause1148 : p 1562 = false ∨ p 1569 = false ∨ p 1576 = true
  clause1149 : p 1562 = false ∨ p 1570 = false ∨ p 1577 = true
  clause1150 : p 1563 = false ∨ p 1568 = false ∨ p 1576 = true
  clause1151 : p 1563 = false ∨ p 1569 = false ∨ p 1577 = true
  clause1152 : p 45 = true ∨ p 1580 = true
structure Block36 (p : Nat → Bool) : Prop where
  clause1153 : p 42 = true ∨ p 1580 = true
  clause1154 : p 42 = true ∨ p 45 = true ∨ p 1581 = true
  clause1155 : p 48 = true ∨ p 1582 = true
  clause1156 : p 47 = true ∨ p 1582 = true
  clause1157 : p 47 = true ∨ p 48 = true ∨ p 1583 = true
  clause1158 : p 1582 = false ∨ p 1584 = true
  clause1159 : p 1583 = false ∨ p 1585 = true
  clause1160 : p 1580 = false ∨ p 1584 = true
  clause1161 : p 1580 = false ∨ p 1582 = false ∨ p 1585 = true
  clause1162 : p 1580 = false ∨ p 1583 = false ∨ p 1586 = true
  clause1163 : p 1581 = false ∨ p 1585 = true
  clause1164 : p 1581 = false ∨ p 1582 = false ∨ p 1586 = true
  clause1165 : p 1581 = false ∨ p 1583 = false ∨ p 1587 = true
  clause1166 : p 53 = true ∨ p 1588 = true
  clause1167 : p 49 = true ∨ p 1588 = true
  clause1168 : p 49 = true ∨ p 53 = true ∨ p 1589 = true
  clause1169 : p 56 = true ∨ p 1590 = true
  clause1170 : p 54 = true ∨ p 1590 = true
  clause1171 : p 54 = true ∨ p 56 = true ∨ p 1591 = true
  clause1172 : p 1590 = false ∨ p 1592 = true
  clause1173 : p 1591 = false ∨ p 1593 = true
  clause1174 : p 1588 = false ∨ p 1592 = true
  clause1175 : p 1588 = false ∨ p 1590 = false ∨ p 1593 = true
  clause1176 : p 1588 = false ∨ p 1591 = false ∨ p 1594 = true
  clause1177 : p 1589 = false ∨ p 1593 = true
  clause1178 : p 1589 = false ∨ p 1590 = false ∨ p 1594 = true
  clause1179 : p 1589 = false ∨ p 1591 = false ∨ p 1595 = true
  clause1180 : p 1592 = false ∨ p 1596 = true
  clause1181 : p 1593 = false ∨ p 1597 = true
  clause1182 : p 1594 = false ∨ p 1598 = true
  clause1183 : p 1595 = false ∨ p 1599 = true
  clause1184 : p 1584 = false ∨ p 1596 = true
structure Block37 (p : Nat → Bool) : Prop where
  clause1185 : p 1584 = false ∨ p 1592 = false ∨ p 1597 = true
  clause1186 : p 1584 = false ∨ p 1593 = false ∨ p 1598 = true
  clause1187 : p 1584 = false ∨ p 1594 = false ∨ p 1599 = true
  clause1188 : p 1585 = false ∨ p 1597 = true
  clause1189 : p 1585 = false ∨ p 1592 = false ∨ p 1598 = true
  clause1190 : p 1585 = false ∨ p 1593 = false ∨ p 1599 = true
  clause1191 : p 1585 = false ∨ p 1594 = false ∨ p 1600 = true
  clause1192 : p 1585 = false ∨ p 1595 = false ∨ p 1601 = true
  clause1193 : p 1586 = false ∨ p 1598 = true
  clause1194 : p 1586 = false ∨ p 1592 = false ∨ p 1599 = true
  clause1195 : p 1586 = false ∨ p 1593 = false ∨ p 1600 = true
  clause1196 : p 1586 = false ∨ p 1594 = false ∨ p 1601 = true
  clause1197 : p 1587 = false ∨ p 1599 = true
  clause1198 : p 1587 = false ∨ p 1592 = false ∨ p 1600 = true
  clause1199 : p 1587 = false ∨ p 1593 = false ∨ p 1601 = true
  clause1200 : p 1573 = false ∨ p 1596 = false ∨ p 1606 = true
  clause1201 : p 1573 = false ∨ p 1597 = false ∨ p 1607 = true
  clause1202 : p 1573 = false ∨ p 1598 = false ∨ p 1608 = true
  clause1203 : p 1573 = false ∨ p 1599 = false ∨ p 1609 = true
  clause1204 : p 1573 = false ∨ p 1600 = false ∨ p 1610 = true
  clause1205 : p 1573 = false ∨ p 1601 = false ∨ p 1611 = true
  clause1206 : p 1574 = false ∨ p 1596 = false ∨ p 1607 = true
  clause1207 : p 1574 = false ∨ p 1597 = false ∨ p 1608 = true
  clause1208 : p 1574 = false ∨ p 1598 = false ∨ p 1609 = true
  clause1209 : p 1574 = false ∨ p 1599 = false ∨ p 1610 = true
  clause1210 : p 1574 = false ∨ p 1600 = false ∨ p 1611 = true
  clause1211 : p 1574 = false ∨ p 1601 = false ∨ p 1612 = true
  clause1212 : p 1575 = false ∨ p 1596 = false ∨ p 1608 = true
  clause1213 : p 1575 = false ∨ p 1597 = false ∨ p 1609 = true
  clause1214 : p 1575 = false ∨ p 1598 = false ∨ p 1610 = true
  clause1215 : p 1575 = false ∨ p 1599 = false ∨ p 1611 = true
  clause1216 : p 1575 = false ∨ p 1600 = false ∨ p 1612 = true
structure Block38 (p : Nat → Bool) : Prop where
  clause1217 : p 1576 = false ∨ p 1596 = false ∨ p 1609 = true
  clause1218 : p 1576 = false ∨ p 1597 = false ∨ p 1610 = true
  clause1219 : p 1576 = false ∨ p 1598 = false ∨ p 1611 = true
  clause1220 : p 1576 = false ∨ p 1599 = false ∨ p 1612 = true
  clause1221 : p 1576 = false ∨ p 1600 = false ∨ p 1613 = true
  clause1222 : p 1576 = false ∨ p 1601 = false ∨ p 1614 = true
  clause1223 : p 1577 = false ∨ p 1598 = false ∨ p 1612 = true
  clause1224 : p 1545 = false ∨ p 1608 = false ∨ p 1629 = true
  clause1225 : p 1545 = false ∨ p 1609 = false ∨ p 1630 = true
  clause1226 : p 1545 = false ∨ p 1610 = false ∨ p 1631 = true
  clause1227 : p 1545 = false ∨ p 1611 = false ∨ p 1632 = true
  clause1228 : p 1545 = false ∨ p 1612 = false ∨ p 1633 = true
  clause1229 : p 1545 = false ∨ p 1613 = false ∨ p 1634 = true
  clause1230 : p 1545 = false ∨ p 1614 = false ∨ p 1635 = true
  clause1231 : p 1546 = false ∨ p 1607 = false ∨ p 1629 = true
  clause1232 : p 1546 = false ∨ p 1608 = false ∨ p 1630 = true
  clause1233 : p 1546 = false ∨ p 1609 = false ∨ p 1631 = true
  clause1234 : p 1546 = false ∨ p 1610 = false ∨ p 1632 = true
  clause1235 : p 1546 = false ∨ p 1611 = false ∨ p 1633 = true
  clause1236 : p 1546 = false ∨ p 1612 = false ∨ p 1634 = true
  clause1237 : p 1546 = false ∨ p 1613 = false ∨ p 1635 = true
  clause1238 : p 1547 = false ∨ p 1606 = false ∨ p 1629 = true
  clause1239 : p 1547 = false ∨ p 1607 = false ∨ p 1630 = true
  clause1240 : p 1547 = false ∨ p 1608 = false ∨ p 1631 = true
  clause1241 : p 1547 = false ∨ p 1609 = false ∨ p 1632 = true
  clause1242 : p 1547 = false ∨ p 1610 = false ∨ p 1633 = true
  clause1243 : p 1547 = false ∨ p 1611 = false ∨ p 1634 = true
  clause1244 : p 1547 = false ∨ p 1612 = false ∨ p 1635 = true
  clause1245 : p 1548 = false ∨ p 1606 = false ∨ p 1630 = true
  clause1246 : p 1548 = false ∨ p 1607 = false ∨ p 1631 = true
  clause1247 : p 1548 = false ∨ p 1608 = false ∨ p 1632 = true
  clause1248 : p 1548 = false ∨ p 1609 = false ∨ p 1633 = true
structure Block39 (p : Nat → Bool) : Prop where
  clause1249 : p 1548 = false ∨ p 1610 = false ∨ p 1634 = true
  clause1250 : p 1548 = false ∨ p 1611 = false ∨ p 1635 = true
  clause1251 : p 1549 = false ∨ p 1606 = false ∨ p 1631 = true
  clause1252 : p 1549 = false ∨ p 1607 = false ∨ p 1632 = true
  clause1253 : p 1549 = false ∨ p 1608 = false ∨ p 1633 = true
  clause1254 : p 1549 = false ∨ p 1609 = false ∨ p 1634 = true
  clause1255 : p 1549 = false ∨ p 1610 = false ∨ p 1635 = true
  clause1256 : p 1550 = false ∨ p 1606 = false ∨ p 1632 = true
  clause1257 : p 1550 = false ∨ p 1607 = false ∨ p 1633 = true
  clause1258 : p 1550 = false ∨ p 1608 = false ∨ p 1634 = true
  clause1259 : p 1550 = false ∨ p 1609 = false ∨ p 1635 = true
  clause1260 : p 1550 = false ∨ p 1610 = false ∨ p 1636 = true
  clause1261 : p 1551 = false ∨ p 1606 = false ∨ p 1633 = true
  clause1262 : p 60 = true ∨ p 1643 = true
  clause1263 : p 58 = true ∨ p 1643 = true
  clause1264 : p 58 = true ∨ p 60 = true ∨ p 1644 = true
  clause1265 : p 65 = true ∨ p 1645 = true
  clause1266 : p 61 = true ∨ p 1645 = true
  clause1267 : p 61 = true ∨ p 65 = true ∨ p 1646 = true
  clause1268 : p 1645 = false ∨ p 1647 = true
  clause1269 : p 1646 = false ∨ p 1648 = true
  clause1270 : p 1643 = false ∨ p 1647 = true
  clause1271 : p 1643 = false ∨ p 1645 = false ∨ p 1648 = true
  clause1272 : p 1643 = false ∨ p 1646 = false ∨ p 1649 = true
  clause1273 : p 1644 = false ∨ p 1648 = true
  clause1274 : p 1644 = false ∨ p 1645 = false ∨ p 1649 = true
  clause1275 : p 1644 = false ∨ p 1646 = false ∨ p 1650 = true
  clause1276 : p 68 = true ∨ p 1651 = true
  clause1277 : p 66 = true ∨ p 1651 = true
  clause1278 : p 66 = true ∨ p 68 = true ∨ p 1652 = true
  clause1279 : p 73 = true ∨ p 1653 = true
  clause1280 : p 69 = true ∨ p 1653 = true
structure Block40 (p : Nat → Bool) : Prop where
  clause1281 : p 69 = true ∨ p 73 = true ∨ p 1654 = true
  clause1282 : p 1653 = false ∨ p 1655 = true
  clause1283 : p 1654 = false ∨ p 1656 = true
  clause1284 : p 1651 = false ∨ p 1655 = true
  clause1285 : p 1651 = false ∨ p 1653 = false ∨ p 1656 = true
  clause1286 : p 1651 = false ∨ p 1654 = false ∨ p 1657 = true
  clause1287 : p 1652 = false ∨ p 1656 = true
  clause1288 : p 1652 = false ∨ p 1653 = false ∨ p 1657 = true
  clause1289 : p 1652 = false ∨ p 1654 = false ∨ p 1658 = true
  clause1290 : p 1655 = false ∨ p 1659 = true
  clause1291 : p 1656 = false ∨ p 1660 = true
  clause1292 : p 1657 = false ∨ p 1661 = true
  clause1293 : p 1658 = false ∨ p 1662 = true
  clause1294 : p 1647 = false ∨ p 1659 = true
  clause1295 : p 1647 = false ∨ p 1655 = false ∨ p 1660 = true
  clause1296 : p 1647 = false ∨ p 1656 = false ∨ p 1661 = true
  clause1297 : p 1647 = false ∨ p 1657 = false ∨ p 1662 = true
  clause1298 : p 1647 = false ∨ p 1658 = false ∨ p 1663 = true
  clause1299 : p 1648 = false ∨ p 1660 = true
  clause1300 : p 1648 = false ∨ p 1655 = false ∨ p 1661 = true
  clause1301 : p 1648 = false ∨ p 1656 = false ∨ p 1662 = true
  clause1302 : p 1648 = false ∨ p 1657 = false ∨ p 1663 = true
  clause1303 : p 1648 = false ∨ p 1658 = false ∨ p 1664 = true
  clause1304 : p 1649 = false ∨ p 1661 = true
  clause1305 : p 1649 = false ∨ p 1655 = false ∨ p 1662 = true
  clause1306 : p 1649 = false ∨ p 1656 = false ∨ p 1663 = true
  clause1307 : p 1649 = false ∨ p 1657 = false ∨ p 1664 = true
  clause1308 : p 1650 = false ∨ p 1662 = true
  clause1309 : p 1650 = false ∨ p 1655 = false ∨ p 1663 = true
  clause1310 : p 1650 = false ∨ p 1656 = false ∨ p 1664 = true
  clause1311 : p 1650 = false ∨ p 1657 = false ∨ p 1665 = true
  clause1312 : p 76 = true ∨ p 1667 = true
structure Block41 (p : Nat → Bool) : Prop where
  clause1313 : p 75 = true ∨ p 1667 = true
  clause1314 : p 75 = true ∨ p 76 = true ∨ p 1668 = true
  clause1315 : p 80 = true ∨ p 1669 = true
  clause1316 : p 78 = true ∨ p 1669 = true
  clause1317 : p 78 = true ∨ p 80 = true ∨ p 1670 = true
  clause1318 : p 1669 = false ∨ p 1671 = true
  clause1319 : p 1670 = false ∨ p 1672 = true
  clause1320 : p 1667 = false ∨ p 1671 = true
  clause1321 : p 1667 = false ∨ p 1669 = false ∨ p 1672 = true
  clause1322 : p 1667 = false ∨ p 1670 = false ∨ p 1673 = true
  clause1323 : p 1668 = false ∨ p 1672 = true
  clause1324 : p 1668 = false ∨ p 1669 = false ∨ p 1673 = true
  clause1325 : p 84 = true ∨ p 1675 = true
  clause1326 : p 83 = true ∨ p 1675 = true
  clause1327 : p 83 = true ∨ p 84 = true ∨ p 1676 = true
  clause1328 : p 91 = true ∨ p 1677 = true
  clause1329 : p 88 = true ∨ p 1677 = true
  clause1330 : p 88 = true ∨ p 91 = true ∨ p 1678 = true
  clause1331 : p 1677 = false ∨ p 1679 = true
  clause1332 : p 1678 = false ∨ p 1680 = true
  clause1333 : p 1675 = false ∨ p 1679 = true
  clause1334 : p 1675 = false ∨ p 1677 = false ∨ p 1680 = true
  clause1335 : p 1675 = false ∨ p 1678 = false ∨ p 1681 = true
  clause1336 : p 1676 = false ∨ p 1680 = true
  clause1337 : p 1676 = false ∨ p 1677 = false ∨ p 1681 = true
  clause1338 : p 1679 = false ∨ p 1683 = true
  clause1339 : p 1680 = false ∨ p 1684 = true
  clause1340 : p 1681 = false ∨ p 1685 = true
  clause1341 : p 1671 = false ∨ p 1683 = true
  clause1342 : p 1671 = false ∨ p 1679 = false ∨ p 1684 = true
  clause1343 : p 1671 = false ∨ p 1680 = false ∨ p 1685 = true
  clause1344 : p 1671 = false ∨ p 1681 = false ∨ p 1686 = true
structure Block42 (p : Nat → Bool) : Prop where
  clause1345 : p 1672 = false ∨ p 1684 = true
  clause1346 : p 1672 = false ∨ p 1679 = false ∨ p 1685 = true
  clause1347 : p 1672 = false ∨ p 1680 = false ∨ p 1686 = true
  clause1348 : p 1673 = false ∨ p 1685 = true
  clause1349 : p 1673 = false ∨ p 1679 = false ∨ p 1686 = true
  clause1350 : p 1685 = false ∨ p 1693 = true
  clause1351 : p 1659 = false ∨ p 1691 = true
  clause1352 : p 1659 = false ∨ p 1683 = false ∨ p 1692 = true
  clause1353 : p 1659 = false ∨ p 1684 = false ∨ p 1693 = true
  clause1354 : p 1659 = false ∨ p 1685 = false ∨ p 1694 = true
  clause1355 : p 1659 = false ∨ p 1686 = false ∨ p 1695 = true
  clause1356 : p 1660 = false ∨ p 1692 = true
  clause1357 : p 1660 = false ∨ p 1683 = false ∨ p 1693 = true
  clause1358 : p 1660 = false ∨ p 1684 = false ∨ p 1694 = true
  clause1359 : p 1660 = false ∨ p 1685 = false ∨ p 1695 = true
  clause1360 : p 1660 = false ∨ p 1686 = false ∨ p 1696 = true
  clause1361 : p 1661 = false ∨ p 1693 = true
  clause1362 : p 1661 = false ∨ p 1683 = false ∨ p 1694 = true
  clause1363 : p 1661 = false ∨ p 1684 = false ∨ p 1695 = true
  clause1364 : p 1661 = false ∨ p 1685 = false ∨ p 1696 = true
  clause1365 : p 1661 = false ∨ p 1686 = false ∨ p 1697 = true
  clause1366 : p 1662 = false ∨ p 1694 = true
  clause1367 : p 1662 = false ∨ p 1683 = false ∨ p 1695 = true
  clause1368 : p 1662 = false ∨ p 1684 = false ∨ p 1696 = true
  clause1369 : p 1662 = false ∨ p 1685 = false ∨ p 1697 = true
  clause1370 : p 1663 = false ∨ p 1695 = true
  clause1371 : p 1663 = false ∨ p 1683 = false ∨ p 1696 = true
  clause1372 : p 1663 = false ∨ p 1684 = false ∨ p 1697 = true
  clause1373 : p 1663 = false ∨ p 1685 = false ∨ p 1698 = true
  clause1374 : p 1664 = false ∨ p 1696 = true
  clause1375 : p 1664 = false ∨ p 1683 = false ∨ p 1697 = true
  clause1376 : p 1664 = false ∨ p 1684 = false ∨ p 1698 = true
structure Block43 (p : Nat → Bool) : Prop where
  clause1377 : p 1665 = false ∨ p 1697 = true
  clause1378 : p 1665 = false ∨ p 1683 = false ∨ p 1698 = true
  clause1379 : p 1665 = false ∨ p 1684 = false ∨ p 1699 = true
  clause1380 : p 94 = true ∨ p 1707 = true
  clause1381 : p 92 = true ∨ p 1707 = true
  clause1382 : p 92 = true ∨ p 94 = true ∨ p 1708 = true
  clause1383 : p 99 = true ∨ p 1709 = true
  clause1384 : p 96 = true ∨ p 1709 = true
  clause1385 : p 96 = true ∨ p 99 = true ∨ p 1710 = true
  clause1386 : p 1709 = false ∨ p 1711 = true
  clause1387 : p 1710 = false ∨ p 1712 = true
  clause1388 : p 1707 = false ∨ p 1711 = true
  clause1389 : p 1707 = false ∨ p 1709 = false ∨ p 1712 = true
  clause1390 : p 1707 = false ∨ p 1710 = false ∨ p 1713 = true
  clause1391 : p 1708 = false ∨ p 1712 = true
  clause1392 : p 1708 = false ∨ p 1709 = false ∨ p 1713 = true
  clause1393 : p 103 = true ∨ p 1715 = true
  clause1394 : p 100 = true ∨ p 1715 = true
  clause1395 : p 100 = true ∨ p 103 = true ∨ p 1716 = true
  clause1396 : p 106 = true ∨ p 1717 = true
  clause1397 : p 104 = true ∨ p 1717 = true
  clause1398 : p 104 = true ∨ p 106 = true ∨ p 1718 = true
  clause1399 : p 1717 = false ∨ p 1719 = true
  clause1400 : p 1718 = false ∨ p 1720 = true
  clause1401 : p 1715 = false ∨ p 1719 = true
  clause1402 : p 1715 = false ∨ p 1717 = false ∨ p 1720 = true
  clause1403 : p 1715 = false ∨ p 1718 = false ∨ p 1721 = true
  clause1404 : p 1716 = false ∨ p 1720 = true
  clause1405 : p 1716 = false ∨ p 1717 = false ∨ p 1721 = true
  clause1406 : p 1716 = false ∨ p 1718 = false ∨ p 1722 = true
  clause1407 : p 1719 = false ∨ p 1723 = true
  clause1408 : p 1720 = false ∨ p 1724 = true
structure Block44 (p : Nat → Bool) : Prop where
  clause1409 : p 1721 = false ∨ p 1725 = true
  clause1410 : p 1722 = false ∨ p 1726 = true
  clause1411 : p 1711 = false ∨ p 1723 = true
  clause1412 : p 1711 = false ∨ p 1719 = false ∨ p 1724 = true
  clause1413 : p 1711 = false ∨ p 1720 = false ∨ p 1725 = true
  clause1414 : p 1711 = false ∨ p 1721 = false ∨ p 1726 = true
  clause1415 : p 1711 = false ∨ p 1722 = false ∨ p 1727 = true
  clause1416 : p 1712 = false ∨ p 1724 = true
  clause1417 : p 1712 = false ∨ p 1719 = false ∨ p 1725 = true
  clause1418 : p 1712 = false ∨ p 1720 = false ∨ p 1726 = true
  clause1419 : p 1712 = false ∨ p 1721 = false ∨ p 1727 = true
  clause1420 : p 1712 = false ∨ p 1722 = false ∨ p 1728 = true
  clause1421 : p 1713 = false ∨ p 1719 = false ∨ p 1726 = true
  clause1422 : p 1713 = false ∨ p 1720 = false ∨ p 1727 = true
  clause1423 : p 109 = true ∨ p 1731 = true
  clause1424 : p 107 = true ∨ p 1731 = true
  clause1425 : p 107 = true ∨ p 109 = true ∨ p 1732 = true
  clause1426 : p 113 = true ∨ p 1733 = true
  clause1427 : p 111 = true ∨ p 1733 = true
  clause1428 : p 111 = true ∨ p 113 = true ∨ p 1734 = true
  clause1429 : p 1733 = false ∨ p 1735 = true
  clause1430 : p 1734 = false ∨ p 1736 = true
  clause1431 : p 1731 = false ∨ p 1735 = true
  clause1432 : p 1731 = false ∨ p 1733 = false ∨ p 1736 = true
  clause1433 : p 1731 = false ∨ p 1734 = false ∨ p 1737 = true
  clause1434 : p 1732 = false ∨ p 1736 = true
  clause1435 : p 1732 = false ∨ p 1733 = false ∨ p 1737 = true
  clause1436 : p 1732 = false ∨ p 1734 = false ∨ p 1738 = true
  clause1437 : p 118 = true ∨ p 1739 = true
  clause1438 : p 116 = true ∨ p 1739 = true
  clause1439 : p 116 = true ∨ p 118 = true ∨ p 1740 = true
  clause1440 : p 124 = true ∨ p 1741 = true
structure Block45 (p : Nat → Bool) : Prop where
  clause1441 : p 121 = true ∨ p 1741 = true
  clause1442 : p 121 = true ∨ p 124 = true ∨ p 1742 = true
  clause1443 : p 1741 = false ∨ p 1743 = true
  clause1444 : p 1742 = false ∨ p 1744 = true
  clause1445 : p 1739 = false ∨ p 1743 = true
  clause1446 : p 1739 = false ∨ p 1741 = false ∨ p 1744 = true
  clause1447 : p 1739 = false ∨ p 1742 = false ∨ p 1745 = true
  clause1448 : p 1740 = false ∨ p 1744 = true
  clause1449 : p 1740 = false ∨ p 1741 = false ∨ p 1745 = true
  clause1450 : p 1740 = false ∨ p 1742 = false ∨ p 1746 = true
  clause1451 : p 1743 = false ∨ p 1747 = true
  clause1452 : p 1744 = false ∨ p 1748 = true
  clause1453 : p 1745 = false ∨ p 1749 = true
  clause1454 : p 1746 = false ∨ p 1750 = true
  clause1455 : p 1735 = false ∨ p 1747 = true
  clause1456 : p 1735 = false ∨ p 1743 = false ∨ p 1748 = true
  clause1457 : p 1735 = false ∨ p 1744 = false ∨ p 1749 = true
  clause1458 : p 1735 = false ∨ p 1745 = false ∨ p 1750 = true
  clause1459 : p 1735 = false ∨ p 1746 = false ∨ p 1751 = true
  clause1460 : p 1736 = false ∨ p 1748 = true
  clause1461 : p 1736 = false ∨ p 1743 = false ∨ p 1749 = true
  clause1462 : p 1736 = false ∨ p 1744 = false ∨ p 1750 = true
  clause1463 : p 1736 = false ∨ p 1745 = false ∨ p 1751 = true
  clause1464 : p 1736 = false ∨ p 1746 = false ∨ p 1752 = true
  clause1465 : p 1737 = false ∨ p 1749 = true
  clause1466 : p 1737 = false ∨ p 1743 = false ∨ p 1750 = true
  clause1467 : p 1737 = false ∨ p 1744 = false ∨ p 1751 = true
  clause1468 : p 1737 = false ∨ p 1745 = false ∨ p 1752 = true
  clause1469 : p 1737 = false ∨ p 1746 = false ∨ p 1753 = true
  clause1470 : p 1738 = false ∨ p 1750 = true
  clause1471 : p 1738 = false ∨ p 1743 = false ∨ p 1751 = true
  clause1472 : p 1738 = false ∨ p 1744 = false ∨ p 1752 = true
structure Block46 (p : Nat → Bool) : Prop where
  clause1473 : p 1738 = false ∨ p 1745 = false ∨ p 1753 = true
  clause1474 : p 1738 = false ∨ p 1746 = false ∨ p 1754 = true
  clause1475 : p 1750 = false ∨ p 1758 = true
  clause1476 : p 1751 = false ∨ p 1759 = true
  clause1477 : p 1752 = false ∨ p 1760 = true
  clause1478 : p 1753 = false ∨ p 1761 = true
  clause1479 : p 1754 = false ∨ p 1762 = true
  clause1480 : p 1723 = false ∨ p 1749 = false ∨ p 1758 = true
  clause1481 : p 1723 = false ∨ p 1750 = false ∨ p 1759 = true
  clause1482 : p 1723 = false ∨ p 1751 = false ∨ p 1760 = true
  clause1483 : p 1723 = false ∨ p 1752 = false ∨ p 1761 = true
  clause1484 : p 1723 = false ∨ p 1753 = false ∨ p 1762 = true
  clause1485 : p 1723 = false ∨ p 1754 = false ∨ p 1763 = true
  clause1486 : p 1724 = false ∨ p 1748 = false ∨ p 1758 = true
  clause1487 : p 1724 = false ∨ p 1749 = false ∨ p 1759 = true
  clause1488 : p 1724 = false ∨ p 1750 = false ∨ p 1760 = true
  clause1489 : p 1724 = false ∨ p 1751 = false ∨ p 1761 = true
  clause1490 : p 1724 = false ∨ p 1752 = false ∨ p 1762 = true
  clause1491 : p 1724 = false ∨ p 1753 = false ∨ p 1763 = true
  clause1492 : p 1725 = false ∨ p 1747 = false ∨ p 1758 = true
  clause1493 : p 1725 = false ∨ p 1748 = false ∨ p 1759 = true
  clause1494 : p 1725 = false ∨ p 1749 = false ∨ p 1760 = true
  clause1495 : p 1725 = false ∨ p 1750 = false ∨ p 1761 = true
  clause1496 : p 1725 = false ∨ p 1751 = false ∨ p 1762 = true
  clause1497 : p 1725 = false ∨ p 1752 = false ∨ p 1763 = true
  clause1498 : p 1726 = false ∨ p 1747 = false ∨ p 1759 = true
  clause1499 : p 1726 = false ∨ p 1748 = false ∨ p 1760 = true
  clause1500 : p 1726 = false ∨ p 1749 = false ∨ p 1761 = true
  clause1501 : p 1726 = false ∨ p 1750 = false ∨ p 1762 = true
  clause1502 : p 1726 = false ∨ p 1751 = false ∨ p 1763 = true
  clause1503 : p 1727 = false ∨ p 1759 = true
  clause1504 : p 1727 = false ∨ p 1747 = false ∨ p 1760 = true
structure Block47 (p : Nat → Bool) : Prop where
  clause1505 : p 1727 = false ∨ p 1748 = false ∨ p 1761 = true
  clause1506 : p 1727 = false ∨ p 1749 = false ∨ p 1762 = true
  clause1507 : p 1727 = false ∨ p 1750 = false ∨ p 1763 = true
  clause1508 : p 1728 = false ∨ p 1747 = false ∨ p 1761 = true
  clause1509 : p 1728 = false ∨ p 1749 = false ∨ p 1763 = true
  clause1510 : p 1691 = false ∨ p 1760 = false ∨ p 1777 = true
  clause1511 : p 1691 = false ∨ p 1761 = false ∨ p 1778 = true
  clause1512 : p 1691 = false ∨ p 1762 = false ∨ p 1779 = true
  clause1513 : p 1691 = false ∨ p 1763 = false ∨ p 1780 = true
  clause1514 : p 1692 = false ∨ p 1758 = false ∨ p 1776 = true
  clause1515 : p 1692 = false ∨ p 1759 = false ∨ p 1777 = true
  clause1516 : p 1692 = false ∨ p 1760 = false ∨ p 1778 = true
  clause1517 : p 1692 = false ∨ p 1761 = false ∨ p 1779 = true
  clause1518 : p 1692 = false ∨ p 1762 = false ∨ p 1780 = true
  clause1519 : p 1692 = false ∨ p 1763 = false ∨ p 1781 = true
  clause1520 : p 1693 = false ∨ p 1758 = false ∨ p 1777 = true
  clause1521 : p 1693 = false ∨ p 1759 = false ∨ p 1778 = true
  clause1522 : p 1693 = false ∨ p 1760 = false ∨ p 1779 = true
  clause1523 : p 1693 = false ∨ p 1761 = false ∨ p 1780 = true
  clause1524 : p 1693 = false ∨ p 1762 = false ∨ p 1781 = true
  clause1525 : p 1693 = false ∨ p 1763 = false ∨ p 1782 = true
  clause1526 : p 1694 = false ∨ p 1758 = false ∨ p 1778 = true
  clause1527 : p 1694 = false ∨ p 1759 = false ∨ p 1779 = true
  clause1528 : p 1694 = false ∨ p 1760 = false ∨ p 1780 = true
  clause1529 : p 1694 = false ∨ p 1761 = false ∨ p 1781 = true
  clause1530 : p 1694 = false ∨ p 1762 = false ∨ p 1782 = true
  clause1531 : p 1695 = false ∨ p 1758 = false ∨ p 1779 = true
  clause1532 : p 1695 = false ∨ p 1759 = false ∨ p 1780 = true
  clause1533 : p 1695 = false ∨ p 1760 = false ∨ p 1781 = true
  clause1534 : p 1695 = false ∨ p 1761 = false ∨ p 1782 = true
  clause1535 : p 1696 = false ∨ p 1758 = false ∨ p 1780 = true
  clause1536 : p 1696 = false ∨ p 1759 = false ∨ p 1781 = true
structure Block48 (p : Nat → Bool) : Prop where
  clause1537 : p 1696 = false ∨ p 1760 = false ∨ p 1782 = true
  clause1538 : p 1696 = false ∨ p 1761 = false ∨ p 1783 = true
  clause1539 : p 1697 = false ∨ p 1758 = false ∨ p 1781 = true
  clause1540 : p 1697 = false ∨ p 1759 = false ∨ p 1782 = true
  clause1541 : p 1697 = false ∨ p 1760 = false ∨ p 1783 = true
  clause1542 : p 1698 = false ∨ p 1758 = false ∨ p 1782 = true
  clause1543 : p 1699 = false ∨ p 1758 = false ∨ p 1783 = true
  clause1544 : p 1629 = false ∨ p 1783 = false ∨ p 1816 = true
  clause1545 : p 1630 = false ∨ p 1782 = false ∨ p 1816 = true
  clause1546 : p 1631 = false ∨ p 1781 = false ∨ p 1816 = true
  clause1547 : p 1632 = false ∨ p 1780 = false ∨ p 1816 = true
  clause1548 : p 1633 = false ∨ p 1779 = false ∨ p 1816 = true
  clause1549 : p 1634 = false ∨ p 1778 = false ∨ p 1816 = true
  clause1550 : p 1635 = false ∨ p 1777 = false ∨ p 1816 = true
  clause1551 : p 1636 = false ∨ p 1776 = false ∨ p 1816 = true
  clause1552 : p 1816 = false
  clause1553 : p 5 = false ∨ p 10 = false ∨ p 19 = false ∨ p 29 = false
  clause1554 : p 8 = false ∨ p 10 = false ∨ p 25 = false ∨ p 29 = false
  clause1555 : p 8 = false ∨ p 10 = false ∨ p 43 = false ∨ p 47 = false
  clause1556 : p 8 = false ∨ p 25 = false ∨ p 43 = false ∨ p 60 = false
  clause1557 : p 10 = false ∨ p 29 = false ∨ p 47 = false ∨ p 67 = false
  clause1558 : p 14 = false ∨ p 15 = false ∨ p 16 = false ∨ p 17 = false
  clause1559 : p 14 = false ∨ p 15 = false ∨ p 24 = false ∨ p 25 = false
  clause1560 : p 14 = false ∨ p 16 = false ∨ p 24 = false ∨ p 26 = false
  clause1561 : p 15 = false ∨ p 19 = false ∨ p 25 = false ∨ p 29 = false
  clause1562 : p 15 = false ∨ p 19 = false ∨ p 71 = false ∨ p 75 = false
  clause1563 : p 20 = false ∨ p 21 = false ∨ p 22 = false ∨ p 23 = false
  clause1564 : p 20 = false ∨ p 22 = false ∨ p 31 = false ∨ p 32 = false
  clause1565 : p 25 = false ∨ p 27 = false ∨ p 60 = false ∨ p 62 = false
  clause1566 : p 25 = false ∨ p 29 = false ∨ p 60 = false ∨ p 67 = false
  clause1567 : p 26 = false ∨ p 27 = false ∨ p 61 = false ∨ p 62 = false
  clause1568 : p 26 = false ∨ p 27 = false ∨ p 78 = false ∨ p 79 = false
structure Block49 (p : Nat → Bool) : Prop where
  clause1569 : p 26 = false ∨ p 61 = false ∨ p 78 = false ∨ p 115 = false
  clause1570 : p 33 = false ∨ p 34 = false ∨ p 35 = false ∨ p 36 = false
  clause1571 : p 33 = false ∨ p 34 = false ∨ p 42 = false ∨ p 43 = false
  clause1572 : p 36 = false ∨ p 37 = false ∨ p 38 = false ∨ p 41 = false
  clause1573 : p 42 = false ∨ p 43 = false ∨ p 46 = false ∨ p 47 = false
  clause1574 : p 42 = false ∨ p 44 = false ∨ p 46 = false ∨ p 49 = false
  clause1575 : p 43 = false ∨ p 47 = false ∨ p 60 = false ∨ p 67 = false
  clause1576 : p 44 = false ∨ p 45 = false ∨ p 49 = false ∨ p 50 = false
  clause1577 : p 46 = false ∨ p 48 = false ∨ p 49 = false ∨ p 50 = false
  clause1578 : p 51 = false ∨ p 53 = false ∨ p 60 = false ∨ p 63 = false
  clause1579 : p 52 = false ∨ p 54 = false ∨ p 58 = false ∨ p 59 = false
  clause1580 : p 55 = false ∨ p 56 = false ∨ p 58 = false ∨ p 59 = false
  clause1581 : p 55 = false ∨ p 66 = false ∨ p 107 = false ∨ p 119 = false
  clause1582 : p 57 = false ∨ p 68 = false ∨ p 109 = false ∨ p 120 = false
  clause1583 : p 60 = false ∨ p 63 = false ∨ p 67 = false ∨ p 69 = false
  clause1584 : p 61 = false ∨ p 62 = false ∨ p 64 = false ∨ p 65 = false
  clause1585 : p 61 = false ∨ p 62 = false ∨ p 115 = false ∨ p 116 = false
  clause1586 : p 61 = false ∨ p 64 = false ∨ p 115 = false ∨ p 118 = false
  clause1587 : p 62 = false ∨ p 65 = false ∨ p 68 = false ∨ p 70 = false
  clause1588 : p 63 = false ∨ p 65 = false ∨ p 69 = false ∨ p 70 = false
  clause1589 : p 67 = false ∨ p 68 = false ∨ p 69 = false ∨ p 70 = false
  clause1590 : p 69 = false ∨ p 70 = false ∨ p 122 = false ∨ p 124 = false
  clause1591 : p 78 = false ∨ p 79 = false ∨ p 82 = false ∨ p 83 = false
  clause1592 : p 78 = false ∨ p 79 = false ∨ p 115 = false ∨ p 116 = false
  clause1593 : p 83 = false ∨ p 85 = false ∨ p 120 = false ∨ p 124 = false
  clause1594 : p 94 = false ∨ p 95 = false ∨ p 98 = false ∨ p 99 = false
  clause1595 : p 94 = false ∨ p 95 = false ∨ p 115 = false ∨ p 116 = false
  clause1596 : p 100 = false ∨ p 101 = false ∨ p 122 = false ∨ p 124 = false
  clause1597 : p 102 = false ∨ p 103 = false ∨ p 104 = false ∨ p 105 = false
  clause1598 : p 102 = false ∨ p 103 = false ∨ p 113 = false ∨ p 114 = false
  clause1599 : p 102 = false ∨ p 104 = false ∨ p 113 = false ∨ p 115 = false
  clause1600 : p 102 = false ∨ p 107 = false ∨ p 113 = false ∨ p 119 = false
structure Block50 (p : Nat → Bool) : Prop where
  clause1601 : p 104 = false ∨ p 105 = false ∨ p 115 = false ∨ p 116 = false
  clause1602 : p 107 = false ∨ p 108 = false ∨ p 110 = false ∨ p 111 = false
  clause1603 : p 107 = false ∨ p 110 = false ∨ p 119 = false ∨ p 121 = false
  clause1604 : p 108 = false ∨ p 109 = false ∨ p 111 = false ∨ p 112 = false
  clause1605 : p 110 = false ∨ p 111 = false ∨ p 121 = false ∨ p 122 = false
  clause1606 : p 111 = false ∨ p 112 = false ∨ p 122 = false ∨ p 124 = false
  clause1607 : p 113 = false ∨ p 114 = false ∨ p 115 = false ∨ p 116 = false
  clause1608 : p 113 = false ∨ p 115 = false ∨ p 117 = false ∨ p 118 = false
  clause1609 : p 113 = false ∨ p 117 = false ∨ p 119 = false ∨ p 121 = false
  clause1610 : p 117 = false ∨ p 118 = false ∨ p 121 = false ∨ p 123 = false
  clause1611 : p 121 = false ∨ p 122 = false ∨ p 123 = false ∨ p 124 = false
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
  block41 : Block41 p
  block42 : Block42 p
  block43 : Block43 p
  block44 : Block44 p
  block45 : Block45 p
  block46 : Block46 p
  block47 : Block47 p
  block48 : Block48 p
  block49 : Block49 p
  block50 : Block50 p
def c1 : List Lit := [(1, false), (2, false), (3, false), (9, false)]
theorem step1 (p : Nat → Bool) (h : Constraints p) : clause p c1 = true := by
  simpa only [c1,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause1
def c2 : List Lit := [(125, false), (2, false), (9, false)]
theorem step2 (p : Nat → Bool) (h : Constraints p) : clause p c2 = true := by
  simpa only [c2,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause2
def c3 : List Lit := [(1, false), (125, true), (3, true), (9, true)]
theorem step3 (p : Nat → Bool) (h : Constraints p) : clause p c3 = true := by
  simpa only [c3,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause3
def c4 : List Lit := [(2, false), (1, true)]
theorem step4 (p : Nat → Bool) (h : Constraints p) : clause p c4 = true := by
  simpa only [c4,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause4
def c5 : List Lit := [(2, true)]
theorem step5 (p : Nat → Bool) (h : Constraints p) : clause p c5 = true := by
  simpa only [c5,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause5
def c6 : List Lit := [(3, false), (127, true), (7, true)]
theorem step6 (p : Nat → Bool) (h : Constraints p) : clause p c6 = true := by
  simpa only [c6,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause6
def c7 : List Lit := [(4, false), (128, true), (6, true)]
theorem step7 (p : Nat → Bool) (h : Constraints p) : clause p c7 = true := by
  simpa only [c7,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause7
def c8 : List Lit := [(4, false), (128, true), (5, true)]
theorem step8 (p : Nat → Bool) (h : Constraints p) : clause p c8 = true := by
  simpa only [c8,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause8
def c9 : List Lit := [(5, false), (4, false), (10, false), (19, false)]
theorem step9 (p : Nat → Bool) (h : Constraints p) : clause p c9 = true := by
  simpa only [c9,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause9
def c10 : List Lit := [(5, false), (129, true), (10, true), (19, true)]
theorem step10 (p : Nat → Bool) (h : Constraints p) : clause p c10 = true := by
  simpa only [c10,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause10
def c11 : List Lit := [(5, false), (129, true), (4, true), (19, true)]
theorem step11 (p : Nat → Bool) (h : Constraints p) : clause p c11 = true := by
  simpa only [c11,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause11
def c12 : List Lit := [(5, false), (129, true), (4, true), (10, true)]
theorem step12 (p : Nat → Bool) (h : Constraints p) : clause p c12 = true := by
  simpa only [c12,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause12
def c13 : List Lit := [(6, false), (4, false), (7, false), (11, false)]
theorem step13 (p : Nat → Bool) (h : Constraints p) : clause p c13 = true := by
  simpa only [c13,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause13
def c14 : List Lit := [(6, false), (130, true), (7, true), (11, true)]
theorem step14 (p : Nat → Bool) (h : Constraints p) : clause p c14 = true := by
  simpa only [c14,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause14
def c15 : List Lit := [(6, false), (130, true), (4, true), (11, true)]
theorem step15 (p : Nat → Bool) (h : Constraints p) : clause p c15 = true := by
  simpa only [c15,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause15
def c16 : List Lit := [(6, false), (130, true), (4, true), (7, true)]
theorem step16 (p : Nat → Bool) (h : Constraints p) : clause p c16 = true := by
  simpa only [c16,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause16
def c17 : List Lit := [(7, false), (3, false), (6, false), (22, false)]
theorem step17 (p : Nat → Bool) (h : Constraints p) : clause p c17 = true := by
  simpa only [c17,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause17
def c18 : List Lit := [(7, false), (131, true), (6, true), (22, true)]
theorem step18 (p : Nat → Bool) (h : Constraints p) : clause p c18 = true := by
  simpa only [c18,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause18
def c19 : List Lit := [(7, false), (131, true), (3, true), (22, true)]
theorem step19 (p : Nat → Bool) (h : Constraints p) : clause p c19 = true := by
  simpa only [c19,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause19
def c20 : List Lit := [(8, false), (10, false), (25, false), (43, false)]
theorem step20 (p : Nat → Bool) (h : Constraints p) : clause p c20 = true := by
  simpa only [c20,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause20
def c21 : List Lit := [(8, false), (132, true), (25, true), (43, true)]
theorem step21 (p : Nat → Bool) (h : Constraints p) : clause p c21 = true := by
  simpa only [c21,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause21
def c22 : List Lit := [(8, false), (132, true), (10, true), (43, true)]
theorem step22 (p : Nat → Bool) (h : Constraints p) : clause p c22 = true := by
  simpa only [c22,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause22
def c23 : List Lit := [(8, false), (132, true), (10, true), (25, true)]
theorem step23 (p : Nat → Bool) (h : Constraints p) : clause p c23 = true := by
  simpa only [c23,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause23
def c24 : List Lit := [(9, false), (1, false), (28, false), (44, false)]
theorem step24 (p : Nat → Bool) (h : Constraints p) : clause p c24 = true := by
  simpa only [c24,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause24
def c25 : List Lit := [(9, false), (133, true), (28, true), (44, true)]
theorem step25 (p : Nat → Bool) (h : Constraints p) : clause p c25 = true := by
  simpa only [c25,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause25
def c26 : List Lit := [(10, false), (5, true), (8, true), (12, true), (13, true), (29, true), (47, true)]
theorem step26 (p : Nat → Bool) (h : Constraints p) : clause p c26 = true := by
  simpa only [c26,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause26
def c27 : List Lit := [(10, false), (5, false), (8, false), (12, false)]
theorem step27 (p : Nat → Bool) (h : Constraints p) : clause p c27 = true := by
  simpa only [c27,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause27
def c28 : List Lit := [(10, false), (5, false), (8, false), (29, false)]
theorem step28 (p : Nat → Bool) (h : Constraints p) : clause p c28 = true := by
  simpa only [c28,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause28
def c29 : List Lit := [(10, false), (5, false), (8, false), (47, false)]
theorem step29 (p : Nat → Bool) (h : Constraints p) : clause p c29 = true := by
  simpa only [c29,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause29
def c30 : List Lit := [(10, false), (5, false), (12, false), (29, false)]
theorem step30 (p : Nat → Bool) (h : Constraints p) : clause p c30 = true := by
  simpa only [c30,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause30
def c31 : List Lit := [(10, false), (5, false), (12, false), (47, false)]
theorem step31 (p : Nat → Bool) (h : Constraints p) : clause p c31 = true := by
  simpa only [c31,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause31
def c32 : List Lit := [(10, false), (5, false), (29, false), (47, false)]
theorem step32 (p : Nat → Bool) (h : Constraints p) : clause p c32 = true := by
  simpa only [c32,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause32
def c33 : List Lit := [(10, false), (8, false), (12, false), (29, false)]
theorem step33 (p : Nat → Bool) (h : Constraints p) : clause p c33 = true := by
  simpa only [c33,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause33
def c34 : List Lit := [(10, false), (8, false), (12, false), (47, false)]
theorem step34 (p : Nat → Bool) (h : Constraints p) : clause p c34 = true := by
  simpa only [c34,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause34
def c35 : List Lit := [(10, false), (8, false), (29, false), (47, false)]
theorem step35 (p : Nat → Bool) (h : Constraints p) : clause p c35 = true := by
  simpa only [c35,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause35
def c36 : List Lit := [(10, false), (12, false), (29, false), (47, false)]
theorem step36 (p : Nat → Bool) (h : Constraints p) : clause p c36 = true := by
  simpa only [c36,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause36
def c37 : List Lit := [(10, false), (134, true), (8, true), (12, true), (13, true), (29, true), (47, true)]
theorem step37 (p : Nat → Bool) (h : Constraints p) : clause p c37 = true := by
  simpa only [c37,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause37
def c38 : List Lit := [(10, false), (134, true), (5, true), (8, true), (13, true), (29, true), (47, true)]
theorem step38 (p : Nat → Bool) (h : Constraints p) : clause p c38 = true := by
  simpa only [c38,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause38
def c39 : List Lit := [(10, false), (134, true), (5, true), (8, true), (12, true), (13, true), (47, true)]
theorem step39 (p : Nat → Bool) (h : Constraints p) : clause p c39 = true := by
  simpa only [c39,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause39
def c40 : List Lit := [(10, false), (134, true), (5, true), (8, true), (12, true), (13, true), (29, true)]
theorem step40 (p : Nat → Bool) (h : Constraints p) : clause p c40 = true := by
  simpa only [c40,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause40
def c41 : List Lit := [(11, false), (6, false), (12, false), (30, false)]
theorem step41 (p : Nat → Bool) (h : Constraints p) : clause p c41 = true := by
  simpa only [c41,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause41
def c42 : List Lit := [(11, false), (6, false), (12, false), (48, false)]
theorem step42 (p : Nat → Bool) (h : Constraints p) : clause p c42 = true := by
  simpa only [c42,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause42
def c43 : List Lit := [(11, false), (6, false), (30, false), (48, false)]
theorem step43 (p : Nat → Bool) (h : Constraints p) : clause p c43 = true := by
  simpa only [c43,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause43
def c44 : List Lit := [(11, false), (12, false), (30, false), (48, false)]
theorem step44 (p : Nat → Bool) (h : Constraints p) : clause p c44 = true := by
  simpa only [c44,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause44
def c45 : List Lit := [(11, false), (135, true), (12, true), (30, true), (48, true)]
theorem step45 (p : Nat → Bool) (h : Constraints p) : clause p c45 = true := by
  simpa only [c45,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause45
def c46 : List Lit := [(11, false), (135, true), (6, true), (12, true), (48, true)]
theorem step46 (p : Nat → Bool) (h : Constraints p) : clause p c46 = true := by
  simpa only [c46,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause46
def c47 : List Lit := [(12, false), (136, true), (11, true)]
theorem step47 (p : Nat → Bool) (h : Constraints p) : clause p c47 = true := by
  simpa only [c47,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause47
def c48 : List Lit := [(12, false), (136, true), (10, true)]
theorem step48 (p : Nat → Bool) (h : Constraints p) : clause p c48 = true := by
  simpa only [c48,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause48
def c49 : List Lit := [(13, false), (137, true)]
theorem step49 (p : Nat → Bool) (h : Constraints p) : clause p c49 = true := by
  simpa only [c49,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause49
def c50 : List Lit := [(14, false), (15, false), (16, false), (24, false)]
theorem step50 (p : Nat → Bool) (h : Constraints p) : clause p c50 = true := by
  simpa only [c50,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause50
def c51 : List Lit := [(14, false), (138, true), (15, true), (24, true)]
theorem step51 (p : Nat → Bool) (h : Constraints p) : clause p c51 = true := by
  simpa only [c51,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause51
def c52 : List Lit := [(14, false), (138, true), (15, true), (16, true)]
theorem step52 (p : Nat → Bool) (h : Constraints p) : clause p c52 = true := by
  simpa only [c52,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause52
def c53 : List Lit := [(15, false), (14, false), (17, false), (51, false)]
theorem step53 (p : Nat → Bool) (h : Constraints p) : clause p c53 = true := by
  simpa only [c53,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause53
def c54 : List Lit := [(15, false), (14, false), (17, false), (71, false)]
theorem step54 (p : Nat → Bool) (h : Constraints p) : clause p c54 = true := by
  simpa only [c54,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause54
def c55 : List Lit := [(15, false), (14, false), (19, false), (25, false)]
theorem step55 (p : Nat → Bool) (h : Constraints p) : clause p c55 = true := by
  simpa only [c55,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause55
def c56 : List Lit := [(15, false), (17, false), (19, false), (25, false)]
theorem step56 (p : Nat → Bool) (h : Constraints p) : clause p c56 = true := by
  simpa only [c56,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause56
def c57 : List Lit := [(15, false), (17, false), (25, false), (51, false)]
theorem step57 (p : Nat → Bool) (h : Constraints p) : clause p c57 = true := by
  simpa only [c57,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause57
def c58 : List Lit := [(15, false), (17, false), (25, false), (71, false)]
theorem step58 (p : Nat → Bool) (h : Constraints p) : clause p c58 = true := by
  simpa only [c58,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause58
def c59 : List Lit := [(16, false), (140, true), (17, true), (26, true)]
theorem step59 (p : Nat → Bool) (h : Constraints p) : clause p c59 = true := by
  simpa only [c59,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause59
def c60 : List Lit := [(16, false), (140, true), (14, true), (26, true)]
theorem step60 (p : Nat → Bool) (h : Constraints p) : clause p c60 = true := by
  simpa only [c60,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause60
def c61 : List Lit := [(16, false), (140, true), (14, true), (17, true)]
theorem step61 (p : Nat → Bool) (h : Constraints p) : clause p c61 = true := by
  simpa only [c61,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause61
def c62 : List Lit := [(17, false), (15, false), (16, false), (18, false)]
theorem step62 (p : Nat → Bool) (h : Constraints p) : clause p c62 = true := by
  simpa only [c62,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause62
def c63 : List Lit := [(17, false), (15, false), (16, false), (27, false)]
theorem step63 (p : Nat → Bool) (h : Constraints p) : clause p c63 = true := by
  simpa only [c63,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause63
def c64 : List Lit := [(17, false), (15, false), (18, false), (27, false)]
theorem step64 (p : Nat → Bool) (h : Constraints p) : clause p c64 = true := by
  simpa only [c64,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause64
def c65 : List Lit := [(17, false), (16, false), (18, false), (27, false)]
theorem step65 (p : Nat → Bool) (h : Constraints p) : clause p c65 = true := by
  simpa only [c65,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause65
def c66 : List Lit := [(17, false), (141, true), (15, true), (18, true), (27, true)]
theorem step66 (p : Nat → Bool) (h : Constraints p) : clause p c66 = true := by
  simpa only [c66,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause66
def c67 : List Lit := [(17, false), (141, true), (15, true), (16, true), (27, true)]
theorem step67 (p : Nat → Bool) (h : Constraints p) : clause p c67 = true := by
  simpa only [c67,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause67
def c68 : List Lit := [(18, false), (142, true), (23, true)]
theorem step68 (p : Nat → Bool) (h : Constraints p) : clause p c68 = true := by
  simpa only [c68,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause68
def c69 : List Lit := [(18, false), (142, true), (17, true)]
theorem step69 (p : Nat → Bool) (h : Constraints p) : clause p c69 = true := by
  simpa only [c69,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause69
def c70 : List Lit := [(19, false), (5, false), (15, false), (21, false)]
theorem step70 (p : Nat → Bool) (h : Constraints p) : clause p c70 = true := by
  simpa only [c70,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause70
def c71 : List Lit := [(19, false), (5, false), (15, false), (29, false)]
theorem step71 (p : Nat → Bool) (h : Constraints p) : clause p c71 = true := by
  simpa only [c71,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause71
def c72 : List Lit := [(19, false), (5, false), (15, false), (75, false)]
theorem step72 (p : Nat → Bool) (h : Constraints p) : clause p c72 = true := by
  simpa only [c72,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause72
def c73 : List Lit := [(19, false), (5, false), (21, false), (29, false)]
theorem step73 (p : Nat → Bool) (h : Constraints p) : clause p c73 = true := by
  simpa only [c73,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause73
def c74 : List Lit := [(19, false), (5, false), (21, false), (75, false)]
theorem step74 (p : Nat → Bool) (h : Constraints p) : clause p c74 = true := by
  simpa only [c74,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause74
def c75 : List Lit := [(19, false), (5, false), (29, false), (75, false)]
theorem step75 (p : Nat → Bool) (h : Constraints p) : clause p c75 = true := by
  simpa only [c75,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause75
def c76 : List Lit := [(19, false), (15, false), (21, false), (29, false)]
theorem step76 (p : Nat → Bool) (h : Constraints p) : clause p c76 = true := by
  simpa only [c76,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause76
def c77 : List Lit := [(19, false), (15, false), (21, false), (75, false)]
theorem step77 (p : Nat → Bool) (h : Constraints p) : clause p c77 = true := by
  simpa only [c77,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause77
def c78 : List Lit := [(19, false), (15, false), (29, false), (75, false)]
theorem step78 (p : Nat → Bool) (h : Constraints p) : clause p c78 = true := by
  simpa only [c78,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause78
def c79 : List Lit := [(19, false), (21, false), (29, false), (75, false)]
theorem step79 (p : Nat → Bool) (h : Constraints p) : clause p c79 = true := by
  simpa only [c79,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause79
def c80 : List Lit := [(20, false), (21, false), (22, false), (31, false)]
theorem step80 (p : Nat → Bool) (h : Constraints p) : clause p c80 = true := by
  simpa only [c80,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause80
def c81 : List Lit := [(20, false), (21, false), (22, false), (58, false)]
theorem step81 (p : Nat → Bool) (h : Constraints p) : clause p c81 = true := by
  simpa only [c81,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause81
def c82 : List Lit := [(20, false), (21, false), (31, false), (58, false)]
theorem step82 (p : Nat → Bool) (h : Constraints p) : clause p c82 = true := by
  simpa only [c82,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause82
def c83 : List Lit := [(20, false), (22, false), (31, false), (58, false)]
theorem step83 (p : Nat → Bool) (h : Constraints p) : clause p c83 = true := by
  simpa only [c83,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause83
def c84 : List Lit := [(144, false), (31, false), (58, false)]
theorem step84 (p : Nat → Bool) (h : Constraints p) : clause p c84 = true := by
  simpa only [c84,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause84
def c85 : List Lit := [(20, false), (144, true), (22, true), (31, true), (58, true)]
theorem step85 (p : Nat → Bool) (h : Constraints p) : clause p c85 = true := by
  simpa only [c85,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause85
def c86 : List Lit := [(20, false), (144, true), (21, true), (22, true), (58, true)]
theorem step86 (p : Nat → Bool) (h : Constraints p) : clause p c86 = true := by
  simpa only [c86,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause86
def c87 : List Lit := [(21, false), (19, false), (20, false), (23, false)]
theorem step87 (p : Nat → Bool) (h : Constraints p) : clause p c87 = true := by
  simpa only [c87,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause87
def c88 : List Lit := [(21, false), (145, true), (20, true), (23, true)]
theorem step88 (p : Nat → Bool) (h : Constraints p) : clause p c88 = true := by
  simpa only [c88,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause88
def c89 : List Lit := [(21, false), (145, true), (19, true), (23, true)]
theorem step89 (p : Nat → Bool) (h : Constraints p) : clause p c89 = true := by
  simpa only [c89,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause89
def c90 : List Lit := [(21, false), (145, true), (19, true), (20, true)]
theorem step90 (p : Nat → Bool) (h : Constraints p) : clause p c90 = true := by
  simpa only [c90,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause90
def c91 : List Lit := [(22, false), (7, false), (20, false), (23, false)]
theorem step91 (p : Nat → Bool) (h : Constraints p) : clause p c91 = true := by
  simpa only [c91,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause91
def c92 : List Lit := [(22, false), (7, false), (20, false), (32, false)]
theorem step92 (p : Nat → Bool) (h : Constraints p) : clause p c92 = true := by
  simpa only [c92,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause92
def c93 : List Lit := [(22, false), (7, false), (20, false), (77, false)]
theorem step93 (p : Nat → Bool) (h : Constraints p) : clause p c93 = true := by
  simpa only [c93,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause93
def c94 : List Lit := [(22, false), (7, false), (23, false), (32, false)]
theorem step94 (p : Nat → Bool) (h : Constraints p) : clause p c94 = true := by
  simpa only [c94,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause94
def c95 : List Lit := [(22, false), (7, false), (23, false), (77, false)]
theorem step95 (p : Nat → Bool) (h : Constraints p) : clause p c95 = true := by
  simpa only [c95,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause95
def c96 : List Lit := [(22, false), (7, false), (32, false), (59, false)]
theorem step96 (p : Nat → Bool) (h : Constraints p) : clause p c96 = true := by
  simpa only [c96,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause96
def c97 : List Lit := [(22, false), (7, false), (32, false), (77, false)]
theorem step97 (p : Nat → Bool) (h : Constraints p) : clause p c97 = true := by
  simpa only [c97,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause97
def c98 : List Lit := [(22, false), (20, false), (23, false), (32, false)]
theorem step98 (p : Nat → Bool) (h : Constraints p) : clause p c98 = true := by
  simpa only [c98,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause98
def c99 : List Lit := [(22, false), (20, false), (23, false), (77, false)]
theorem step99 (p : Nat → Bool) (h : Constraints p) : clause p c99 = true := by
  simpa only [c99,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause99
def c100 : List Lit := [(22, false), (20, false), (32, false), (59, false)]
theorem step100 (p : Nat → Bool) (h : Constraints p) : clause p c100 = true := by
  simpa only [c100,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause100
def c101 : List Lit := [(22, false), (20, false), (32, false), (77, false)]
theorem step101 (p : Nat → Bool) (h : Constraints p) : clause p c101 = true := by
  simpa only [c101,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause101
def c102 : List Lit := [(22, false), (20, false), (59, false), (77, false)]
theorem step102 (p : Nat → Bool) (h : Constraints p) : clause p c102 = true := by
  simpa only [c102,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause102
def c103 : List Lit := [(22, false), (23, false), (32, false), (59, false)]
theorem step103 (p : Nat → Bool) (h : Constraints p) : clause p c103 = true := by
  simpa only [c103,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause103
def c104 : List Lit := [(22, false), (23, false), (32, false), (77, false)]
theorem step104 (p : Nat → Bool) (h : Constraints p) : clause p c104 = true := by
  simpa only [c104,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause104
def c105 : List Lit := [(22, false), (23, false), (59, false), (77, false)]
theorem step105 (p : Nat → Bool) (h : Constraints p) : clause p c105 = true := by
  simpa only [c105,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause105
def c106 : List Lit := [(22, false), (32, false), (59, false), (77, false)]
theorem step106 (p : Nat → Bool) (h : Constraints p) : clause p c106 = true := by
  simpa only [c106,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause106
def c107 : List Lit := [(23, false), (18, false), (21, false), (22, false)]
theorem step107 (p : Nat → Bool) (h : Constraints p) : clause p c107 = true := by
  simpa only [c107,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause107
def c108 : List Lit := [(23, false), (147, true), (21, true), (22, true)]
theorem step108 (p : Nat → Bool) (h : Constraints p) : clause p c108 = true := by
  simpa only [c108,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause108
def c109 : List Lit := [(23, false), (147, true), (18, true), (22, true)]
theorem step109 (p : Nat → Bool) (h : Constraints p) : clause p c109 = true := by
  simpa only [c109,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause109
def c110 : List Lit := [(24, false), (14, false), (25, false), (28, false)]
theorem step110 (p : Nat → Bool) (h : Constraints p) : clause p c110 = true := by
  simpa only [c110,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause110
def c111 : List Lit := [(24, false), (25, false), (26, false), (28, false)]
theorem step111 (p : Nat → Bool) (h : Constraints p) : clause p c111 = true := by
  simpa only [c111,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause111
def c112 : List Lit := [(24, false), (148, true), (25, true), (26, true), (28, true)]
theorem step112 (p : Nat → Bool) (h : Constraints p) : clause p c112 = true := by
  simpa only [c112,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause112
def c113 : List Lit := [(24, false), (148, true), (14, true), (26, true), (28, true)]
theorem step113 (p : Nat → Bool) (h : Constraints p) : clause p c113 = true := by
  simpa only [c113,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause113
def c114 : List Lit := [(24, false), (148, true), (14, true), (25, true), (28, true)]
theorem step114 (p : Nat → Bool) (h : Constraints p) : clause p c114 = true := by
  simpa only [c114,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause114
def c115 : List Lit := [(25, false), (8, false), (15, false), (24, false)]
theorem step115 (p : Nat → Bool) (h : Constraints p) : clause p c115 = true := by
  simpa only [c115,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause115
def c116 : List Lit := [(25, false), (8, false), (15, false), (29, false)]
theorem step116 (p : Nat → Bool) (h : Constraints p) : clause p c116 = true := by
  simpa only [c116,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause116
def c117 : List Lit := [(25, false), (8, false), (15, false), (60, false)]
theorem step117 (p : Nat → Bool) (h : Constraints p) : clause p c117 = true := by
  simpa only [c117,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause117
def c118 : List Lit := [(25, false), (8, false), (24, false), (27, false)]
theorem step118 (p : Nat → Bool) (h : Constraints p) : clause p c118 = true := by
  simpa only [c118,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause118
def c119 : List Lit := [(25, false), (8, false), (24, false), (29, false)]
theorem step119 (p : Nat → Bool) (h : Constraints p) : clause p c119 = true := by
  simpa only [c119,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause119
def c120 : List Lit := [(25, false), (8, false), (24, false), (60, false)]
theorem step120 (p : Nat → Bool) (h : Constraints p) : clause p c120 = true := by
  simpa only [c120,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause120
def c121 : List Lit := [(25, false), (8, false), (27, false), (29, false)]
theorem step121 (p : Nat → Bool) (h : Constraints p) : clause p c121 = true := by
  simpa only [c121,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause121
def c122 : List Lit := [(25, false), (8, false), (27, false), (60, false)]
theorem step122 (p : Nat → Bool) (h : Constraints p) : clause p c122 = true := by
  simpa only [c122,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause122
def c123 : List Lit := [(25, false), (8, false), (29, false), (60, false)]
theorem step123 (p : Nat → Bool) (h : Constraints p) : clause p c123 = true := by
  simpa only [c123,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause123
def c124 : List Lit := [(25, false), (15, false), (24, false), (27, false)]
theorem step124 (p : Nat → Bool) (h : Constraints p) : clause p c124 = true := by
  simpa only [c124,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause124
def c125 : List Lit := [(25, false), (15, false), (24, false), (29, false)]
theorem step125 (p : Nat → Bool) (h : Constraints p) : clause p c125 = true := by
  simpa only [c125,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause125
def c126 : List Lit := [(25, false), (15, false), (24, false), (60, false)]
theorem step126 (p : Nat → Bool) (h : Constraints p) : clause p c126 = true := by
  simpa only [c126,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause126
def c127 : List Lit := [(25, false), (15, false), (27, false), (60, false)]
theorem step127 (p : Nat → Bool) (h : Constraints p) : clause p c127 = true := by
  simpa only [c127,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause127
def c128 : List Lit := [(25, false), (15, false), (29, false), (60, false)]
theorem step128 (p : Nat → Bool) (h : Constraints p) : clause p c128 = true := by
  simpa only [c128,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause128
def c129 : List Lit := [(25, false), (24, false), (27, false), (29, false)]
theorem step129 (p : Nat → Bool) (h : Constraints p) : clause p c129 = true := by
  simpa only [c129,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause129
def c130 : List Lit := [(25, false), (24, false), (27, false), (60, false)]
theorem step130 (p : Nat → Bool) (h : Constraints p) : clause p c130 = true := by
  simpa only [c130,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause130
def c131 : List Lit := [(25, false), (24, false), (29, false), (60, false)]
theorem step131 (p : Nat → Bool) (h : Constraints p) : clause p c131 = true := by
  simpa only [c131,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause131
def c132 : List Lit := [(25, false), (27, false), (29, false), (60, false)]
theorem step132 (p : Nat → Bool) (h : Constraints p) : clause p c132 = true := by
  simpa only [c132,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause132
def c133 : List Lit := [(25, false), (149, true), (8, true), (15, true), (27, true), (29, true), (60, true)]
theorem step133 (p : Nat → Bool) (h : Constraints p) : clause p c133 = true := by
  simpa only [c133,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause133
def c134 : List Lit := [(26, false), (16, false), (24, false), (27, false)]
theorem step134 (p : Nat → Bool) (h : Constraints p) : clause p c134 = true := by
  simpa only [c134,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause134
def c135 : List Lit := [(26, false), (16, false), (24, false), (30, false)]
theorem step135 (p : Nat → Bool) (h : Constraints p) : clause p c135 = true := by
  simpa only [c135,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause135
def c136 : List Lit := [(26, false), (16, false), (24, false), (61, false)]
theorem step136 (p : Nat → Bool) (h : Constraints p) : clause p c136 = true := by
  simpa only [c136,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause136
def c137 : List Lit := [(26, false), (16, false), (24, false), (78, false)]
theorem step137 (p : Nat → Bool) (h : Constraints p) : clause p c137 = true := by
  simpa only [c137,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause137
def c138 : List Lit := [(26, false), (16, false), (27, false), (30, false)]
theorem step138 (p : Nat → Bool) (h : Constraints p) : clause p c138 = true := by
  simpa only [c138,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause138
def c139 : List Lit := [(26, false), (16, false), (27, false), (61, false)]
theorem step139 (p : Nat → Bool) (h : Constraints p) : clause p c139 = true := by
  simpa only [c139,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause139
def c140 : List Lit := [(26, false), (16, false), (27, false), (78, false)]
theorem step140 (p : Nat → Bool) (h : Constraints p) : clause p c140 = true := by
  simpa only [c140,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause140
def c141 : List Lit := [(26, false), (16, false), (30, false), (61, false)]
theorem step141 (p : Nat → Bool) (h : Constraints p) : clause p c141 = true := by
  simpa only [c141,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause141
def c142 : List Lit := [(26, false), (16, false), (30, false), (78, false)]
theorem step142 (p : Nat → Bool) (h : Constraints p) : clause p c142 = true := by
  simpa only [c142,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause142
def c143 : List Lit := [(26, false), (16, false), (61, false), (78, false)]
theorem step143 (p : Nat → Bool) (h : Constraints p) : clause p c143 = true := by
  simpa only [c143,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause143
def c144 : List Lit := [(26, false), (24, false), (27, false), (30, false)]
theorem step144 (p : Nat → Bool) (h : Constraints p) : clause p c144 = true := by
  simpa only [c144,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause144
def c145 : List Lit := [(26, false), (24, false), (27, false), (61, false)]
theorem step145 (p : Nat → Bool) (h : Constraints p) : clause p c145 = true := by
  simpa only [c145,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause145
def c146 : List Lit := [(26, false), (24, false), (27, false), (78, false)]
theorem step146 (p : Nat → Bool) (h : Constraints p) : clause p c146 = true := by
  simpa only [c146,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause146
def c147 : List Lit := [(26, false), (24, false), (30, false), (61, false)]
theorem step147 (p : Nat → Bool) (h : Constraints p) : clause p c147 = true := by
  simpa only [c147,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause147
def c148 : List Lit := [(26, false), (24, false), (30, false), (78, false)]
theorem step148 (p : Nat → Bool) (h : Constraints p) : clause p c148 = true := by
  simpa only [c148,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause148
def c149 : List Lit := [(26, false), (24, false), (61, false), (78, false)]
theorem step149 (p : Nat → Bool) (h : Constraints p) : clause p c149 = true := by
  simpa only [c149,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause149
def c150 : List Lit := [(26, false), (27, false), (30, false), (61, false)]
theorem step150 (p : Nat → Bool) (h : Constraints p) : clause p c150 = true := by
  simpa only [c150,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause150
def c151 : List Lit := [(26, false), (27, false), (30, false), (78, false)]
theorem step151 (p : Nat → Bool) (h : Constraints p) : clause p c151 = true := by
  simpa only [c151,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause151
def c152 : List Lit := [(26, false), (27, false), (61, false), (78, false)]
theorem step152 (p : Nat → Bool) (h : Constraints p) : clause p c152 = true := by
  simpa only [c152,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause152
def c153 : List Lit := [(26, false), (30, false), (61, false), (78, false)]
theorem step153 (p : Nat → Bool) (h : Constraints p) : clause p c153 = true := by
  simpa only [c153,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause153
def c154 : List Lit := [(27, false), (17, false), (25, false), (79, false)]
theorem step154 (p : Nat → Bool) (h : Constraints p) : clause p c154 = true := by
  simpa only [c154,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause154
def c155 : List Lit := [(27, false), (151, true), (25, true), (26, true), (62, true), (79, true)]
theorem step155 (p : Nat → Bool) (h : Constraints p) : clause p c155 = true := by
  simpa only [c155,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause155
def c156 : List Lit := [(28, false), (9, false), (24, false), (31, false)]
theorem step156 (p : Nat → Bool) (h : Constraints p) : clause p c156 = true := by
  simpa only [c156,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause156
def c157 : List Lit := [(28, false), (9, false), (24, false), (80, false)]
theorem step157 (p : Nat → Bool) (h : Constraints p) : clause p c157 = true := by
  simpa only [c157,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause157
def c158 : List Lit := [(28, false), (9, false), (31, false), (80, false)]
theorem step158 (p : Nat → Bool) (h : Constraints p) : clause p c158 = true := by
  simpa only [c158,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause158
def c159 : List Lit := [(28, false), (24, false), (31, false), (80, false)]
theorem step159 (p : Nat → Bool) (h : Constraints p) : clause p c159 = true := by
  simpa only [c159,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause159
def c160 : List Lit := [(29, false), (10, false), (19, false), (25, false)]
theorem step160 (p : Nat → Bool) (h : Constraints p) : clause p c160 = true := by
  simpa only [c160,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause160
def c161 : List Lit := [(29, false), (10, false), (19, false), (67, false)]
theorem step161 (p : Nat → Bool) (h : Constraints p) : clause p c161 = true := by
  simpa only [c161,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause161
def c162 : List Lit := [(29, false), (10, false), (25, false), (67, false)]
theorem step162 (p : Nat → Bool) (h : Constraints p) : clause p c162 = true := by
  simpa only [c162,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause162
def c163 : List Lit := [(29, false), (19, false), (25, false), (67, false)]
theorem step163 (p : Nat → Bool) (h : Constraints p) : clause p c163 = true := by
  simpa only [c163,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause163
def c164 : List Lit := [(29, false), (153, true), (19, true), (25, true), (67, true)]
theorem step164 (p : Nat → Bool) (h : Constraints p) : clause p c164 = true := by
  simpa only [c164,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause164
def c165 : List Lit := [(29, false), (153, true), (10, true), (25, true), (67, true)]
theorem step165 (p : Nat → Bool) (h : Constraints p) : clause p c165 = true := by
  simpa only [c165,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause165
def c166 : List Lit := [(29, false), (153, true), (10, true), (19, true), (67, true)]
theorem step166 (p : Nat → Bool) (h : Constraints p) : clause p c166 = true := by
  simpa only [c166,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause166
def c167 : List Lit := [(29, false), (153, true), (10, true), (19, true), (25, true)]
theorem step167 (p : Nat → Bool) (h : Constraints p) : clause p c167 = true := by
  simpa only [c167,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause167
def c168 : List Lit := [(30, false), (11, false), (26, false), (32, false)]
theorem step168 (p : Nat → Bool) (h : Constraints p) : clause p c168 = true := by
  simpa only [c168,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause168
def c169 : List Lit := [(30, false), (11, false), (32, false), (82, false)]
theorem step169 (p : Nat → Bool) (h : Constraints p) : clause p c169 = true := by
  simpa only [c169,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause169
def c170 : List Lit := [(30, false), (26, false), (32, false), (82, false)]
theorem step170 (p : Nat → Bool) (h : Constraints p) : clause p c170 = true := by
  simpa only [c170,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause170
def c171 : List Lit := [(30, false), (154, true), (26, true), (32, true), (82, true)]
theorem step171 (p : Nat → Bool) (h : Constraints p) : clause p c171 = true := by
  simpa only [c171,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause171
def c172 : List Lit := [(30, false), (154, true), (11, true), (32, true), (82, true)]
theorem step172 (p : Nat → Bool) (h : Constraints p) : clause p c172 = true := by
  simpa only [c172,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause172
def c173 : List Lit := [(30, false), (154, true), (11, true), (26, true), (82, true)]
theorem step173 (p : Nat → Bool) (h : Constraints p) : clause p c173 = true := by
  simpa only [c173,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause173
def c174 : List Lit := [(30, false), (154, true), (11, true), (26, true), (32, true)]
theorem step174 (p : Nat → Bool) (h : Constraints p) : clause p c174 = true := by
  simpa only [c174,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause174
def c175 : List Lit := [(31, false), (20, false), (28, false), (32, false)]
theorem step175 (p : Nat → Bool) (h : Constraints p) : clause p c175 = true := by
  simpa only [c175,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause175
def c176 : List Lit := [(31, false), (155, true), (28, true), (32, true)]
theorem step176 (p : Nat → Bool) (h : Constraints p) : clause p c176 = true := by
  simpa only [c176,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause176
def c177 : List Lit := [(31, false), (155, true), (20, true), (32, true)]
theorem step177 (p : Nat → Bool) (h : Constraints p) : clause p c177 = true := by
  simpa only [c177,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause177
def c178 : List Lit := [(31, false), (155, true), (20, true), (28, true)]
theorem step178 (p : Nat → Bool) (h : Constraints p) : clause p c178 = true := by
  simpa only [c178,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause178
def c179 : List Lit := [(32, false), (22, false), (30, false), (31, false)]
theorem step179 (p : Nat → Bool) (h : Constraints p) : clause p c179 = true := by
  simpa only [c179,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause179
def c180 : List Lit := [(32, false), (156, true), (22, true), (31, true)]
theorem step180 (p : Nat → Bool) (h : Constraints p) : clause p c180 = true := by
  simpa only [c180,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause180
def c181 : List Lit := [(32, false), (156, true), (22, true), (30, true)]
theorem step181 (p : Nat → Bool) (h : Constraints p) : clause p c181 = true := by
  simpa only [c181,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause181
def c182 : List Lit := [(33, false), (157, true), (35, true), (42, true)]
theorem step182 (p : Nat → Bool) (h : Constraints p) : clause p c182 = true := by
  simpa only [c182,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause182
def c183 : List Lit := [(33, false), (157, true), (34, true), (42, true)]
theorem step183 (p : Nat → Bool) (h : Constraints p) : clause p c183 = true := by
  simpa only [c183,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause183
def c184 : List Lit := [(34, false), (158, true), (33, true), (36, true), (43, true), (86, true)]
theorem step184 (p : Nat → Bool) (h : Constraints p) : clause p c184 = true := by
  simpa only [c184,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause184
def c185 : List Lit := [(34, false), (158, true), (33, true), (36, true), (43, true), (51, true)]
theorem step185 (p : Nat → Bool) (h : Constraints p) : clause p c185 = true := by
  simpa only [c185,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause185
def c186 : List Lit := [(35, false), (159, true), (36, true)]
theorem step186 (p : Nat → Bool) (h : Constraints p) : clause p c186 = true := by
  simpa only [c186,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause186
def c187 : List Lit := [(35, false), (159, true), (33, true)]
theorem step187 (p : Nat → Bool) (h : Constraints p) : clause p c187 = true := by
  simpa only [c187,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause187
def c188 : List Lit := [(36, false), (34, false), (35, false), (38, false)]
theorem step188 (p : Nat → Bool) (h : Constraints p) : clause p c188 = true := by
  simpa only [c188,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause188
def c189 : List Lit := [(36, false), (34, false), (37, false), (38, false)]
theorem step189 (p : Nat → Bool) (h : Constraints p) : clause p c189 = true := by
  simpa only [c189,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause189
def c190 : List Lit := [(36, false), (35, false), (37, false), (38, false)]
theorem step190 (p : Nat → Bool) (h : Constraints p) : clause p c190 = true := by
  simpa only [c190,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause190
def c191 : List Lit := [(36, false), (160, true), (34, true), (37, true), (38, true)]
theorem step191 (p : Nat → Bool) (h : Constraints p) : clause p c191 = true := by
  simpa only [c191,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause191
def c192 : List Lit := [(37, false), (36, false), (41, false), (89, false)]
theorem step192 (p : Nat → Bool) (h : Constraints p) : clause p c192 = true := by
  simpa only [c192,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause192
def c193 : List Lit := [(37, false), (161, true), (36, true), (89, true)]
theorem step193 (p : Nat → Bool) (h : Constraints p) : clause p c193 = true := by
  simpa only [c193,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause193
def c194 : List Lit := [(37, false), (161, true), (36, true), (41, true)]
theorem step194 (p : Nat → Bool) (h : Constraints p) : clause p c194 = true := by
  simpa only [c194,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause194
def c195 : List Lit := [(38, false), (36, false), (41, false), (57, false)]
theorem step195 (p : Nat → Bool) (h : Constraints p) : clause p c195 = true := by
  simpa only [c195,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause195
def c196 : List Lit := [(38, false), (162, true), (36, true), (57, true)]
theorem step196 (p : Nat → Bool) (h : Constraints p) : clause p c196 = true := by
  simpa only [c196,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause196
def c197 : List Lit := [(39, false), (40, false), (49, false), (58, false)]
theorem step197 (p : Nat → Bool) (h : Constraints p) : clause p c197 = true := by
  simpa only [c197,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause197
def c198 : List Lit := [(39, false), (163, true), (49, true), (58, true)]
theorem step198 (p : Nat → Bool) (h : Constraints p) : clause p c198 = true := by
  simpa only [c198,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause198
def c199 : List Lit := [(40, false), (164, true), (41, true)]
theorem step199 (p : Nat → Bool) (h : Constraints p) : clause p c199 = true := by
  simpa only [c199,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause199
def c200 : List Lit := [(40, false), (164, true), (39, true)]
theorem step200 (p : Nat → Bool) (h : Constraints p) : clause p c200 = true := by
  simpa only [c200,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause200
def c201 : List Lit := [(41, false), (37, false), (38, false), (40, false)]
theorem step201 (p : Nat → Bool) (h : Constraints p) : clause p c201 = true := by
  simpa only [c201,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause201
def c202 : List Lit := [(41, false), (165, true), (37, true), (38, true)]
theorem step202 (p : Nat → Bool) (h : Constraints p) : clause p c202 = true := by
  simpa only [c202,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause202
def c203 : List Lit := [(42, false), (33, false), (43, false), (44, false)]
theorem step203 (p : Nat → Bool) (h : Constraints p) : clause p c203 = true := by
  simpa only [c203,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause203
def c204 : List Lit := [(42, false), (33, false), (43, false), (46, false)]
theorem step204 (p : Nat → Bool) (h : Constraints p) : clause p c204 = true := by
  simpa only [c204,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause204
def c205 : List Lit := [(42, false), (33, false), (44, false), (46, false)]
theorem step205 (p : Nat → Bool) (h : Constraints p) : clause p c205 = true := by
  simpa only [c205,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause205
def c206 : List Lit := [(42, false), (166, true), (43, true), (44, true), (46, true)]
theorem step206 (p : Nat → Bool) (h : Constraints p) : clause p c206 = true := by
  simpa only [c206,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause206
def c207 : List Lit := [(42, false), (166, true), (33, true), (44, true), (46, true)]
theorem step207 (p : Nat → Bool) (h : Constraints p) : clause p c207 = true := by
  simpa only [c207,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause207
def c208 : List Lit := [(43, false), (8, false), (34, false), (42, false)]
theorem step208 (p : Nat → Bool) (h : Constraints p) : clause p c208 = true := by
  simpa only [c208,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause208
def c209 : List Lit := [(43, false), (8, false), (34, false), (47, false)]
theorem step209 (p : Nat → Bool) (h : Constraints p) : clause p c209 = true := by
  simpa only [c209,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause209
def c210 : List Lit := [(43, false), (8, false), (34, false), (60, false)]
theorem step210 (p : Nat → Bool) (h : Constraints p) : clause p c210 = true := by
  simpa only [c210,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause210
def c211 : List Lit := [(43, false), (8, false), (42, false), (47, false)]
theorem step211 (p : Nat → Bool) (h : Constraints p) : clause p c211 = true := by
  simpa only [c211,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause211
def c212 : List Lit := [(43, false), (8, false), (42, false), (60, false)]
theorem step212 (p : Nat → Bool) (h : Constraints p) : clause p c212 = true := by
  simpa only [c212,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause212
def c213 : List Lit := [(43, false), (8, false), (47, false), (60, false)]
theorem step213 (p : Nat → Bool) (h : Constraints p) : clause p c213 = true := by
  simpa only [c213,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause213
def c214 : List Lit := [(43, false), (34, false), (42, false), (47, false)]
theorem step214 (p : Nat → Bool) (h : Constraints p) : clause p c214 = true := by
  simpa only [c214,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause214
def c215 : List Lit := [(43, false), (34, false), (42, false), (60, false)]
theorem step215 (p : Nat → Bool) (h : Constraints p) : clause p c215 = true := by
  simpa only [c215,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause215
def c216 : List Lit := [(43, false), (34, false), (47, false), (60, false)]
theorem step216 (p : Nat → Bool) (h : Constraints p) : clause p c216 = true := by
  simpa only [c216,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause216
def c217 : List Lit := [(43, false), (42, false), (47, false), (60, false)]
theorem step217 (p : Nat → Bool) (h : Constraints p) : clause p c217 = true := by
  simpa only [c217,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause217
def c218 : List Lit := [(44, false), (9, false), (42, false), (45, false)]
theorem step218 (p : Nat → Bool) (h : Constraints p) : clause p c218 = true := by
  simpa only [c218,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause218
def c219 : List Lit := [(44, false), (9, false), (42, false), (49, false)]
theorem step219 (p : Nat → Bool) (h : Constraints p) : clause p c219 = true := by
  simpa only [c219,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause219
def c220 : List Lit := [(44, false), (9, false), (45, false), (49, false)]
theorem step220 (p : Nat → Bool) (h : Constraints p) : clause p c220 = true := by
  simpa only [c220,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause220
def c221 : List Lit := [(44, false), (9, false), (45, false), (96, false)]
theorem step221 (p : Nat → Bool) (h : Constraints p) : clause p c221 = true := by
  simpa only [c221,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause221
def c222 : List Lit := [(44, false), (9, false), (49, false), (96, false)]
theorem step222 (p : Nat → Bool) (h : Constraints p) : clause p c222 = true := by
  simpa only [c222,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause222
def c223 : List Lit := [(44, false), (42, false), (45, false), (49, false)]
theorem step223 (p : Nat → Bool) (h : Constraints p) : clause p c223 = true := by
  simpa only [c223,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause223
def c224 : List Lit := [(44, false), (42, false), (45, false), (96, false)]
theorem step224 (p : Nat → Bool) (h : Constraints p) : clause p c224 = true := by
  simpa only [c224,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause224
def c225 : List Lit := [(44, false), (42, false), (49, false), (96, false)]
theorem step225 (p : Nat → Bool) (h : Constraints p) : clause p c225 = true := by
  simpa only [c225,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause225
def c226 : List Lit := [(44, false), (45, false), (49, false), (96, false)]
theorem step226 (p : Nat → Bool) (h : Constraints p) : clause p c226 = true := by
  simpa only [c226,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause226
def c227 : List Lit := [(44, false), (168, true), (9, true), (42, true), (49, true), (96, true)]
theorem step227 (p : Nat → Bool) (h : Constraints p) : clause p c227 = true := by
  simpa only [c227,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause227
def c228 : List Lit := [(45, false), (44, false), (50, false), (64, false)]
theorem step228 (p : Nat → Bool) (h : Constraints p) : clause p c228 = true := by
  simpa only [c228,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause228
def c229 : List Lit := [(45, false), (169, true), (50, true), (64, true)]
theorem step229 (p : Nat → Bool) (h : Constraints p) : clause p c229 = true := by
  simpa only [c229,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause229
def c230 : List Lit := [(45, false), (169, true), (44, true), (64, true)]
theorem step230 (p : Nat → Bool) (h : Constraints p) : clause p c230 = true := by
  simpa only [c230,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause230
def c231 : List Lit := [(45, false), (169, true), (44, true), (50, true)]
theorem step231 (p : Nat → Bool) (h : Constraints p) : clause p c231 = true := by
  simpa only [c231,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause231
def c232 : List Lit := [(46, false), (42, false), (47, false), (48, false)]
theorem step232 (p : Nat → Bool) (h : Constraints p) : clause p c232 = true := by
  simpa only [c232,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause232
def c233 : List Lit := [(46, false), (42, false), (47, false), (49, false)]
theorem step233 (p : Nat → Bool) (h : Constraints p) : clause p c233 = true := by
  simpa only [c233,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause233
def c234 : List Lit := [(46, false), (42, false), (47, false), (66, false)]
theorem step234 (p : Nat → Bool) (h : Constraints p) : clause p c234 = true := by
  simpa only [c234,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause234
def c235 : List Lit := [(46, false), (42, false), (48, false), (49, false)]
theorem step235 (p : Nat → Bool) (h : Constraints p) : clause p c235 = true := by
  simpa only [c235,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause235
def c236 : List Lit := [(46, false), (42, false), (48, false), (66, false)]
theorem step236 (p : Nat → Bool) (h : Constraints p) : clause p c236 = true := by
  simpa only [c236,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause236
def c237 : List Lit := [(46, false), (42, false), (49, false), (66, false)]
theorem step237 (p : Nat → Bool) (h : Constraints p) : clause p c237 = true := by
  simpa only [c237,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause237
def c238 : List Lit := [(46, false), (47, false), (48, false), (49, false)]
theorem step238 (p : Nat → Bool) (h : Constraints p) : clause p c238 = true := by
  simpa only [c238,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause238
def c239 : List Lit := [(46, false), (47, false), (48, false), (66, false)]
theorem step239 (p : Nat → Bool) (h : Constraints p) : clause p c239 = true := by
  simpa only [c239,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause239
def c240 : List Lit := [(46, false), (47, false), (49, false), (66, false)]
theorem step240 (p : Nat → Bool) (h : Constraints p) : clause p c240 = true := by
  simpa only [c240,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause240
def c241 : List Lit := [(46, false), (48, false), (49, false), (66, false)]
theorem step241 (p : Nat → Bool) (h : Constraints p) : clause p c241 = true := by
  simpa only [c241,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause241
def c242 : List Lit := [(46, false), (170, true), (42, true), (47, true), (49, true), (66, true)]
theorem step242 (p : Nat → Bool) (h : Constraints p) : clause p c242 = true := by
  simpa only [c242,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause242
def c243 : List Lit := [(47, false), (10, false), (43, false), (46, false)]
theorem step243 (p : Nat → Bool) (h : Constraints p) : clause p c243 = true := by
  simpa only [c243,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause243
def c244 : List Lit := [(47, false), (10, false), (46, false), (67, false)]
theorem step244 (p : Nat → Bool) (h : Constraints p) : clause p c244 = true := by
  simpa only [c244,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause244
def c245 : List Lit := [(47, false), (43, false), (46, false), (67, false)]
theorem step245 (p : Nat → Bool) (h : Constraints p) : clause p c245 = true := by
  simpa only [c245,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause245
def c246 : List Lit := [(47, false), (171, true), (43, true), (46, true), (67, true)]
theorem step246 (p : Nat → Bool) (h : Constraints p) : clause p c246 = true := by
  simpa only [c246,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause246
def c247 : List Lit := [(47, false), (171, true), (10, true), (46, true), (67, true)]
theorem step247 (p : Nat → Bool) (h : Constraints p) : clause p c247 = true := by
  simpa only [c247,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause247
def c248 : List Lit := [(47, false), (171, true), (10, true), (43, true), (67, true)]
theorem step248 (p : Nat → Bool) (h : Constraints p) : clause p c248 = true := by
  simpa only [c248,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause248
def c249 : List Lit := [(47, false), (171, true), (10, true), (43, true), (46, true)]
theorem step249 (p : Nat → Bool) (h : Constraints p) : clause p c249 = true := by
  simpa only [c249,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause249
def c250 : List Lit := [(48, false), (11, false), (46, false), (50, false)]
theorem step250 (p : Nat → Bool) (h : Constraints p) : clause p c250 = true := by
  simpa only [c250,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause250
def c251 : List Lit := [(48, false), (172, true), (46, true), (50, true), (98, true)]
theorem step251 (p : Nat → Bool) (h : Constraints p) : clause p c251 = true := by
  simpa only [c251,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause251
def c252 : List Lit := [(48, false), (172, true), (11, true), (46, true), (98, true)]
theorem step252 (p : Nat → Bool) (h : Constraints p) : clause p c252 = true := by
  simpa only [c252,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause252
def c253 : List Lit := [(48, false), (172, true), (11, true), (46, true), (50, true)]
theorem step253 (p : Nat → Bool) (h : Constraints p) : clause p c253 = true := by
  simpa only [c253,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause253
def c254 : List Lit := [(49, false), (39, false), (44, false), (46, false)]
theorem step254 (p : Nat → Bool) (h : Constraints p) : clause p c254 = true := by
  simpa only [c254,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause254
def c255 : List Lit := [(49, false), (39, false), (44, false), (50, false)]
theorem step255 (p : Nat → Bool) (h : Constraints p) : clause p c255 = true := by
  simpa only [c255,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause255
def c256 : List Lit := [(49, false), (39, false), (46, false), (50, false)]
theorem step256 (p : Nat → Bool) (h : Constraints p) : clause p c256 = true := by
  simpa only [c256,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause256
def c257 : List Lit := [(49, false), (44, false), (46, false), (50, false)]
theorem step257 (p : Nat → Bool) (h : Constraints p) : clause p c257 = true := by
  simpa only [c257,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause257
def c258 : List Lit := [(49, false), (173, true), (44, true), (46, true), (50, true)]
theorem step258 (p : Nat → Bool) (h : Constraints p) : clause p c258 = true := by
  simpa only [c258,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause258
def c259 : List Lit := [(49, false), (173, true), (39, true), (46, true), (50, true)]
theorem step259 (p : Nat → Bool) (h : Constraints p) : clause p c259 = true := by
  simpa only [c259,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause259
def c260 : List Lit := [(49, false), (173, true), (39, true), (44, true), (50, true)]
theorem step260 (p : Nat → Bool) (h : Constraints p) : clause p c260 = true := by
  simpa only [c260,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause260
def c261 : List Lit := [(49, false), (173, true), (39, true), (44, true), (46, true)]
theorem step261 (p : Nat → Bool) (h : Constraints p) : clause p c261 = true := by
  simpa only [c261,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause261
def c262 : List Lit := [(50, false), (45, false), (48, false), (49, false)]
theorem step262 (p : Nat → Bool) (h : Constraints p) : clause p c262 = true := by
  simpa only [c262,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause262
def c263 : List Lit := [(174, false), (45, false), (48, false)]
theorem step263 (p : Nat → Bool) (h : Constraints p) : clause p c263 = true := by
  simpa only [c263,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause263
def c264 : List Lit := [(50, false), (174, true), (48, true), (49, true)]
theorem step264 (p : Nat → Bool) (h : Constraints p) : clause p c264 = true := by
  simpa only [c264,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause264
def c265 : List Lit := [(51, false), (15, false), (34, false), (53, false)]
theorem step265 (p : Nat → Bool) (h : Constraints p) : clause p c265 = true := by
  simpa only [c265,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause265
def c266 : List Lit := [(51, false), (15, false), (53, false), (60, false)]
theorem step266 (p : Nat → Bool) (h : Constraints p) : clause p c266 = true := by
  simpa only [c266,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause266
def c267 : List Lit := [(51, false), (34, false), (53, false), (60, false)]
theorem step267 (p : Nat → Bool) (h : Constraints p) : clause p c267 = true := by
  simpa only [c267,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause267
def c268 : List Lit := [(51, false), (34, false), (53, false), (103, false)]
theorem step268 (p : Nat → Bool) (h : Constraints p) : clause p c268 = true := by
  simpa only [c268,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause268
def c269 : List Lit := [(51, false), (53, false), (60, false), (103, false)]
theorem step269 (p : Nat → Bool) (h : Constraints p) : clause p c269 = true := by
  simpa only [c269,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause269
def c270 : List Lit := [(52, false), (53, false), (54, false), (58, false)]
theorem step270 (p : Nat → Bool) (h : Constraints p) : clause p c270 = true := by
  simpa only [c270,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause270
def c271 : List Lit := [(52, false), (176, true), (54, true), (58, true)]
theorem step271 (p : Nat → Bool) (h : Constraints p) : clause p c271 = true := by
  simpa only [c271,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause271
def c272 : List Lit := [(52, false), (176, true), (53, true), (58, true)]
theorem step272 (p : Nat → Bool) (h : Constraints p) : clause p c272 = true := by
  simpa only [c272,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause272
def c273 : List Lit := [(53, false), (51, false), (52, false), (63, false)]
theorem step273 (p : Nat → Bool) (h : Constraints p) : clause p c273 = true := by
  simpa only [c273,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause273
def c274 : List Lit := [(53, false), (177, true), (52, true), (63, true)]
theorem step274 (p : Nat → Bool) (h : Constraints p) : clause p c274 = true := by
  simpa only [c274,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause274
def c275 : List Lit := [(53, false), (177, true), (51, true), (63, true)]
theorem step275 (p : Nat → Bool) (h : Constraints p) : clause p c275 = true := by
  simpa only [c275,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause275
def c276 : List Lit := [(53, false), (177, true), (51, true), (52, true)]
theorem step276 (p : Nat → Bool) (h : Constraints p) : clause p c276 = true := by
  simpa only [c276,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause276
def c277 : List Lit := [(54, false), (52, false), (59, false), (64, false)]
theorem step277 (p : Nat → Bool) (h : Constraints p) : clause p c277 = true := by
  simpa only [c277,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause277
def c278 : List Lit := [(54, false), (178, true), (59, true), (64, true)]
theorem step278 (p : Nat → Bool) (h : Constraints p) : clause p c278 = true := by
  simpa only [c278,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause278
def c279 : List Lit := [(54, false), (178, true), (52, true), (64, true)]
theorem step279 (p : Nat → Bool) (h : Constraints p) : clause p c279 = true := by
  simpa only [c279,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause279
def c280 : List Lit := [(54, false), (178, true), (52, true), (59, true)]
theorem step280 (p : Nat → Bool) (h : Constraints p) : clause p c280 = true := by
  simpa only [c280,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause280
def c281 : List Lit := [(55, false), (56, false), (58, false), (66, false)]
theorem step281 (p : Nat → Bool) (h : Constraints p) : clause p c281 = true := by
  simpa only [c281,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause281
def c282 : List Lit := [(55, false), (56, false), (58, false), (107, false)]
theorem step282 (p : Nat → Bool) (h : Constraints p) : clause p c282 = true := by
  simpa only [c282,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause282
def c283 : List Lit := [(55, false), (56, false), (66, false), (107, false)]
theorem step283 (p : Nat → Bool) (h : Constraints p) : clause p c283 = true := by
  simpa only [c283,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause283
def c284 : List Lit := [(55, false), (58, false), (66, false), (107, false)]
theorem step284 (p : Nat → Bool) (h : Constraints p) : clause p c284 = true := by
  simpa only [c284,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause284
def c285 : List Lit := [(55, false), (179, true), (58, true), (66, true), (107, true)]
theorem step285 (p : Nat → Bool) (h : Constraints p) : clause p c285 = true := by
  simpa only [c285,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause285
def c286 : List Lit := [(55, false), (179, true), (56, true), (58, true), (107, true)]
theorem step286 (p : Nat → Bool) (h : Constraints p) : clause p c286 = true := by
  simpa only [c286,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause286
def c287 : List Lit := [(56, false), (55, false), (57, false), (59, false)]
theorem step287 (p : Nat → Bool) (h : Constraints p) : clause p c287 = true := by
  simpa only [c287,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause287
def c288 : List Lit := [(56, false), (180, true), (57, true), (59, true)]
theorem step288 (p : Nat → Bool) (h : Constraints p) : clause p c288 = true := by
  simpa only [c288,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause288
def c289 : List Lit := [(56, false), (180, true), (55, true), (59, true)]
theorem step289 (p : Nat → Bool) (h : Constraints p) : clause p c289 = true := by
  simpa only [c289,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause289
def c290 : List Lit := [(56, false), (180, true), (55, true), (57, true)]
theorem step290 (p : Nat → Bool) (h : Constraints p) : clause p c290 = true := by
  simpa only [c290,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause290
def c291 : List Lit := [(57, false), (38, false), (56, false), (68, false)]
theorem step291 (p : Nat → Bool) (h : Constraints p) : clause p c291 = true := by
  simpa only [c291,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause291
def c292 : List Lit := [(57, false), (38, false), (56, false), (109, false)]
theorem step292 (p : Nat → Bool) (h : Constraints p) : clause p c292 = true := by
  simpa only [c292,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause292
def c293 : List Lit := [(57, false), (38, false), (68, false), (109, false)]
theorem step293 (p : Nat → Bool) (h : Constraints p) : clause p c293 = true := by
  simpa only [c293,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause293
def c294 : List Lit := [(57, false), (56, false), (68, false), (109, false)]
theorem step294 (p : Nat → Bool) (h : Constraints p) : clause p c294 = true := by
  simpa only [c294,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause294
def c295 : List Lit := [(58, false), (20, false), (39, false), (55, false)]
theorem step295 (p : Nat → Bool) (h : Constraints p) : clause p c295 = true := by
  simpa only [c295,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause295
def c296 : List Lit := [(58, false), (20, false), (39, false), (59, false)]
theorem step296 (p : Nat → Bool) (h : Constraints p) : clause p c296 = true := by
  simpa only [c296,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause296
def c297 : List Lit := [(58, false), (20, false), (52, false), (55, false)]
theorem step297 (p : Nat → Bool) (h : Constraints p) : clause p c297 = true := by
  simpa only [c297,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause297
def c298 : List Lit := [(58, false), (20, false), (52, false), (59, false)]
theorem step298 (p : Nat → Bool) (h : Constraints p) : clause p c298 = true := by
  simpa only [c298,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause298
def c299 : List Lit := [(58, false), (20, false), (55, false), (59, false)]
theorem step299 (p : Nat → Bool) (h : Constraints p) : clause p c299 = true := by
  simpa only [c299,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause299
def c300 : List Lit := [(58, false), (20, false), (55, false), (110, false)]
theorem step300 (p : Nat → Bool) (h : Constraints p) : clause p c300 = true := by
  simpa only [c300,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause300
def c301 : List Lit := [(58, false), (39, false), (52, false), (55, false)]
theorem step301 (p : Nat → Bool) (h : Constraints p) : clause p c301 = true := by
  simpa only [c301,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause301
def c302 : List Lit := [(58, false), (39, false), (52, false), (59, false)]
theorem step302 (p : Nat → Bool) (h : Constraints p) : clause p c302 = true := by
  simpa only [c302,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause302
def c303 : List Lit := [(58, false), (39, false), (55, false), (59, false)]
theorem step303 (p : Nat → Bool) (h : Constraints p) : clause p c303 = true := by
  simpa only [c303,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause303
def c304 : List Lit := [(58, false), (39, false), (55, false), (110, false)]
theorem step304 (p : Nat → Bool) (h : Constraints p) : clause p c304 = true := by
  simpa only [c304,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause304
def c305 : List Lit := [(58, false), (52, false), (55, false), (59, false)]
theorem step305 (p : Nat → Bool) (h : Constraints p) : clause p c305 = true := by
  simpa only [c305,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause305
def c306 : List Lit := [(58, false), (52, false), (55, false), (110, false)]
theorem step306 (p : Nat → Bool) (h : Constraints p) : clause p c306 = true := by
  simpa only [c306,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause306
def c307 : List Lit := [(58, false), (52, false), (59, false), (110, false)]
theorem step307 (p : Nat → Bool) (h : Constraints p) : clause p c307 = true := by
  simpa only [c307,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause307
def c308 : List Lit := [(59, false), (22, false), (54, false), (56, false)]
theorem step308 (p : Nat → Bool) (h : Constraints p) : clause p c308 = true := by
  simpa only [c308,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause308
def c309 : List Lit := [(59, false), (22, false), (54, false), (58, false)]
theorem step309 (p : Nat → Bool) (h : Constraints p) : clause p c309 = true := by
  simpa only [c309,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause309
def c310 : List Lit := [(59, false), (22, false), (56, false), (58, false)]
theorem step310 (p : Nat → Bool) (h : Constraints p) : clause p c310 = true := by
  simpa only [c310,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause310
def c311 : List Lit := [(59, false), (54, false), (56, false), (58, false)]
theorem step311 (p : Nat → Bool) (h : Constraints p) : clause p c311 = true := by
  simpa only [c311,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause311
def c312 : List Lit := [(59, false), (183, true), (22, true), (56, true), (58, true)]
theorem step312 (p : Nat → Bool) (h : Constraints p) : clause p c312 = true := by
  simpa only [c312,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause312
def c313 : List Lit := [(59, false), (183, true), (22, true), (54, true), (58, true)]
theorem step313 (p : Nat → Bool) (h : Constraints p) : clause p c313 = true := by
  simpa only [c313,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause313
def c314 : List Lit := [(60, false), (25, false), (43, false), (51, false)]
theorem step314 (p : Nat → Bool) (h : Constraints p) : clause p c314 = true := by
  simpa only [c314,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause314
def c315 : List Lit := [(60, false), (25, false), (43, false), (62, false)]
theorem step315 (p : Nat → Bool) (h : Constraints p) : clause p c315 = true := by
  simpa only [c315,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause315
def c316 : List Lit := [(60, false), (25, false), (43, false), (63, false)]
theorem step316 (p : Nat → Bool) (h : Constraints p) : clause p c316 = true := by
  simpa only [c316,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause316
def c317 : List Lit := [(60, false), (25, false), (43, false), (67, false)]
theorem step317 (p : Nat → Bool) (h : Constraints p) : clause p c317 = true := by
  simpa only [c317,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause317
def c318 : List Lit := [(60, false), (25, false), (51, false), (62, false)]
theorem step318 (p : Nat → Bool) (h : Constraints p) : clause p c318 = true := by
  simpa only [c318,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause318
def c319 : List Lit := [(60, false), (25, false), (51, false), (63, false)]
theorem step319 (p : Nat → Bool) (h : Constraints p) : clause p c319 = true := by
  simpa only [c319,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause319
def c320 : List Lit := [(60, false), (25, false), (51, false), (67, false)]
theorem step320 (p : Nat → Bool) (h : Constraints p) : clause p c320 = true := by
  simpa only [c320,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause320
def c321 : List Lit := [(60, false), (25, false), (62, false), (63, false)]
theorem step321 (p : Nat → Bool) (h : Constraints p) : clause p c321 = true := by
  simpa only [c321,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause321
def c322 : List Lit := [(60, false), (25, false), (63, false), (67, false)]
theorem step322 (p : Nat → Bool) (h : Constraints p) : clause p c322 = true := by
  simpa only [c322,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause322
def c323 : List Lit := [(60, false), (43, false), (51, false), (62, false)]
theorem step323 (p : Nat → Bool) (h : Constraints p) : clause p c323 = true := by
  simpa only [c323,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause323
def c324 : List Lit := [(60, false), (43, false), (51, false), (63, false)]
theorem step324 (p : Nat → Bool) (h : Constraints p) : clause p c324 = true := by
  simpa only [c324,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause324
def c325 : List Lit := [(60, false), (43, false), (51, false), (67, false)]
theorem step325 (p : Nat → Bool) (h : Constraints p) : clause p c325 = true := by
  simpa only [c325,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause325
def c326 : List Lit := [(60, false), (43, false), (62, false), (63, false)]
theorem step326 (p : Nat → Bool) (h : Constraints p) : clause p c326 = true := by
  simpa only [c326,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause326
def c327 : List Lit := [(60, false), (43, false), (62, false), (67, false)]
theorem step327 (p : Nat → Bool) (h : Constraints p) : clause p c327 = true := by
  simpa only [c327,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause327
def c328 : List Lit := [(60, false), (43, false), (63, false), (67, false)]
theorem step328 (p : Nat → Bool) (h : Constraints p) : clause p c328 = true := by
  simpa only [c328,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause328
def c329 : List Lit := [(60, false), (43, false), (67, false), (114, false)]
theorem step329 (p : Nat → Bool) (h : Constraints p) : clause p c329 = true := by
  simpa only [c329,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause329
def c330 : List Lit := [(60, false), (51, false), (62, false), (67, false)]
theorem step330 (p : Nat → Bool) (h : Constraints p) : clause p c330 = true := by
  simpa only [c330,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause330
def c331 : List Lit := [(60, false), (62, false), (63, false), (67, false)]
theorem step331 (p : Nat → Bool) (h : Constraints p) : clause p c331 = true := by
  simpa only [c331,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause331
def c332 : List Lit := [(60, false), (184, true), (43, true), (51, true), (62, true), (63, true), (67, true), (114, true)]
theorem step332 (p : Nat → Bool) (h : Constraints p) : clause p c332 = true := by
  simpa only [c332,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause332
def c333 : List Lit := [(60, false), (184, true), (25, true), (43, true), (51, true), (62, true), (67, true), (114, true)]
theorem step333 (p : Nat → Bool) (h : Constraints p) : clause p c333 = true := by
  simpa only [c333,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause333
def c334 : List Lit := [(61, false), (26, false), (62, false), (64, false)]
theorem step334 (p : Nat → Bool) (h : Constraints p) : clause p c334 = true := by
  simpa only [c334,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause334
def c335 : List Lit := [(61, false), (26, false), (64, false), (115, false)]
theorem step335 (p : Nat → Bool) (h : Constraints p) : clause p c335 = true := by
  simpa only [c335,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause335
def c336 : List Lit := [(61, false), (62, false), (64, false), (115, false)]
theorem step336 (p : Nat → Bool) (h : Constraints p) : clause p c336 = true := by
  simpa only [c336,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause336
def c337 : List Lit := [(61, false), (185, true), (62, true), (64, true), (115, true)]
theorem step337 (p : Nat → Bool) (h : Constraints p) : clause p c337 = true := by
  simpa only [c337,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause337
def c338 : List Lit := [(61, false), (185, true), (26, true), (64, true), (115, true)]
theorem step338 (p : Nat → Bool) (h : Constraints p) : clause p c338 = true := by
  simpa only [c338,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause338
def c339 : List Lit := [(61, false), (185, true), (26, true), (62, true), (115, true)]
theorem step339 (p : Nat → Bool) (h : Constraints p) : clause p c339 = true := by
  simpa only [c339,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause339
def c340 : List Lit := [(61, false), (185, true), (26, true), (62, true), (64, true)]
theorem step340 (p : Nat → Bool) (h : Constraints p) : clause p c340 = true := by
  simpa only [c340,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause340
def c341 : List Lit := [(62, false), (27, false), (60, false), (61, false)]
theorem step341 (p : Nat → Bool) (h : Constraints p) : clause p c341 = true := by
  simpa only [c341,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause341
def c342 : List Lit := [(62, false), (27, false), (60, false), (65, false)]
theorem step342 (p : Nat → Bool) (h : Constraints p) : clause p c342 = true := by
  simpa only [c342,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause342
def c343 : List Lit := [(62, false), (27, false), (60, false), (116, false)]
theorem step343 (p : Nat → Bool) (h : Constraints p) : clause p c343 = true := by
  simpa only [c343,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause343
def c344 : List Lit := [(62, false), (27, false), (61, false), (65, false)]
theorem step344 (p : Nat → Bool) (h : Constraints p) : clause p c344 = true := by
  simpa only [c344,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause344
def c345 : List Lit := [(62, false), (27, false), (61, false), (68, false)]
theorem step345 (p : Nat → Bool) (h : Constraints p) : clause p c345 = true := by
  simpa only [c345,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause345
def c346 : List Lit := [(62, false), (27, false), (61, false), (116, false)]
theorem step346 (p : Nat → Bool) (h : Constraints p) : clause p c346 = true := by
  simpa only [c346,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause346
def c347 : List Lit := [(62, false), (27, false), (65, false), (68, false)]
theorem step347 (p : Nat → Bool) (h : Constraints p) : clause p c347 = true := by
  simpa only [c347,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause347
def c348 : List Lit := [(62, false), (27, false), (68, false), (116, false)]
theorem step348 (p : Nat → Bool) (h : Constraints p) : clause p c348 = true := by
  simpa only [c348,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause348
def c349 : List Lit := [(62, false), (60, false), (61, false), (65, false)]
theorem step349 (p : Nat → Bool) (h : Constraints p) : clause p c349 = true := by
  simpa only [c349,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause349
def c350 : List Lit := [(62, false), (60, false), (61, false), (68, false)]
theorem step350 (p : Nat → Bool) (h : Constraints p) : clause p c350 = true := by
  simpa only [c350,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause350
def c351 : List Lit := [(62, false), (60, false), (61, false), (116, false)]
theorem step351 (p : Nat → Bool) (h : Constraints p) : clause p c351 = true := by
  simpa only [c351,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause351
def c352 : List Lit := [(62, false), (60, false), (65, false), (68, false)]
theorem step352 (p : Nat → Bool) (h : Constraints p) : clause p c352 = true := by
  simpa only [c352,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause352
def c353 : List Lit := [(62, false), (60, false), (65, false), (116, false)]
theorem step353 (p : Nat → Bool) (h : Constraints p) : clause p c353 = true := by
  simpa only [c353,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause353
def c354 : List Lit := [(62, false), (60, false), (68, false), (116, false)]
theorem step354 (p : Nat → Bool) (h : Constraints p) : clause p c354 = true := by
  simpa only [c354,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause354
def c355 : List Lit := [(62, false), (61, false), (65, false), (68, false)]
theorem step355 (p : Nat → Bool) (h : Constraints p) : clause p c355 = true := by
  simpa only [c355,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause355
def c356 : List Lit := [(62, false), (61, false), (65, false), (116, false)]
theorem step356 (p : Nat → Bool) (h : Constraints p) : clause p c356 = true := by
  simpa only [c356,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause356
def c357 : List Lit := [(62, false), (61, false), (68, false), (116, false)]
theorem step357 (p : Nat → Bool) (h : Constraints p) : clause p c357 = true := by
  simpa only [c357,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause357
def c358 : List Lit := [(62, false), (65, false), (68, false), (116, false)]
theorem step358 (p : Nat → Bool) (h : Constraints p) : clause p c358 = true := by
  simpa only [c358,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause358
def c359 : List Lit := [(62, false), (186, true), (27, true), (60, true), (65, true), (68, true), (116, true)]
theorem step359 (p : Nat → Bool) (h : Constraints p) : clause p c359 = true := by
  simpa only [c359,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause359
def c360 : List Lit := [(62, false), (186, true), (27, true), (60, true), (61, true), (68, true), (116, true)]
theorem step360 (p : Nat → Bool) (h : Constraints p) : clause p c360 = true := by
  simpa only [c360,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause360
def c361 : List Lit := [(62, false), (186, true), (27, true), (60, true), (61, true), (65, true), (116, true)]
theorem step361 (p : Nat → Bool) (h : Constraints p) : clause p c361 = true := by
  simpa only [c361,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause361
def c362 : List Lit := [(63, false), (53, false), (60, false), (65, false)]
theorem step362 (p : Nat → Bool) (h : Constraints p) : clause p c362 = true := by
  simpa only [c362,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause362
def c363 : List Lit := [(63, false), (53, false), (60, false), (69, false)]
theorem step363 (p : Nat → Bool) (h : Constraints p) : clause p c363 = true := by
  simpa only [c363,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause363
def c364 : List Lit := [(63, false), (53, false), (65, false), (69, false)]
theorem step364 (p : Nat → Bool) (h : Constraints p) : clause p c364 = true := by
  simpa only [c364,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause364
def c365 : List Lit := [(63, false), (60, false), (65, false), (69, false)]
theorem step365 (p : Nat → Bool) (h : Constraints p) : clause p c365 = true := by
  simpa only [c365,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause365
def c366 : List Lit := [(64, false), (45, false), (54, false), (61, false)]
theorem step366 (p : Nat → Bool) (h : Constraints p) : clause p c366 = true := by
  simpa only [c366,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause366
def c367 : List Lit := [(64, false), (45, false), (54, false), (65, false)]
theorem step367 (p : Nat → Bool) (h : Constraints p) : clause p c367 = true := by
  simpa only [c367,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause367
def c368 : List Lit := [(64, false), (45, false), (54, false), (118, false)]
theorem step368 (p : Nat → Bool) (h : Constraints p) : clause p c368 = true := by
  simpa only [c368,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause368
def c369 : List Lit := [(64, false), (45, false), (61, false), (65, false)]
theorem step369 (p : Nat → Bool) (h : Constraints p) : clause p c369 = true := by
  simpa only [c369,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause369
def c370 : List Lit := [(64, false), (45, false), (61, false), (118, false)]
theorem step370 (p : Nat → Bool) (h : Constraints p) : clause p c370 = true := by
  simpa only [c370,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause370
def c371 : List Lit := [(64, false), (45, false), (65, false), (118, false)]
theorem step371 (p : Nat → Bool) (h : Constraints p) : clause p c371 = true := by
  simpa only [c371,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause371
def c372 : List Lit := [(64, false), (54, false), (61, false), (65, false)]
theorem step372 (p : Nat → Bool) (h : Constraints p) : clause p c372 = true := by
  simpa only [c372,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause372
def c373 : List Lit := [(64, false), (54, false), (61, false), (118, false)]
theorem step373 (p : Nat → Bool) (h : Constraints p) : clause p c373 = true := by
  simpa only [c373,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause373
def c374 : List Lit := [(64, false), (54, false), (65, false), (118, false)]
theorem step374 (p : Nat → Bool) (h : Constraints p) : clause p c374 = true := by
  simpa only [c374,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause374
def c375 : List Lit := [(64, false), (61, false), (65, false), (118, false)]
theorem step375 (p : Nat → Bool) (h : Constraints p) : clause p c375 = true := by
  simpa only [c375,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause375
def c376 : List Lit := [(64, false), (188, true), (45, true), (54, true), (61, true), (65, true)]
theorem step376 (p : Nat → Bool) (h : Constraints p) : clause p c376 = true := by
  simpa only [c376,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause376
def c377 : List Lit := [(65, false), (62, false), (63, false), (64, false)]
theorem step377 (p : Nat → Bool) (h : Constraints p) : clause p c377 = true := by
  simpa only [c377,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause377
def c378 : List Lit := [(65, false), (63, false), (64, false), (70, false)]
theorem step378 (p : Nat → Bool) (h : Constraints p) : clause p c378 = true := by
  simpa only [c378,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause378
def c379 : List Lit := [(65, false), (189, true), (63, true), (64, true), (70, true)]
theorem step379 (p : Nat → Bool) (h : Constraints p) : clause p c379 = true := by
  simpa only [c379,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause379
def c380 : List Lit := [(65, false), (189, true), (62, true), (64, true), (70, true)]
theorem step380 (p : Nat → Bool) (h : Constraints p) : clause p c380 = true := by
  simpa only [c380,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause380
def c381 : List Lit := [(65, false), (189, true), (62, true), (63, true), (70, true)]
theorem step381 (p : Nat → Bool) (h : Constraints p) : clause p c381 = true := by
  simpa only [c381,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause381
def c382 : List Lit := [(65, false), (189, true), (62, true), (63, true), (64, true)]
theorem step382 (p : Nat → Bool) (h : Constraints p) : clause p c382 = true := by
  simpa only [c382,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause382
def c383 : List Lit := [(66, false), (46, false), (55, false), (119, false)]
theorem step383 (p : Nat → Bool) (h : Constraints p) : clause p c383 = true := by
  simpa only [c383,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause383
def c384 : List Lit := [(66, false), (190, true), (55, true), (67, true), (119, true)]
theorem step384 (p : Nat → Bool) (h : Constraints p) : clause p c384 = true := by
  simpa only [c384,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause384
def c385 : List Lit := [(66, false), (190, true), (46, true), (67, true), (119, true)]
theorem step385 (p : Nat → Bool) (h : Constraints p) : clause p c385 = true := by
  simpa only [c385,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause385
def c386 : List Lit := [(66, false), (190, true), (46, true), (55, true), (119, true)]
theorem step386 (p : Nat → Bool) (h : Constraints p) : clause p c386 = true := by
  simpa only [c386,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause386
def c387 : List Lit := [(66, false), (190, true), (46, true), (55, true), (67, true)]
theorem step387 (p : Nat → Bool) (h : Constraints p) : clause p c387 = true := by
  simpa only [c387,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause387
def c388 : List Lit := [(67, false), (29, false), (47, false), (60, false)]
theorem step388 (p : Nat → Bool) (h : Constraints p) : clause p c388 = true := by
  simpa only [c388,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause388
def c389 : List Lit := [(67, false), (29, false), (47, false), (66, false)]
theorem step389 (p : Nat → Bool) (h : Constraints p) : clause p c389 = true := by
  simpa only [c389,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause389
def c390 : List Lit := [(67, false), (29, false), (47, false), (68, false)]
theorem step390 (p : Nat → Bool) (h : Constraints p) : clause p c390 = true := by
  simpa only [c390,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause390
def c391 : List Lit := [(67, false), (29, false), (47, false), (69, false)]
theorem step391 (p : Nat → Bool) (h : Constraints p) : clause p c391 = true := by
  simpa only [c391,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause391
def c392 : List Lit := [(67, false), (29, false), (60, false), (66, false)]
theorem step392 (p : Nat → Bool) (h : Constraints p) : clause p c392 = true := by
  simpa only [c392,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause392
def c393 : List Lit := [(67, false), (29, false), (60, false), (68, false)]
theorem step393 (p : Nat → Bool) (h : Constraints p) : clause p c393 = true := by
  simpa only [c393,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause393
def c394 : List Lit := [(67, false), (29, false), (60, false), (69, false)]
theorem step394 (p : Nat → Bool) (h : Constraints p) : clause p c394 = true := by
  simpa only [c394,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause394
def c395 : List Lit := [(67, false), (29, false), (66, false), (68, false)]
theorem step395 (p : Nat → Bool) (h : Constraints p) : clause p c395 = true := by
  simpa only [c395,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause395
def c396 : List Lit := [(67, false), (29, false), (66, false), (69, false)]
theorem step396 (p : Nat → Bool) (h : Constraints p) : clause p c396 = true := by
  simpa only [c396,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause396
def c397 : List Lit := [(67, false), (29, false), (68, false), (69, false)]
theorem step397 (p : Nat → Bool) (h : Constraints p) : clause p c397 = true := by
  simpa only [c397,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause397
def c398 : List Lit := [(67, false), (47, false), (60, false), (66, false)]
theorem step398 (p : Nat → Bool) (h : Constraints p) : clause p c398 = true := by
  simpa only [c398,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause398
def c399 : List Lit := [(67, false), (47, false), (60, false), (68, false)]
theorem step399 (p : Nat → Bool) (h : Constraints p) : clause p c399 = true := by
  simpa only [c399,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause399
def c400 : List Lit := [(67, false), (47, false), (60, false), (69, false)]
theorem step400 (p : Nat → Bool) (h : Constraints p) : clause p c400 = true := by
  simpa only [c400,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause400
def c401 : List Lit := [(67, false), (47, false), (66, false), (68, false)]
theorem step401 (p : Nat → Bool) (h : Constraints p) : clause p c401 = true := by
  simpa only [c401,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause401
def c402 : List Lit := [(67, false), (47, false), (66, false), (69, false)]
theorem step402 (p : Nat → Bool) (h : Constraints p) : clause p c402 = true := by
  simpa only [c402,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause402
def c403 : List Lit := [(67, false), (47, false), (68, false), (69, false)]
theorem step403 (p : Nat → Bool) (h : Constraints p) : clause p c403 = true := by
  simpa only [c403,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause403
def c404 : List Lit := [(67, false), (60, false), (66, false), (68, false)]
theorem step404 (p : Nat → Bool) (h : Constraints p) : clause p c404 = true := by
  simpa only [c404,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause404
def c405 : List Lit := [(67, false), (60, false), (66, false), (69, false)]
theorem step405 (p : Nat → Bool) (h : Constraints p) : clause p c405 = true := by
  simpa only [c405,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause405
def c406 : List Lit := [(67, false), (60, false), (68, false), (69, false)]
theorem step406 (p : Nat → Bool) (h : Constraints p) : clause p c406 = true := by
  simpa only [c406,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause406
def c407 : List Lit := [(67, false), (66, false), (68, false), (69, false)]
theorem step407 (p : Nat → Bool) (h : Constraints p) : clause p c407 = true := by
  simpa only [c407,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause407
def c408 : List Lit := [(68, false), (57, false), (62, false), (67, false)]
theorem step408 (p : Nat → Bool) (h : Constraints p) : clause p c408 = true := by
  simpa only [c408,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause408
def c409 : List Lit := [(68, false), (57, false), (62, false), (70, false)]
theorem step409 (p : Nat → Bool) (h : Constraints p) : clause p c409 = true := by
  simpa only [c409,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause409
def c410 : List Lit := [(68, false), (57, false), (67, false), (70, false)]
theorem step410 (p : Nat → Bool) (h : Constraints p) : clause p c410 = true := by
  simpa only [c410,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause410
def c411 : List Lit := [(68, false), (57, false), (70, false), (120, false)]
theorem step411 (p : Nat → Bool) (h : Constraints p) : clause p c411 = true := by
  simpa only [c411,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause411
def c412 : List Lit := [(68, false), (62, false), (70, false), (120, false)]
theorem step412 (p : Nat → Bool) (h : Constraints p) : clause p c412 = true := by
  simpa only [c412,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause412
def c413 : List Lit := [(68, false), (192, true), (62, true), (67, true), (70, true), (120, true)]
theorem step413 (p : Nat → Bool) (h : Constraints p) : clause p c413 = true := by
  simpa only [c413,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause413
def c414 : List Lit := [(68, false), (192, true), (57, true), (67, true), (70, true), (120, true)]
theorem step414 (p : Nat → Bool) (h : Constraints p) : clause p c414 = true := by
  simpa only [c414,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause414
def c415 : List Lit := [(68, false), (192, true), (57, true), (62, true), (67, true), (120, true)]
theorem step415 (p : Nat → Bool) (h : Constraints p) : clause p c415 = true := by
  simpa only [c415,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause415
def c416 : List Lit := [(68, false), (192, true), (57, true), (62, true), (67, true), (70, true)]
theorem step416 (p : Nat → Bool) (h : Constraints p) : clause p c416 = true := by
  simpa only [c416,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause416
def c417 : List Lit := [(69, false), (63, false), (67, false), (70, false)]
theorem step417 (p : Nat → Bool) (h : Constraints p) : clause p c417 = true := by
  simpa only [c417,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause417
def c418 : List Lit := [(69, false), (63, false), (67, false), (122, false)]
theorem step418 (p : Nat → Bool) (h : Constraints p) : clause p c418 = true := by
  simpa only [c418,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause418
def c419 : List Lit := [(69, false), (193, true), (67, true), (70, true), (122, true)]
theorem step419 (p : Nat → Bool) (h : Constraints p) : clause p c419 = true := by
  simpa only [c419,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause419
def c420 : List Lit := [(69, false), (193, true), (63, true), (70, true), (122, true)]
theorem step420 (p : Nat → Bool) (h : Constraints p) : clause p c420 = true := by
  simpa only [c420,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause420
def c421 : List Lit := [(69, false), (193, true), (63, true), (67, true), (122, true)]
theorem step421 (p : Nat → Bool) (h : Constraints p) : clause p c421 = true := by
  simpa only [c421,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause421
def c422 : List Lit := [(69, false), (193, true), (63, true), (67, true), (70, true)]
theorem step422 (p : Nat → Bool) (h : Constraints p) : clause p c422 = true := by
  simpa only [c422,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause422
def c423 : List Lit := [(70, false), (65, true), (68, true), (69, true), (124, true)]
theorem step423 (p : Nat → Bool) (h : Constraints p) : clause p c423 = true := by
  simpa only [c423,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause423
def c424 : List Lit := [(70, false), (65, false), (68, false), (69, false)]
theorem step424 (p : Nat → Bool) (h : Constraints p) : clause p c424 = true := by
  simpa only [c424,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause424
def c425 : List Lit := [(70, false), (65, false), (68, false), (124, false)]
theorem step425 (p : Nat → Bool) (h : Constraints p) : clause p c425 = true := by
  simpa only [c425,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause425
def c426 : List Lit := [(70, false), (65, false), (69, false), (124, false)]
theorem step426 (p : Nat → Bool) (h : Constraints p) : clause p c426 = true := by
  simpa only [c426,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause426
def c427 : List Lit := [(70, false), (68, false), (69, false), (124, false)]
theorem step427 (p : Nat → Bool) (h : Constraints p) : clause p c427 = true := by
  simpa only [c427,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause427
def c428 : List Lit := [(70, false), (194, true), (65, true), (69, true), (124, true)]
theorem step428 (p : Nat → Bool) (h : Constraints p) : clause p c428 = true := by
  simpa only [c428,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause428
def c429 : List Lit := [(70, false), (194, true), (65, true), (68, true), (124, true)]
theorem step429 (p : Nat → Bool) (h : Constraints p) : clause p c429 = true := by
  simpa only [c429,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause429
def c430 : List Lit := [(71, false), (15, false), (75, false), (103, false)]
theorem step430 (p : Nat → Bool) (h : Constraints p) : clause p c430 = true := by
  simpa only [c430,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause430
def c431 : List Lit := [(71, false), (195, true), (15, true), (103, true)]
theorem step431 (p : Nat → Bool) (h : Constraints p) : clause p c431 = true := by
  simpa only [c431,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause431
def c432 : List Lit := [(72, false), (196, true), (80, true)]
theorem step432 (p : Nat → Bool) (h : Constraints p) : clause p c432 = true := by
  simpa only [c432,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause432
def c433 : List Lit := [(73, false), (197, true), (77, true)]
theorem step433 (p : Nat → Bool) (h : Constraints p) : clause p c433 = true := by
  simpa only [c433,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause433
def c434 : List Lit := [(73, false), (197, true), (72, true)]
theorem step434 (p : Nat → Bool) (h : Constraints p) : clause p c434 = true := by
  simpa only [c434,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause434
def c435 : List Lit := [(74, false), (75, false), (76, false), (107, false)]
theorem step435 (p : Nat → Bool) (h : Constraints p) : clause p c435 = true := by
  simpa only [c435,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause435
def c436 : List Lit := [(74, false), (198, true), (75, true), (107, true)]
theorem step436 (p : Nat → Bool) (h : Constraints p) : clause p c436 = true := by
  simpa only [c436,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause436
def c437 : List Lit := [(75, false), (19, false), (74, false), (108, false)]
theorem step437 (p : Nat → Bool) (h : Constraints p) : clause p c437 = true := by
  simpa only [c437,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause437
def c438 : List Lit := [(75, false), (199, true), (71, true), (74, true), (108, true)]
theorem step438 (p : Nat → Bool) (h : Constraints p) : clause p c438 = true := by
  simpa only [c438,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause438
def c439 : List Lit := [(75, false), (199, true), (19, true), (74, true), (108, true)]
theorem step439 (p : Nat → Bool) (h : Constraints p) : clause p c439 = true := by
  simpa only [c439,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause439
def c440 : List Lit := [(75, false), (199, true), (19, true), (71, true), (108, true)]
theorem step440 (p : Nat → Bool) (h : Constraints p) : clause p c440 = true := by
  simpa only [c440,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause440
def c441 : List Lit := [(76, false), (74, false), (77, false), (82, false)]
theorem step441 (p : Nat → Bool) (h : Constraints p) : clause p c441 = true := by
  simpa only [c441,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause441
def c442 : List Lit := [(76, false), (200, true), (77, true), (82, true)]
theorem step442 (p : Nat → Bool) (h : Constraints p) : clause p c442 = true := by
  simpa only [c442,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause442
def c443 : List Lit := [(76, false), (200, true), (74, true), (82, true)]
theorem step443 (p : Nat → Bool) (h : Constraints p) : clause p c443 = true := by
  simpa only [c443,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause443
def c444 : List Lit := [(76, false), (200, true), (74, true), (77, true)]
theorem step444 (p : Nat → Bool) (h : Constraints p) : clause p c444 = true := by
  simpa only [c444,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause444
def c445 : List Lit := [(77, false), (22, false), (73, false), (76, false)]
theorem step445 (p : Nat → Bool) (h : Constraints p) : clause p c445 = true := by
  simpa only [c445,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause445
def c446 : List Lit := [(77, false), (201, true), (22, true), (76, true)]
theorem step446 (p : Nat → Bool) (h : Constraints p) : clause p c446 = true := by
  simpa only [c446,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause446
def c447 : List Lit := [(77, false), (201, true), (22, true), (73, true)]
theorem step447 (p : Nat → Bool) (h : Constraints p) : clause p c447 = true := by
  simpa only [c447,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause447
def c448 : List Lit := [(78, false), (26, false), (79, false), (115, false)]
theorem step448 (p : Nat → Bool) (h : Constraints p) : clause p c448 = true := by
  simpa only [c448,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause448
def c449 : List Lit := [(78, false), (202, true), (79, true), (82, true), (115, true)]
theorem step449 (p : Nat → Bool) (h : Constraints p) : clause p c449 = true := by
  simpa only [c449,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause449
def c450 : List Lit := [(78, false), (202, true), (26, true), (82, true), (115, true)]
theorem step450 (p : Nat → Bool) (h : Constraints p) : clause p c450 = true := by
  simpa only [c450,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause450
def c451 : List Lit := [(78, false), (202, true), (26, true), (79, true), (115, true)]
theorem step451 (p : Nat → Bool) (h : Constraints p) : clause p c451 = true := by
  simpa only [c451,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause451
def c452 : List Lit := [(78, false), (202, true), (26, true), (79, true), (82, true)]
theorem step452 (p : Nat → Bool) (h : Constraints p) : clause p c452 = true := by
  simpa only [c452,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause452
def c453 : List Lit := [(79, false), (27, false), (78, false), (83, false)]
theorem step453 (p : Nat → Bool) (h : Constraints p) : clause p c453 = true := by
  simpa only [c453,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause453
def c454 : List Lit := [(79, false), (27, false), (78, false), (116, false)]
theorem step454 (p : Nat → Bool) (h : Constraints p) : clause p c454 = true := by
  simpa only [c454,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause454
def c455 : List Lit := [(79, false), (78, false), (83, false), (116, false)]
theorem step455 (p : Nat → Bool) (h : Constraints p) : clause p c455 = true := by
  simpa only [c455,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause455
def c456 : List Lit := [(79, false), (203, true), (27, true), (83, true), (116, true)]
theorem step456 (p : Nat → Bool) (h : Constraints p) : clause p c456 = true := by
  simpa only [c456,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause456
def c457 : List Lit := [(79, false), (203, true), (27, true), (78, true), (116, true)]
theorem step457 (p : Nat → Bool) (h : Constraints p) : clause p c457 = true := by
  simpa only [c457,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause457
def c458 : List Lit := [(80, false), (28, false), (72, false), (81, false)]
theorem step458 (p : Nat → Bool) (h : Constraints p) : clause p c458 = true := by
  simpa only [c458,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause458
def c459 : List Lit := [(80, false), (72, false), (81, false), (117, false)]
theorem step459 (p : Nat → Bool) (h : Constraints p) : clause p c459 = true := by
  simpa only [c459,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause459
def c460 : List Lit := [(81, false), (205, true), (80, true)]
theorem step460 (p : Nat → Bool) (h : Constraints p) : clause p c460 = true := by
  simpa only [c460,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause460
def c461 : List Lit := [(82, false), (30, false), (76, false), (78, false)]
theorem step461 (p : Nat → Bool) (h : Constraints p) : clause p c461 = true := by
  simpa only [c461,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause461
def c462 : List Lit := [(82, false), (30, false), (76, false), (83, false)]
theorem step462 (p : Nat → Bool) (h : Constraints p) : clause p c462 = true := by
  simpa only [c462,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause462
def c463 : List Lit := [(82, false), (30, false), (78, false), (83, false)]
theorem step463 (p : Nat → Bool) (h : Constraints p) : clause p c463 = true := by
  simpa only [c463,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause463
def c464 : List Lit := [(82, false), (76, false), (78, false), (83, false)]
theorem step464 (p : Nat → Bool) (h : Constraints p) : clause p c464 = true := by
  simpa only [c464,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause464
def c465 : List Lit := [(83, false), (79, false), (82, false), (85, false)]
theorem step465 (p : Nat → Bool) (h : Constraints p) : clause p c465 = true := by
  simpa only [c465,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause465
def c466 : List Lit := [(83, false), (79, false), (85, false), (120, false)]
theorem step466 (p : Nat → Bool) (h : Constraints p) : clause p c466 = true := by
  simpa only [c466,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause466
def c467 : List Lit := [(83, false), (82, false), (85, false), (120, false)]
theorem step467 (p : Nat → Bool) (h : Constraints p) : clause p c467 = true := by
  simpa only [c467,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause467
def c468 : List Lit := [(83, false), (207, true), (82, true), (85, true), (120, true)]
theorem step468 (p : Nat → Bool) (h : Constraints p) : clause p c468 = true := by
  simpa only [c468,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause468
def c469 : List Lit := [(83, false), (207, true), (79, true), (85, true), (120, true)]
theorem step469 (p : Nat → Bool) (h : Constraints p) : clause p c469 = true := by
  simpa only [c469,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause469
def c470 : List Lit := [(83, false), (207, true), (79, true), (82, true), (120, true)]
theorem step470 (p : Nat → Bool) (h : Constraints p) : clause p c470 = true := by
  simpa only [c470,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause470
def c471 : List Lit := [(83, false), (207, true), (79, true), (82, true), (85, true)]
theorem step471 (p : Nat → Bool) (h : Constraints p) : clause p c471 = true := by
  simpa only [c471,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause471
def c472 : List Lit := [(84, false), (81, false), (85, false), (122, false)]
theorem step472 (p : Nat → Bool) (h : Constraints p) : clause p c472 = true := by
  simpa only [c472,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause472
def c473 : List Lit := [(84, false), (208, true), (85, true), (122, true)]
theorem step473 (p : Nat → Bool) (h : Constraints p) : clause p c473 = true := by
  simpa only [c473,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause473
def c474 : List Lit := [(84, false), (208, true), (81, true), (122, true)]
theorem step474 (p : Nat → Bool) (h : Constraints p) : clause p c474 = true := by
  simpa only [c474,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause474
def c475 : List Lit := [(84, false), (208, true), (81, true), (85, true)]
theorem step475 (p : Nat → Bool) (h : Constraints p) : clause p c475 = true := by
  simpa only [c475,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause475
def c476 : List Lit := [(85, false), (83, true), (84, true), (124, true)]
theorem step476 (p : Nat → Bool) (h : Constraints p) : clause p c476 = true := by
  simpa only [c476,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause476
def c477 : List Lit := [(85, false), (83, false), (84, false), (124, false)]
theorem step477 (p : Nat → Bool) (h : Constraints p) : clause p c477 = true := by
  simpa only [c477,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause477
def c478 : List Lit := [(85, false), (209, true), (83, true), (124, true)]
theorem step478 (p : Nat → Bool) (h : Constraints p) : clause p c478 = true := by
  simpa only [c478,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause478
def c479 : List Lit := [(86, false), (34, false), (91, false), (103, false)]
theorem step479 (p : Nat → Bool) (h : Constraints p) : clause p c479 = true := by
  simpa only [c479,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause479
def c480 : List Lit := [(210, false), (34, false), (91, false)]
theorem step480 (p : Nat → Bool) (h : Constraints p) : clause p c480 = true := by
  simpa only [c480,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause480
def c481 : List Lit := [(210, false), (91, false), (103, false)]
theorem step481 (p : Nat → Bool) (h : Constraints p) : clause p c481 = true := by
  simpa only [c481,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause481
def c482 : List Lit := [(86, false), (210, true), (34, true), (103, true)]
theorem step482 (p : Nat → Bool) (h : Constraints p) : clause p c482 = true := by
  simpa only [c482,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause482
def c483 : List Lit := [(87, false), (211, true), (96, true)]
theorem step483 (p : Nat → Bool) (h : Constraints p) : clause p c483 = true := by
  simpa only [c483,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause483
def c484 : List Lit := [(87, false), (211, true), (88, true)]
theorem step484 (p : Nat → Bool) (h : Constraints p) : clause p c484 = true := by
  simpa only [c484,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause484
def c485 : List Lit := [(88, false), (87, false), (89, false), (93, false)]
theorem step485 (p : Nat → Bool) (h : Constraints p) : clause p c485 = true := by
  simpa only [c485,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause485
def c486 : List Lit := [(88, false), (212, true), (89, true), (93, true)]
theorem step486 (p : Nat → Bool) (h : Constraints p) : clause p c486 = true := by
  simpa only [c486,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause486
def c487 : List Lit := [(88, false), (212, true), (87, true), (89, true)]
theorem step487 (p : Nat → Bool) (h : Constraints p) : clause p c487 = true := by
  simpa only [c487,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause487
def c488 : List Lit := [(89, false), (37, false), (88, false), (106, false)]
theorem step488 (p : Nat → Bool) (h : Constraints p) : clause p c488 = true := by
  simpa only [c488,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause488
def c489 : List Lit := [(90, false), (91, false), (92, false), (107, false)]
theorem step489 (p : Nat → Bool) (h : Constraints p) : clause p c489 = true := by
  simpa only [c489,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause489
def c490 : List Lit := [(90, false), (214, true), (91, true), (107, true)]
theorem step490 (p : Nat → Bool) (h : Constraints p) : clause p c490 = true := by
  simpa only [c490,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause490
def c491 : List Lit := [(91, false), (215, true), (90, true), (108, true)]
theorem step491 (p : Nat → Bool) (h : Constraints p) : clause p c491 = true := by
  simpa only [c491,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause491
def c492 : List Lit := [(91, false), (215, true), (86, true), (108, true)]
theorem step492 (p : Nat → Bool) (h : Constraints p) : clause p c492 = true := by
  simpa only [c492,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause492
def c493 : List Lit := [(92, false), (90, false), (93, false), (98, false)]
theorem step493 (p : Nat → Bool) (h : Constraints p) : clause p c493 = true := by
  simpa only [c493,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause493
def c494 : List Lit := [(92, false), (216, true), (93, true), (98, true)]
theorem step494 (p : Nat → Bool) (h : Constraints p) : clause p c494 = true := by
  simpa only [c494,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause494
def c495 : List Lit := [(92, false), (216, true), (90, true), (98, true)]
theorem step495 (p : Nat → Bool) (h : Constraints p) : clause p c495 = true := by
  simpa only [c495,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause495
def c496 : List Lit := [(92, false), (216, true), (90, true), (93, true)]
theorem step496 (p : Nat → Bool) (h : Constraints p) : clause p c496 = true := by
  simpa only [c496,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause496
def c497 : List Lit := [(93, false), (217, true), (88, true)]
theorem step497 (p : Nat → Bool) (h : Constraints p) : clause p c497 = true := by
  simpa only [c497,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause497
def c498 : List Lit := [(94, false), (218, true), (98, true), (115, true)]
theorem step498 (p : Nat → Bool) (h : Constraints p) : clause p c498 = true := by
  simpa only [c498,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause498
def c499 : List Lit := [(94, false), (218, true), (95, true), (115, true)]
theorem step499 (p : Nat → Bool) (h : Constraints p) : clause p c499 = true := by
  simpa only [c499,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause499
def c500 : List Lit := [(94, false), (218, true), (95, true), (98, true)]
theorem step500 (p : Nat → Bool) (h : Constraints p) : clause p c500 = true := by
  simpa only [c500,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause500
def c501 : List Lit := [(95, false), (94, false), (99, false), (116, false)]
theorem step501 (p : Nat → Bool) (h : Constraints p) : clause p c501 = true := by
  simpa only [c501,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause501
def c502 : List Lit := [(95, false), (219, true), (99, true), (116, true)]
theorem step502 (p : Nat → Bool) (h : Constraints p) : clause p c502 = true := by
  simpa only [c502,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause502
def c503 : List Lit := [(95, false), (219, true), (94, true), (116, true)]
theorem step503 (p : Nat → Bool) (h : Constraints p) : clause p c503 = true := by
  simpa only [c503,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause503
def c504 : List Lit := [(96, false), (44, false), (97, false), (117, false)]
theorem step504 (p : Nat → Bool) (h : Constraints p) : clause p c504 = true := by
  simpa only [c504,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause504
def c505 : List Lit := [(96, false), (220, true), (87, true), (97, true), (117, true)]
theorem step505 (p : Nat → Bool) (h : Constraints p) : clause p c505 = true := by
  simpa only [c505,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause505
def c506 : List Lit := [(96, false), (220, true), (44, true), (87, true), (117, true)]
theorem step506 (p : Nat → Bool) (h : Constraints p) : clause p c506 = true := by
  simpa only [c506,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause506
def c507 : List Lit := [(96, false), (220, true), (44, true), (87, true), (97, true)]
theorem step507 (p : Nat → Bool) (h : Constraints p) : clause p c507 = true := by
  simpa only [c507,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause507
def c508 : List Lit := [(97, false), (221, true), (100, true)]
theorem step508 (p : Nat → Bool) (h : Constraints p) : clause p c508 = true := by
  simpa only [c508,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause508
def c509 : List Lit := [(97, false), (221, true), (96, true)]
theorem step509 (p : Nat → Bool) (h : Constraints p) : clause p c509 = true := by
  simpa only [c509,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause509
def c510 : List Lit := [(98, false), (48, false), (92, false), (94, false)]
theorem step510 (p : Nat → Bool) (h : Constraints p) : clause p c510 = true := by
  simpa only [c510,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause510
def c511 : List Lit := [(98, false), (48, false), (92, false), (99, false)]
theorem step511 (p : Nat → Bool) (h : Constraints p) : clause p c511 = true := by
  simpa only [c511,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause511
def c512 : List Lit := [(98, false), (48, false), (94, false), (99, false)]
theorem step512 (p : Nat → Bool) (h : Constraints p) : clause p c512 = true := by
  simpa only [c512,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause512
def c513 : List Lit := [(98, false), (92, false), (94, false), (99, false)]
theorem step513 (p : Nat → Bool) (h : Constraints p) : clause p c513 = true := by
  simpa only [c513,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause513
def c514 : List Lit := [(99, false), (95, false), (98, false), (101, false)]
theorem step514 (p : Nat → Bool) (h : Constraints p) : clause p c514 = true := by
  simpa only [c514,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause514
def c515 : List Lit := [(99, false), (95, false), (101, false), (120, false)]
theorem step515 (p : Nat → Bool) (h : Constraints p) : clause p c515 = true := by
  simpa only [c515,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause515
def c516 : List Lit := [(99, false), (223, true), (98, true), (101, true), (120, true)]
theorem step516 (p : Nat → Bool) (h : Constraints p) : clause p c516 = true := by
  simpa only [c516,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause516
def c517 : List Lit := [(99, false), (223, true), (95, true), (98, true), (120, true)]
theorem step517 (p : Nat → Bool) (h : Constraints p) : clause p c517 = true := by
  simpa only [c517,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause517
def c518 : List Lit := [(100, false), (97, false), (101, false), (122, false)]
theorem step518 (p : Nat → Bool) (h : Constraints p) : clause p c518 = true := by
  simpa only [c518,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause518
def c519 : List Lit := [(100, false), (224, true), (101, true), (122, true)]
theorem step519 (p : Nat → Bool) (h : Constraints p) : clause p c519 = true := by
  simpa only [c519,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause519
def c520 : List Lit := [(100, false), (224, true), (97, true), (122, true)]
theorem step520 (p : Nat → Bool) (h : Constraints p) : clause p c520 = true := by
  simpa only [c520,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause520
def c521 : List Lit := [(101, false), (99, false), (100, false), (124, false)]
theorem step521 (p : Nat → Bool) (h : Constraints p) : clause p c521 = true := by
  simpa only [c521,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause521
def c522 : List Lit := [(101, false), (225, true), (99, true), (124, true)]
theorem step522 (p : Nat → Bool) (h : Constraints p) : clause p c522 = true := by
  simpa only [c522,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause522
def c523 : List Lit := [(102, false), (103, false), (104, false), (107, false)]
theorem step523 (p : Nat → Bool) (h : Constraints p) : clause p c523 = true := by
  simpa only [c523,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause523
def c524 : List Lit := [(102, false), (103, false), (104, false), (113, false)]
theorem step524 (p : Nat → Bool) (h : Constraints p) : clause p c524 = true := by
  simpa only [c524,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause524
def c525 : List Lit := [(102, false), (103, false), (107, false), (113, false)]
theorem step525 (p : Nat → Bool) (h : Constraints p) : clause p c525 = true := by
  simpa only [c525,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause525
def c526 : List Lit := [(102, false), (104, false), (107, false), (113, false)]
theorem step526 (p : Nat → Bool) (h : Constraints p) : clause p c526 = true := by
  simpa only [c526,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause526
def c527 : List Lit := [(102, false), (226, true), (103, true), (107, true), (113, true)]
theorem step527 (p : Nat → Bool) (h : Constraints p) : clause p c527 = true := by
  simpa only [c527,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause527
def c528 : List Lit := [(103, false), (51, false), (71, false), (86, false)]
theorem step528 (p : Nat → Bool) (h : Constraints p) : clause p c528 = true := by
  simpa only [c528,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause528
def c529 : List Lit := [(103, false), (51, false), (86, false), (102, false)]
theorem step529 (p : Nat → Bool) (h : Constraints p) : clause p c529 = true := by
  simpa only [c529,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause529
def c530 : List Lit := [(103, false), (51, false), (102, false), (108, false)]
theorem step530 (p : Nat → Bool) (h : Constraints p) : clause p c530 = true := by
  simpa only [c530,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause530
def c531 : List Lit := [(103, false), (71, false), (86, false), (102, false)]
theorem step531 (p : Nat → Bool) (h : Constraints p) : clause p c531 = true := by
  simpa only [c531,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause531
def c532 : List Lit := [(103, false), (71, false), (86, false), (105, false)]
theorem step532 (p : Nat → Bool) (h : Constraints p) : clause p c532 = true := by
  simpa only [c532,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause532
def c533 : List Lit := [(103, false), (71, false), (86, false), (114, false)]
theorem step533 (p : Nat → Bool) (h : Constraints p) : clause p c533 = true := by
  simpa only [c533,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause533
def c534 : List Lit := [(103, false), (86, false), (102, false), (114, false)]
theorem step534 (p : Nat → Bool) (h : Constraints p) : clause p c534 = true := by
  simpa only [c534,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause534
def c535 : List Lit := [(103, false), (102, false), (105, false), (108, false)]
theorem step535 (p : Nat → Bool) (h : Constraints p) : clause p c535 = true := by
  simpa only [c535,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause535
def c536 : List Lit := [(103, false), (105, false), (108, false), (114, false)]
theorem step536 (p : Nat → Bool) (h : Constraints p) : clause p c536 = true := by
  simpa only [c536,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause536
def c537 : List Lit := [(104, false), (228, true), (105, true), (115, true)]
theorem step537 (p : Nat → Bool) (h : Constraints p) : clause p c537 = true := by
  simpa only [c537,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause537
def c538 : List Lit := [(104, false), (228, true), (102, true), (115, true)]
theorem step538 (p : Nat → Bool) (h : Constraints p) : clause p c538 = true := by
  simpa only [c538,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause538
def c539 : List Lit := [(104, false), (228, true), (102, true), (105, true)]
theorem step539 (p : Nat → Bool) (h : Constraints p) : clause p c539 = true := by
  simpa only [c539,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause539
def c540 : List Lit := [(105, false), (103, false), (104, false), (106, false)]
theorem step540 (p : Nat → Bool) (h : Constraints p) : clause p c540 = true := by
  simpa only [c540,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause540
def c541 : List Lit := [(105, false), (103, false), (104, false), (109, false)]
theorem step541 (p : Nat → Bool) (h : Constraints p) : clause p c541 = true := by
  simpa only [c541,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause541
def c542 : List Lit := [(105, false), (103, false), (104, false), (116, false)]
theorem step542 (p : Nat → Bool) (h : Constraints p) : clause p c542 = true := by
  simpa only [c542,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause542
def c543 : List Lit := [(105, false), (103, false), (106, false), (109, false)]
theorem step543 (p : Nat → Bool) (h : Constraints p) : clause p c543 = true := by
  simpa only [c543,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause543
def c544 : List Lit := [(105, false), (103, false), (106, false), (116, false)]
theorem step544 (p : Nat → Bool) (h : Constraints p) : clause p c544 = true := by
  simpa only [c544,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause544
def c545 : List Lit := [(105, false), (103, false), (109, false), (116, false)]
theorem step545 (p : Nat → Bool) (h : Constraints p) : clause p c545 = true := by
  simpa only [c545,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause545
def c546 : List Lit := [(105, false), (104, false), (106, false), (109, false)]
theorem step546 (p : Nat → Bool) (h : Constraints p) : clause p c546 = true := by
  simpa only [c546,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause546
def c547 : List Lit := [(105, false), (104, false), (106, false), (116, false)]
theorem step547 (p : Nat → Bool) (h : Constraints p) : clause p c547 = true := by
  simpa only [c547,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause547
def c548 : List Lit := [(105, false), (104, false), (109, false), (116, false)]
theorem step548 (p : Nat → Bool) (h : Constraints p) : clause p c548 = true := by
  simpa only [c548,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause548
def c549 : List Lit := [(105, false), (106, false), (109, false), (116, false)]
theorem step549 (p : Nat → Bool) (h : Constraints p) : clause p c549 = true := by
  simpa only [c549,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause549
def c550 : List Lit := [(105, false), (229, true), (103, true), (104, true), (109, true), (116, true)]
theorem step550 (p : Nat → Bool) (h : Constraints p) : clause p c550 = true := by
  simpa only [c550,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause550
def c551 : List Lit := [(106, false), (89, false), (105, false), (112, false)]
theorem step551 (p : Nat → Bool) (h : Constraints p) : clause p c551 = true := by
  simpa only [c551,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause551
def c552 : List Lit := [(106, false), (230, true), (105, true), (112, true)]
theorem step552 (p : Nat → Bool) (h : Constraints p) : clause p c552 = true := by
  simpa only [c552,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause552
def c553 : List Lit := [(106, false), (230, true), (89, true), (112, true)]
theorem step553 (p : Nat → Bool) (h : Constraints p) : clause p c553 = true := by
  simpa only [c553,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause553
def c554 : List Lit := [(106, false), (230, true), (89, true), (105, true)]
theorem step554 (p : Nat → Bool) (h : Constraints p) : clause p c554 = true := by
  simpa only [c554,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause554
def c555 : List Lit := [(107, false), (55, false), (74, false), (90, false)]
theorem step555 (p : Nat → Bool) (h : Constraints p) : clause p c555 = true := by
  simpa only [c555,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause555
def c556 : List Lit := [(107, false), (55, false), (90, false), (102, false)]
theorem step556 (p : Nat → Bool) (h : Constraints p) : clause p c556 = true := by
  simpa only [c556,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause556
def c557 : List Lit := [(107, false), (55, false), (90, false), (110, false)]
theorem step557 (p : Nat → Bool) (h : Constraints p) : clause p c557 = true := by
  simpa only [c557,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause557
def c558 : List Lit := [(107, false), (55, false), (90, false), (119, false)]
theorem step558 (p : Nat → Bool) (h : Constraints p) : clause p c558 = true := by
  simpa only [c558,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause558
def c559 : List Lit := [(107, false), (55, false), (102, false), (108, false)]
theorem step559 (p : Nat → Bool) (h : Constraints p) : clause p c559 = true := by
  simpa only [c559,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause559
def c560 : List Lit := [(107, false), (55, false), (102, false), (110, false)]
theorem step560 (p : Nat → Bool) (h : Constraints p) : clause p c560 = true := by
  simpa only [c560,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause560
def c561 : List Lit := [(107, false), (55, false), (108, false), (110, false)]
theorem step561 (p : Nat → Bool) (h : Constraints p) : clause p c561 = true := by
  simpa only [c561,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause561
def c562 : List Lit := [(107, false), (74, false), (90, false), (119, false)]
theorem step562 (p : Nat → Bool) (h : Constraints p) : clause p c562 = true := by
  simpa only [c562,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause562
def c563 : List Lit := [(107, false), (74, false), (102, false), (110, false)]
theorem step563 (p : Nat → Bool) (h : Constraints p) : clause p c563 = true := by
  simpa only [c563,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause563
def c564 : List Lit := [(107, false), (74, false), (108, false), (119, false)]
theorem step564 (p : Nat → Bool) (h : Constraints p) : clause p c564 = true := by
  simpa only [c564,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause564
def c565 : List Lit := [(107, false), (90, false), (102, false), (110, false)]
theorem step565 (p : Nat → Bool) (h : Constraints p) : clause p c565 = true := by
  simpa only [c565,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause565
def c566 : List Lit := [(107, false), (90, false), (108, false), (119, false)]
theorem step566 (p : Nat → Bool) (h : Constraints p) : clause p c566 = true := by
  simpa only [c566,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause566
def c567 : List Lit := [(107, false), (90, false), (110, false), (119, false)]
theorem step567 (p : Nat → Bool) (h : Constraints p) : clause p c567 = true := by
  simpa only [c567,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause567
def c568 : List Lit := [(107, false), (102, false), (108, false), (110, false)]
theorem step568 (p : Nat → Bool) (h : Constraints p) : clause p c568 = true := by
  simpa only [c568,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause568
def c569 : List Lit := [(107, false), (102, false), (108, false), (119, false)]
theorem step569 (p : Nat → Bool) (h : Constraints p) : clause p c569 = true := by
  simpa only [c569,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause569
def c570 : List Lit := [(107, false), (108, false), (110, false), (119, false)]
theorem step570 (p : Nat → Bool) (h : Constraints p) : clause p c570 = true := by
  simpa only [c570,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause570
def c571 : List Lit := [(108, false), (75, false), (91, false), (103, false)]
theorem step571 (p : Nat → Bool) (h : Constraints p) : clause p c571 = true := by
  simpa only [c571,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause571
def c572 : List Lit := [(108, false), (75, false), (91, false), (107, false)]
theorem step572 (p : Nat → Bool) (h : Constraints p) : clause p c572 = true := by
  simpa only [c572,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause572
def c573 : List Lit := [(108, false), (75, false), (91, false), (109, false)]
theorem step573 (p : Nat → Bool) (h : Constraints p) : clause p c573 = true := by
  simpa only [c573,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause573
def c574 : List Lit := [(108, false), (75, false), (91, false), (111, false)]
theorem step574 (p : Nat → Bool) (h : Constraints p) : clause p c574 = true := by
  simpa only [c574,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause574
def c575 : List Lit := [(108, false), (75, false), (103, false), (107, false)]
theorem step575 (p : Nat → Bool) (h : Constraints p) : clause p c575 = true := by
  simpa only [c575,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause575
def c576 : List Lit := [(108, false), (75, false), (103, false), (109, false)]
theorem step576 (p : Nat → Bool) (h : Constraints p) : clause p c576 = true := by
  simpa only [c576,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause576
def c577 : List Lit := [(108, false), (75, false), (103, false), (111, false)]
theorem step577 (p : Nat → Bool) (h : Constraints p) : clause p c577 = true := by
  simpa only [c577,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause577
def c578 : List Lit := [(108, false), (75, false), (107, false), (109, false)]
theorem step578 (p : Nat → Bool) (h : Constraints p) : clause p c578 = true := by
  simpa only [c578,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause578
def c579 : List Lit := [(108, false), (75, false), (107, false), (111, false)]
theorem step579 (p : Nat → Bool) (h : Constraints p) : clause p c579 = true := by
  simpa only [c579,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause579
def c580 : List Lit := [(108, false), (75, false), (109, false), (111, false)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true := by
  simpa only [c580,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause580
def c581 : List Lit := [(108, false), (91, false), (103, false), (107, false)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true := by
  simpa only [c581,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause581
def c582 : List Lit := [(108, false), (91, false), (103, false), (109, false)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true := by
  simpa only [c582,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause582
def c583 : List Lit := [(108, false), (91, false), (103, false), (111, false)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true := by
  simpa only [c583,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause583
def c584 : List Lit := [(108, false), (91, false), (107, false), (109, false)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true := by
  simpa only [c584,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause584
def c585 : List Lit := [(108, false), (91, false), (107, false), (111, false)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true := by
  simpa only [c585,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause585
def c586 : List Lit := [(108, false), (91, false), (109, false), (111, false)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true := by
  simpa only [c586,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause586
def c587 : List Lit := [(108, false), (103, false), (107, false), (109, false)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true := by
  simpa only [c587,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause587
def c588 : List Lit := [(108, false), (103, false), (107, false), (111, false)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true := by
  simpa only [c588,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause588
def c589 : List Lit := [(108, false), (103, false), (109, false), (111, false)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true := by
  simpa only [c589,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause589
def c590 : List Lit := [(108, false), (107, false), (109, false), (111, false)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true := by
  simpa only [c590,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause590
def c591 : List Lit := [(109, false), (57, false), (105, false), (112, false)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true := by
  simpa only [c591,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause591
def c592 : List Lit := [(109, false), (57, false), (108, false), (112, false)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true := by
  simpa only [c592,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause592
def c593 : List Lit := [(109, false), (105, false), (112, false), (120, false)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true := by
  simpa only [c593,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause593
def c594 : List Lit := [(109, false), (108, false), (112, false), (120, false)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true := by
  simpa only [c594,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause594
def c595 : List Lit := [(109, false), (233, true), (105, true), (108, true), (112, true), (120, true)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true := by
  simpa only [c595,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause595
def c596 : List Lit := [(109, false), (233, true), (57, true), (105, true), (108, true), (120, true)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true := by
  simpa only [c596,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause596
def c597 : List Lit := [(110, false), (58, true), (107, true), (111, true), (121, true)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true := by
  simpa only [c597,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause597
def c598 : List Lit := [(110, false), (58, false), (107, false), (111, false)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true := by
  simpa only [c598,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause598
def c599 : List Lit := [(110, false), (58, false), (107, false), (121, false)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true := by
  simpa only [c599,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause599
def c600 : List Lit := [(110, false), (58, false), (111, false), (121, false)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true := by
  simpa only [c600,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause600
def c601 : List Lit := [(110, false), (107, false), (111, false), (121, false)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true := by
  simpa only [c601,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause601
def c602 : List Lit := [(110, false), (234, true), (58, true), (107, true), (121, true)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true := by
  simpa only [c602,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause602
def c603 : List Lit := [(110, false), (234, true), (58, true), (107, true), (111, true)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true := by
  simpa only [c603,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause603
def c604 : List Lit := [(111, false), (108, false), (112, false), (122, false)]
theorem step604 (p : Nat → Bool) (h : Constraints p) : clause p c604 = true := by
  simpa only [c604,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause604
def c605 : List Lit := [(111, false), (235, true), (110, true), (112, true), (122, true)]
theorem step605 (p : Nat → Bool) (h : Constraints p) : clause p c605 = true := by
  simpa only [c605,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause605
def c606 : List Lit := [(111, false), (235, true), (108, true), (112, true), (122, true)]
theorem step606 (p : Nat → Bool) (h : Constraints p) : clause p c606 = true := by
  simpa only [c606,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause606
def c607 : List Lit := [(111, false), (235, true), (108, true), (110, true), (122, true)]
theorem step607 (p : Nat → Bool) (h : Constraints p) : clause p c607 = true := by
  simpa only [c607,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause607
def c608 : List Lit := [(111, false), (235, true), (108, true), (110, true), (112, true)]
theorem step608 (p : Nat → Bool) (h : Constraints p) : clause p c608 = true := by
  simpa only [c608,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause608
def c609 : List Lit := [(112, false), (106, false), (109, false), (111, false)]
theorem step609 (p : Nat → Bool) (h : Constraints p) : clause p c609 = true := by
  simpa only [c609,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause609
def c610 : List Lit := [(112, false), (106, false), (109, false), (124, false)]
theorem step610 (p : Nat → Bool) (h : Constraints p) : clause p c610 = true := by
  simpa only [c610,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause610
def c611 : List Lit := [(112, false), (106, false), (111, false), (124, false)]
theorem step611 (p : Nat → Bool) (h : Constraints p) : clause p c611 = true := by
  simpa only [c611,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause611
def c612 : List Lit := [(112, false), (109, false), (111, false), (124, false)]
theorem step612 (p : Nat → Bool) (h : Constraints p) : clause p c612 = true := by
  simpa only [c612,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause612
def c613 : List Lit := [(236, false), (106, false), (109, false)]
theorem step613 (p : Nat → Bool) (h : Constraints p) : clause p c613 = true := by
  simpa only [c613,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause613
def c614 : List Lit := [(236, false), (106, false), (111, false)]
theorem step614 (p : Nat → Bool) (h : Constraints p) : clause p c614 = true := by
  simpa only [c614,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause614
def c615 : List Lit := [(112, false), (236, true), (109, true), (111, true), (124, true)]
theorem step615 (p : Nat → Bool) (h : Constraints p) : clause p c615 = true := by
  simpa only [c615,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause615
def c616 : List Lit := [(113, false), (237, true), (114, true), (115, true), (117, true), (119, true)]
theorem step616 (p : Nat → Bool) (h : Constraints p) : clause p c616 = true := by
  simpa only [c616,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause616
def c617 : List Lit := [(113, false), (237, true), (102, true), (115, true), (117, true), (119, true)]
theorem step617 (p : Nat → Bool) (h : Constraints p) : clause p c617 = true := by
  simpa only [c617,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause617
def c618 : List Lit := [(113, false), (237, true), (102, true), (114, true), (117, true), (119, true)]
theorem step618 (p : Nat → Bool) (h : Constraints p) : clause p c618 = true := by
  simpa only [c618,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause618
def c619 : List Lit := [(113, false), (237, true), (102, true), (114, true), (115, true), (119, true)]
theorem step619 (p : Nat → Bool) (h : Constraints p) : clause p c619 = true := by
  simpa only [c619,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause619
def c620 : List Lit := [(113, false), (237, true), (102, true), (114, true), (115, true), (117, true)]
theorem step620 (p : Nat → Bool) (h : Constraints p) : clause p c620 = true := by
  simpa only [c620,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause620
def c621 : List Lit := [(114, false), (60, false), (103, false), (113, false)]
theorem step621 (p : Nat → Bool) (h : Constraints p) : clause p c621 = true := by
  simpa only [c621,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause621
def c622 : List Lit := [(114, false), (60, false), (103, false), (116, false)]
theorem step622 (p : Nat → Bool) (h : Constraints p) : clause p c622 = true := by
  simpa only [c622,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause622
def c623 : List Lit := [(114, false), (60, false), (113, false), (116, false)]
theorem step623 (p : Nat → Bool) (h : Constraints p) : clause p c623 = true := by
  simpa only [c623,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause623
def c624 : List Lit := [(114, false), (103, false), (113, false), (116, false)]
theorem step624 (p : Nat → Bool) (h : Constraints p) : clause p c624 = true := by
  simpa only [c624,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause624
def c625 : List Lit := [(114, false), (238, true), (60, true), (103, true), (116, true)]
theorem step625 (p : Nat → Bool) (h : Constraints p) : clause p c625 = true := by
  simpa only [c625,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause625
def c626 : List Lit := [(115, false), (61, false), (78, false), (94, false)]
theorem step626 (p : Nat → Bool) (h : Constraints p) : clause p c626 = true := by
  simpa only [c626,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause626
def c627 : List Lit := [(115, false), (61, false), (78, false), (104, false)]
theorem step627 (p : Nat → Bool) (h : Constraints p) : clause p c627 = true := by
  simpa only [c627,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause627
def c628 : List Lit := [(115, false), (61, false), (78, false), (113, false)]
theorem step628 (p : Nat → Bool) (h : Constraints p) : clause p c628 = true := by
  simpa only [c628,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause628
def c629 : List Lit := [(115, false), (61, false), (78, false), (116, false)]
theorem step629 (p : Nat → Bool) (h : Constraints p) : clause p c629 = true := by
  simpa only [c629,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause629
def c630 : List Lit := [(115, false), (61, false), (78, false), (118, false)]
theorem step630 (p : Nat → Bool) (h : Constraints p) : clause p c630 = true := by
  simpa only [c630,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause630
def c631 : List Lit := [(115, false), (61, false), (94, false), (104, false)]
theorem step631 (p : Nat → Bool) (h : Constraints p) : clause p c631 = true := by
  simpa only [c631,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause631
def c632 : List Lit := [(115, false), (61, false), (94, false), (113, false)]
theorem step632 (p : Nat → Bool) (h : Constraints p) : clause p c632 = true := by
  simpa only [c632,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause632
def c633 : List Lit := [(115, false), (61, false), (94, false), (116, false)]
theorem step633 (p : Nat → Bool) (h : Constraints p) : clause p c633 = true := by
  simpa only [c633,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause633
def c634 : List Lit := [(115, false), (61, false), (94, false), (118, false)]
theorem step634 (p : Nat → Bool) (h : Constraints p) : clause p c634 = true := by
  simpa only [c634,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause634
def c635 : List Lit := [(115, false), (61, false), (104, false), (113, false)]
theorem step635 (p : Nat → Bool) (h : Constraints p) : clause p c635 = true := by
  simpa only [c635,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause635
def c636 : List Lit := [(115, false), (61, false), (104, false), (116, false)]
theorem step636 (p : Nat → Bool) (h : Constraints p) : clause p c636 = true := by
  simpa only [c636,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause636
def c637 : List Lit := [(115, false), (61, false), (104, false), (118, false)]
theorem step637 (p : Nat → Bool) (h : Constraints p) : clause p c637 = true := by
  simpa only [c637,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause637
def c638 : List Lit := [(115, false), (61, false), (113, false), (116, false)]
theorem step638 (p : Nat → Bool) (h : Constraints p) : clause p c638 = true := by
  simpa only [c638,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause638
def c639 : List Lit := [(115, false), (61, false), (113, false), (118, false)]
theorem step639 (p : Nat → Bool) (h : Constraints p) : clause p c639 = true := by
  simpa only [c639,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause639
def c640 : List Lit := [(115, false), (61, false), (116, false), (118, false)]
theorem step640 (p : Nat → Bool) (h : Constraints p) : clause p c640 = true := by
  simpa only [c640,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause640
def c641 : List Lit := [(115, false), (78, false), (94, false), (104, false)]
theorem step641 (p : Nat → Bool) (h : Constraints p) : clause p c641 = true := by
  simpa only [c641,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause641
def c642 : List Lit := [(115, false), (78, false), (94, false), (113, false)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true := by
  simpa only [c642,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause642
def c643 : List Lit := [(115, false), (78, false), (94, false), (116, false)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true := by
  simpa only [c643,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause643
def c644 : List Lit := [(115, false), (78, false), (94, false), (118, false)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true := by
  simpa only [c644,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause644
def c645 : List Lit := [(115, false), (78, false), (104, false), (113, false)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true := by
  simpa only [c645,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause645
def c646 : List Lit := [(115, false), (78, false), (104, false), (116, false)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true := by
  simpa only [c646,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause646
def c647 : List Lit := [(115, false), (78, false), (104, false), (118, false)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true := by
  simpa only [c647,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause647
def c648 : List Lit := [(115, false), (78, false), (113, false), (116, false)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true := by
  simpa only [c648,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause648
def c649 : List Lit := [(115, false), (78, false), (113, false), (118, false)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true := by
  simpa only [c649,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause649
def c650 : List Lit := [(115, false), (78, false), (116, false), (118, false)]
theorem step650 (p : Nat → Bool) (h : Constraints p) : clause p c650 = true := by
  simpa only [c650,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause650
def c651 : List Lit := [(115, false), (94, false), (104, false), (113, false)]
theorem step651 (p : Nat → Bool) (h : Constraints p) : clause p c651 = true := by
  simpa only [c651,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause651
def c652 : List Lit := [(115, false), (94, false), (104, false), (116, false)]
theorem step652 (p : Nat → Bool) (h : Constraints p) : clause p c652 = true := by
  simpa only [c652,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause652
def c653 : List Lit := [(115, false), (94, false), (104, false), (118, false)]
theorem step653 (p : Nat → Bool) (h : Constraints p) : clause p c653 = true := by
  simpa only [c653,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause653
def c654 : List Lit := [(115, false), (94, false), (113, false), (116, false)]
theorem step654 (p : Nat → Bool) (h : Constraints p) : clause p c654 = true := by
  simpa only [c654,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause654
def c655 : List Lit := [(115, false), (94, false), (113, false), (118, false)]
theorem step655 (p : Nat → Bool) (h : Constraints p) : clause p c655 = true := by
  simpa only [c655,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause655
def c656 : List Lit := [(115, false), (94, false), (116, false), (118, false)]
theorem step656 (p : Nat → Bool) (h : Constraints p) : clause p c656 = true := by
  simpa only [c656,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause656
def c657 : List Lit := [(115, false), (104, false), (113, false), (116, false)]
theorem step657 (p : Nat → Bool) (h : Constraints p) : clause p c657 = true := by
  simpa only [c657,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause657
def c658 : List Lit := [(115, false), (104, false), (113, false), (118, false)]
theorem step658 (p : Nat → Bool) (h : Constraints p) : clause p c658 = true := by
  simpa only [c658,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause658
def c659 : List Lit := [(115, false), (104, false), (116, false), (118, false)]
theorem step659 (p : Nat → Bool) (h : Constraints p) : clause p c659 = true := by
  simpa only [c659,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause659
def c660 : List Lit := [(115, false), (113, false), (116, false), (118, false)]
theorem step660 (p : Nat → Bool) (h : Constraints p) : clause p c660 = true := by
  simpa only [c660,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause660
def c661 : List Lit := [(115, false), (239, true), (61, true), (94, true), (104, true), (113, true), (116, true), (118, true)]
theorem step661 (p : Nat → Bool) (h : Constraints p) : clause p c661 = true := by
  simpa only [c661,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause661
def c662 : List Lit := [(116, false), (62, false), (79, false), (105, false)]
theorem step662 (p : Nat → Bool) (h : Constraints p) : clause p c662 = true := by
  simpa only [c662,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause662
def c663 : List Lit := [(116, false), (62, false), (95, false), (105, false)]
theorem step663 (p : Nat → Bool) (h : Constraints p) : clause p c663 = true := by
  simpa only [c663,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause663
def c664 : List Lit := [(116, false), (79, false), (95, false), (105, false)]
theorem step664 (p : Nat → Bool) (h : Constraints p) : clause p c664 = true := by
  simpa only [c664,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause664
def c665 : List Lit := [(116, false), (79, false), (95, false), (115, false)]
theorem step665 (p : Nat → Bool) (h : Constraints p) : clause p c665 = true := by
  simpa only [c665,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause665
def c666 : List Lit := [(116, false), (79, false), (115, false), (120, false)]
theorem step666 (p : Nat → Bool) (h : Constraints p) : clause p c666 = true := by
  simpa only [c666,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause666
def c667 : List Lit := [(116, false), (95, false), (105, false), (114, false)]
theorem step667 (p : Nat → Bool) (h : Constraints p) : clause p c667 = true := by
  simpa only [c667,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause667
def c668 : List Lit := [(116, false), (95, false), (105, false), (120, false)]
theorem step668 (p : Nat → Bool) (h : Constraints p) : clause p c668 = true := by
  simpa only [c668,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause668
def c669 : List Lit := [(116, false), (240, true), (62, true), (95, true), (105, true), (114, true), (115, true), (120, true)]
theorem step669 (p : Nat → Bool) (h : Constraints p) : clause p c669 = true := by
  simpa only [c669,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause669
def c670 : List Lit := [(116, false), (240, true), (62, true), (79, true), (105, true), (114, true), (115, true), (120, true)]
theorem step670 (p : Nat → Bool) (h : Constraints p) : clause p c670 = true := by
  simpa only [c670,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause670
def c671 : List Lit := [(116, false), (240, true), (62, true), (79, true), (95, true), (105, true), (114, true), (120, true)]
theorem step671 (p : Nat → Bool) (h : Constraints p) : clause p c671 = true := by
  simpa only [c671,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause671
def c672 : List Lit := [(117, false), (80, false), (96, false), (113, false)]
theorem step672 (p : Nat → Bool) (h : Constraints p) : clause p c672 = true := by
  simpa only [c672,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause672
def c673 : List Lit := [(117, false), (80, false), (96, false), (118, false)]
theorem step673 (p : Nat → Bool) (h : Constraints p) : clause p c673 = true := by
  simpa only [c673,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause673
def c674 : List Lit := [(117, false), (80, false), (96, false), (121, false)]
theorem step674 (p : Nat → Bool) (h : Constraints p) : clause p c674 = true := by
  simpa only [c674,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause674
def c675 : List Lit := [(117, false), (80, false), (113, false), (118, false)]
theorem step675 (p : Nat → Bool) (h : Constraints p) : clause p c675 = true := by
  simpa only [c675,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause675
def c676 : List Lit := [(117, false), (80, false), (113, false), (121, false)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true := by
  simpa only [c676,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause676
def c677 : List Lit := [(117, false), (80, false), (118, false), (121, false)]
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true := by
  simpa only [c677,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause677
def c678 : List Lit := [(117, false), (96, false), (113, false), (118, false)]
theorem step678 (p : Nat → Bool) (h : Constraints p) : clause p c678 = true := by
  simpa only [c678,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause678
def c679 : List Lit := [(117, false), (96, false), (113, false), (121, false)]
theorem step679 (p : Nat → Bool) (h : Constraints p) : clause p c679 = true := by
  simpa only [c679,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause679
def c680 : List Lit := [(117, false), (96, false), (118, false), (121, false)]
theorem step680 (p : Nat → Bool) (h : Constraints p) : clause p c680 = true := by
  simpa only [c680,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause680
def c681 : List Lit := [(117, false), (113, false), (118, false), (121, false)]
theorem step681 (p : Nat → Bool) (h : Constraints p) : clause p c681 = true := by
  simpa only [c681,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause681
def c682 : List Lit := [(118, false), (64, false), (115, false), (117, false)]
theorem step682 (p : Nat → Bool) (h : Constraints p) : clause p c682 = true := by
  simpa only [c682,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause682
def c683 : List Lit := [(118, false), (64, false), (115, false), (123, false)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true := by
  simpa only [c683,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause683
def c684 : List Lit := [(118, false), (242, true), (115, true), (117, true), (123, true)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true := by
  simpa only [c684,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause684
def c685 : List Lit := [(118, false), (242, true), (64, true), (117, true), (123, true)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true := by
  simpa only [c685,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause685
def c686 : List Lit := [(118, false), (242, true), (64, true), (115, true), (123, true)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true := by
  simpa only [c686,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause686
def c687 : List Lit := [(118, false), (242, true), (64, true), (115, true), (117, true)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true := by
  simpa only [c687,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause687
def c688 : List Lit := [(119, false), (66, false), (107, false), (113, false)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true := by
  simpa only [c688,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause688
def c689 : List Lit := [(119, false), (66, false), (107, false), (121, false)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true := by
  simpa only [c689,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause689
def c690 : List Lit := [(119, false), (66, false), (113, false), (121, false)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true := by
  simpa only [c690,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause690
def c691 : List Lit := [(119, false), (107, false), (113, false), (121, false)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true := by
  simpa only [c691,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause691
def c692 : List Lit := [(243, false), (66, false), (113, false)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true := by
  simpa only [c692,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause692
def c693 : List Lit := [(243, false), (66, false), (121, false)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true := by
  simpa only [c693,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause693
def c694 : List Lit := [(119, false), (243, true), (107, true), (113, true), (121, true)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true := by
  simpa only [c694,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause694
def c695 : List Lit := [(119, false), (243, true), (66, true), (107, true), (121, true)]
theorem step695 (p : Nat → Bool) (h : Constraints p) : clause p c695 = true := by
  simpa only [c695,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause695
def c696 : List Lit := [(119, false), (243, true), (66, true), (107, true), (113, true)]
theorem step696 (p : Nat → Bool) (h : Constraints p) : clause p c696 = true := by
  simpa only [c696,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause696
def c697 : List Lit := [(120, false), (68, false), (83, false), (99, false)]
theorem step697 (p : Nat → Bool) (h : Constraints p) : clause p c697 = true := by
  simpa only [c697,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause697
def c698 : List Lit := [(120, false), (68, false), (83, false), (109, false)]
theorem step698 (p : Nat → Bool) (h : Constraints p) : clause p c698 = true := by
  simpa only [c698,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause698
def c699 : List Lit := [(120, false), (68, false), (83, false), (116, false)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true := by
  simpa only [c699,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause699
def c700 : List Lit := [(120, false), (68, false), (83, false), (124, false)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true := by
  simpa only [c700,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause700
def c701 : List Lit := [(120, false), (68, false), (99, false), (109, false)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true := by
  simpa only [c701,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause701
def c702 : List Lit := [(120, false), (68, false), (99, false), (116, false)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true := by
  simpa only [c702,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause702
def c703 : List Lit := [(120, false), (68, false), (99, false), (124, false)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true := by
  simpa only [c703,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause703
def c704 : List Lit := [(120, false), (68, false), (109, false), (116, false)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true := by
  simpa only [c704,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause704
def c705 : List Lit := [(120, false), (68, false), (109, false), (124, false)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true := by
  simpa only [c705,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause705
def c706 : List Lit := [(120, false), (68, false), (116, false), (124, false)]
theorem step706 (p : Nat → Bool) (h : Constraints p) : clause p c706 = true := by
  simpa only [c706,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause706
def c707 : List Lit := [(120, false), (83, false), (99, false), (109, false)]
theorem step707 (p : Nat → Bool) (h : Constraints p) : clause p c707 = true := by
  simpa only [c707,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause707
def c708 : List Lit := [(120, false), (83, false), (99, false), (116, false)]
theorem step708 (p : Nat → Bool) (h : Constraints p) : clause p c708 = true := by
  simpa only [c708,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause708
def c709 : List Lit := [(120, false), (83, false), (99, false), (124, false)]
theorem step709 (p : Nat → Bool) (h : Constraints p) : clause p c709 = true := by
  simpa only [c709,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause709
def c710 : List Lit := [(120, false), (83, false), (109, false), (116, false)]
theorem step710 (p : Nat → Bool) (h : Constraints p) : clause p c710 = true := by
  simpa only [c710,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause710
def c711 : List Lit := [(120, false), (83, false), (109, false), (124, false)]
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true := by
  simpa only [c711,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause711
def c712 : List Lit := [(120, false), (83, false), (116, false), (124, false)]
theorem step712 (p : Nat → Bool) (h : Constraints p) : clause p c712 = true := by
  simpa only [c712,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause712
def c713 : List Lit := [(120, false), (99, false), (109, false), (116, false)]
theorem step713 (p : Nat → Bool) (h : Constraints p) : clause p c713 = true := by
  simpa only [c713,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause713
def c714 : List Lit := [(120, false), (99, false), (109, false), (124, false)]
theorem step714 (p : Nat → Bool) (h : Constraints p) : clause p c714 = true := by
  simpa only [c714,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause714
def c715 : List Lit := [(120, false), (109, false), (116, false), (124, false)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true := by
  simpa only [c715,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause715
def c716 : List Lit := [(121, false), (110, false), (117, false), (119, false)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true := by
  simpa only [c716,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause716
def c717 : List Lit := [(121, false), (110, false), (119, false), (123, false)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true := by
  simpa only [c717,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause717
def c718 : List Lit := [(121, false), (110, false), (122, false), (123, false)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true := by
  simpa only [c718,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause718
def c719 : List Lit := [(121, false), (117, false), (119, false), (122, false)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true := by
  simpa only [c719,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause719
def c720 : List Lit := [(121, false), (119, false), (122, false), (123, false)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true := by
  simpa only [c720,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause720
def c721 : List Lit := [(121, false), (245, true), (117, true), (119, true), (122, true), (123, true)]
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true := by
  simpa only [c721,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause721
def c722 : List Lit := [(121, false), (245, true), (110, true), (119, true), (122, true), (123, true)]
theorem step722 (p : Nat → Bool) (h : Constraints p) : clause p c722 = true := by
  simpa only [c722,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause722
def c723 : List Lit := [(121, false), (245, true), (110, true), (117, true), (122, true), (123, true)]
theorem step723 (p : Nat → Bool) (h : Constraints p) : clause p c723 = true := by
  simpa only [c723,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause723
def c724 : List Lit := [(121, false), (245, true), (110, true), (117, true), (119, true), (123, true)]
theorem step724 (p : Nat → Bool) (h : Constraints p) : clause p c724 = true := by
  simpa only [c724,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause724
def c725 : List Lit := [(121, false), (245, true), (110, true), (117, true), (119, true), (122, true)]
theorem step725 (p : Nat → Bool) (h : Constraints p) : clause p c725 = true := by
  simpa only [c725,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause725
def c726 : List Lit := [(122, false), (69, false), (84, false), (100, false)]
theorem step726 (p : Nat → Bool) (h : Constraints p) : clause p c726 = true := by
  simpa only [c726,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause726
def c727 : List Lit := [(122, false), (69, false), (84, false), (111, false)]
theorem step727 (p : Nat → Bool) (h : Constraints p) : clause p c727 = true := by
  simpa only [c727,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause727
def c728 : List Lit := [(122, false), (69, false), (84, false), (121, false)]
theorem step728 (p : Nat → Bool) (h : Constraints p) : clause p c728 = true := by
  simpa only [c728,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause728
def c729 : List Lit := [(122, false), (69, false), (84, false), (124, false)]
theorem step729 (p : Nat → Bool) (h : Constraints p) : clause p c729 = true := by
  simpa only [c729,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause729
def c730 : List Lit := [(122, false), (69, false), (100, false), (111, false)]
theorem step730 (p : Nat → Bool) (h : Constraints p) : clause p c730 = true := by
  simpa only [c730,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause730
def c731 : List Lit := [(122, false), (69, false), (100, false), (121, false)]
theorem step731 (p : Nat → Bool) (h : Constraints p) : clause p c731 = true := by
  simpa only [c731,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause731
def c732 : List Lit := [(122, false), (69, false), (100, false), (124, false)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true := by
  simpa only [c732,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause732
def c733 : List Lit := [(122, false), (69, false), (111, false), (121, false)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true := by
  simpa only [c733,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause733
def c734 : List Lit := [(122, false), (69, false), (111, false), (124, false)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true := by
  simpa only [c734,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause734
def c735 : List Lit := [(122, false), (69, false), (121, false), (124, false)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true := by
  simpa only [c735,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause735
def c736 : List Lit := [(122, false), (84, false), (100, false), (111, false)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true := by
  simpa only [c736,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause736
def c737 : List Lit := [(122, false), (84, false), (100, false), (121, false)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true := by
  simpa only [c737,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause737
def c738 : List Lit := [(122, false), (84, false), (100, false), (124, false)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true := by
  simpa only [c738,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause738
def c739 : List Lit := [(122, false), (84, false), (111, false), (121, false)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true := by
  simpa only [c739,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause739
def c740 : List Lit := [(122, false), (84, false), (111, false), (124, false)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true := by
  simpa only [c740,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause740
def c741 : List Lit := [(122, false), (84, false), (121, false), (124, false)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true := by
  simpa only [c741,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause741
def c742 : List Lit := [(122, false), (100, false), (111, false), (121, false)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true := by
  simpa only [c742,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause742
def c743 : List Lit := [(122, false), (100, false), (111, false), (124, false)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true := by
  simpa only [c743,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause743
def c744 : List Lit := [(122, false), (100, false), (121, false), (124, false)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true := by
  simpa only [c744,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause744
def c745 : List Lit := [(122, false), (111, false), (121, false), (124, false)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true := by
  simpa only [c745,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause745
def c746 : List Lit := [(123, false), (118, false), (121, false), (124, false)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true := by
  simpa only [c746,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause746
def c747 : List Lit := [(123, false), (247, true), (121, true), (124, true)]
theorem step747 (p : Nat → Bool) (h : Constraints p) : clause p c747 = true := by
  simpa only [c747,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause747
def c748 : List Lit := [(123, false), (247, true), (118, true), (124, true)]
theorem step748 (p : Nat → Bool) (h : Constraints p) : clause p c748 = true := by
  simpa only [c748,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause748
def c749 : List Lit := [(124, false), (70, false), (101, false), (112, false)]
theorem step749 (p : Nat → Bool) (h : Constraints p) : clause p c749 = true := by
  simpa only [c749,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause749
def c750 : List Lit := [(124, false), (70, false), (101, false), (123, false)]
theorem step750 (p : Nat → Bool) (h : Constraints p) : clause p c750 = true := by
  simpa only [c750,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause750
def c751 : List Lit := [(124, false), (70, false), (112, false), (120, false)]
theorem step751 (p : Nat → Bool) (h : Constraints p) : clause p c751 = true := by
  simpa only [c751,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause751
def c752 : List Lit := [(124, false), (70, false), (112, false), (122, false)]
theorem step752 (p : Nat → Bool) (h : Constraints p) : clause p c752 = true := by
  simpa only [c752,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause752
def c753 : List Lit := [(124, false), (70, false), (112, false), (123, false)]
theorem step753 (p : Nat → Bool) (h : Constraints p) : clause p c753 = true := by
  simpa only [c753,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause753
def c754 : List Lit := [(124, false), (70, false), (120, false), (123, false)]
theorem step754 (p : Nat → Bool) (h : Constraints p) : clause p c754 = true := by
  simpa only [c754,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause754
def c755 : List Lit := [(124, false), (70, false), (122, false), (123, false)]
theorem step755 (p : Nat → Bool) (h : Constraints p) : clause p c755 = true := by
  simpa only [c755,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause755
def c756 : List Lit := [(124, false), (85, false), (101, false), (112, false)]
theorem step756 (p : Nat → Bool) (h : Constraints p) : clause p c756 = true := by
  simpa only [c756,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause756
def c757 : List Lit := [(124, false), (85, false), (101, false), (123, false)]
theorem step757 (p : Nat → Bool) (h : Constraints p) : clause p c757 = true := by
  simpa only [c757,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause757
def c758 : List Lit := [(124, false), (85, false), (112, false), (122, false)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true := by
  simpa only [c758,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause758
def c759 : List Lit := [(124, false), (85, false), (112, false), (123, false)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true := by
  simpa only [c759,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause759
def c760 : List Lit := [(124, false), (85, false), (122, false), (123, false)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true := by
  simpa only [c760,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause760
def c761 : List Lit := [(124, false), (101, false), (112, false), (120, false)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true := by
  simpa only [c761,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause761
def c762 : List Lit := [(124, false), (101, false), (112, false), (122, false)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true := by
  simpa only [c762,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause762
def c763 : List Lit := [(124, false), (101, false), (112, false), (123, false)]
theorem step763 (p : Nat → Bool) (h : Constraints p) : clause p c763 = true := by
  simpa only [c763,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause763
def c764 : List Lit := [(124, false), (101, false), (120, false), (123, false)]
theorem step764 (p : Nat → Bool) (h : Constraints p) : clause p c764 = true := by
  simpa only [c764,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause764
def c765 : List Lit := [(124, false), (112, false), (120, false), (122, false)]
theorem step765 (p : Nat → Bool) (h : Constraints p) : clause p c765 = true := by
  simpa only [c765,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause765
def c766 : List Lit := [(124, false), (112, false), (120, false), (123, false)]
theorem step766 (p : Nat → Bool) (h : Constraints p) : clause p c766 = true := by
  simpa only [c766,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause766
def c767 : List Lit := [(124, false), (112, false), (122, false), (123, false)]
theorem step767 (p : Nat → Bool) (h : Constraints p) : clause p c767 = true := by
  simpa only [c767,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause767
def c768 : List Lit := [(124, false), (120, false), (122, false), (123, false)]
theorem step768 (p : Nat → Bool) (h : Constraints p) : clause p c768 = true := by
  simpa only [c768,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause768
def c769 : List Lit := [(127, false)]
theorem step769 (p : Nat → Bool) (h : Constraints p) : clause p c769 = true := by
  simpa only [c769,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause769
def c770 : List Lit := [(129, false)]
theorem step770 (p : Nat → Bool) (h : Constraints p) : clause p c770 = true := by
  simpa only [c770,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause770
def c771 : List Lit := [(130, false)]
theorem step771 (p : Nat → Bool) (h : Constraints p) : clause p c771 = true := by
  simpa only [c771,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause771
def c772 : List Lit := [(132, false)]
theorem step772 (p : Nat → Bool) (h : Constraints p) : clause p c772 = true := by
  simpa only [c772,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause772
def c773 : List Lit := [(133, false)]
theorem step773 (p : Nat → Bool) (h : Constraints p) : clause p c773 = true := by
  simpa only [c773,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause773
def c774 : List Lit := [(136, false)]
theorem step774 (p : Nat → Bool) (h : Constraints p) : clause p c774 = true := by
  simpa only [c774,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause774
def c775 : List Lit := [(137, false)]
theorem step775 (p : Nat → Bool) (h : Constraints p) : clause p c775 = true := by
  simpa only [c775,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause775
def c776 : List Lit := [(140, false)]
theorem step776 (p : Nat → Bool) (h : Constraints p) : clause p c776 = true := by
  simpa only [c776,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause776
def c777 : List Lit := [(142, false)]
theorem step777 (p : Nat → Bool) (h : Constraints p) : clause p c777 = true := by
  simpa only [c777,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause777
def c778 : List Lit := [(145, false)]
theorem step778 (p : Nat → Bool) (h : Constraints p) : clause p c778 = true := by
  simpa only [c778,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause778
def c779 : List Lit := [(148, false)]
theorem step779 (p : Nat → Bool) (h : Constraints p) : clause p c779 = true := by
  simpa only [c779,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause779
def c780 : List Lit := [(151, false)]
theorem step780 (p : Nat → Bool) (h : Constraints p) : clause p c780 = true := by
  simpa only [c780,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause780
def c781 : List Lit := [(153, false)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true := by
  simpa only [c781,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause781
def c782 : List Lit := [(154, false)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true := by
  simpa only [c782,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause782
def c783 : List Lit := [(155, false)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true := by
  simpa only [c783,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause783
def c784 : List Lit := [(158, false)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true := by
  simpa only [c784,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause784
def c785 : List Lit := [(159, false)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true := by
  simpa only [c785,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause785
def c786 : List Lit := [(161, false)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true := by
  simpa only [c786,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause786
def c787 : List Lit := [(162, false)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true := by
  simpa only [c787,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause787
def c788 : List Lit := [(164, false)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true := by
  simpa only [c788,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause788
def c789 : List Lit := [(166, false)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true := by
  simpa only [c789,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause789
def c790 : List Lit := [(169, false)]
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true := by
  simpa only [c790,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause790
def c791 : List Lit := [(171, false)]
theorem step791 (p : Nat → Bool) (h : Constraints p) : clause p c791 = true := by
  simpa only [c791,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause791
def c792 : List Lit := [(172, false)]
theorem step792 (p : Nat → Bool) (h : Constraints p) : clause p c792 = true := by
  simpa only [c792,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause792
def c793 : List Lit := [(173, false)]
theorem step793 (p : Nat → Bool) (h : Constraints p) : clause p c793 = true := by
  simpa only [c793,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause793
def c794 : List Lit := [(177, false)]
theorem step794 (p : Nat → Bool) (h : Constraints p) : clause p c794 = true := by
  simpa only [c794,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause794
def c795 : List Lit := [(178, false)]
theorem step795 (p : Nat → Bool) (h : Constraints p) : clause p c795 = true := by
  simpa only [c795,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause795
def c796 : List Lit := [(180, false)]
theorem step796 (p : Nat → Bool) (h : Constraints p) : clause p c796 = true := by
  simpa only [c796,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause796
def c797 : List Lit := [(184, false)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true := by
  simpa only [c797,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause797
def c798 : List Lit := [(185, false)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true := by
  simpa only [c798,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause798
def c799 : List Lit := [(189, false)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true := by
  simpa only [c799,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause799
def c800 : List Lit := [(190, false)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true := by
  simpa only [c800,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause800
def c801 : List Lit := [(192, false)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true := by
  simpa only [c801,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause801
def c802 : List Lit := [(193, false)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true := by
  simpa only [c802,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause802
def c803 : List Lit := [(197, false)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true := by
  simpa only [c803,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause803
def c804 : List Lit := [(199, false)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true := by
  simpa only [c804,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause804
def c805 : List Lit := [(200, false)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true := by
  simpa only [c805,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause805
def c806 : List Lit := [(202, false)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true := by
  simpa only [c806,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause806
def c807 : List Lit := [(207, false)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true := by
  simpa only [c807,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause807
def c808 : List Lit := [(208, false)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true := by
  simpa only [c808,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause808
def c809 : List Lit := [(212, false)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true := by
  simpa only [c809,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause809
def c810 : List Lit := [(215, false)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true := by
  simpa only [c810,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause810
def c811 : List Lit := [(216, false)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true := by
  simpa only [c811,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause811
def c812 : List Lit := [(218, false)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true := by
  simpa only [c812,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause812
def c813 : List Lit := [(220, false)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true := by
  simpa only [c813,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause813
def c814 : List Lit := [(223, false)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true := by
  simpa only [c814,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause814
def c815 : List Lit := [(224, false)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true := by
  simpa only [c815,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause815
def c816 : List Lit := [(228, false)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true := by
  simpa only [c816,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause816
def c817 : List Lit := [(230, false)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true := by
  simpa only [c817,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause817
def c818 : List Lit := [(233, false)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true := by
  simpa only [c818,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause818
def c819 : List Lit := [(235, false)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true := by
  simpa only [c819,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause819
def c820 : List Lit := [(237, false)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true := by
  simpa only [c820,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause820
def c821 : List Lit := [(240, false)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true := by
  simpa only [c821,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause821
def c822 : List Lit := [(242, false)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true := by
  simpa only [c822,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause822
def c823 : List Lit := [(245, false)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true := by
  simpa only [c823,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause823
def c824 : List Lit := [(128, false), (249, true)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true := by
  simpa only [c824,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause824
def c825 : List Lit := [(249, false), (251, true)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true := by
  simpa only [c825,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause825
def c826 : List Lit := [(125, false), (251, true)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true := by
  simpa only [c826,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause826
def c827 : List Lit := [(125, false), (249, false), (252, true)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true := by
  simpa only [c827,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause827
def c828 : List Lit := [(131, false), (255, true)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true := by
  simpa only [c828,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause828
def c829 : List Lit := [(255, false), (257, true)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true := by
  simpa only [c829,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause829
def c830 : List Lit := [(257, false), (259, true)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true := by
  simpa only [c830,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause830
def c831 : List Lit := [(251, false), (259, true)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true := by
  simpa only [c831,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause831
def c832 : List Lit := [(252, false), (260, true)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true := by
  simpa only [c832,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause832
def c833 : List Lit := [(134, false), (261, true)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true := by
  simpa only [c833,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause833
def c834 : List Lit := [(135, false), (263, true)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true := by
  simpa only [c834,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause834
def c835 : List Lit := [(263, false), (265, true)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true := by
  simpa only [c835,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause835
def c836 : List Lit := [(261, false), (265, true)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true := by
  simpa only [c836,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause836
def c837 : List Lit := [(138, false), (267, true)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true := by
  simpa only [c837,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause837
def c838 : List Lit := [(267, false), (271, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true := by
  simpa only [c838,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause838
def c839 : List Lit := [(271, false), (273, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true := by
  simpa only [c839,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause839
def c840 : List Lit := [(265, false), (273, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true := by
  simpa only [c840,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause840
def c841 : List Lit := [(273, false), (275, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true := by
  simpa only [c841,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause841
def c842 : List Lit := [(259, false), (275, true)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true := by
  simpa only [c842,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause842
def c843 : List Lit := [(259, false), (273, false), (276, true)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true := by
  simpa only [c843,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause843
def c844 : List Lit := [(260, false), (276, true)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true := by
  simpa only [c844,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause844
def c845 : List Lit := [(141, false), (279, true)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true := by
  simpa only [c845,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause845
def c846 : List Lit := [(144, false), (281, true)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true := by
  simpa only [c846,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause846
def c847 : List Lit := [(147, false), (283, true)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true := by
  simpa only [c847,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause847
def c848 : List Lit := [(283, false), (285, true)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true := by
  simpa only [c848,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause848
def c849 : List Lit := [(281, false), (285, true)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true := by
  simpa only [c849,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause849
def c850 : List Lit := [(281, false), (283, false), (286, true)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true := by
  simpa only [c850,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause850
def c851 : List Lit := [(285, false), (287, true)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true := by
  simpa only [c851,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause851
def c852 : List Lit := [(286, false), (288, true)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true := by
  simpa only [c852,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause852
def c853 : List Lit := [(279, false), (287, true)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true := by
  simpa only [c853,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause853
def c854 : List Lit := [(279, false), (285, false), (288, true)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true := by
  simpa only [c854,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause854
def c855 : List Lit := [(149, false), (289, true)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true := by
  simpa only [c855,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause855
def c856 : List Lit := [(289, false), (293, true)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true := by
  simpa only [c856,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause856
def c857 : List Lit := [(293, false), (301, true)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true := by
  simpa only [c857,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause857
def c858 : List Lit := [(301, false), (303, true)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true := by
  simpa only [c858,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause858
def c859 : List Lit := [(287, false), (303, true)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true := by
  simpa only [c859,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause859
def c860 : List Lit := [(288, false), (304, true)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true := by
  simpa only [c860,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause860
def c861 : List Lit := [(303, false), (305, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true := by
  simpa only [c861,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause861
def c862 : List Lit := [(304, false), (306, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true := by
  simpa only [c862,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause862
def c863 : List Lit := [(275, false), (305, true)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true := by
  simpa only [c863,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause863
def c864 : List Lit := [(275, false), (303, false), (306, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true := by
  simpa only [c864,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause864
def c865 : List Lit := [(276, false), (306, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true := by
  simpa only [c865,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause865
def c866 : List Lit := [(157, false), (307, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true := by
  simpa only [c866,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause866
def c867 : List Lit := [(307, false), (309, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true := by
  simpa only [c867,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause867
def c868 : List Lit := [(156, false), (309, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true := by
  simpa only [c868,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause868
def c869 : List Lit := [(156, false), (307, false), (310, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true := by
  simpa only [c869,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause869
def c870 : List Lit := [(160, false), (311, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true := by
  simpa only [c870,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause870
def c871 : List Lit := [(311, false), (315, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true := by
  simpa only [c871,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause871
def c872 : List Lit := [(315, false), (317, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true := by
  simpa only [c872,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause872
def c873 : List Lit := [(309, false), (317, true)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true := by
  simpa only [c873,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause873
def c874 : List Lit := [(310, false), (318, true)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true := by
  simpa only [c874,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause874
def c875 : List Lit := [(163, false), (319, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true := by
  simpa only [c875,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause875
def c876 : List Lit := [(165, false), (321, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true := by
  simpa only [c876,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause876
def c877 : List Lit := [(321, false), (323, true)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true := by
  simpa only [c877,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause877
def c878 : List Lit := [(319, false), (323, true)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true := by
  simpa only [c878,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause878
def c879 : List Lit := [(168, false), (325, true)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true := by
  simpa only [c879,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause879
def c880 : List Lit := [(170, false), (327, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true := by
  simpa only [c880,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause880
def c881 : List Lit := [(327, false), (329, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true := by
  simpa only [c881,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause881
def c882 : List Lit := [(325, false), (329, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true := by
  simpa only [c882,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause882
def c883 : List Lit := [(329, false), (331, true)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true := by
  simpa only [c883,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause883
def c884 : List Lit := [(323, false), (331, true)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true := by
  simpa only [c884,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause884
def c885 : List Lit := [(331, false), (333, true)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true := by
  simpa only [c885,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause885
def c886 : List Lit := [(317, false), (333, true)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true := by
  simpa only [c886,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause886
def c887 : List Lit := [(317, false), (331, false), (334, true)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true := by
  simpa only [c887,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause887
def c888 : List Lit := [(318, false), (334, true)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true := by
  simpa only [c888,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause888
def c889 : List Lit := [(174, false), (337, true)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true := by
  simpa only [c889,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause889
def c890 : List Lit := [(337, false), (339, true)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true := by
  simpa only [c890,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause890
def c891 : List Lit := [(176, false), (341, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true := by
  simpa only [c891,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause891
def c892 : List Lit := [(341, false), (345, true)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true := by
  simpa only [c892,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause892
def c893 : List Lit := [(345, false), (347, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true := by
  simpa only [c893,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause893
def c894 : List Lit := [(339, false), (347, true)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true := by
  simpa only [c894,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause894
def c895 : List Lit := [(339, false), (345, false), (348, true)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true := by
  simpa only [c895,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause895
def c896 : List Lit := [(179, false), (349, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true := by
  simpa only [c896,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause896
def c897 : List Lit := [(349, false), (353, true)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true := by
  simpa only [c897,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause897
def c898 : List Lit := [(183, false), (355, true)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true := by
  simpa only [c898,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause898
def c899 : List Lit := [(186, false), (357, true)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true := by
  simpa only [c899,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause899
def c900 : List Lit := [(357, false), (359, true)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true := by
  simpa only [c900,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause900
def c901 : List Lit := [(355, false), (359, true)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true := by
  simpa only [c901,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause901
def c902 : List Lit := [(359, false), (361, true)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true := by
  simpa only [c902,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause902
def c903 : List Lit := [(353, false), (361, true)]
theorem step903 (p : Nat → Bool) (h : Constraints p) : clause p c903 = true := by
  simpa only [c903,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause903
def c904 : List Lit := [(353, false), (359, false), (362, true)]
theorem step904 (p : Nat → Bool) (h : Constraints p) : clause p c904 = true := by
  simpa only [c904,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause904
def c905 : List Lit := [(361, false), (363, true)]
theorem step905 (p : Nat → Bool) (h : Constraints p) : clause p c905 = true := by
  simpa only [c905,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause905
def c906 : List Lit := [(362, false), (364, true)]
theorem step906 (p : Nat → Bool) (h : Constraints p) : clause p c906 = true := by
  simpa only [c906,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause906
def c907 : List Lit := [(347, false), (363, true)]
theorem step907 (p : Nat → Bool) (h : Constraints p) : clause p c907 = true := by
  simpa only [c907,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause907
def c908 : List Lit := [(347, false), (361, false), (364, true)]
theorem step908 (p : Nat → Bool) (h : Constraints p) : clause p c908 = true := by
  simpa only [c908,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause908
def c909 : List Lit := [(348, false), (364, true)]
theorem step909 (p : Nat → Bool) (h : Constraints p) : clause p c909 = true := by
  simpa only [c909,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause909
def c910 : List Lit := [(363, false), (365, true)]
theorem step910 (p : Nat → Bool) (h : Constraints p) : clause p c910 = true := by
  simpa only [c910,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause910
def c911 : List Lit := [(364, false), (366, true)]
theorem step911 (p : Nat → Bool) (h : Constraints p) : clause p c911 = true := by
  simpa only [c911,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause911
def c912 : List Lit := [(333, false), (365, true)]
theorem step912 (p : Nat → Bool) (h : Constraints p) : clause p c912 = true := by
  simpa only [c912,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause912
def c913 : List Lit := [(333, false), (363, false), (366, true)]
theorem step913 (p : Nat → Bool) (h : Constraints p) : clause p c913 = true := by
  simpa only [c913,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause913
def c914 : List Lit := [(334, false), (366, true)]
theorem step914 (p : Nat → Bool) (h : Constraints p) : clause p c914 = true := by
  simpa only [c914,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause914
def c915 : List Lit := [(365, false), (367, true)]
theorem step915 (p : Nat → Bool) (h : Constraints p) : clause p c915 = true := by
  simpa only [c915,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause915
def c916 : List Lit := [(366, false), (368, true)]
theorem step916 (p : Nat → Bool) (h : Constraints p) : clause p c916 = true := by
  simpa only [c916,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause916
def c917 : List Lit := [(305, false), (367, true)]
theorem step917 (p : Nat → Bool) (h : Constraints p) : clause p c917 = true := by
  simpa only [c917,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause917
def c918 : List Lit := [(305, false), (365, false), (368, true)]
theorem step918 (p : Nat → Bool) (h : Constraints p) : clause p c918 = true := by
  simpa only [c918,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause918
def c919 : List Lit := [(306, false), (368, true)]
theorem step919 (p : Nat → Bool) (h : Constraints p) : clause p c919 = true := by
  simpa only [c919,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause919
def c920 : List Lit := [(188, false), (369, true)]
theorem step920 (p : Nat → Bool) (h : Constraints p) : clause p c920 = true := by
  simpa only [c920,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause920
def c921 : List Lit := [(369, false), (371, true)]
theorem step921 (p : Nat → Bool) (h : Constraints p) : clause p c921 = true := by
  simpa only [c921,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause921
def c922 : List Lit := [(371, false), (379, true)]
theorem step922 (p : Nat → Bool) (h : Constraints p) : clause p c922 = true := by
  simpa only [c922,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause922
def c923 : List Lit := [(195, false), (381, true)]
theorem step923 (p : Nat → Bool) (h : Constraints p) : clause p c923 = true := by
  simpa only [c923,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause923
def c924 : List Lit := [(194, false), (381, true)]
theorem step924 (p : Nat → Bool) (h : Constraints p) : clause p c924 = true := by
  simpa only [c924,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause924
def c925 : List Lit := [(196, false), (383, true)]
theorem step925 (p : Nat → Bool) (h : Constraints p) : clause p c925 = true := by
  simpa only [c925,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause925
def c926 : List Lit := [(383, false), (385, true)]
theorem step926 (p : Nat → Bool) (h : Constraints p) : clause p c926 = true := by
  simpa only [c926,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause926
def c927 : List Lit := [(381, false), (385, true)]
theorem step927 (p : Nat → Bool) (h : Constraints p) : clause p c927 = true := by
  simpa only [c927,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause927
def c928 : List Lit := [(198, false), (387, true)]
theorem step928 (p : Nat → Bool) (h : Constraints p) : clause p c928 = true := by
  simpa only [c928,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause928
def c929 : List Lit := [(201, false), (389, true)]
theorem step929 (p : Nat → Bool) (h : Constraints p) : clause p c929 = true := by
  simpa only [c929,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause929
def c930 : List Lit := [(389, false), (391, true)]
theorem step930 (p : Nat → Bool) (h : Constraints p) : clause p c930 = true := by
  simpa only [c930,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause930
def c931 : List Lit := [(387, false), (391, true)]
theorem step931 (p : Nat → Bool) (h : Constraints p) : clause p c931 = true := by
  simpa only [c931,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause931
def c932 : List Lit := [(391, false), (393, true)]
theorem step932 (p : Nat → Bool) (h : Constraints p) : clause p c932 = true := by
  simpa only [c932,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause932
def c933 : List Lit := [(385, false), (393, true)]
theorem step933 (p : Nat → Bool) (h : Constraints p) : clause p c933 = true := by
  simpa only [c933,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause933
def c934 : List Lit := [(393, false), (395, true)]
theorem step934 (p : Nat → Bool) (h : Constraints p) : clause p c934 = true := by
  simpa only [c934,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause934
def c935 : List Lit := [(379, false), (395, true)]
theorem step935 (p : Nat → Bool) (h : Constraints p) : clause p c935 = true := by
  simpa only [c935,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause935
def c936 : List Lit := [(203, false), (397, true)]
theorem step936 (p : Nat → Bool) (h : Constraints p) : clause p c936 = true := by
  simpa only [c936,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause936
def c937 : List Lit := [(205, false), (399, true)]
theorem step937 (p : Nat → Bool) (h : Constraints p) : clause p c937 = true := by
  simpa only [c937,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause937
def c938 : List Lit := [(399, false), (401, true)]
theorem step938 (p : Nat → Bool) (h : Constraints p) : clause p c938 = true := by
  simpa only [c938,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause938
def c939 : List Lit := [(397, false), (401, true)]
theorem step939 (p : Nat → Bool) (h : Constraints p) : clause p c939 = true := by
  simpa only [c939,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause939
def c940 : List Lit := [(209, false), (405, true)]
theorem step940 (p : Nat → Bool) (h : Constraints p) : clause p c940 = true := by
  simpa only [c940,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause940
def c941 : List Lit := [(405, false), (407, true)]
theorem step941 (p : Nat → Bool) (h : Constraints p) : clause p c941 = true := by
  simpa only [c941,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause941
def c942 : List Lit := [(407, false), (409, true)]
theorem step942 (p : Nat → Bool) (h : Constraints p) : clause p c942 = true := by
  simpa only [c942,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause942
def c943 : List Lit := [(401, false), (409, true)]
theorem step943 (p : Nat → Bool) (h : Constraints p) : clause p c943 = true := by
  simpa only [c943,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause943
def c944 : List Lit := [(211, false), (411, true)]
theorem step944 (p : Nat → Bool) (h : Constraints p) : clause p c944 = true := by
  simpa only [c944,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause944
def c945 : List Lit := [(210, false), (411, true)]
theorem step945 (p : Nat → Bool) (h : Constraints p) : clause p c945 = true := by
  simpa only [c945,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause945
def c946 : List Lit := [(411, false), (415, true)]
theorem step946 (p : Nat → Bool) (h : Constraints p) : clause p c946 = true := by
  simpa only [c946,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause946
def c947 : List Lit := [(214, false), (417, true)]
theorem step947 (p : Nat → Bool) (h : Constraints p) : clause p c947 = true := by
  simpa only [c947,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause947
def c948 : List Lit := [(217, false), (419, true)]
theorem step948 (p : Nat → Bool) (h : Constraints p) : clause p c948 = true := by
  simpa only [c948,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause948
def c949 : List Lit := [(419, false), (421, true)]
theorem step949 (p : Nat → Bool) (h : Constraints p) : clause p c949 = true := by
  simpa only [c949,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause949
def c950 : List Lit := [(417, false), (421, true)]
theorem step950 (p : Nat → Bool) (h : Constraints p) : clause p c950 = true := by
  simpa only [c950,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause950
def c951 : List Lit := [(421, false), (423, true)]
theorem step951 (p : Nat → Bool) (h : Constraints p) : clause p c951 = true := by
  simpa only [c951,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause951
def c952 : List Lit := [(415, false), (423, true)]
theorem step952 (p : Nat → Bool) (h : Constraints p) : clause p c952 = true := by
  simpa only [c952,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause952
def c953 : List Lit := [(415, false), (421, false), (424, true)]
theorem step953 (p : Nat → Bool) (h : Constraints p) : clause p c953 = true := by
  simpa only [c953,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause953
def c954 : List Lit := [(423, false), (425, true)]
theorem step954 (p : Nat → Bool) (h : Constraints p) : clause p c954 = true := by
  simpa only [c954,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause954
def c955 : List Lit := [(424, false), (426, true)]
theorem step955 (p : Nat → Bool) (h : Constraints p) : clause p c955 = true := by
  simpa only [c955,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause955
def c956 : List Lit := [(409, false), (425, true)]
theorem step956 (p : Nat → Bool) (h : Constraints p) : clause p c956 = true := by
  simpa only [c956,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause956
def c957 : List Lit := [(425, false), (427, true)]
theorem step957 (p : Nat → Bool) (h : Constraints p) : clause p c957 = true := by
  simpa only [c957,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause957
def c958 : List Lit := [(426, false), (428, true)]
theorem step958 (p : Nat → Bool) (h : Constraints p) : clause p c958 = true := by
  simpa only [c958,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause958
def c959 : List Lit := [(395, false), (427, true)]
theorem step959 (p : Nat → Bool) (h : Constraints p) : clause p c959 = true := by
  simpa only [c959,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause959
def c960 : List Lit := [(395, false), (425, false), (428, true)]
theorem step960 (p : Nat → Bool) (h : Constraints p) : clause p c960 = true := by
  simpa only [c960,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block29.clause960
def c961 : List Lit := [(219, false), (429, true)]
theorem step961 (p : Nat → Bool) (h : Constraints p) : clause p c961 = true := by
  simpa only [c961,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause961
def c962 : List Lit := [(429, false), (431, true)]
theorem step962 (p : Nat → Bool) (h : Constraints p) : clause p c962 = true := by
  simpa only [c962,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause962
def c963 : List Lit := [(221, false), (433, true)]
theorem step963 (p : Nat → Bool) (h : Constraints p) : clause p c963 = true := by
  simpa only [c963,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause963
def c964 : List Lit := [(433, false), (437, true)]
theorem step964 (p : Nat → Bool) (h : Constraints p) : clause p c964 = true := by
  simpa only [c964,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause964
def c965 : List Lit := [(437, false), (439, true)]
theorem step965 (p : Nat → Bool) (h : Constraints p) : clause p c965 = true := by
  simpa only [c965,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause965
def c966 : List Lit := [(431, false), (439, true)]
theorem step966 (p : Nat → Bool) (h : Constraints p) : clause p c966 = true := by
  simpa only [c966,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause966
def c967 : List Lit := [(226, false), (441, true)]
theorem step967 (p : Nat → Bool) (h : Constraints p) : clause p c967 = true := by
  simpa only [c967,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause967
def c968 : List Lit := [(225, false), (441, true)]
theorem step968 (p : Nat → Bool) (h : Constraints p) : clause p c968 = true := by
  simpa only [c968,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause968
def c969 : List Lit := [(225, false), (226, false), (442, true)]
theorem step969 (p : Nat → Bool) (h : Constraints p) : clause p c969 = true := by
  simpa only [c969,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause969
def c970 : List Lit := [(441, false), (445, true)]
theorem step970 (p : Nat → Bool) (h : Constraints p) : clause p c970 = true := by
  simpa only [c970,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause970
def c971 : List Lit := [(442, false), (446, true)]
theorem step971 (p : Nat → Bool) (h : Constraints p) : clause p c971 = true := by
  simpa only [c971,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause971
def c972 : List Lit := [(229, false), (447, true)]
theorem step972 (p : Nat → Bool) (h : Constraints p) : clause p c972 = true := by
  simpa only [c972,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause972
def c973 : List Lit := [(447, false), (451, true)]
theorem step973 (p : Nat → Bool) (h : Constraints p) : clause p c973 = true := by
  simpa only [c973,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause973
def c974 : List Lit := [(451, false), (453, true)]
theorem step974 (p : Nat → Bool) (h : Constraints p) : clause p c974 = true := by
  simpa only [c974,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause974
def c975 : List Lit := [(445, false), (453, true)]
theorem step975 (p : Nat → Bool) (h : Constraints p) : clause p c975 = true := by
  simpa only [c975,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause975
def c976 : List Lit := [(446, false), (454, true)]
theorem step976 (p : Nat → Bool) (h : Constraints p) : clause p c976 = true := by
  simpa only [c976,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause976
def c977 : List Lit := [(453, false), (455, true)]
theorem step977 (p : Nat → Bool) (h : Constraints p) : clause p c977 = true := by
  simpa only [c977,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause977
def c978 : List Lit := [(454, false), (456, true)]
theorem step978 (p : Nat → Bool) (h : Constraints p) : clause p c978 = true := by
  simpa only [c978,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause978
def c979 : List Lit := [(439, false), (455, true)]
theorem step979 (p : Nat → Bool) (h : Constraints p) : clause p c979 = true := by
  simpa only [c979,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause979
def c980 : List Lit := [(439, false), (453, false), (456, true)]
theorem step980 (p : Nat → Bool) (h : Constraints p) : clause p c980 = true := by
  simpa only [c980,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause980
def c981 : List Lit := [(234, false), (457, true)]
theorem step981 (p : Nat → Bool) (h : Constraints p) : clause p c981 = true := by
  simpa only [c981,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause981
def c982 : List Lit := [(236, false), (459, true)]
theorem step982 (p : Nat → Bool) (h : Constraints p) : clause p c982 = true := by
  simpa only [c982,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause982
def c983 : List Lit := [(459, false), (461, true)]
theorem step983 (p : Nat → Bool) (h : Constraints p) : clause p c983 = true := by
  simpa only [c983,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause983
def c984 : List Lit := [(457, false), (461, true)]
theorem step984 (p : Nat → Bool) (h : Constraints p) : clause p c984 = true := by
  simpa only [c984,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause984
def c985 : List Lit := [(238, false), (463, true)]
theorem step985 (p : Nat → Bool) (h : Constraints p) : clause p c985 = true := by
  simpa only [c985,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause985
def c986 : List Lit := [(239, false), (465, true)]
theorem step986 (p : Nat → Bool) (h : Constraints p) : clause p c986 = true := by
  simpa only [c986,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause986
def c987 : List Lit := [(465, false), (467, true)]
theorem step987 (p : Nat → Bool) (h : Constraints p) : clause p c987 = true := by
  simpa only [c987,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause987
def c988 : List Lit := [(463, false), (467, true)]
theorem step988 (p : Nat → Bool) (h : Constraints p) : clause p c988 = true := by
  simpa only [c988,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause988
def c989 : List Lit := [(467, false), (469, true)]
theorem step989 (p : Nat → Bool) (h : Constraints p) : clause p c989 = true := by
  simpa only [c989,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause989
def c990 : List Lit := [(461, false), (469, true)]
theorem step990 (p : Nat → Bool) (h : Constraints p) : clause p c990 = true := by
  simpa only [c990,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause990
def c991 : List Lit := [(243, false), (473, true)]
theorem step991 (p : Nat → Bool) (h : Constraints p) : clause p c991 = true := by
  simpa only [c991,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause991
def c992 : List Lit := [(473, false), (475, true)]
theorem step992 (p : Nat → Bool) (h : Constraints p) : clause p c992 = true := by
  simpa only [c992,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block30.clause992
def c993 : List Lit := [(247, false), (479, true)]
theorem step993 (p : Nat → Bool) (h : Constraints p) : clause p c993 = true := by
  simpa only [c993,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause993
def c994 : List Lit := [(479, false), (481, true)]
theorem step994 (p : Nat → Bool) (h : Constraints p) : clause p c994 = true := by
  simpa only [c994,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause994
def c995 : List Lit := [(481, false), (483, true)]
theorem step995 (p : Nat → Bool) (h : Constraints p) : clause p c995 = true := by
  simpa only [c995,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause995
def c996 : List Lit := [(475, false), (483, true)]
theorem step996 (p : Nat → Bool) (h : Constraints p) : clause p c996 = true := by
  simpa only [c996,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause996
def c997 : List Lit := [(475, false), (481, false), (484, true)]
theorem step997 (p : Nat → Bool) (h : Constraints p) : clause p c997 = true := by
  simpa only [c997,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause997
def c998 : List Lit := [(483, false), (485, true)]
theorem step998 (p : Nat → Bool) (h : Constraints p) : clause p c998 = true := by
  simpa only [c998,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause998
def c999 : List Lit := [(484, false), (486, true)]
theorem step999 (p : Nat → Bool) (h : Constraints p) : clause p c999 = true := by
  simpa only [c999,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause999
def c1000 : List Lit := [(469, false), (485, true)]
theorem step1000 (p : Nat → Bool) (h : Constraints p) : clause p c1000 = true := by
  simpa only [c1000,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1000
def c1001 : List Lit := [(469, false), (483, false), (486, true)]
theorem step1001 (p : Nat → Bool) (h : Constraints p) : clause p c1001 = true := by
  simpa only [c1001,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1001
def c1002 : List Lit := [(485, false), (487, true)]
theorem step1002 (p : Nat → Bool) (h : Constraints p) : clause p c1002 = true := by
  simpa only [c1002,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1002
def c1003 : List Lit := [(486, false), (488, true)]
theorem step1003 (p : Nat → Bool) (h : Constraints p) : clause p c1003 = true := by
  simpa only [c1003,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1003
def c1004 : List Lit := [(455, false), (487, true)]
theorem step1004 (p : Nat → Bool) (h : Constraints p) : clause p c1004 = true := by
  simpa only [c1004,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1004
def c1005 : List Lit := [(455, false), (485, false), (488, true)]
theorem step1005 (p : Nat → Bool) (h : Constraints p) : clause p c1005 = true := by
  simpa only [c1005,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1005
def c1006 : List Lit := [(456, false), (488, true)]
theorem step1006 (p : Nat → Bool) (h : Constraints p) : clause p c1006 = true := by
  simpa only [c1006,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1006
def c1007 : List Lit := [(487, false), (489, true)]
theorem step1007 (p : Nat → Bool) (h : Constraints p) : clause p c1007 = true := by
  simpa only [c1007,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1007
def c1008 : List Lit := [(488, false), (490, true)]
theorem step1008 (p : Nat → Bool) (h : Constraints p) : clause p c1008 = true := by
  simpa only [c1008,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1008
def c1009 : List Lit := [(427, false), (489, true)]
theorem step1009 (p : Nat → Bool) (h : Constraints p) : clause p c1009 = true := by
  simpa only [c1009,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1009
def c1010 : List Lit := [(427, false), (487, false), (490, true)]
theorem step1010 (p : Nat → Bool) (h : Constraints p) : clause p c1010 = true := by
  simpa only [c1010,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1010
def c1011 : List Lit := [(428, false), (490, true)]
theorem step1011 (p : Nat → Bool) (h : Constraints p) : clause p c1011 = true := by
  simpa only [c1011,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1011
def c1012 : List Lit := [(490, false), (492, true)]
theorem step1012 (p : Nat → Bool) (h : Constraints p) : clause p c1012 = true := by
  simpa only [c1012,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1012
def c1013 : List Lit := [(367, false), (489, false), (492, true)]
theorem step1013 (p : Nat → Bool) (h : Constraints p) : clause p c1013 = true := by
  simpa only [c1013,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1013
def c1014 : List Lit := [(368, false), (492, true)]
theorem step1014 (p : Nat → Bool) (h : Constraints p) : clause p c1014 = true := by
  simpa only [c1014,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1014
def c1015 : List Lit := [(492, false)]
theorem step1015 (p : Nat → Bool) (h : Constraints p) : clause p c1015 = true := by
  simpa only [c1015,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1015
def c1016 : List Lit := [(5, true), (1497, true)]
theorem step1016 (p : Nat → Bool) (h : Constraints p) : clause p c1016 = true := by
  simpa only [c1016,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1016
def c1017 : List Lit := [(3, true), (1497, true)]
theorem step1017 (p : Nat → Bool) (h : Constraints p) : clause p c1017 = true := by
  simpa only [c1017,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1017
def c1018 : List Lit := [(3, true), (5, true), (1498, true)]
theorem step1018 (p : Nat → Bool) (h : Constraints p) : clause p c1018 = true := by
  simpa only [c1018,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1018
def c1019 : List Lit := [(1497, false), (1499, true)]
theorem step1019 (p : Nat → Bool) (h : Constraints p) : clause p c1019 = true := by
  simpa only [c1019,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1019
def c1020 : List Lit := [(1498, false), (1500, true)]
theorem step1020 (p : Nat → Bool) (h : Constraints p) : clause p c1020 = true := by
  simpa only [c1020,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1020
def c1021 : List Lit := [(8, true), (1502, true)]
theorem step1021 (p : Nat → Bool) (h : Constraints p) : clause p c1021 = true := by
  simpa only [c1021,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1021
def c1022 : List Lit := [(6, true), (1502, true)]
theorem step1022 (p : Nat → Bool) (h : Constraints p) : clause p c1022 = true := by
  simpa only [c1022,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1022
def c1023 : List Lit := [(6, true), (8, true), (1503, true)]
theorem step1023 (p : Nat → Bool) (h : Constraints p) : clause p c1023 = true := by
  simpa only [c1023,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1023
def c1024 : List Lit := [(12, true), (1504, true)]
theorem step1024 (p : Nat → Bool) (h : Constraints p) : clause p c1024 = true := by
  simpa only [c1024,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block31.clause1024
def c1025 : List Lit := [(9, true), (1504, true)]
theorem step1025 (p : Nat → Bool) (h : Constraints p) : clause p c1025 = true := by
  simpa only [c1025,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1025
def c1026 : List Lit := [(9, true), (12, true), (1505, true)]
theorem step1026 (p : Nat → Bool) (h : Constraints p) : clause p c1026 = true := by
  simpa only [c1026,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1026
def c1027 : List Lit := [(1504, false), (1506, true)]
theorem step1027 (p : Nat → Bool) (h : Constraints p) : clause p c1027 = true := by
  simpa only [c1027,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1027
def c1028 : List Lit := [(1505, false), (1507, true)]
theorem step1028 (p : Nat → Bool) (h : Constraints p) : clause p c1028 = true := by
  simpa only [c1028,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1028
def c1029 : List Lit := [(1502, false), (1506, true)]
theorem step1029 (p : Nat → Bool) (h : Constraints p) : clause p c1029 = true := by
  simpa only [c1029,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1029
def c1030 : List Lit := [(1502, false), (1504, false), (1507, true)]
theorem step1030 (p : Nat → Bool) (h : Constraints p) : clause p c1030 = true := by
  simpa only [c1030,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1030
def c1031 : List Lit := [(1502, false), (1505, false), (1508, true)]
theorem step1031 (p : Nat → Bool) (h : Constraints p) : clause p c1031 = true := by
  simpa only [c1031,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1031
def c1032 : List Lit := [(1503, false), (1507, true)]
theorem step1032 (p : Nat → Bool) (h : Constraints p) : clause p c1032 = true := by
  simpa only [c1032,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1032
def c1033 : List Lit := [(1503, false), (1504, false), (1508, true)]
theorem step1033 (p : Nat → Bool) (h : Constraints p) : clause p c1033 = true := by
  simpa only [c1033,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1033
def c1034 : List Lit := [(1503, false), (1505, false), (1509, true)]
theorem step1034 (p : Nat → Bool) (h : Constraints p) : clause p c1034 = true := by
  simpa only [c1034,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1034
def c1035 : List Lit := [(1507, false), (1511, true)]
theorem step1035 (p : Nat → Bool) (h : Constraints p) : clause p c1035 = true := by
  simpa only [c1035,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1035
def c1036 : List Lit := [(1508, false), (1512, true)]
theorem step1036 (p : Nat → Bool) (h : Constraints p) : clause p c1036 = true := by
  simpa only [c1036,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1036
def c1037 : List Lit := [(1509, false), (1513, true)]
theorem step1037 (p : Nat → Bool) (h : Constraints p) : clause p c1037 = true := by
  simpa only [c1037,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1037
def c1038 : List Lit := [(1499, false), (1506, false), (1511, true)]
theorem step1038 (p : Nat → Bool) (h : Constraints p) : clause p c1038 = true := by
  simpa only [c1038,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1038
def c1039 : List Lit := [(1499, false), (1507, false), (1512, true)]
theorem step1039 (p : Nat → Bool) (h : Constraints p) : clause p c1039 = true := by
  simpa only [c1039,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1039
def c1040 : List Lit := [(1499, false), (1508, false), (1513, true)]
theorem step1040 (p : Nat → Bool) (h : Constraints p) : clause p c1040 = true := by
  simpa only [c1040,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1040
def c1041 : List Lit := [(1499, false), (1509, false), (1514, true)]
theorem step1041 (p : Nat → Bool) (h : Constraints p) : clause p c1041 = true := by
  simpa only [c1041,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1041
def c1042 : List Lit := [(1500, false), (1511, true)]
theorem step1042 (p : Nat → Bool) (h : Constraints p) : clause p c1042 = true := by
  simpa only [c1042,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1042
def c1043 : List Lit := [(1500, false), (1506, false), (1512, true)]
theorem step1043 (p : Nat → Bool) (h : Constraints p) : clause p c1043 = true := by
  simpa only [c1043,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1043
def c1044 : List Lit := [(1500, false), (1507, false), (1513, true)]
theorem step1044 (p : Nat → Bool) (h : Constraints p) : clause p c1044 = true := by
  simpa only [c1044,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1044
def c1045 : List Lit := [(1500, false), (1508, false), (1514, true)]
theorem step1045 (p : Nat → Bool) (h : Constraints p) : clause p c1045 = true := by
  simpa only [c1045,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1045
def c1046 : List Lit := [(1500, false), (1509, false), (1515, true)]
theorem step1046 (p : Nat → Bool) (h : Constraints p) : clause p c1046 = true := by
  simpa only [c1046,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1046
def c1047 : List Lit := [(13, true), (1517, true)]
theorem step1047 (p : Nat → Bool) (h : Constraints p) : clause p c1047 = true := by
  simpa only [c1047,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1047
def c1048 : List Lit := [(13, true), (15, true), (1518, true)]
theorem step1048 (p : Nat → Bool) (h : Constraints p) : clause p c1048 = true := by
  simpa only [c1048,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1048
def c1049 : List Lit := [(18, true), (1519, true)]
theorem step1049 (p : Nat → Bool) (h : Constraints p) : clause p c1049 = true := by
  simpa only [c1049,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1049
def c1050 : List Lit := [(16, true), (1519, true)]
theorem step1050 (p : Nat → Bool) (h : Constraints p) : clause p c1050 = true := by
  simpa only [c1050,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1050
def c1051 : List Lit := [(16, true), (18, true), (1520, true)]
theorem step1051 (p : Nat → Bool) (h : Constraints p) : clause p c1051 = true := by
  simpa only [c1051,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1051
def c1052 : List Lit := [(1517, false), (1521, true)]
theorem step1052 (p : Nat → Bool) (h : Constraints p) : clause p c1052 = true := by
  simpa only [c1052,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1052
def c1053 : List Lit := [(1517, false), (1519, false), (1522, true)]
theorem step1053 (p : Nat → Bool) (h : Constraints p) : clause p c1053 = true := by
  simpa only [c1053,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1053
def c1054 : List Lit := [(1517, false), (1520, false), (1523, true)]
theorem step1054 (p : Nat → Bool) (h : Constraints p) : clause p c1054 = true := by
  simpa only [c1054,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1054
def c1055 : List Lit := [(1518, false), (1522, true)]
theorem step1055 (p : Nat → Bool) (h : Constraints p) : clause p c1055 = true := by
  simpa only [c1055,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1055
def c1056 : List Lit := [(1518, false), (1519, false), (1523, true)]
theorem step1056 (p : Nat → Bool) (h : Constraints p) : clause p c1056 = true := by
  simpa only [c1056,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block32.clause1056
def c1057 : List Lit := [(1518, false), (1520, false), (1524, true)]
theorem step1057 (p : Nat → Bool) (h : Constraints p) : clause p c1057 = true := by
  simpa only [c1057,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1057
def c1058 : List Lit := [(22, true), (1525, true)]
theorem step1058 (p : Nat → Bool) (h : Constraints p) : clause p c1058 = true := by
  simpa only [c1058,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1058
def c1059 : List Lit := [(21, true), (1525, true)]
theorem step1059 (p : Nat → Bool) (h : Constraints p) : clause p c1059 = true := by
  simpa only [c1059,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1059
def c1060 : List Lit := [(21, true), (22, true), (1526, true)]
theorem step1060 (p : Nat → Bool) (h : Constraints p) : clause p c1060 = true := by
  simpa only [c1060,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1060
def c1061 : List Lit := [(27, true), (1527, true)]
theorem step1061 (p : Nat → Bool) (h : Constraints p) : clause p c1061 = true := by
  simpa only [c1061,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1061
def c1062 : List Lit := [(24, true), (1527, true)]
theorem step1062 (p : Nat → Bool) (h : Constraints p) : clause p c1062 = true := by
  simpa only [c1062,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1062
def c1063 : List Lit := [(24, true), (27, true), (1528, true)]
theorem step1063 (p : Nat → Bool) (h : Constraints p) : clause p c1063 = true := by
  simpa only [c1063,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1063
def c1064 : List Lit := [(1527, false), (1529, true)]
theorem step1064 (p : Nat → Bool) (h : Constraints p) : clause p c1064 = true := by
  simpa only [c1064,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1064
def c1065 : List Lit := [(1528, false), (1530, true)]
theorem step1065 (p : Nat → Bool) (h : Constraints p) : clause p c1065 = true := by
  simpa only [c1065,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1065
def c1066 : List Lit := [(1525, false), (1529, true)]
theorem step1066 (p : Nat → Bool) (h : Constraints p) : clause p c1066 = true := by
  simpa only [c1066,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1066
def c1067 : List Lit := [(1525, false), (1527, false), (1530, true)]
theorem step1067 (p : Nat → Bool) (h : Constraints p) : clause p c1067 = true := by
  simpa only [c1067,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1067
def c1068 : List Lit := [(1525, false), (1528, false), (1531, true)]
theorem step1068 (p : Nat → Bool) (h : Constraints p) : clause p c1068 = true := by
  simpa only [c1068,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1068
def c1069 : List Lit := [(1526, false), (1530, true)]
theorem step1069 (p : Nat → Bool) (h : Constraints p) : clause p c1069 = true := by
  simpa only [c1069,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1069
def c1070 : List Lit := [(1526, false), (1527, false), (1531, true)]
theorem step1070 (p : Nat → Bool) (h : Constraints p) : clause p c1070 = true := by
  simpa only [c1070,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1070
def c1071 : List Lit := [(1526, false), (1528, false), (1532, true)]
theorem step1071 (p : Nat → Bool) (h : Constraints p) : clause p c1071 = true := by
  simpa only [c1071,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1071
def c1072 : List Lit := [(1521, false), (1530, false), (1535, true)]
theorem step1072 (p : Nat → Bool) (h : Constraints p) : clause p c1072 = true := by
  simpa only [c1072,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1072
def c1073 : List Lit := [(1521, false), (1531, false), (1536, true)]
theorem step1073 (p : Nat → Bool) (h : Constraints p) : clause p c1073 = true := by
  simpa only [c1073,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1073
def c1074 : List Lit := [(1522, false), (1534, true)]
theorem step1074 (p : Nat → Bool) (h : Constraints p) : clause p c1074 = true := by
  simpa only [c1074,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1074
def c1075 : List Lit := [(1522, false), (1529, false), (1535, true)]
theorem step1075 (p : Nat → Bool) (h : Constraints p) : clause p c1075 = true := by
  simpa only [c1075,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1075
def c1076 : List Lit := [(1522, false), (1530, false), (1536, true)]
theorem step1076 (p : Nat → Bool) (h : Constraints p) : clause p c1076 = true := by
  simpa only [c1076,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1076
def c1077 : List Lit := [(1522, false), (1531, false), (1537, true)]
theorem step1077 (p : Nat → Bool) (h : Constraints p) : clause p c1077 = true := by
  simpa only [c1077,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1077
def c1078 : List Lit := [(1522, false), (1532, false), (1538, true)]
theorem step1078 (p : Nat → Bool) (h : Constraints p) : clause p c1078 = true := by
  simpa only [c1078,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1078
def c1079 : List Lit := [(1523, false), (1535, true)]
theorem step1079 (p : Nat → Bool) (h : Constraints p) : clause p c1079 = true := by
  simpa only [c1079,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1079
def c1080 : List Lit := [(1523, false), (1529, false), (1536, true)]
theorem step1080 (p : Nat → Bool) (h : Constraints p) : clause p c1080 = true := by
  simpa only [c1080,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1080
def c1081 : List Lit := [(1523, false), (1530, false), (1537, true)]
theorem step1081 (p : Nat → Bool) (h : Constraints p) : clause p c1081 = true := by
  simpa only [c1081,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1081
def c1082 : List Lit := [(1523, false), (1531, false), (1538, true)]
theorem step1082 (p : Nat → Bool) (h : Constraints p) : clause p c1082 = true := by
  simpa only [c1082,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1082
def c1083 : List Lit := [(1523, false), (1532, false), (1539, true)]
theorem step1083 (p : Nat → Bool) (h : Constraints p) : clause p c1083 = true := by
  simpa only [c1083,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1083
def c1084 : List Lit := [(1524, false), (1536, true)]
theorem step1084 (p : Nat → Bool) (h : Constraints p) : clause p c1084 = true := by
  simpa only [c1084,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1084
def c1085 : List Lit := [(1524, false), (1529, false), (1537, true)]
theorem step1085 (p : Nat → Bool) (h : Constraints p) : clause p c1085 = true := by
  simpa only [c1085,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1085
def c1086 : List Lit := [(1524, false), (1530, false), (1538, true)]
theorem step1086 (p : Nat → Bool) (h : Constraints p) : clause p c1086 = true := by
  simpa only [c1086,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1086
def c1087 : List Lit := [(1524, false), (1531, false), (1539, true)]
theorem step1087 (p : Nat → Bool) (h : Constraints p) : clause p c1087 = true := by
  simpa only [c1087,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1087
def c1088 : List Lit := [(1524, false), (1532, false), (1540, true)]
theorem step1088 (p : Nat → Bool) (h : Constraints p) : clause p c1088 = true := by
  simpa only [c1088,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block33.clause1088
def c1089 : List Lit := [(1511, false), (1535, false), (1545, true)]
theorem step1089 (p : Nat → Bool) (h : Constraints p) : clause p c1089 = true := by
  simpa only [c1089,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1089
def c1090 : List Lit := [(1511, false), (1536, false), (1546, true)]
theorem step1090 (p : Nat → Bool) (h : Constraints p) : clause p c1090 = true := by
  simpa only [c1090,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1090
def c1091 : List Lit := [(1511, false), (1537, false), (1547, true)]
theorem step1091 (p : Nat → Bool) (h : Constraints p) : clause p c1091 = true := by
  simpa only [c1091,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1091
def c1092 : List Lit := [(1511, false), (1538, false), (1548, true)]
theorem step1092 (p : Nat → Bool) (h : Constraints p) : clause p c1092 = true := by
  simpa only [c1092,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1092
def c1093 : List Lit := [(1511, false), (1539, false), (1549, true)]
theorem step1093 (p : Nat → Bool) (h : Constraints p) : clause p c1093 = true := by
  simpa only [c1093,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1093
def c1094 : List Lit := [(1511, false), (1540, false), (1550, true)]
theorem step1094 (p : Nat → Bool) (h : Constraints p) : clause p c1094 = true := by
  simpa only [c1094,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1094
def c1095 : List Lit := [(1512, false), (1535, false), (1546, true)]
theorem step1095 (p : Nat → Bool) (h : Constraints p) : clause p c1095 = true := by
  simpa only [c1095,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1095
def c1096 : List Lit := [(1512, false), (1536, false), (1547, true)]
theorem step1096 (p : Nat → Bool) (h : Constraints p) : clause p c1096 = true := by
  simpa only [c1096,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1096
def c1097 : List Lit := [(1512, false), (1537, false), (1548, true)]
theorem step1097 (p : Nat → Bool) (h : Constraints p) : clause p c1097 = true := by
  simpa only [c1097,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1097
def c1098 : List Lit := [(1512, false), (1538, false), (1549, true)]
theorem step1098 (p : Nat → Bool) (h : Constraints p) : clause p c1098 = true := by
  simpa only [c1098,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1098
def c1099 : List Lit := [(1512, false), (1540, false), (1551, true)]
theorem step1099 (p : Nat → Bool) (h : Constraints p) : clause p c1099 = true := by
  simpa only [c1099,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1099
def c1100 : List Lit := [(1513, false), (1535, false), (1547, true)]
theorem step1100 (p : Nat → Bool) (h : Constraints p) : clause p c1100 = true := by
  simpa only [c1100,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1100
def c1101 : List Lit := [(1513, false), (1536, false), (1548, true)]
theorem step1101 (p : Nat → Bool) (h : Constraints p) : clause p c1101 = true := by
  simpa only [c1101,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1101
def c1102 : List Lit := [(1513, false), (1537, false), (1549, true)]
theorem step1102 (p : Nat → Bool) (h : Constraints p) : clause p c1102 = true := by
  simpa only [c1102,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1102
def c1103 : List Lit := [(1513, false), (1538, false), (1550, true)]
theorem step1103 (p : Nat → Bool) (h : Constraints p) : clause p c1103 = true := by
  simpa only [c1103,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1103
def c1104 : List Lit := [(1514, false), (1534, false), (1547, true)]
theorem step1104 (p : Nat → Bool) (h : Constraints p) : clause p c1104 = true := by
  simpa only [c1104,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1104
def c1105 : List Lit := [(1514, false), (1535, false), (1548, true)]
theorem step1105 (p : Nat → Bool) (h : Constraints p) : clause p c1105 = true := by
  simpa only [c1105,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1105
def c1106 : List Lit := [(1514, false), (1536, false), (1549, true)]
theorem step1106 (p : Nat → Bool) (h : Constraints p) : clause p c1106 = true := by
  simpa only [c1106,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1106
def c1107 : List Lit := [(1515, false), (1535, false), (1549, true)]
theorem step1107 (p : Nat → Bool) (h : Constraints p) : clause p c1107 = true := by
  simpa only [c1107,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1107
def c1108 : List Lit := [(1515, false), (1536, false), (1550, true)]
theorem step1108 (p : Nat → Bool) (h : Constraints p) : clause p c1108 = true := by
  simpa only [c1108,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1108
def c1109 : List Lit := [(30, true), (1556, true)]
theorem step1109 (p : Nat → Bool) (h : Constraints p) : clause p c1109 = true := by
  simpa only [c1109,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1109
def c1110 : List Lit := [(29, true), (1556, true)]
theorem step1110 (p : Nat → Bool) (h : Constraints p) : clause p c1110 = true := by
  simpa only [c1110,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1110
def c1111 : List Lit := [(29, true), (30, true), (1557, true)]
theorem step1111 (p : Nat → Bool) (h : Constraints p) : clause p c1111 = true := by
  simpa only [c1111,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1111
def c1112 : List Lit := [(34, true), (1558, true)]
theorem step1112 (p : Nat → Bool) (h : Constraints p) : clause p c1112 = true := by
  simpa only [c1112,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1112
def c1113 : List Lit := [(31, true), (1558, true)]
theorem step1113 (p : Nat → Bool) (h : Constraints p) : clause p c1113 = true := by
  simpa only [c1113,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1113
def c1114 : List Lit := [(31, true), (34, true), (1559, true)]
theorem step1114 (p : Nat → Bool) (h : Constraints p) : clause p c1114 = true := by
  simpa only [c1114,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1114
def c1115 : List Lit := [(1558, false), (1560, true)]
theorem step1115 (p : Nat → Bool) (h : Constraints p) : clause p c1115 = true := by
  simpa only [c1115,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1115
def c1116 : List Lit := [(1559, false), (1561, true)]
theorem step1116 (p : Nat → Bool) (h : Constraints p) : clause p c1116 = true := by
  simpa only [c1116,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1116
def c1117 : List Lit := [(1556, false), (1560, true)]
theorem step1117 (p : Nat → Bool) (h : Constraints p) : clause p c1117 = true := by
  simpa only [c1117,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1117
def c1118 : List Lit := [(1556, false), (1558, false), (1561, true)]
theorem step1118 (p : Nat → Bool) (h : Constraints p) : clause p c1118 = true := by
  simpa only [c1118,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1118
def c1119 : List Lit := [(1556, false), (1559, false), (1562, true)]
theorem step1119 (p : Nat → Bool) (h : Constraints p) : clause p c1119 = true := by
  simpa only [c1119,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1119
def c1120 : List Lit := [(1557, false), (1561, true)]
theorem step1120 (p : Nat → Bool) (h : Constraints p) : clause p c1120 = true := by
  simpa only [c1120,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block34.clause1120
def c1121 : List Lit := [(1557, false), (1558, false), (1562, true)]
theorem step1121 (p : Nat → Bool) (h : Constraints p) : clause p c1121 = true := by
  simpa only [c1121,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1121
def c1122 : List Lit := [(1557, false), (1559, false), (1563, true)]
theorem step1122 (p : Nat → Bool) (h : Constraints p) : clause p c1122 = true := by
  simpa only [c1122,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1122
def c1123 : List Lit := [(37, true), (1564, true)]
theorem step1123 (p : Nat → Bool) (h : Constraints p) : clause p c1123 = true := by
  simpa only [c1123,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1123
def c1124 : List Lit := [(35, true), (1564, true)]
theorem step1124 (p : Nat → Bool) (h : Constraints p) : clause p c1124 = true := by
  simpa only [c1124,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1124
def c1125 : List Lit := [(35, true), (37, true), (1565, true)]
theorem step1125 (p : Nat → Bool) (h : Constraints p) : clause p c1125 = true := by
  simpa only [c1125,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1125
def c1126 : List Lit := [(40, true), (1566, true)]
theorem step1126 (p : Nat → Bool) (h : Constraints p) : clause p c1126 = true := by
  simpa only [c1126,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1126
def c1127 : List Lit := [(38, true), (1566, true)]
theorem step1127 (p : Nat → Bool) (h : Constraints p) : clause p c1127 = true := by
  simpa only [c1127,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1127
def c1128 : List Lit := [(38, true), (40, true), (1567, true)]
theorem step1128 (p : Nat → Bool) (h : Constraints p) : clause p c1128 = true := by
  simpa only [c1128,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1128
def c1129 : List Lit := [(1566, false), (1568, true)]
theorem step1129 (p : Nat → Bool) (h : Constraints p) : clause p c1129 = true := by
  simpa only [c1129,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1129
def c1130 : List Lit := [(1567, false), (1569, true)]
theorem step1130 (p : Nat → Bool) (h : Constraints p) : clause p c1130 = true := by
  simpa only [c1130,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1130
def c1131 : List Lit := [(1564, false), (1568, true)]
theorem step1131 (p : Nat → Bool) (h : Constraints p) : clause p c1131 = true := by
  simpa only [c1131,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1131
def c1132 : List Lit := [(1564, false), (1566, false), (1569, true)]
theorem step1132 (p : Nat → Bool) (h : Constraints p) : clause p c1132 = true := by
  simpa only [c1132,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1132
def c1133 : List Lit := [(1564, false), (1567, false), (1570, true)]
theorem step1133 (p : Nat → Bool) (h : Constraints p) : clause p c1133 = true := by
  simpa only [c1133,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1133
def c1134 : List Lit := [(1565, false), (1569, true)]
theorem step1134 (p : Nat → Bool) (h : Constraints p) : clause p c1134 = true := by
  simpa only [c1134,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1134
def c1135 : List Lit := [(1565, false), (1566, false), (1570, true)]
theorem step1135 (p : Nat → Bool) (h : Constraints p) : clause p c1135 = true := by
  simpa only [c1135,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1135
def c1136 : List Lit := [(1565, false), (1567, false), (1571, true)]
theorem step1136 (p : Nat → Bool) (h : Constraints p) : clause p c1136 = true := by
  simpa only [c1136,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1136
def c1137 : List Lit := [(1569, false), (1573, true)]
theorem step1137 (p : Nat → Bool) (h : Constraints p) : clause p c1137 = true := by
  simpa only [c1137,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1137
def c1138 : List Lit := [(1570, false), (1574, true)]
theorem step1138 (p : Nat → Bool) (h : Constraints p) : clause p c1138 = true := by
  simpa only [c1138,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1138
def c1139 : List Lit := [(1571, false), (1575, true)]
theorem step1139 (p : Nat → Bool) (h : Constraints p) : clause p c1139 = true := by
  simpa only [c1139,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1139
def c1140 : List Lit := [(1560, false), (1568, false), (1573, true)]
theorem step1140 (p : Nat → Bool) (h : Constraints p) : clause p c1140 = true := by
  simpa only [c1140,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1140
def c1141 : List Lit := [(1560, false), (1569, false), (1574, true)]
theorem step1141 (p : Nat → Bool) (h : Constraints p) : clause p c1141 = true := by
  simpa only [c1141,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1141
def c1142 : List Lit := [(1560, false), (1570, false), (1575, true)]
theorem step1142 (p : Nat → Bool) (h : Constraints p) : clause p c1142 = true := by
  simpa only [c1142,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1142
def c1143 : List Lit := [(1560, false), (1571, false), (1576, true)]
theorem step1143 (p : Nat → Bool) (h : Constraints p) : clause p c1143 = true := by
  simpa only [c1143,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1143
def c1144 : List Lit := [(1561, false), (1568, false), (1574, true)]
theorem step1144 (p : Nat → Bool) (h : Constraints p) : clause p c1144 = true := by
  simpa only [c1144,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1144
def c1145 : List Lit := [(1561, false), (1569, false), (1575, true)]
theorem step1145 (p : Nat → Bool) (h : Constraints p) : clause p c1145 = true := by
  simpa only [c1145,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1145
def c1146 : List Lit := [(1561, false), (1570, false), (1576, true)]
theorem step1146 (p : Nat → Bool) (h : Constraints p) : clause p c1146 = true := by
  simpa only [c1146,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1146
def c1147 : List Lit := [(1562, false), (1568, false), (1575, true)]
theorem step1147 (p : Nat → Bool) (h : Constraints p) : clause p c1147 = true := by
  simpa only [c1147,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1147
def c1148 : List Lit := [(1562, false), (1569, false), (1576, true)]
theorem step1148 (p : Nat → Bool) (h : Constraints p) : clause p c1148 = true := by
  simpa only [c1148,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1148
def c1149 : List Lit := [(1562, false), (1570, false), (1577, true)]
theorem step1149 (p : Nat → Bool) (h : Constraints p) : clause p c1149 = true := by
  simpa only [c1149,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1149
def c1150 : List Lit := [(1563, false), (1568, false), (1576, true)]
theorem step1150 (p : Nat → Bool) (h : Constraints p) : clause p c1150 = true := by
  simpa only [c1150,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1150
def c1151 : List Lit := [(1563, false), (1569, false), (1577, true)]
theorem step1151 (p : Nat → Bool) (h : Constraints p) : clause p c1151 = true := by
  simpa only [c1151,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1151
def c1152 : List Lit := [(45, true), (1580, true)]
theorem step1152 (p : Nat → Bool) (h : Constraints p) : clause p c1152 = true := by
  simpa only [c1152,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block35.clause1152
def c1153 : List Lit := [(42, true), (1580, true)]
theorem step1153 (p : Nat → Bool) (h : Constraints p) : clause p c1153 = true := by
  simpa only [c1153,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1153
def c1154 : List Lit := [(42, true), (45, true), (1581, true)]
theorem step1154 (p : Nat → Bool) (h : Constraints p) : clause p c1154 = true := by
  simpa only [c1154,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1154
def c1155 : List Lit := [(48, true), (1582, true)]
theorem step1155 (p : Nat → Bool) (h : Constraints p) : clause p c1155 = true := by
  simpa only [c1155,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1155
def c1156 : List Lit := [(47, true), (1582, true)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true := by
  simpa only [c1156,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1156
def c1157 : List Lit := [(47, true), (48, true), (1583, true)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true := by
  simpa only [c1157,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1157
def c1158 : List Lit := [(1582, false), (1584, true)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true := by
  simpa only [c1158,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1158
def c1159 : List Lit := [(1583, false), (1585, true)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true := by
  simpa only [c1159,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1159
def c1160 : List Lit := [(1580, false), (1584, true)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true := by
  simpa only [c1160,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1160
def c1161 : List Lit := [(1580, false), (1582, false), (1585, true)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true := by
  simpa only [c1161,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1161
def c1162 : List Lit := [(1580, false), (1583, false), (1586, true)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true := by
  simpa only [c1162,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1162
def c1163 : List Lit := [(1581, false), (1585, true)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true := by
  simpa only [c1163,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1163
def c1164 : List Lit := [(1581, false), (1582, false), (1586, true)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true := by
  simpa only [c1164,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1164
def c1165 : List Lit := [(1581, false), (1583, false), (1587, true)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true := by
  simpa only [c1165,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1165
def c1166 : List Lit := [(53, true), (1588, true)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true := by
  simpa only [c1166,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1166
def c1167 : List Lit := [(49, true), (1588, true)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true := by
  simpa only [c1167,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1167
def c1168 : List Lit := [(49, true), (53, true), (1589, true)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true := by
  simpa only [c1168,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1168
def c1169 : List Lit := [(56, true), (1590, true)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true := by
  simpa only [c1169,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1169
def c1170 : List Lit := [(54, true), (1590, true)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true := by
  simpa only [c1170,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1170
def c1171 : List Lit := [(54, true), (56, true), (1591, true)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true := by
  simpa only [c1171,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1171
def c1172 : List Lit := [(1590, false), (1592, true)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true := by
  simpa only [c1172,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1172
def c1173 : List Lit := [(1591, false), (1593, true)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true := by
  simpa only [c1173,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1173
def c1174 : List Lit := [(1588, false), (1592, true)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true := by
  simpa only [c1174,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1174
def c1175 : List Lit := [(1588, false), (1590, false), (1593, true)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true := by
  simpa only [c1175,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1175
def c1176 : List Lit := [(1588, false), (1591, false), (1594, true)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true := by
  simpa only [c1176,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1176
def c1177 : List Lit := [(1589, false), (1593, true)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true := by
  simpa only [c1177,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1177
def c1178 : List Lit := [(1589, false), (1590, false), (1594, true)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true := by
  simpa only [c1178,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1178
def c1179 : List Lit := [(1589, false), (1591, false), (1595, true)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true := by
  simpa only [c1179,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1179
def c1180 : List Lit := [(1592, false), (1596, true)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true := by
  simpa only [c1180,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1180
def c1181 : List Lit := [(1593, false), (1597, true)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true := by
  simpa only [c1181,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1181
def c1182 : List Lit := [(1594, false), (1598, true)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true := by
  simpa only [c1182,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1182
def c1183 : List Lit := [(1595, false), (1599, true)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true := by
  simpa only [c1183,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1183
def c1184 : List Lit := [(1584, false), (1596, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true := by
  simpa only [c1184,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block36.clause1184
def c1185 : List Lit := [(1584, false), (1592, false), (1597, true)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true := by
  simpa only [c1185,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1185
def c1186 : List Lit := [(1584, false), (1593, false), (1598, true)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true := by
  simpa only [c1186,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1186
def c1187 : List Lit := [(1584, false), (1594, false), (1599, true)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true := by
  simpa only [c1187,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1187
def c1188 : List Lit := [(1585, false), (1597, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true := by
  simpa only [c1188,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1188
def c1189 : List Lit := [(1585, false), (1592, false), (1598, true)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true := by
  simpa only [c1189,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1189
def c1190 : List Lit := [(1585, false), (1593, false), (1599, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true := by
  simpa only [c1190,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1190
def c1191 : List Lit := [(1585, false), (1594, false), (1600, true)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true := by
  simpa only [c1191,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1191
def c1192 : List Lit := [(1585, false), (1595, false), (1601, true)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true := by
  simpa only [c1192,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1192
def c1193 : List Lit := [(1586, false), (1598, true)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true := by
  simpa only [c1193,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1193
def c1194 : List Lit := [(1586, false), (1592, false), (1599, true)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true := by
  simpa only [c1194,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1194
def c1195 : List Lit := [(1586, false), (1593, false), (1600, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true := by
  simpa only [c1195,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1195
def c1196 : List Lit := [(1586, false), (1594, false), (1601, true)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true := by
  simpa only [c1196,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1196
def c1197 : List Lit := [(1587, false), (1599, true)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true := by
  simpa only [c1197,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1197
def c1198 : List Lit := [(1587, false), (1592, false), (1600, true)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true := by
  simpa only [c1198,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1198
def c1199 : List Lit := [(1587, false), (1593, false), (1601, true)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true := by
  simpa only [c1199,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1199
def c1200 : List Lit := [(1573, false), (1596, false), (1606, true)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true := by
  simpa only [c1200,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1200
def c1201 : List Lit := [(1573, false), (1597, false), (1607, true)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true := by
  simpa only [c1201,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1201
def c1202 : List Lit := [(1573, false), (1598, false), (1608, true)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true := by
  simpa only [c1202,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1202
def c1203 : List Lit := [(1573, false), (1599, false), (1609, true)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true := by
  simpa only [c1203,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1203
def c1204 : List Lit := [(1573, false), (1600, false), (1610, true)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true := by
  simpa only [c1204,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1204
def c1205 : List Lit := [(1573, false), (1601, false), (1611, true)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true := by
  simpa only [c1205,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1205
def c1206 : List Lit := [(1574, false), (1596, false), (1607, true)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true := by
  simpa only [c1206,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1206
def c1207 : List Lit := [(1574, false), (1597, false), (1608, true)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true := by
  simpa only [c1207,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1207
def c1208 : List Lit := [(1574, false), (1598, false), (1609, true)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true := by
  simpa only [c1208,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1208
def c1209 : List Lit := [(1574, false), (1599, false), (1610, true)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true := by
  simpa only [c1209,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1209
def c1210 : List Lit := [(1574, false), (1600, false), (1611, true)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true := by
  simpa only [c1210,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1210
def c1211 : List Lit := [(1574, false), (1601, false), (1612, true)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true := by
  simpa only [c1211,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1211
def c1212 : List Lit := [(1575, false), (1596, false), (1608, true)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true := by
  simpa only [c1212,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1212
def c1213 : List Lit := [(1575, false), (1597, false), (1609, true)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true := by
  simpa only [c1213,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1213
def c1214 : List Lit := [(1575, false), (1598, false), (1610, true)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true := by
  simpa only [c1214,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1214
def c1215 : List Lit := [(1575, false), (1599, false), (1611, true)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true := by
  simpa only [c1215,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1215
def c1216 : List Lit := [(1575, false), (1600, false), (1612, true)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true := by
  simpa only [c1216,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block37.clause1216
def c1217 : List Lit := [(1576, false), (1596, false), (1609, true)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true := by
  simpa only [c1217,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1217
def c1218 : List Lit := [(1576, false), (1597, false), (1610, true)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true := by
  simpa only [c1218,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1218
def c1219 : List Lit := [(1576, false), (1598, false), (1611, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true := by
  simpa only [c1219,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1219
def c1220 : List Lit := [(1576, false), (1599, false), (1612, true)]
theorem step1220 (p : Nat → Bool) (h : Constraints p) : clause p c1220 = true := by
  simpa only [c1220,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1220
def c1221 : List Lit := [(1576, false), (1600, false), (1613, true)]
theorem step1221 (p : Nat → Bool) (h : Constraints p) : clause p c1221 = true := by
  simpa only [c1221,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1221
def c1222 : List Lit := [(1576, false), (1601, false), (1614, true)]
theorem step1222 (p : Nat → Bool) (h : Constraints p) : clause p c1222 = true := by
  simpa only [c1222,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1222
def c1223 : List Lit := [(1577, false), (1598, false), (1612, true)]
theorem step1223 (p : Nat → Bool) (h : Constraints p) : clause p c1223 = true := by
  simpa only [c1223,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1223
def c1224 : List Lit := [(1545, false), (1608, false), (1629, true)]
theorem step1224 (p : Nat → Bool) (h : Constraints p) : clause p c1224 = true := by
  simpa only [c1224,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1224
def c1225 : List Lit := [(1545, false), (1609, false), (1630, true)]
theorem step1225 (p : Nat → Bool) (h : Constraints p) : clause p c1225 = true := by
  simpa only [c1225,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1225
def c1226 : List Lit := [(1545, false), (1610, false), (1631, true)]
theorem step1226 (p : Nat → Bool) (h : Constraints p) : clause p c1226 = true := by
  simpa only [c1226,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1226
def c1227 : List Lit := [(1545, false), (1611, false), (1632, true)]
theorem step1227 (p : Nat → Bool) (h : Constraints p) : clause p c1227 = true := by
  simpa only [c1227,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1227
def c1228 : List Lit := [(1545, false), (1612, false), (1633, true)]
theorem step1228 (p : Nat → Bool) (h : Constraints p) : clause p c1228 = true := by
  simpa only [c1228,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1228
def c1229 : List Lit := [(1545, false), (1613, false), (1634, true)]
theorem step1229 (p : Nat → Bool) (h : Constraints p) : clause p c1229 = true := by
  simpa only [c1229,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1229
def c1230 : List Lit := [(1545, false), (1614, false), (1635, true)]
theorem step1230 (p : Nat → Bool) (h : Constraints p) : clause p c1230 = true := by
  simpa only [c1230,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1230
def c1231 : List Lit := [(1546, false), (1607, false), (1629, true)]
theorem step1231 (p : Nat → Bool) (h : Constraints p) : clause p c1231 = true := by
  simpa only [c1231,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1231
def c1232 : List Lit := [(1546, false), (1608, false), (1630, true)]
theorem step1232 (p : Nat → Bool) (h : Constraints p) : clause p c1232 = true := by
  simpa only [c1232,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1232
def c1233 : List Lit := [(1546, false), (1609, false), (1631, true)]
theorem step1233 (p : Nat → Bool) (h : Constraints p) : clause p c1233 = true := by
  simpa only [c1233,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1233
def c1234 : List Lit := [(1546, false), (1610, false), (1632, true)]
theorem step1234 (p : Nat → Bool) (h : Constraints p) : clause p c1234 = true := by
  simpa only [c1234,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1234
def c1235 : List Lit := [(1546, false), (1611, false), (1633, true)]
theorem step1235 (p : Nat → Bool) (h : Constraints p) : clause p c1235 = true := by
  simpa only [c1235,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1235
def c1236 : List Lit := [(1546, false), (1612, false), (1634, true)]
theorem step1236 (p : Nat → Bool) (h : Constraints p) : clause p c1236 = true := by
  simpa only [c1236,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1236
def c1237 : List Lit := [(1546, false), (1613, false), (1635, true)]
theorem step1237 (p : Nat → Bool) (h : Constraints p) : clause p c1237 = true := by
  simpa only [c1237,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1237
def c1238 : List Lit := [(1547, false), (1606, false), (1629, true)]
theorem step1238 (p : Nat → Bool) (h : Constraints p) : clause p c1238 = true := by
  simpa only [c1238,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1238
def c1239 : List Lit := [(1547, false), (1607, false), (1630, true)]
theorem step1239 (p : Nat → Bool) (h : Constraints p) : clause p c1239 = true := by
  simpa only [c1239,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1239
def c1240 : List Lit := [(1547, false), (1608, false), (1631, true)]
theorem step1240 (p : Nat → Bool) (h : Constraints p) : clause p c1240 = true := by
  simpa only [c1240,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1240
def c1241 : List Lit := [(1547, false), (1609, false), (1632, true)]
theorem step1241 (p : Nat → Bool) (h : Constraints p) : clause p c1241 = true := by
  simpa only [c1241,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1241
def c1242 : List Lit := [(1547, false), (1610, false), (1633, true)]
theorem step1242 (p : Nat → Bool) (h : Constraints p) : clause p c1242 = true := by
  simpa only [c1242,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1242
def c1243 : List Lit := [(1547, false), (1611, false), (1634, true)]
theorem step1243 (p : Nat → Bool) (h : Constraints p) : clause p c1243 = true := by
  simpa only [c1243,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1243
def c1244 : List Lit := [(1547, false), (1612, false), (1635, true)]
theorem step1244 (p : Nat → Bool) (h : Constraints p) : clause p c1244 = true := by
  simpa only [c1244,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1244
def c1245 : List Lit := [(1548, false), (1606, false), (1630, true)]
theorem step1245 (p : Nat → Bool) (h : Constraints p) : clause p c1245 = true := by
  simpa only [c1245,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1245
def c1246 : List Lit := [(1548, false), (1607, false), (1631, true)]
theorem step1246 (p : Nat → Bool) (h : Constraints p) : clause p c1246 = true := by
  simpa only [c1246,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1246
def c1247 : List Lit := [(1548, false), (1608, false), (1632, true)]
theorem step1247 (p : Nat → Bool) (h : Constraints p) : clause p c1247 = true := by
  simpa only [c1247,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1247
def c1248 : List Lit := [(1548, false), (1609, false), (1633, true)]
theorem step1248 (p : Nat → Bool) (h : Constraints p) : clause p c1248 = true := by
  simpa only [c1248,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block38.clause1248
def c1249 : List Lit := [(1548, false), (1610, false), (1634, true)]
theorem step1249 (p : Nat → Bool) (h : Constraints p) : clause p c1249 = true := by
  simpa only [c1249,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1249
def c1250 : List Lit := [(1548, false), (1611, false), (1635, true)]
theorem step1250 (p : Nat → Bool) (h : Constraints p) : clause p c1250 = true := by
  simpa only [c1250,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1250
def c1251 : List Lit := [(1549, false), (1606, false), (1631, true)]
theorem step1251 (p : Nat → Bool) (h : Constraints p) : clause p c1251 = true := by
  simpa only [c1251,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1251
def c1252 : List Lit := [(1549, false), (1607, false), (1632, true)]
theorem step1252 (p : Nat → Bool) (h : Constraints p) : clause p c1252 = true := by
  simpa only [c1252,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1252
def c1253 : List Lit := [(1549, false), (1608, false), (1633, true)]
theorem step1253 (p : Nat → Bool) (h : Constraints p) : clause p c1253 = true := by
  simpa only [c1253,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1253
def c1254 : List Lit := [(1549, false), (1609, false), (1634, true)]
theorem step1254 (p : Nat → Bool) (h : Constraints p) : clause p c1254 = true := by
  simpa only [c1254,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1254
def c1255 : List Lit := [(1549, false), (1610, false), (1635, true)]
theorem step1255 (p : Nat → Bool) (h : Constraints p) : clause p c1255 = true := by
  simpa only [c1255,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1255
def c1256 : List Lit := [(1550, false), (1606, false), (1632, true)]
theorem step1256 (p : Nat → Bool) (h : Constraints p) : clause p c1256 = true := by
  simpa only [c1256,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1256
def c1257 : List Lit := [(1550, false), (1607, false), (1633, true)]
theorem step1257 (p : Nat → Bool) (h : Constraints p) : clause p c1257 = true := by
  simpa only [c1257,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1257
def c1258 : List Lit := [(1550, false), (1608, false), (1634, true)]
theorem step1258 (p : Nat → Bool) (h : Constraints p) : clause p c1258 = true := by
  simpa only [c1258,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1258
def c1259 : List Lit := [(1550, false), (1609, false), (1635, true)]
theorem step1259 (p : Nat → Bool) (h : Constraints p) : clause p c1259 = true := by
  simpa only [c1259,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1259
def c1260 : List Lit := [(1550, false), (1610, false), (1636, true)]
theorem step1260 (p : Nat → Bool) (h : Constraints p) : clause p c1260 = true := by
  simpa only [c1260,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1260
def c1261 : List Lit := [(1551, false), (1606, false), (1633, true)]
theorem step1261 (p : Nat → Bool) (h : Constraints p) : clause p c1261 = true := by
  simpa only [c1261,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1261
def c1262 : List Lit := [(60, true), (1643, true)]
theorem step1262 (p : Nat → Bool) (h : Constraints p) : clause p c1262 = true := by
  simpa only [c1262,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1262
def c1263 : List Lit := [(58, true), (1643, true)]
theorem step1263 (p : Nat → Bool) (h : Constraints p) : clause p c1263 = true := by
  simpa only [c1263,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1263
def c1264 : List Lit := [(58, true), (60, true), (1644, true)]
theorem step1264 (p : Nat → Bool) (h : Constraints p) : clause p c1264 = true := by
  simpa only [c1264,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1264
def c1265 : List Lit := [(65, true), (1645, true)]
theorem step1265 (p : Nat → Bool) (h : Constraints p) : clause p c1265 = true := by
  simpa only [c1265,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1265
def c1266 : List Lit := [(61, true), (1645, true)]
theorem step1266 (p : Nat → Bool) (h : Constraints p) : clause p c1266 = true := by
  simpa only [c1266,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1266
def c1267 : List Lit := [(61, true), (65, true), (1646, true)]
theorem step1267 (p : Nat → Bool) (h : Constraints p) : clause p c1267 = true := by
  simpa only [c1267,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1267
def c1268 : List Lit := [(1645, false), (1647, true)]
theorem step1268 (p : Nat → Bool) (h : Constraints p) : clause p c1268 = true := by
  simpa only [c1268,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1268
def c1269 : List Lit := [(1646, false), (1648, true)]
theorem step1269 (p : Nat → Bool) (h : Constraints p) : clause p c1269 = true := by
  simpa only [c1269,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1269
def c1270 : List Lit := [(1643, false), (1647, true)]
theorem step1270 (p : Nat → Bool) (h : Constraints p) : clause p c1270 = true := by
  simpa only [c1270,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1270
def c1271 : List Lit := [(1643, false), (1645, false), (1648, true)]
theorem step1271 (p : Nat → Bool) (h : Constraints p) : clause p c1271 = true := by
  simpa only [c1271,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1271
def c1272 : List Lit := [(1643, false), (1646, false), (1649, true)]
theorem step1272 (p : Nat → Bool) (h : Constraints p) : clause p c1272 = true := by
  simpa only [c1272,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1272
def c1273 : List Lit := [(1644, false), (1648, true)]
theorem step1273 (p : Nat → Bool) (h : Constraints p) : clause p c1273 = true := by
  simpa only [c1273,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1273
def c1274 : List Lit := [(1644, false), (1645, false), (1649, true)]
theorem step1274 (p : Nat → Bool) (h : Constraints p) : clause p c1274 = true := by
  simpa only [c1274,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1274
def c1275 : List Lit := [(1644, false), (1646, false), (1650, true)]
theorem step1275 (p : Nat → Bool) (h : Constraints p) : clause p c1275 = true := by
  simpa only [c1275,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1275
def c1276 : List Lit := [(68, true), (1651, true)]
theorem step1276 (p : Nat → Bool) (h : Constraints p) : clause p c1276 = true := by
  simpa only [c1276,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1276
def c1277 : List Lit := [(66, true), (1651, true)]
theorem step1277 (p : Nat → Bool) (h : Constraints p) : clause p c1277 = true := by
  simpa only [c1277,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1277
def c1278 : List Lit := [(66, true), (68, true), (1652, true)]
theorem step1278 (p : Nat → Bool) (h : Constraints p) : clause p c1278 = true := by
  simpa only [c1278,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1278
def c1279 : List Lit := [(73, true), (1653, true)]
theorem step1279 (p : Nat → Bool) (h : Constraints p) : clause p c1279 = true := by
  simpa only [c1279,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1279
def c1280 : List Lit := [(69, true), (1653, true)]
theorem step1280 (p : Nat → Bool) (h : Constraints p) : clause p c1280 = true := by
  simpa only [c1280,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block39.clause1280
def c1281 : List Lit := [(69, true), (73, true), (1654, true)]
theorem step1281 (p : Nat → Bool) (h : Constraints p) : clause p c1281 = true := by
  simpa only [c1281,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1281
def c1282 : List Lit := [(1653, false), (1655, true)]
theorem step1282 (p : Nat → Bool) (h : Constraints p) : clause p c1282 = true := by
  simpa only [c1282,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1282
def c1283 : List Lit := [(1654, false), (1656, true)]
theorem step1283 (p : Nat → Bool) (h : Constraints p) : clause p c1283 = true := by
  simpa only [c1283,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1283
def c1284 : List Lit := [(1651, false), (1655, true)]
theorem step1284 (p : Nat → Bool) (h : Constraints p) : clause p c1284 = true := by
  simpa only [c1284,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1284
def c1285 : List Lit := [(1651, false), (1653, false), (1656, true)]
theorem step1285 (p : Nat → Bool) (h : Constraints p) : clause p c1285 = true := by
  simpa only [c1285,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1285
def c1286 : List Lit := [(1651, false), (1654, false), (1657, true)]
theorem step1286 (p : Nat → Bool) (h : Constraints p) : clause p c1286 = true := by
  simpa only [c1286,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1286
def c1287 : List Lit := [(1652, false), (1656, true)]
theorem step1287 (p : Nat → Bool) (h : Constraints p) : clause p c1287 = true := by
  simpa only [c1287,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1287
def c1288 : List Lit := [(1652, false), (1653, false), (1657, true)]
theorem step1288 (p : Nat → Bool) (h : Constraints p) : clause p c1288 = true := by
  simpa only [c1288,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1288
def c1289 : List Lit := [(1652, false), (1654, false), (1658, true)]
theorem step1289 (p : Nat → Bool) (h : Constraints p) : clause p c1289 = true := by
  simpa only [c1289,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1289
def c1290 : List Lit := [(1655, false), (1659, true)]
theorem step1290 (p : Nat → Bool) (h : Constraints p) : clause p c1290 = true := by
  simpa only [c1290,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1290
def c1291 : List Lit := [(1656, false), (1660, true)]
theorem step1291 (p : Nat → Bool) (h : Constraints p) : clause p c1291 = true := by
  simpa only [c1291,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1291
def c1292 : List Lit := [(1657, false), (1661, true)]
theorem step1292 (p : Nat → Bool) (h : Constraints p) : clause p c1292 = true := by
  simpa only [c1292,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1292
def c1293 : List Lit := [(1658, false), (1662, true)]
theorem step1293 (p : Nat → Bool) (h : Constraints p) : clause p c1293 = true := by
  simpa only [c1293,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1293
def c1294 : List Lit := [(1647, false), (1659, true)]
theorem step1294 (p : Nat → Bool) (h : Constraints p) : clause p c1294 = true := by
  simpa only [c1294,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1294
def c1295 : List Lit := [(1647, false), (1655, false), (1660, true)]
theorem step1295 (p : Nat → Bool) (h : Constraints p) : clause p c1295 = true := by
  simpa only [c1295,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1295
def c1296 : List Lit := [(1647, false), (1656, false), (1661, true)]
theorem step1296 (p : Nat → Bool) (h : Constraints p) : clause p c1296 = true := by
  simpa only [c1296,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1296
def c1297 : List Lit := [(1647, false), (1657, false), (1662, true)]
theorem step1297 (p : Nat → Bool) (h : Constraints p) : clause p c1297 = true := by
  simpa only [c1297,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1297
def c1298 : List Lit := [(1647, false), (1658, false), (1663, true)]
theorem step1298 (p : Nat → Bool) (h : Constraints p) : clause p c1298 = true := by
  simpa only [c1298,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1298
def c1299 : List Lit := [(1648, false), (1660, true)]
theorem step1299 (p : Nat → Bool) (h : Constraints p) : clause p c1299 = true := by
  simpa only [c1299,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1299
def c1300 : List Lit := [(1648, false), (1655, false), (1661, true)]
theorem step1300 (p : Nat → Bool) (h : Constraints p) : clause p c1300 = true := by
  simpa only [c1300,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1300
def c1301 : List Lit := [(1648, false), (1656, false), (1662, true)]
theorem step1301 (p : Nat → Bool) (h : Constraints p) : clause p c1301 = true := by
  simpa only [c1301,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1301
def c1302 : List Lit := [(1648, false), (1657, false), (1663, true)]
theorem step1302 (p : Nat → Bool) (h : Constraints p) : clause p c1302 = true := by
  simpa only [c1302,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1302
def c1303 : List Lit := [(1648, false), (1658, false), (1664, true)]
theorem step1303 (p : Nat → Bool) (h : Constraints p) : clause p c1303 = true := by
  simpa only [c1303,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1303
def c1304 : List Lit := [(1649, false), (1661, true)]
theorem step1304 (p : Nat → Bool) (h : Constraints p) : clause p c1304 = true := by
  simpa only [c1304,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1304
def c1305 : List Lit := [(1649, false), (1655, false), (1662, true)]
theorem step1305 (p : Nat → Bool) (h : Constraints p) : clause p c1305 = true := by
  simpa only [c1305,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1305
def c1306 : List Lit := [(1649, false), (1656, false), (1663, true)]
theorem step1306 (p : Nat → Bool) (h : Constraints p) : clause p c1306 = true := by
  simpa only [c1306,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1306
def c1307 : List Lit := [(1649, false), (1657, false), (1664, true)]
theorem step1307 (p : Nat → Bool) (h : Constraints p) : clause p c1307 = true := by
  simpa only [c1307,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1307
def c1308 : List Lit := [(1650, false), (1662, true)]
theorem step1308 (p : Nat → Bool) (h : Constraints p) : clause p c1308 = true := by
  simpa only [c1308,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1308
def c1309 : List Lit := [(1650, false), (1655, false), (1663, true)]
theorem step1309 (p : Nat → Bool) (h : Constraints p) : clause p c1309 = true := by
  simpa only [c1309,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1309
def c1310 : List Lit := [(1650, false), (1656, false), (1664, true)]
theorem step1310 (p : Nat → Bool) (h : Constraints p) : clause p c1310 = true := by
  simpa only [c1310,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1310
def c1311 : List Lit := [(1650, false), (1657, false), (1665, true)]
theorem step1311 (p : Nat → Bool) (h : Constraints p) : clause p c1311 = true := by
  simpa only [c1311,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1311
def c1312 : List Lit := [(76, true), (1667, true)]
theorem step1312 (p : Nat → Bool) (h : Constraints p) : clause p c1312 = true := by
  simpa only [c1312,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block40.clause1312
def c1313 : List Lit := [(75, true), (1667, true)]
theorem step1313 (p : Nat → Bool) (h : Constraints p) : clause p c1313 = true := by
  simpa only [c1313,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1313
def c1314 : List Lit := [(75, true), (76, true), (1668, true)]
theorem step1314 (p : Nat → Bool) (h : Constraints p) : clause p c1314 = true := by
  simpa only [c1314,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1314
def c1315 : List Lit := [(80, true), (1669, true)]
theorem step1315 (p : Nat → Bool) (h : Constraints p) : clause p c1315 = true := by
  simpa only [c1315,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1315
def c1316 : List Lit := [(78, true), (1669, true)]
theorem step1316 (p : Nat → Bool) (h : Constraints p) : clause p c1316 = true := by
  simpa only [c1316,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1316
def c1317 : List Lit := [(78, true), (80, true), (1670, true)]
theorem step1317 (p : Nat → Bool) (h : Constraints p) : clause p c1317 = true := by
  simpa only [c1317,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1317
def c1318 : List Lit := [(1669, false), (1671, true)]
theorem step1318 (p : Nat → Bool) (h : Constraints p) : clause p c1318 = true := by
  simpa only [c1318,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1318
def c1319 : List Lit := [(1670, false), (1672, true)]
theorem step1319 (p : Nat → Bool) (h : Constraints p) : clause p c1319 = true := by
  simpa only [c1319,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1319
def c1320 : List Lit := [(1667, false), (1671, true)]
theorem step1320 (p : Nat → Bool) (h : Constraints p) : clause p c1320 = true := by
  simpa only [c1320,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1320
def c1321 : List Lit := [(1667, false), (1669, false), (1672, true)]
theorem step1321 (p : Nat → Bool) (h : Constraints p) : clause p c1321 = true := by
  simpa only [c1321,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1321
def c1322 : List Lit := [(1667, false), (1670, false), (1673, true)]
theorem step1322 (p : Nat → Bool) (h : Constraints p) : clause p c1322 = true := by
  simpa only [c1322,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1322
def c1323 : List Lit := [(1668, false), (1672, true)]
theorem step1323 (p : Nat → Bool) (h : Constraints p) : clause p c1323 = true := by
  simpa only [c1323,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1323
def c1324 : List Lit := [(1668, false), (1669, false), (1673, true)]
theorem step1324 (p : Nat → Bool) (h : Constraints p) : clause p c1324 = true := by
  simpa only [c1324,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1324
def c1325 : List Lit := [(84, true), (1675, true)]
theorem step1325 (p : Nat → Bool) (h : Constraints p) : clause p c1325 = true := by
  simpa only [c1325,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1325
def c1326 : List Lit := [(83, true), (1675, true)]
theorem step1326 (p : Nat → Bool) (h : Constraints p) : clause p c1326 = true := by
  simpa only [c1326,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1326
def c1327 : List Lit := [(83, true), (84, true), (1676, true)]
theorem step1327 (p : Nat → Bool) (h : Constraints p) : clause p c1327 = true := by
  simpa only [c1327,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1327
def c1328 : List Lit := [(91, true), (1677, true)]
theorem step1328 (p : Nat → Bool) (h : Constraints p) : clause p c1328 = true := by
  simpa only [c1328,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1328
def c1329 : List Lit := [(88, true), (1677, true)]
theorem step1329 (p : Nat → Bool) (h : Constraints p) : clause p c1329 = true := by
  simpa only [c1329,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1329
def c1330 : List Lit := [(88, true), (91, true), (1678, true)]
theorem step1330 (p : Nat → Bool) (h : Constraints p) : clause p c1330 = true := by
  simpa only [c1330,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1330
def c1331 : List Lit := [(1677, false), (1679, true)]
theorem step1331 (p : Nat → Bool) (h : Constraints p) : clause p c1331 = true := by
  simpa only [c1331,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1331
def c1332 : List Lit := [(1678, false), (1680, true)]
theorem step1332 (p : Nat → Bool) (h : Constraints p) : clause p c1332 = true := by
  simpa only [c1332,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1332
def c1333 : List Lit := [(1675, false), (1679, true)]
theorem step1333 (p : Nat → Bool) (h : Constraints p) : clause p c1333 = true := by
  simpa only [c1333,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1333
def c1334 : List Lit := [(1675, false), (1677, false), (1680, true)]
theorem step1334 (p : Nat → Bool) (h : Constraints p) : clause p c1334 = true := by
  simpa only [c1334,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1334
def c1335 : List Lit := [(1675, false), (1678, false), (1681, true)]
theorem step1335 (p : Nat → Bool) (h : Constraints p) : clause p c1335 = true := by
  simpa only [c1335,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1335
def c1336 : List Lit := [(1676, false), (1680, true)]
theorem step1336 (p : Nat → Bool) (h : Constraints p) : clause p c1336 = true := by
  simpa only [c1336,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1336
def c1337 : List Lit := [(1676, false), (1677, false), (1681, true)]
theorem step1337 (p : Nat → Bool) (h : Constraints p) : clause p c1337 = true := by
  simpa only [c1337,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1337
def c1338 : List Lit := [(1679, false), (1683, true)]
theorem step1338 (p : Nat → Bool) (h : Constraints p) : clause p c1338 = true := by
  simpa only [c1338,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1338
def c1339 : List Lit := [(1680, false), (1684, true)]
theorem step1339 (p : Nat → Bool) (h : Constraints p) : clause p c1339 = true := by
  simpa only [c1339,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1339
def c1340 : List Lit := [(1681, false), (1685, true)]
theorem step1340 (p : Nat → Bool) (h : Constraints p) : clause p c1340 = true := by
  simpa only [c1340,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1340
def c1341 : List Lit := [(1671, false), (1683, true)]
theorem step1341 (p : Nat → Bool) (h : Constraints p) : clause p c1341 = true := by
  simpa only [c1341,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1341
def c1342 : List Lit := [(1671, false), (1679, false), (1684, true)]
theorem step1342 (p : Nat → Bool) (h : Constraints p) : clause p c1342 = true := by
  simpa only [c1342,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1342
def c1343 : List Lit := [(1671, false), (1680, false), (1685, true)]
theorem step1343 (p : Nat → Bool) (h : Constraints p) : clause p c1343 = true := by
  simpa only [c1343,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1343
def c1344 : List Lit := [(1671, false), (1681, false), (1686, true)]
theorem step1344 (p : Nat → Bool) (h : Constraints p) : clause p c1344 = true := by
  simpa only [c1344,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block41.clause1344
def c1345 : List Lit := [(1672, false), (1684, true)]
theorem step1345 (p : Nat → Bool) (h : Constraints p) : clause p c1345 = true := by
  simpa only [c1345,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1345
def c1346 : List Lit := [(1672, false), (1679, false), (1685, true)]
theorem step1346 (p : Nat → Bool) (h : Constraints p) : clause p c1346 = true := by
  simpa only [c1346,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1346
def c1347 : List Lit := [(1672, false), (1680, false), (1686, true)]
theorem step1347 (p : Nat → Bool) (h : Constraints p) : clause p c1347 = true := by
  simpa only [c1347,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1347
def c1348 : List Lit := [(1673, false), (1685, true)]
theorem step1348 (p : Nat → Bool) (h : Constraints p) : clause p c1348 = true := by
  simpa only [c1348,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1348
def c1349 : List Lit := [(1673, false), (1679, false), (1686, true)]
theorem step1349 (p : Nat → Bool) (h : Constraints p) : clause p c1349 = true := by
  simpa only [c1349,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1349
def c1350 : List Lit := [(1685, false), (1693, true)]
theorem step1350 (p : Nat → Bool) (h : Constraints p) : clause p c1350 = true := by
  simpa only [c1350,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1350
def c1351 : List Lit := [(1659, false), (1691, true)]
theorem step1351 (p : Nat → Bool) (h : Constraints p) : clause p c1351 = true := by
  simpa only [c1351,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1351
def c1352 : List Lit := [(1659, false), (1683, false), (1692, true)]
theorem step1352 (p : Nat → Bool) (h : Constraints p) : clause p c1352 = true := by
  simpa only [c1352,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1352
def c1353 : List Lit := [(1659, false), (1684, false), (1693, true)]
theorem step1353 (p : Nat → Bool) (h : Constraints p) : clause p c1353 = true := by
  simpa only [c1353,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1353
def c1354 : List Lit := [(1659, false), (1685, false), (1694, true)]
theorem step1354 (p : Nat → Bool) (h : Constraints p) : clause p c1354 = true := by
  simpa only [c1354,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1354
def c1355 : List Lit := [(1659, false), (1686, false), (1695, true)]
theorem step1355 (p : Nat → Bool) (h : Constraints p) : clause p c1355 = true := by
  simpa only [c1355,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1355
def c1356 : List Lit := [(1660, false), (1692, true)]
theorem step1356 (p : Nat → Bool) (h : Constraints p) : clause p c1356 = true := by
  simpa only [c1356,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1356
def c1357 : List Lit := [(1660, false), (1683, false), (1693, true)]
theorem step1357 (p : Nat → Bool) (h : Constraints p) : clause p c1357 = true := by
  simpa only [c1357,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1357
def c1358 : List Lit := [(1660, false), (1684, false), (1694, true)]
theorem step1358 (p : Nat → Bool) (h : Constraints p) : clause p c1358 = true := by
  simpa only [c1358,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1358
def c1359 : List Lit := [(1660, false), (1685, false), (1695, true)]
theorem step1359 (p : Nat → Bool) (h : Constraints p) : clause p c1359 = true := by
  simpa only [c1359,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1359
def c1360 : List Lit := [(1660, false), (1686, false), (1696, true)]
theorem step1360 (p : Nat → Bool) (h : Constraints p) : clause p c1360 = true := by
  simpa only [c1360,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1360
def c1361 : List Lit := [(1661, false), (1693, true)]
theorem step1361 (p : Nat → Bool) (h : Constraints p) : clause p c1361 = true := by
  simpa only [c1361,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1361
def c1362 : List Lit := [(1661, false), (1683, false), (1694, true)]
theorem step1362 (p : Nat → Bool) (h : Constraints p) : clause p c1362 = true := by
  simpa only [c1362,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1362
def c1363 : List Lit := [(1661, false), (1684, false), (1695, true)]
theorem step1363 (p : Nat → Bool) (h : Constraints p) : clause p c1363 = true := by
  simpa only [c1363,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1363
def c1364 : List Lit := [(1661, false), (1685, false), (1696, true)]
theorem step1364 (p : Nat → Bool) (h : Constraints p) : clause p c1364 = true := by
  simpa only [c1364,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1364
def c1365 : List Lit := [(1661, false), (1686, false), (1697, true)]
theorem step1365 (p : Nat → Bool) (h : Constraints p) : clause p c1365 = true := by
  simpa only [c1365,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1365
def c1366 : List Lit := [(1662, false), (1694, true)]
theorem step1366 (p : Nat → Bool) (h : Constraints p) : clause p c1366 = true := by
  simpa only [c1366,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1366
def c1367 : List Lit := [(1662, false), (1683, false), (1695, true)]
theorem step1367 (p : Nat → Bool) (h : Constraints p) : clause p c1367 = true := by
  simpa only [c1367,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1367
def c1368 : List Lit := [(1662, false), (1684, false), (1696, true)]
theorem step1368 (p : Nat → Bool) (h : Constraints p) : clause p c1368 = true := by
  simpa only [c1368,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1368
def c1369 : List Lit := [(1662, false), (1685, false), (1697, true)]
theorem step1369 (p : Nat → Bool) (h : Constraints p) : clause p c1369 = true := by
  simpa only [c1369,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1369
def c1370 : List Lit := [(1663, false), (1695, true)]
theorem step1370 (p : Nat → Bool) (h : Constraints p) : clause p c1370 = true := by
  simpa only [c1370,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1370
def c1371 : List Lit := [(1663, false), (1683, false), (1696, true)]
theorem step1371 (p : Nat → Bool) (h : Constraints p) : clause p c1371 = true := by
  simpa only [c1371,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1371
def c1372 : List Lit := [(1663, false), (1684, false), (1697, true)]
theorem step1372 (p : Nat → Bool) (h : Constraints p) : clause p c1372 = true := by
  simpa only [c1372,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1372
def c1373 : List Lit := [(1663, false), (1685, false), (1698, true)]
theorem step1373 (p : Nat → Bool) (h : Constraints p) : clause p c1373 = true := by
  simpa only [c1373,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1373
def c1374 : List Lit := [(1664, false), (1696, true)]
theorem step1374 (p : Nat → Bool) (h : Constraints p) : clause p c1374 = true := by
  simpa only [c1374,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1374
def c1375 : List Lit := [(1664, false), (1683, false), (1697, true)]
theorem step1375 (p : Nat → Bool) (h : Constraints p) : clause p c1375 = true := by
  simpa only [c1375,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1375
def c1376 : List Lit := [(1664, false), (1684, false), (1698, true)]
theorem step1376 (p : Nat → Bool) (h : Constraints p) : clause p c1376 = true := by
  simpa only [c1376,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block42.clause1376
def c1377 : List Lit := [(1665, false), (1697, true)]
theorem step1377 (p : Nat → Bool) (h : Constraints p) : clause p c1377 = true := by
  simpa only [c1377,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1377
def c1378 : List Lit := [(1665, false), (1683, false), (1698, true)]
theorem step1378 (p : Nat → Bool) (h : Constraints p) : clause p c1378 = true := by
  simpa only [c1378,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1378
def c1379 : List Lit := [(1665, false), (1684, false), (1699, true)]
theorem step1379 (p : Nat → Bool) (h : Constraints p) : clause p c1379 = true := by
  simpa only [c1379,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1379
def c1380 : List Lit := [(94, true), (1707, true)]
theorem step1380 (p : Nat → Bool) (h : Constraints p) : clause p c1380 = true := by
  simpa only [c1380,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1380
def c1381 : List Lit := [(92, true), (1707, true)]
theorem step1381 (p : Nat → Bool) (h : Constraints p) : clause p c1381 = true := by
  simpa only [c1381,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1381
def c1382 : List Lit := [(92, true), (94, true), (1708, true)]
theorem step1382 (p : Nat → Bool) (h : Constraints p) : clause p c1382 = true := by
  simpa only [c1382,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1382
def c1383 : List Lit := [(99, true), (1709, true)]
theorem step1383 (p : Nat → Bool) (h : Constraints p) : clause p c1383 = true := by
  simpa only [c1383,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1383
def c1384 : List Lit := [(96, true), (1709, true)]
theorem step1384 (p : Nat → Bool) (h : Constraints p) : clause p c1384 = true := by
  simpa only [c1384,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1384
def c1385 : List Lit := [(96, true), (99, true), (1710, true)]
theorem step1385 (p : Nat → Bool) (h : Constraints p) : clause p c1385 = true := by
  simpa only [c1385,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1385
def c1386 : List Lit := [(1709, false), (1711, true)]
theorem step1386 (p : Nat → Bool) (h : Constraints p) : clause p c1386 = true := by
  simpa only [c1386,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1386
def c1387 : List Lit := [(1710, false), (1712, true)]
theorem step1387 (p : Nat → Bool) (h : Constraints p) : clause p c1387 = true := by
  simpa only [c1387,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1387
def c1388 : List Lit := [(1707, false), (1711, true)]
theorem step1388 (p : Nat → Bool) (h : Constraints p) : clause p c1388 = true := by
  simpa only [c1388,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1388
def c1389 : List Lit := [(1707, false), (1709, false), (1712, true)]
theorem step1389 (p : Nat → Bool) (h : Constraints p) : clause p c1389 = true := by
  simpa only [c1389,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1389
def c1390 : List Lit := [(1707, false), (1710, false), (1713, true)]
theorem step1390 (p : Nat → Bool) (h : Constraints p) : clause p c1390 = true := by
  simpa only [c1390,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1390
def c1391 : List Lit := [(1708, false), (1712, true)]
theorem step1391 (p : Nat → Bool) (h : Constraints p) : clause p c1391 = true := by
  simpa only [c1391,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1391
def c1392 : List Lit := [(1708, false), (1709, false), (1713, true)]
theorem step1392 (p : Nat → Bool) (h : Constraints p) : clause p c1392 = true := by
  simpa only [c1392,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1392
def c1393 : List Lit := [(103, true), (1715, true)]
theorem step1393 (p : Nat → Bool) (h : Constraints p) : clause p c1393 = true := by
  simpa only [c1393,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1393
def c1394 : List Lit := [(100, true), (1715, true)]
theorem step1394 (p : Nat → Bool) (h : Constraints p) : clause p c1394 = true := by
  simpa only [c1394,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1394
def c1395 : List Lit := [(100, true), (103, true), (1716, true)]
theorem step1395 (p : Nat → Bool) (h : Constraints p) : clause p c1395 = true := by
  simpa only [c1395,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1395
def c1396 : List Lit := [(106, true), (1717, true)]
theorem step1396 (p : Nat → Bool) (h : Constraints p) : clause p c1396 = true := by
  simpa only [c1396,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1396
def c1397 : List Lit := [(104, true), (1717, true)]
theorem step1397 (p : Nat → Bool) (h : Constraints p) : clause p c1397 = true := by
  simpa only [c1397,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1397
def c1398 : List Lit := [(104, true), (106, true), (1718, true)]
theorem step1398 (p : Nat → Bool) (h : Constraints p) : clause p c1398 = true := by
  simpa only [c1398,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1398
def c1399 : List Lit := [(1717, false), (1719, true)]
theorem step1399 (p : Nat → Bool) (h : Constraints p) : clause p c1399 = true := by
  simpa only [c1399,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1399
def c1400 : List Lit := [(1718, false), (1720, true)]
theorem step1400 (p : Nat → Bool) (h : Constraints p) : clause p c1400 = true := by
  simpa only [c1400,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1400
def c1401 : List Lit := [(1715, false), (1719, true)]
theorem step1401 (p : Nat → Bool) (h : Constraints p) : clause p c1401 = true := by
  simpa only [c1401,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1401
def c1402 : List Lit := [(1715, false), (1717, false), (1720, true)]
theorem step1402 (p : Nat → Bool) (h : Constraints p) : clause p c1402 = true := by
  simpa only [c1402,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1402
def c1403 : List Lit := [(1715, false), (1718, false), (1721, true)]
theorem step1403 (p : Nat → Bool) (h : Constraints p) : clause p c1403 = true := by
  simpa only [c1403,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1403
def c1404 : List Lit := [(1716, false), (1720, true)]
theorem step1404 (p : Nat → Bool) (h : Constraints p) : clause p c1404 = true := by
  simpa only [c1404,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1404
def c1405 : List Lit := [(1716, false), (1717, false), (1721, true)]
theorem step1405 (p : Nat → Bool) (h : Constraints p) : clause p c1405 = true := by
  simpa only [c1405,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1405
def c1406 : List Lit := [(1716, false), (1718, false), (1722, true)]
theorem step1406 (p : Nat → Bool) (h : Constraints p) : clause p c1406 = true := by
  simpa only [c1406,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1406
def c1407 : List Lit := [(1719, false), (1723, true)]
theorem step1407 (p : Nat → Bool) (h : Constraints p) : clause p c1407 = true := by
  simpa only [c1407,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1407
def c1408 : List Lit := [(1720, false), (1724, true)]
theorem step1408 (p : Nat → Bool) (h : Constraints p) : clause p c1408 = true := by
  simpa only [c1408,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block43.clause1408
def c1409 : List Lit := [(1721, false), (1725, true)]
theorem step1409 (p : Nat → Bool) (h : Constraints p) : clause p c1409 = true := by
  simpa only [c1409,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1409
def c1410 : List Lit := [(1722, false), (1726, true)]
theorem step1410 (p : Nat → Bool) (h : Constraints p) : clause p c1410 = true := by
  simpa only [c1410,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1410
def c1411 : List Lit := [(1711, false), (1723, true)]
theorem step1411 (p : Nat → Bool) (h : Constraints p) : clause p c1411 = true := by
  simpa only [c1411,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1411
def c1412 : List Lit := [(1711, false), (1719, false), (1724, true)]
theorem step1412 (p : Nat → Bool) (h : Constraints p) : clause p c1412 = true := by
  simpa only [c1412,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1412
def c1413 : List Lit := [(1711, false), (1720, false), (1725, true)]
theorem step1413 (p : Nat → Bool) (h : Constraints p) : clause p c1413 = true := by
  simpa only [c1413,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1413
def c1414 : List Lit := [(1711, false), (1721, false), (1726, true)]
theorem step1414 (p : Nat → Bool) (h : Constraints p) : clause p c1414 = true := by
  simpa only [c1414,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1414
def c1415 : List Lit := [(1711, false), (1722, false), (1727, true)]
theorem step1415 (p : Nat → Bool) (h : Constraints p) : clause p c1415 = true := by
  simpa only [c1415,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1415
def c1416 : List Lit := [(1712, false), (1724, true)]
theorem step1416 (p : Nat → Bool) (h : Constraints p) : clause p c1416 = true := by
  simpa only [c1416,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1416
def c1417 : List Lit := [(1712, false), (1719, false), (1725, true)]
theorem step1417 (p : Nat → Bool) (h : Constraints p) : clause p c1417 = true := by
  simpa only [c1417,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1417
def c1418 : List Lit := [(1712, false), (1720, false), (1726, true)]
theorem step1418 (p : Nat → Bool) (h : Constraints p) : clause p c1418 = true := by
  simpa only [c1418,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1418
def c1419 : List Lit := [(1712, false), (1721, false), (1727, true)]
theorem step1419 (p : Nat → Bool) (h : Constraints p) : clause p c1419 = true := by
  simpa only [c1419,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1419
def c1420 : List Lit := [(1712, false), (1722, false), (1728, true)]
theorem step1420 (p : Nat → Bool) (h : Constraints p) : clause p c1420 = true := by
  simpa only [c1420,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1420
def c1421 : List Lit := [(1713, false), (1719, false), (1726, true)]
theorem step1421 (p : Nat → Bool) (h : Constraints p) : clause p c1421 = true := by
  simpa only [c1421,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1421
def c1422 : List Lit := [(1713, false), (1720, false), (1727, true)]
theorem step1422 (p : Nat → Bool) (h : Constraints p) : clause p c1422 = true := by
  simpa only [c1422,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1422
def c1423 : List Lit := [(109, true), (1731, true)]
theorem step1423 (p : Nat → Bool) (h : Constraints p) : clause p c1423 = true := by
  simpa only [c1423,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1423
def c1424 : List Lit := [(107, true), (1731, true)]
theorem step1424 (p : Nat → Bool) (h : Constraints p) : clause p c1424 = true := by
  simpa only [c1424,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1424
def c1425 : List Lit := [(107, true), (109, true), (1732, true)]
theorem step1425 (p : Nat → Bool) (h : Constraints p) : clause p c1425 = true := by
  simpa only [c1425,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1425
def c1426 : List Lit := [(113, true), (1733, true)]
theorem step1426 (p : Nat → Bool) (h : Constraints p) : clause p c1426 = true := by
  simpa only [c1426,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1426
def c1427 : List Lit := [(111, true), (1733, true)]
theorem step1427 (p : Nat → Bool) (h : Constraints p) : clause p c1427 = true := by
  simpa only [c1427,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1427
def c1428 : List Lit := [(111, true), (113, true), (1734, true)]
theorem step1428 (p : Nat → Bool) (h : Constraints p) : clause p c1428 = true := by
  simpa only [c1428,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1428
def c1429 : List Lit := [(1733, false), (1735, true)]
theorem step1429 (p : Nat → Bool) (h : Constraints p) : clause p c1429 = true := by
  simpa only [c1429,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1429
def c1430 : List Lit := [(1734, false), (1736, true)]
theorem step1430 (p : Nat → Bool) (h : Constraints p) : clause p c1430 = true := by
  simpa only [c1430,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1430
def c1431 : List Lit := [(1731, false), (1735, true)]
theorem step1431 (p : Nat → Bool) (h : Constraints p) : clause p c1431 = true := by
  simpa only [c1431,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1431
def c1432 : List Lit := [(1731, false), (1733, false), (1736, true)]
theorem step1432 (p : Nat → Bool) (h : Constraints p) : clause p c1432 = true := by
  simpa only [c1432,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1432
def c1433 : List Lit := [(1731, false), (1734, false), (1737, true)]
theorem step1433 (p : Nat → Bool) (h : Constraints p) : clause p c1433 = true := by
  simpa only [c1433,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1433
def c1434 : List Lit := [(1732, false), (1736, true)]
theorem step1434 (p : Nat → Bool) (h : Constraints p) : clause p c1434 = true := by
  simpa only [c1434,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1434
def c1435 : List Lit := [(1732, false), (1733, false), (1737, true)]
theorem step1435 (p : Nat → Bool) (h : Constraints p) : clause p c1435 = true := by
  simpa only [c1435,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1435
def c1436 : List Lit := [(1732, false), (1734, false), (1738, true)]
theorem step1436 (p : Nat → Bool) (h : Constraints p) : clause p c1436 = true := by
  simpa only [c1436,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1436
def c1437 : List Lit := [(118, true), (1739, true)]
theorem step1437 (p : Nat → Bool) (h : Constraints p) : clause p c1437 = true := by
  simpa only [c1437,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1437
def c1438 : List Lit := [(116, true), (1739, true)]
theorem step1438 (p : Nat → Bool) (h : Constraints p) : clause p c1438 = true := by
  simpa only [c1438,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1438
def c1439 : List Lit := [(116, true), (118, true), (1740, true)]
theorem step1439 (p : Nat → Bool) (h : Constraints p) : clause p c1439 = true := by
  simpa only [c1439,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1439
def c1440 : List Lit := [(124, true), (1741, true)]
theorem step1440 (p : Nat → Bool) (h : Constraints p) : clause p c1440 = true := by
  simpa only [c1440,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block44.clause1440
def c1441 : List Lit := [(121, true), (1741, true)]
theorem step1441 (p : Nat → Bool) (h : Constraints p) : clause p c1441 = true := by
  simpa only [c1441,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1441
def c1442 : List Lit := [(121, true), (124, true), (1742, true)]
theorem step1442 (p : Nat → Bool) (h : Constraints p) : clause p c1442 = true := by
  simpa only [c1442,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1442
def c1443 : List Lit := [(1741, false), (1743, true)]
theorem step1443 (p : Nat → Bool) (h : Constraints p) : clause p c1443 = true := by
  simpa only [c1443,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1443
def c1444 : List Lit := [(1742, false), (1744, true)]
theorem step1444 (p : Nat → Bool) (h : Constraints p) : clause p c1444 = true := by
  simpa only [c1444,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1444
def c1445 : List Lit := [(1739, false), (1743, true)]
theorem step1445 (p : Nat → Bool) (h : Constraints p) : clause p c1445 = true := by
  simpa only [c1445,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1445
def c1446 : List Lit := [(1739, false), (1741, false), (1744, true)]
theorem step1446 (p : Nat → Bool) (h : Constraints p) : clause p c1446 = true := by
  simpa only [c1446,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1446
def c1447 : List Lit := [(1739, false), (1742, false), (1745, true)]
theorem step1447 (p : Nat → Bool) (h : Constraints p) : clause p c1447 = true := by
  simpa only [c1447,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1447
def c1448 : List Lit := [(1740, false), (1744, true)]
theorem step1448 (p : Nat → Bool) (h : Constraints p) : clause p c1448 = true := by
  simpa only [c1448,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1448
def c1449 : List Lit := [(1740, false), (1741, false), (1745, true)]
theorem step1449 (p : Nat → Bool) (h : Constraints p) : clause p c1449 = true := by
  simpa only [c1449,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1449
def c1450 : List Lit := [(1740, false), (1742, false), (1746, true)]
theorem step1450 (p : Nat → Bool) (h : Constraints p) : clause p c1450 = true := by
  simpa only [c1450,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1450
def c1451 : List Lit := [(1743, false), (1747, true)]
theorem step1451 (p : Nat → Bool) (h : Constraints p) : clause p c1451 = true := by
  simpa only [c1451,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1451
def c1452 : List Lit := [(1744, false), (1748, true)]
theorem step1452 (p : Nat → Bool) (h : Constraints p) : clause p c1452 = true := by
  simpa only [c1452,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1452
def c1453 : List Lit := [(1745, false), (1749, true)]
theorem step1453 (p : Nat → Bool) (h : Constraints p) : clause p c1453 = true := by
  simpa only [c1453,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1453
def c1454 : List Lit := [(1746, false), (1750, true)]
theorem step1454 (p : Nat → Bool) (h : Constraints p) : clause p c1454 = true := by
  simpa only [c1454,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1454
def c1455 : List Lit := [(1735, false), (1747, true)]
theorem step1455 (p : Nat → Bool) (h : Constraints p) : clause p c1455 = true := by
  simpa only [c1455,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1455
def c1456 : List Lit := [(1735, false), (1743, false), (1748, true)]
theorem step1456 (p : Nat → Bool) (h : Constraints p) : clause p c1456 = true := by
  simpa only [c1456,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1456
def c1457 : List Lit := [(1735, false), (1744, false), (1749, true)]
theorem step1457 (p : Nat → Bool) (h : Constraints p) : clause p c1457 = true := by
  simpa only [c1457,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1457
def c1458 : List Lit := [(1735, false), (1745, false), (1750, true)]
theorem step1458 (p : Nat → Bool) (h : Constraints p) : clause p c1458 = true := by
  simpa only [c1458,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1458
def c1459 : List Lit := [(1735, false), (1746, false), (1751, true)]
theorem step1459 (p : Nat → Bool) (h : Constraints p) : clause p c1459 = true := by
  simpa only [c1459,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1459
def c1460 : List Lit := [(1736, false), (1748, true)]
theorem step1460 (p : Nat → Bool) (h : Constraints p) : clause p c1460 = true := by
  simpa only [c1460,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1460
def c1461 : List Lit := [(1736, false), (1743, false), (1749, true)]
theorem step1461 (p : Nat → Bool) (h : Constraints p) : clause p c1461 = true := by
  simpa only [c1461,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1461
def c1462 : List Lit := [(1736, false), (1744, false), (1750, true)]
theorem step1462 (p : Nat → Bool) (h : Constraints p) : clause p c1462 = true := by
  simpa only [c1462,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1462
def c1463 : List Lit := [(1736, false), (1745, false), (1751, true)]
theorem step1463 (p : Nat → Bool) (h : Constraints p) : clause p c1463 = true := by
  simpa only [c1463,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1463
def c1464 : List Lit := [(1736, false), (1746, false), (1752, true)]
theorem step1464 (p : Nat → Bool) (h : Constraints p) : clause p c1464 = true := by
  simpa only [c1464,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1464
def c1465 : List Lit := [(1737, false), (1749, true)]
theorem step1465 (p : Nat → Bool) (h : Constraints p) : clause p c1465 = true := by
  simpa only [c1465,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1465
def c1466 : List Lit := [(1737, false), (1743, false), (1750, true)]
theorem step1466 (p : Nat → Bool) (h : Constraints p) : clause p c1466 = true := by
  simpa only [c1466,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1466
def c1467 : List Lit := [(1737, false), (1744, false), (1751, true)]
theorem step1467 (p : Nat → Bool) (h : Constraints p) : clause p c1467 = true := by
  simpa only [c1467,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1467
def c1468 : List Lit := [(1737, false), (1745, false), (1752, true)]
theorem step1468 (p : Nat → Bool) (h : Constraints p) : clause p c1468 = true := by
  simpa only [c1468,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1468
def c1469 : List Lit := [(1737, false), (1746, false), (1753, true)]
theorem step1469 (p : Nat → Bool) (h : Constraints p) : clause p c1469 = true := by
  simpa only [c1469,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1469
def c1470 : List Lit := [(1738, false), (1750, true)]
theorem step1470 (p : Nat → Bool) (h : Constraints p) : clause p c1470 = true := by
  simpa only [c1470,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1470
def c1471 : List Lit := [(1738, false), (1743, false), (1751, true)]
theorem step1471 (p : Nat → Bool) (h : Constraints p) : clause p c1471 = true := by
  simpa only [c1471,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1471
def c1472 : List Lit := [(1738, false), (1744, false), (1752, true)]
theorem step1472 (p : Nat → Bool) (h : Constraints p) : clause p c1472 = true := by
  simpa only [c1472,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block45.clause1472
def c1473 : List Lit := [(1738, false), (1745, false), (1753, true)]
theorem step1473 (p : Nat → Bool) (h : Constraints p) : clause p c1473 = true := by
  simpa only [c1473,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1473
def c1474 : List Lit := [(1738, false), (1746, false), (1754, true)]
theorem step1474 (p : Nat → Bool) (h : Constraints p) : clause p c1474 = true := by
  simpa only [c1474,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1474
def c1475 : List Lit := [(1750, false), (1758, true)]
theorem step1475 (p : Nat → Bool) (h : Constraints p) : clause p c1475 = true := by
  simpa only [c1475,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1475
def c1476 : List Lit := [(1751, false), (1759, true)]
theorem step1476 (p : Nat → Bool) (h : Constraints p) : clause p c1476 = true := by
  simpa only [c1476,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1476
def c1477 : List Lit := [(1752, false), (1760, true)]
theorem step1477 (p : Nat → Bool) (h : Constraints p) : clause p c1477 = true := by
  simpa only [c1477,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1477
def c1478 : List Lit := [(1753, false), (1761, true)]
theorem step1478 (p : Nat → Bool) (h : Constraints p) : clause p c1478 = true := by
  simpa only [c1478,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1478
def c1479 : List Lit := [(1754, false), (1762, true)]
theorem step1479 (p : Nat → Bool) (h : Constraints p) : clause p c1479 = true := by
  simpa only [c1479,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1479
def c1480 : List Lit := [(1723, false), (1749, false), (1758, true)]
theorem step1480 (p : Nat → Bool) (h : Constraints p) : clause p c1480 = true := by
  simpa only [c1480,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1480
def c1481 : List Lit := [(1723, false), (1750, false), (1759, true)]
theorem step1481 (p : Nat → Bool) (h : Constraints p) : clause p c1481 = true := by
  simpa only [c1481,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1481
def c1482 : List Lit := [(1723, false), (1751, false), (1760, true)]
theorem step1482 (p : Nat → Bool) (h : Constraints p) : clause p c1482 = true := by
  simpa only [c1482,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1482
def c1483 : List Lit := [(1723, false), (1752, false), (1761, true)]
theorem step1483 (p : Nat → Bool) (h : Constraints p) : clause p c1483 = true := by
  simpa only [c1483,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1483
def c1484 : List Lit := [(1723, false), (1753, false), (1762, true)]
theorem step1484 (p : Nat → Bool) (h : Constraints p) : clause p c1484 = true := by
  simpa only [c1484,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1484
def c1485 : List Lit := [(1723, false), (1754, false), (1763, true)]
theorem step1485 (p : Nat → Bool) (h : Constraints p) : clause p c1485 = true := by
  simpa only [c1485,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1485
def c1486 : List Lit := [(1724, false), (1748, false), (1758, true)]
theorem step1486 (p : Nat → Bool) (h : Constraints p) : clause p c1486 = true := by
  simpa only [c1486,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1486
def c1487 : List Lit := [(1724, false), (1749, false), (1759, true)]
theorem step1487 (p : Nat → Bool) (h : Constraints p) : clause p c1487 = true := by
  simpa only [c1487,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1487
def c1488 : List Lit := [(1724, false), (1750, false), (1760, true)]
theorem step1488 (p : Nat → Bool) (h : Constraints p) : clause p c1488 = true := by
  simpa only [c1488,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1488
def c1489 : List Lit := [(1724, false), (1751, false), (1761, true)]
theorem step1489 (p : Nat → Bool) (h : Constraints p) : clause p c1489 = true := by
  simpa only [c1489,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1489
def c1490 : List Lit := [(1724, false), (1752, false), (1762, true)]
theorem step1490 (p : Nat → Bool) (h : Constraints p) : clause p c1490 = true := by
  simpa only [c1490,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1490
def c1491 : List Lit := [(1724, false), (1753, false), (1763, true)]
theorem step1491 (p : Nat → Bool) (h : Constraints p) : clause p c1491 = true := by
  simpa only [c1491,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1491
def c1492 : List Lit := [(1725, false), (1747, false), (1758, true)]
theorem step1492 (p : Nat → Bool) (h : Constraints p) : clause p c1492 = true := by
  simpa only [c1492,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1492
def c1493 : List Lit := [(1725, false), (1748, false), (1759, true)]
theorem step1493 (p : Nat → Bool) (h : Constraints p) : clause p c1493 = true := by
  simpa only [c1493,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1493
def c1494 : List Lit := [(1725, false), (1749, false), (1760, true)]
theorem step1494 (p : Nat → Bool) (h : Constraints p) : clause p c1494 = true := by
  simpa only [c1494,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1494
def c1495 : List Lit := [(1725, false), (1750, false), (1761, true)]
theorem step1495 (p : Nat → Bool) (h : Constraints p) : clause p c1495 = true := by
  simpa only [c1495,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1495
def c1496 : List Lit := [(1725, false), (1751, false), (1762, true)]
theorem step1496 (p : Nat → Bool) (h : Constraints p) : clause p c1496 = true := by
  simpa only [c1496,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1496
def c1497 : List Lit := [(1725, false), (1752, false), (1763, true)]
theorem step1497 (p : Nat → Bool) (h : Constraints p) : clause p c1497 = true := by
  simpa only [c1497,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1497
def c1498 : List Lit := [(1726, false), (1747, false), (1759, true)]
theorem step1498 (p : Nat → Bool) (h : Constraints p) : clause p c1498 = true := by
  simpa only [c1498,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1498
def c1499 : List Lit := [(1726, false), (1748, false), (1760, true)]
theorem step1499 (p : Nat → Bool) (h : Constraints p) : clause p c1499 = true := by
  simpa only [c1499,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1499
def c1500 : List Lit := [(1726, false), (1749, false), (1761, true)]
theorem step1500 (p : Nat → Bool) (h : Constraints p) : clause p c1500 = true := by
  simpa only [c1500,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1500
def c1501 : List Lit := [(1726, false), (1750, false), (1762, true)]
theorem step1501 (p : Nat → Bool) (h : Constraints p) : clause p c1501 = true := by
  simpa only [c1501,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1501
def c1502 : List Lit := [(1726, false), (1751, false), (1763, true)]
theorem step1502 (p : Nat → Bool) (h : Constraints p) : clause p c1502 = true := by
  simpa only [c1502,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1502
def c1503 : List Lit := [(1727, false), (1759, true)]
theorem step1503 (p : Nat → Bool) (h : Constraints p) : clause p c1503 = true := by
  simpa only [c1503,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1503
def c1504 : List Lit := [(1727, false), (1747, false), (1760, true)]
theorem step1504 (p : Nat → Bool) (h : Constraints p) : clause p c1504 = true := by
  simpa only [c1504,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block46.clause1504
def c1505 : List Lit := [(1727, false), (1748, false), (1761, true)]
theorem step1505 (p : Nat → Bool) (h : Constraints p) : clause p c1505 = true := by
  simpa only [c1505,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1505
def c1506 : List Lit := [(1727, false), (1749, false), (1762, true)]
theorem step1506 (p : Nat → Bool) (h : Constraints p) : clause p c1506 = true := by
  simpa only [c1506,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1506
def c1507 : List Lit := [(1727, false), (1750, false), (1763, true)]
theorem step1507 (p : Nat → Bool) (h : Constraints p) : clause p c1507 = true := by
  simpa only [c1507,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1507
def c1508 : List Lit := [(1728, false), (1747, false), (1761, true)]
theorem step1508 (p : Nat → Bool) (h : Constraints p) : clause p c1508 = true := by
  simpa only [c1508,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1508
def c1509 : List Lit := [(1728, false), (1749, false), (1763, true)]
theorem step1509 (p : Nat → Bool) (h : Constraints p) : clause p c1509 = true := by
  simpa only [c1509,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1509
def c1510 : List Lit := [(1691, false), (1760, false), (1777, true)]
theorem step1510 (p : Nat → Bool) (h : Constraints p) : clause p c1510 = true := by
  simpa only [c1510,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1510
def c1511 : List Lit := [(1691, false), (1761, false), (1778, true)]
theorem step1511 (p : Nat → Bool) (h : Constraints p) : clause p c1511 = true := by
  simpa only [c1511,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1511
def c1512 : List Lit := [(1691, false), (1762, false), (1779, true)]
theorem step1512 (p : Nat → Bool) (h : Constraints p) : clause p c1512 = true := by
  simpa only [c1512,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1512
def c1513 : List Lit := [(1691, false), (1763, false), (1780, true)]
theorem step1513 (p : Nat → Bool) (h : Constraints p) : clause p c1513 = true := by
  simpa only [c1513,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1513
def c1514 : List Lit := [(1692, false), (1758, false), (1776, true)]
theorem step1514 (p : Nat → Bool) (h : Constraints p) : clause p c1514 = true := by
  simpa only [c1514,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1514
def c1515 : List Lit := [(1692, false), (1759, false), (1777, true)]
theorem step1515 (p : Nat → Bool) (h : Constraints p) : clause p c1515 = true := by
  simpa only [c1515,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1515
def c1516 : List Lit := [(1692, false), (1760, false), (1778, true)]
theorem step1516 (p : Nat → Bool) (h : Constraints p) : clause p c1516 = true := by
  simpa only [c1516,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1516
def c1517 : List Lit := [(1692, false), (1761, false), (1779, true)]
theorem step1517 (p : Nat → Bool) (h : Constraints p) : clause p c1517 = true := by
  simpa only [c1517,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1517
def c1518 : List Lit := [(1692, false), (1762, false), (1780, true)]
theorem step1518 (p : Nat → Bool) (h : Constraints p) : clause p c1518 = true := by
  simpa only [c1518,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1518
def c1519 : List Lit := [(1692, false), (1763, false), (1781, true)]
theorem step1519 (p : Nat → Bool) (h : Constraints p) : clause p c1519 = true := by
  simpa only [c1519,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1519
def c1520 : List Lit := [(1693, false), (1758, false), (1777, true)]
theorem step1520 (p : Nat → Bool) (h : Constraints p) : clause p c1520 = true := by
  simpa only [c1520,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1520
def c1521 : List Lit := [(1693, false), (1759, false), (1778, true)]
theorem step1521 (p : Nat → Bool) (h : Constraints p) : clause p c1521 = true := by
  simpa only [c1521,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1521
def c1522 : List Lit := [(1693, false), (1760, false), (1779, true)]
theorem step1522 (p : Nat → Bool) (h : Constraints p) : clause p c1522 = true := by
  simpa only [c1522,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1522
def c1523 : List Lit := [(1693, false), (1761, false), (1780, true)]
theorem step1523 (p : Nat → Bool) (h : Constraints p) : clause p c1523 = true := by
  simpa only [c1523,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1523
def c1524 : List Lit := [(1693, false), (1762, false), (1781, true)]
theorem step1524 (p : Nat → Bool) (h : Constraints p) : clause p c1524 = true := by
  simpa only [c1524,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1524
def c1525 : List Lit := [(1693, false), (1763, false), (1782, true)]
theorem step1525 (p : Nat → Bool) (h : Constraints p) : clause p c1525 = true := by
  simpa only [c1525,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1525
def c1526 : List Lit := [(1694, false), (1758, false), (1778, true)]
theorem step1526 (p : Nat → Bool) (h : Constraints p) : clause p c1526 = true := by
  simpa only [c1526,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1526
def c1527 : List Lit := [(1694, false), (1759, false), (1779, true)]
theorem step1527 (p : Nat → Bool) (h : Constraints p) : clause p c1527 = true := by
  simpa only [c1527,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1527
def c1528 : List Lit := [(1694, false), (1760, false), (1780, true)]
theorem step1528 (p : Nat → Bool) (h : Constraints p) : clause p c1528 = true := by
  simpa only [c1528,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1528
def c1529 : List Lit := [(1694, false), (1761, false), (1781, true)]
theorem step1529 (p : Nat → Bool) (h : Constraints p) : clause p c1529 = true := by
  simpa only [c1529,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1529
def c1530 : List Lit := [(1694, false), (1762, false), (1782, true)]
theorem step1530 (p : Nat → Bool) (h : Constraints p) : clause p c1530 = true := by
  simpa only [c1530,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1530
def c1531 : List Lit := [(1695, false), (1758, false), (1779, true)]
theorem step1531 (p : Nat → Bool) (h : Constraints p) : clause p c1531 = true := by
  simpa only [c1531,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1531
def c1532 : List Lit := [(1695, false), (1759, false), (1780, true)]
theorem step1532 (p : Nat → Bool) (h : Constraints p) : clause p c1532 = true := by
  simpa only [c1532,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1532
def c1533 : List Lit := [(1695, false), (1760, false), (1781, true)]
theorem step1533 (p : Nat → Bool) (h : Constraints p) : clause p c1533 = true := by
  simpa only [c1533,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1533
def c1534 : List Lit := [(1695, false), (1761, false), (1782, true)]
theorem step1534 (p : Nat → Bool) (h : Constraints p) : clause p c1534 = true := by
  simpa only [c1534,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1534
def c1535 : List Lit := [(1696, false), (1758, false), (1780, true)]
theorem step1535 (p : Nat → Bool) (h : Constraints p) : clause p c1535 = true := by
  simpa only [c1535,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1535
def c1536 : List Lit := [(1696, false), (1759, false), (1781, true)]
theorem step1536 (p : Nat → Bool) (h : Constraints p) : clause p c1536 = true := by
  simpa only [c1536,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block47.clause1536
def c1537 : List Lit := [(1696, false), (1760, false), (1782, true)]
theorem step1537 (p : Nat → Bool) (h : Constraints p) : clause p c1537 = true := by
  simpa only [c1537,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1537
def c1538 : List Lit := [(1696, false), (1761, false), (1783, true)]
theorem step1538 (p : Nat → Bool) (h : Constraints p) : clause p c1538 = true := by
  simpa only [c1538,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1538
def c1539 : List Lit := [(1697, false), (1758, false), (1781, true)]
theorem step1539 (p : Nat → Bool) (h : Constraints p) : clause p c1539 = true := by
  simpa only [c1539,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1539
def c1540 : List Lit := [(1697, false), (1759, false), (1782, true)]
theorem step1540 (p : Nat → Bool) (h : Constraints p) : clause p c1540 = true := by
  simpa only [c1540,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1540
def c1541 : List Lit := [(1697, false), (1760, false), (1783, true)]
theorem step1541 (p : Nat → Bool) (h : Constraints p) : clause p c1541 = true := by
  simpa only [c1541,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1541
def c1542 : List Lit := [(1698, false), (1758, false), (1782, true)]
theorem step1542 (p : Nat → Bool) (h : Constraints p) : clause p c1542 = true := by
  simpa only [c1542,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1542
def c1543 : List Lit := [(1699, false), (1758, false), (1783, true)]
theorem step1543 (p : Nat → Bool) (h : Constraints p) : clause p c1543 = true := by
  simpa only [c1543,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1543
def c1544 : List Lit := [(1629, false), (1783, false), (1816, true)]
theorem step1544 (p : Nat → Bool) (h : Constraints p) : clause p c1544 = true := by
  simpa only [c1544,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1544
def c1545 : List Lit := [(1630, false), (1782, false), (1816, true)]
theorem step1545 (p : Nat → Bool) (h : Constraints p) : clause p c1545 = true := by
  simpa only [c1545,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1545
def c1546 : List Lit := [(1631, false), (1781, false), (1816, true)]
theorem step1546 (p : Nat → Bool) (h : Constraints p) : clause p c1546 = true := by
  simpa only [c1546,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1546
def c1547 : List Lit := [(1632, false), (1780, false), (1816, true)]
theorem step1547 (p : Nat → Bool) (h : Constraints p) : clause p c1547 = true := by
  simpa only [c1547,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1547
def c1548 : List Lit := [(1633, false), (1779, false), (1816, true)]
theorem step1548 (p : Nat → Bool) (h : Constraints p) : clause p c1548 = true := by
  simpa only [c1548,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1548
def c1549 : List Lit := [(1634, false), (1778, false), (1816, true)]
theorem step1549 (p : Nat → Bool) (h : Constraints p) : clause p c1549 = true := by
  simpa only [c1549,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1549
def c1550 : List Lit := [(1635, false), (1777, false), (1816, true)]
theorem step1550 (p : Nat → Bool) (h : Constraints p) : clause p c1550 = true := by
  simpa only [c1550,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1550
def c1551 : List Lit := [(1636, false), (1776, false), (1816, true)]
theorem step1551 (p : Nat → Bool) (h : Constraints p) : clause p c1551 = true := by
  simpa only [c1551,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1551
def c1552 : List Lit := [(1816, false)]
theorem step1552 (p : Nat → Bool) (h : Constraints p) : clause p c1552 = true := by
  simpa only [c1552,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1552
def c1553 : List Lit := [(5, false), (10, false), (19, false), (29, false)]
theorem step1553 (p : Nat → Bool) (h : Constraints p) : clause p c1553 = true := by
  simpa only [c1553,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1553
def c1554 : List Lit := [(8, false), (10, false), (25, false), (29, false)]
theorem step1554 (p : Nat → Bool) (h : Constraints p) : clause p c1554 = true := by
  simpa only [c1554,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1554
def c1555 : List Lit := [(8, false), (10, false), (43, false), (47, false)]
theorem step1555 (p : Nat → Bool) (h : Constraints p) : clause p c1555 = true := by
  simpa only [c1555,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1555
def c1556 : List Lit := [(8, false), (25, false), (43, false), (60, false)]
theorem step1556 (p : Nat → Bool) (h : Constraints p) : clause p c1556 = true := by
  simpa only [c1556,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1556
def c1557 : List Lit := [(10, false), (29, false), (47, false), (67, false)]
theorem step1557 (p : Nat → Bool) (h : Constraints p) : clause p c1557 = true := by
  simpa only [c1557,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1557
def c1558 : List Lit := [(14, false), (15, false), (16, false), (17, false)]
theorem step1558 (p : Nat → Bool) (h : Constraints p) : clause p c1558 = true := by
  simpa only [c1558,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1558
def c1559 : List Lit := [(14, false), (15, false), (24, false), (25, false)]
theorem step1559 (p : Nat → Bool) (h : Constraints p) : clause p c1559 = true := by
  simpa only [c1559,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1559
def c1560 : List Lit := [(14, false), (16, false), (24, false), (26, false)]
theorem step1560 (p : Nat → Bool) (h : Constraints p) : clause p c1560 = true := by
  simpa only [c1560,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1560
def c1561 : List Lit := [(15, false), (19, false), (25, false), (29, false)]
theorem step1561 (p : Nat → Bool) (h : Constraints p) : clause p c1561 = true := by
  simpa only [c1561,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1561
def c1562 : List Lit := [(15, false), (19, false), (71, false), (75, false)]
theorem step1562 (p : Nat → Bool) (h : Constraints p) : clause p c1562 = true := by
  simpa only [c1562,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1562
def c1563 : List Lit := [(20, false), (21, false), (22, false), (23, false)]
theorem step1563 (p : Nat → Bool) (h : Constraints p) : clause p c1563 = true := by
  simpa only [c1563,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1563
def c1564 : List Lit := [(20, false), (22, false), (31, false), (32, false)]
theorem step1564 (p : Nat → Bool) (h : Constraints p) : clause p c1564 = true := by
  simpa only [c1564,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1564
def c1565 : List Lit := [(25, false), (27, false), (60, false), (62, false)]
theorem step1565 (p : Nat → Bool) (h : Constraints p) : clause p c1565 = true := by
  simpa only [c1565,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1565
def c1566 : List Lit := [(25, false), (29, false), (60, false), (67, false)]
theorem step1566 (p : Nat → Bool) (h : Constraints p) : clause p c1566 = true := by
  simpa only [c1566,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1566
def c1567 : List Lit := [(26, false), (27, false), (61, false), (62, false)]
theorem step1567 (p : Nat → Bool) (h : Constraints p) : clause p c1567 = true := by
  simpa only [c1567,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1567
def c1568 : List Lit := [(26, false), (27, false), (78, false), (79, false)]
theorem step1568 (p : Nat → Bool) (h : Constraints p) : clause p c1568 = true := by
  simpa only [c1568,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block48.clause1568
def c1569 : List Lit := [(26, false), (61, false), (78, false), (115, false)]
theorem step1569 (p : Nat → Bool) (h : Constraints p) : clause p c1569 = true := by
  simpa only [c1569,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1569
def c1570 : List Lit := [(33, false), (34, false), (35, false), (36, false)]
theorem step1570 (p : Nat → Bool) (h : Constraints p) : clause p c1570 = true := by
  simpa only [c1570,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1570
def c1571 : List Lit := [(33, false), (34, false), (42, false), (43, false)]
theorem step1571 (p : Nat → Bool) (h : Constraints p) : clause p c1571 = true := by
  simpa only [c1571,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1571
def c1572 : List Lit := [(36, false), (37, false), (38, false), (41, false)]
theorem step1572 (p : Nat → Bool) (h : Constraints p) : clause p c1572 = true := by
  simpa only [c1572,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1572
def c1573 : List Lit := [(42, false), (43, false), (46, false), (47, false)]
theorem step1573 (p : Nat → Bool) (h : Constraints p) : clause p c1573 = true := by
  simpa only [c1573,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1573
def c1574 : List Lit := [(42, false), (44, false), (46, false), (49, false)]
theorem step1574 (p : Nat → Bool) (h : Constraints p) : clause p c1574 = true := by
  simpa only [c1574,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1574
def c1575 : List Lit := [(43, false), (47, false), (60, false), (67, false)]
theorem step1575 (p : Nat → Bool) (h : Constraints p) : clause p c1575 = true := by
  simpa only [c1575,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1575
def c1576 : List Lit := [(44, false), (45, false), (49, false), (50, false)]
theorem step1576 (p : Nat → Bool) (h : Constraints p) : clause p c1576 = true := by
  simpa only [c1576,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1576
def c1577 : List Lit := [(46, false), (48, false), (49, false), (50, false)]
theorem step1577 (p : Nat → Bool) (h : Constraints p) : clause p c1577 = true := by
  simpa only [c1577,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1577
def c1578 : List Lit := [(51, false), (53, false), (60, false), (63, false)]
theorem step1578 (p : Nat → Bool) (h : Constraints p) : clause p c1578 = true := by
  simpa only [c1578,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1578
def c1579 : List Lit := [(52, false), (54, false), (58, false), (59, false)]
theorem step1579 (p : Nat → Bool) (h : Constraints p) : clause p c1579 = true := by
  simpa only [c1579,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1579
def c1580 : List Lit := [(55, false), (56, false), (58, false), (59, false)]
theorem step1580 (p : Nat → Bool) (h : Constraints p) : clause p c1580 = true := by
  simpa only [c1580,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1580
def c1581 : List Lit := [(55, false), (66, false), (107, false), (119, false)]
theorem step1581 (p : Nat → Bool) (h : Constraints p) : clause p c1581 = true := by
  simpa only [c1581,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1581
def c1582 : List Lit := [(57, false), (68, false), (109, false), (120, false)]
theorem step1582 (p : Nat → Bool) (h : Constraints p) : clause p c1582 = true := by
  simpa only [c1582,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1582
def c1583 : List Lit := [(60, false), (63, false), (67, false), (69, false)]
theorem step1583 (p : Nat → Bool) (h : Constraints p) : clause p c1583 = true := by
  simpa only [c1583,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1583
def c1584 : List Lit := [(61, false), (62, false), (64, false), (65, false)]
theorem step1584 (p : Nat → Bool) (h : Constraints p) : clause p c1584 = true := by
  simpa only [c1584,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1584
def c1585 : List Lit := [(61, false), (62, false), (115, false), (116, false)]
theorem step1585 (p : Nat → Bool) (h : Constraints p) : clause p c1585 = true := by
  simpa only [c1585,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1585
def c1586 : List Lit := [(61, false), (64, false), (115, false), (118, false)]
theorem step1586 (p : Nat → Bool) (h : Constraints p) : clause p c1586 = true := by
  simpa only [c1586,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1586
def c1587 : List Lit := [(62, false), (65, false), (68, false), (70, false)]
theorem step1587 (p : Nat → Bool) (h : Constraints p) : clause p c1587 = true := by
  simpa only [c1587,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1587
def c1588 : List Lit := [(63, false), (65, false), (69, false), (70, false)]
theorem step1588 (p : Nat → Bool) (h : Constraints p) : clause p c1588 = true := by
  simpa only [c1588,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1588
def c1589 : List Lit := [(67, false), (68, false), (69, false), (70, false)]
theorem step1589 (p : Nat → Bool) (h : Constraints p) : clause p c1589 = true := by
  simpa only [c1589,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1589
def c1590 : List Lit := [(69, false), (70, false), (122, false), (124, false)]
theorem step1590 (p : Nat → Bool) (h : Constraints p) : clause p c1590 = true := by
  simpa only [c1590,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1590
def c1591 : List Lit := [(78, false), (79, false), (82, false), (83, false)]
theorem step1591 (p : Nat → Bool) (h : Constraints p) : clause p c1591 = true := by
  simpa only [c1591,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1591
def c1592 : List Lit := [(78, false), (79, false), (115, false), (116, false)]
theorem step1592 (p : Nat → Bool) (h : Constraints p) : clause p c1592 = true := by
  simpa only [c1592,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1592
def c1593 : List Lit := [(83, false), (85, false), (120, false), (124, false)]
theorem step1593 (p : Nat → Bool) (h : Constraints p) : clause p c1593 = true := by
  simpa only [c1593,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1593
def c1594 : List Lit := [(94, false), (95, false), (98, false), (99, false)]
theorem step1594 (p : Nat → Bool) (h : Constraints p) : clause p c1594 = true := by
  simpa only [c1594,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1594
def c1595 : List Lit := [(94, false), (95, false), (115, false), (116, false)]
theorem step1595 (p : Nat → Bool) (h : Constraints p) : clause p c1595 = true := by
  simpa only [c1595,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1595
def c1596 : List Lit := [(100, false), (101, false), (122, false), (124, false)]
theorem step1596 (p : Nat → Bool) (h : Constraints p) : clause p c1596 = true := by
  simpa only [c1596,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1596
def c1597 : List Lit := [(102, false), (103, false), (104, false), (105, false)]
theorem step1597 (p : Nat → Bool) (h : Constraints p) : clause p c1597 = true := by
  simpa only [c1597,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1597
def c1598 : List Lit := [(102, false), (103, false), (113, false), (114, false)]
theorem step1598 (p : Nat → Bool) (h : Constraints p) : clause p c1598 = true := by
  simpa only [c1598,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1598
def c1599 : List Lit := [(102, false), (104, false), (113, false), (115, false)]
theorem step1599 (p : Nat → Bool) (h : Constraints p) : clause p c1599 = true := by
  simpa only [c1599,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1599
def c1600 : List Lit := [(102, false), (107, false), (113, false), (119, false)]
theorem step1600 (p : Nat → Bool) (h : Constraints p) : clause p c1600 = true := by
  simpa only [c1600,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block49.clause1600
def c1601 : List Lit := [(104, false), (105, false), (115, false), (116, false)]
theorem step1601 (p : Nat → Bool) (h : Constraints p) : clause p c1601 = true := by
  simpa only [c1601,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1601
def c1602 : List Lit := [(107, false), (108, false), (110, false), (111, false)]
theorem step1602 (p : Nat → Bool) (h : Constraints p) : clause p c1602 = true := by
  simpa only [c1602,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1602
def c1603 : List Lit := [(107, false), (110, false), (119, false), (121, false)]
theorem step1603 (p : Nat → Bool) (h : Constraints p) : clause p c1603 = true := by
  simpa only [c1603,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1603
def c1604 : List Lit := [(108, false), (109, false), (111, false), (112, false)]
theorem step1604 (p : Nat → Bool) (h : Constraints p) : clause p c1604 = true := by
  simpa only [c1604,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1604
def c1605 : List Lit := [(110, false), (111, false), (121, false), (122, false)]
theorem step1605 (p : Nat → Bool) (h : Constraints p) : clause p c1605 = true := by
  simpa only [c1605,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1605
def c1606 : List Lit := [(111, false), (112, false), (122, false), (124, false)]
theorem step1606 (p : Nat → Bool) (h : Constraints p) : clause p c1606 = true := by
  simpa only [c1606,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1606
def c1607 : List Lit := [(113, false), (114, false), (115, false), (116, false)]
theorem step1607 (p : Nat → Bool) (h : Constraints p) : clause p c1607 = true := by
  simpa only [c1607,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1607
def c1608 : List Lit := [(113, false), (115, false), (117, false), (118, false)]
theorem step1608 (p : Nat → Bool) (h : Constraints p) : clause p c1608 = true := by
  simpa only [c1608,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1608
def c1609 : List Lit := [(113, false), (117, false), (119, false), (121, false)]
theorem step1609 (p : Nat → Bool) (h : Constraints p) : clause p c1609 = true := by
  simpa only [c1609,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1609
def c1610 : List Lit := [(117, false), (118, false), (121, false), (123, false)]
theorem step1610 (p : Nat → Bool) (h : Constraints p) : clause p c1610 = true := by
  simpa only [c1610,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1610
def c1611 : List Lit := [(121, false), (122, false), (123, false), (124, false)]
theorem step1611 (p : Nat → Bool) (h : Constraints p) : clause p c1611 = true := by
  simpa only [c1611,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block50.clause1611
end B112E020
