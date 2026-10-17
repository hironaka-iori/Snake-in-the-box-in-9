import TreeRup
namespace B112E091
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
structure Block0 (p : Nat → Bool) : Prop where
  clause1 : p 1 = false ∨ p 2 = false ∨ p 4 = false ∨ p 18 = false
  clause2 : p 1 = false ∨ p 107 = true ∨ p 4 = true ∨ p 18 = true
  clause3 : p 108 = false ∨ p 2 = true
  clause4 : p 2 = false ∨ p 1 = true ∨ p 3 = true
  clause5 : p 2 = false ∨ p 108 = true ∨ p 3 = true
  clause6 : p 2 = false ∨ p 108 = true ∨ p 1 = true
  clause7 : p 3 = false ∨ p 2 = false ∨ p 8 = false ∨ p 11 = false
  clause8 : p 3 = false ∨ p 109 = true ∨ p 2 = true ∨ p 8 = true
  clause9 : p 4 = false ∨ p 1 = false ∨ p 5 = false ∨ p 6 = false
  clause10 : p 4 = false ∨ p 1 = false ∨ p 5 = false ∨ p 13 = false
  clause11 : p 4 = false ∨ p 1 = false ∨ p 5 = false ∨ p 22 = false
  clause12 : p 4 = false ∨ p 1 = false ∨ p 5 = false ∨ p 67 = false
  clause13 : p 4 = false ∨ p 1 = false ∨ p 6 = false ∨ p 13 = false
  clause14 : p 4 = false ∨ p 1 = false ∨ p 6 = false ∨ p 22 = false
  clause15 : p 4 = false ∨ p 1 = false ∨ p 6 = false ∨ p 67 = false
  clause16 : p 4 = false ∨ p 1 = false ∨ p 13 = false ∨ p 22 = false
  clause17 : p 4 = false ∨ p 1 = false ∨ p 13 = false ∨ p 67 = false
  clause18 : p 4 = false ∨ p 1 = false ∨ p 22 = false ∨ p 67 = false
  clause19 : p 4 = false ∨ p 5 = false ∨ p 6 = false ∨ p 67 = false
  clause20 : p 4 = false ∨ p 5 = false ∨ p 13 = false ∨ p 67 = false
  clause21 : p 4 = false ∨ p 5 = false ∨ p 22 = false ∨ p 67 = false
  clause22 : p 4 = false ∨ p 6 = false ∨ p 22 = false ∨ p 67 = false
  clause23 : p 5 = false ∨ p 4 = false ∨ p 7 = false ∨ p 14 = false
  clause24 : p 5 = false ∨ p 4 = false ∨ p 7 = false ∨ p 23 = false
  clause25 : p 5 = false ∨ p 4 = false ∨ p 14 = false ∨ p 23 = false
  clause26 : p 5 = false ∨ p 7 = false ∨ p 14 = false ∨ p 23 = false
  clause27 : p 6 = false ∨ p 4 = false ∨ p 7 = false ∨ p 8 = false
  clause28 : p 6 = false ∨ p 4 = false ∨ p 7 = false ∨ p 15 = false
  clause29 : p 6 = false ∨ p 4 = false ∨ p 8 = false ∨ p 15 = false
  clause30 : p 6 = false ∨ p 7 = false ∨ p 8 = false ∨ p 15 = false
  clause31 : p 113 = false ∨ p 7 = true
  clause32 : p 7 = false ∨ p 5 = true ∨ p 6 = true ∨ p 16 = true
structure Block1 (p : Nat → Bool) : Prop where
  clause33 : p 7 = false ∨ p 113 = true ∨ p 6 = true ∨ p 16 = true
  clause34 : p 7 = false ∨ p 113 = true ∨ p 5 = true ∨ p 16 = true
  clause35 : p 7 = false ∨ p 113 = true ∨ p 5 = true ∨ p 6 = true
  clause36 : p 8 = false ∨ p 3 = true ∨ p 6 = true ∨ p 24 = true
  clause37 : p 8 = false ∨ p 114 = true ∨ p 6 = true ∨ p 24 = true
  clause38 : p 8 = false ∨ p 114 = true ∨ p 3 = true ∨ p 6 = true
  clause39 : p 9 = false ∨ p 12 = false ∨ p 16 = false ∨ p 28 = false
  clause40 : p 10 = false ∨ p 116 = true ∨ p 17 = true
  clause41 : p 10 = false ∨ p 116 = true ∨ p 12 = true
  clause42 : p 11 = false ∨ p 3 = true ∨ p 12 = true
  clause43 : p 11 = false ∨ p 117 = true ∨ p 12 = true
  clause44 : p 11 = false ∨ p 117 = true ∨ p 3 = true
  clause45 : p 12 = false ∨ p 9 = false ∨ p 10 = false ∨ p 11 = false
  clause46 : p 13 = false ∨ p 4 = false ∨ p 14 = false ∨ p 15 = false
  clause47 : p 13 = false ∨ p 119 = true ∨ p 4 = true ∨ p 15 = true
  clause48 : p 13 = false ∨ p 119 = true ∨ p 4 = true ∨ p 14 = true
  clause49 : p 14 = false ∨ p 5 = true ∨ p 13 = true ∨ p 16 = true ∨ p 17 = true
  clause50 : p 14 = false ∨ p 120 = true ∨ p 13 = true ∨ p 16 = true ∨ p 17 = true
  clause51 : p 14 = false ∨ p 120 = true ∨ p 5 = true ∨ p 13 = true ∨ p 16 = true
  clause52 : p 15 = false ∨ p 6 = true ∨ p 13 = true ∨ p 16 = true
  clause53 : p 15 = false ∨ p 121 = true ∨ p 13 = true ∨ p 16 = true
  clause54 : p 15 = false ∨ p 121 = true ∨ p 6 = true ∨ p 16 = true
  clause55 : p 15 = false ∨ p 121 = true ∨ p 6 = true ∨ p 13 = true
  clause56 : p 16 = false ∨ p 7 = false ∨ p 9 = false ∨ p 14 = false
  clause57 : p 16 = false ∨ p 7 = false ∨ p 9 = false ∨ p 15 = false
  clause58 : p 16 = false ∨ p 7 = false ∨ p 14 = false ∨ p 15 = false
  clause59 : p 16 = false ∨ p 9 = false ∨ p 14 = false ∨ p 15 = false
  clause60 : p 17 = false ∨ p 123 = true ∨ p 14 = true
  clause61 : p 17 = false ∨ p 123 = true ∨ p 10 = true
  clause62 : p 18 = false ∨ p 1 = false ∨ p 22 = false ∨ p 26 = false
  clause63 : p 19 = false ∨ p 18 = false ∨ p 20 = false ∨ p 23 = false
  clause64 : p 19 = false ∨ p 125 = true ∨ p 18 = true ∨ p 23 = true
structure Block2 (p : Nat → Bool) : Prop where
  clause65 : p 19 = false ∨ p 125 = true ∨ p 18 = true ∨ p 20 = true
  clause66 : p 20 = false ∨ p 126 = true ∨ p 21 = true
  clause67 : p 20 = false ∨ p 126 = true ∨ p 19 = true
  clause68 : p 21 = false ∨ p 127 = true ∨ p 25 = true
  clause69 : p 22 = false ∨ p 4 = false ∨ p 18 = false ∨ p 52 = false
  clause70 : p 22 = false ∨ p 4 = false ∨ p 23 = false ∨ p 52 = false
  clause71 : p 22 = false ∨ p 18 = false ∨ p 23 = false ∨ p 52 = false
  clause72 : p 22 = false ∨ p 128 = true ∨ p 4 = true ∨ p 18 = true ∨ p 23 = true
  clause73 : p 23 = false ∨ p 5 = true ∨ p 19 = true ∨ p 22 = true
  clause74 : p 23 = false ∨ p 129 = true ∨ p 19 = true ∨ p 22 = true
  clause75 : p 23 = false ∨ p 129 = true ∨ p 5 = true ∨ p 22 = true
  clause76 : p 23 = false ∨ p 129 = true ∨ p 5 = true ∨ p 19 = true
  clause77 : p 24 = false ∨ p 8 = false ∨ p 25 = false ∨ p 32 = false
  clause78 : p 26 = false ∨ p 18 = false ∨ p 27 = false ∨ p 29 = false
  clause79 : p 26 = false ∨ p 132 = true ∨ p 18 = true ∨ p 29 = true
  clause80 : p 26 = false ∨ p 132 = true ∨ p 18 = true ∨ p 27 = true
  clause81 : p 133 = false ∨ p 27 = true
  clause82 : p 27 = false ∨ p 133 = true ∨ p 28 = true
  clause83 : p 27 = false ∨ p 133 = true ∨ p 26 = true
  clause84 : p 28 = false ∨ p 9 = false ∨ p 27 = false ∨ p 30 = false
  clause85 : p 28 = false ∨ p 134 = true ∨ p 9 = true ∨ p 30 = true
  clause86 : p 135 = false ∨ p 29 = true
  clause87 : p 29 = false ∨ p 135 = true ∨ p 31 = true
  clause88 : p 29 = false ∨ p 135 = true ∨ p 26 = true
  clause89 : p 136 = false ∨ p 30 = true
  clause90 : p 30 = false ∨ p 28 = false ∨ p 33 = false ∨ p 56 = false
  clause91 : p 31 = false ∨ p 137 = true ∨ p 32 = true
  clause92 : p 31 = false ∨ p 137 = true ∨ p 29 = true
  clause93 : p 32 = false ∨ p 138 = true ∨ p 31 = true ∨ p 33 = true
  clause94 : p 32 = false ∨ p 138 = true ∨ p 24 = true ∨ p 33 = true
  clause95 : p 32 = false ∨ p 138 = true ∨ p 24 = true ∨ p 31 = true
  clause96 : p 33 = false ∨ p 139 = true ∨ p 25 = true ∨ p 30 = true
structure Block3 (p : Nat → Bool) : Prop where
  clause97 : p 34 = false ∨ p 35 = false ∨ p 37 = false ∨ p 57 = false
  clause98 : p 34 = false ∨ p 35 = false ∨ p 37 = false ∨ p 76 = false
  clause99 : p 34 = false ∨ p 35 = false ∨ p 57 = false ∨ p 76 = false
  clause100 : p 34 = false ∨ p 37 = false ∨ p 57 = false ∨ p 76 = false
  clause101 : p 34 = false ∨ p 140 = true ∨ p 37 = true ∨ p 57 = true ∨ p 76 = true
  clause102 : p 34 = false ∨ p 140 = true ∨ p 35 = true ∨ p 37 = true ∨ p 76 = true
  clause103 : p 35 = false ∨ p 34 = true ∨ p 36 = true ∨ p 43 = true
  clause104 : p 35 = false ∨ p 141 = true ∨ p 36 = true ∨ p 43 = true
  clause105 : p 35 = false ∨ p 141 = true ∨ p 34 = true ∨ p 43 = true
  clause106 : p 36 = false ∨ p 35 = false ∨ p 41 = false ∨ p 45 = false
  clause107 : p 36 = false ∨ p 142 = true ∨ p 41 = true ∨ p 45 = true
  clause108 : p 36 = false ∨ p 142 = true ∨ p 35 = true ∨ p 45 = true
  clause109 : p 36 = false ∨ p 142 = true ∨ p 35 = true ∨ p 41 = true
  clause110 : p 37 = false ∨ p 34 = false ∨ p 38 = false ∨ p 39 = false
  clause111 : p 37 = false ∨ p 34 = false ∨ p 38 = false ∨ p 47 = false
  clause112 : p 37 = false ∨ p 38 = false ∨ p 39 = false ∨ p 58 = false
  clause113 : p 37 = false ∨ p 38 = false ∨ p 47 = false ∨ p 58 = false
  clause114 : p 38 = false ∨ p 37 = false ∨ p 40 = false ∨ p 48 = false
  clause115 : p 38 = false ∨ p 37 = false ∨ p 40 = false ∨ p 81 = false
  clause116 : p 38 = false ∨ p 37 = false ∨ p 48 = false ∨ p 81 = false
  clause117 : p 38 = false ∨ p 40 = false ∨ p 48 = false ∨ p 81 = false
  clause118 : p 39 = false ∨ p 37 = false ∨ p 40 = false ∨ p 41 = false
  clause119 : p 39 = false ∨ p 37 = false ∨ p 41 = false ∨ p 49 = false
  clause120 : p 39 = false ∨ p 40 = false ∨ p 41 = false ∨ p 49 = false
  clause121 : p 39 = false ∨ p 145 = true ∨ p 37 = true ∨ p 40 = true ∨ p 41 = true
  clause122 : p 146 = false ∨ p 40 = true
  clause123 : p 40 = false ∨ p 38 = true ∨ p 39 = true ∨ p 50 = true
  clause124 : p 146 = false ∨ p 38 = false ∨ p 39 = false
  clause125 : p 40 = false ∨ p 146 = true ∨ p 39 = true ∨ p 50 = true
  clause126 : p 40 = false ∨ p 146 = true ∨ p 38 = true ∨ p 50 = true
  clause127 : p 40 = false ∨ p 146 = true ∨ p 38 = true ∨ p 39 = true
  clause128 : p 41 = false ∨ p 36 = false ∨ p 39 = false ∨ p 59 = false
structure Block4 (p : Nat → Bool) : Prop where
  clause129 : p 41 = false ∨ p 147 = true ∨ p 39 = true ∨ p 59 = true ∨ p 82 = true
  clause130 : p 41 = false ∨ p 147 = true ∨ p 36 = true ∨ p 59 = true ∨ p 82 = true
  clause131 : p 42 = false ∨ p 46 = false ∨ p 50 = false ∨ p 86 = false
  clause132 : p 42 = false ∨ p 148 = true ∨ p 50 = true ∨ p 86 = true
  clause133 : p 42 = false ∨ p 148 = true ∨ p 46 = true ∨ p 50 = true
  clause134 : p 43 = false ∨ p 35 = false ∨ p 44 = false ∨ p 45 = false
  clause135 : p 43 = false ∨ p 35 = false ∨ p 44 = false ∨ p 62 = false
  clause136 : p 43 = false ∨ p 35 = false ∨ p 44 = false ∨ p 87 = false
  clause137 : p 43 = false ∨ p 35 = false ∨ p 45 = false ∨ p 62 = false
  clause138 : p 43 = false ∨ p 35 = false ∨ p 45 = false ∨ p 87 = false
  clause139 : p 43 = false ∨ p 35 = false ∨ p 62 = false ∨ p 87 = false
  clause140 : p 43 = false ∨ p 44 = false ∨ p 45 = false ∨ p 62 = false
  clause141 : p 43 = false ∨ p 44 = false ∨ p 45 = false ∨ p 87 = false
  clause142 : p 43 = false ∨ p 45 = false ∨ p 62 = false ∨ p 87 = false
  clause143 : p 44 = false ∨ p 43 = false ∨ p 46 = false ∨ p 51 = false
  clause144 : p 44 = false ∨ p 150 = true ∨ p 46 = true ∨ p 51 = true
  clause145 : p 44 = false ∨ p 150 = true ∨ p 43 = true ∨ p 51 = true
  clause146 : p 44 = false ∨ p 150 = true ∨ p 43 = true ∨ p 46 = true
  clause147 : p 45 = false ∨ p 151 = true ∨ p 43 = true ∨ p 46 = true
  clause148 : p 45 = false ∨ p 151 = true ∨ p 36 = true ∨ p 46 = true
  clause149 : p 45 = false ∨ p 151 = true ∨ p 36 = true ∨ p 43 = true
  clause150 : p 46 = false ∨ p 42 = false ∨ p 44 = false ∨ p 45 = false
  clause151 : p 46 = false ∨ p 152 = true ∨ p 44 = true ∨ p 45 = true
  clause152 : p 47 = false ∨ p 37 = false ∨ p 48 = false ∨ p 49 = false
  clause153 : p 47 = false ∨ p 153 = true ∨ p 37 = true ∨ p 49 = true
  clause154 : p 47 = false ∨ p 153 = true ∨ p 37 = true ∨ p 48 = true
  clause155 : p 48 = false ∨ p 38 = true ∨ p 47 = true ∨ p 50 = true ∨ p 51 = true
  clause156 : p 48 = false ∨ p 38 = false ∨ p 47 = false ∨ p 51 = false
  clause157 : p 48 = false ∨ p 38 = false ∨ p 50 = false ∨ p 51 = false
  clause158 : p 48 = false ∨ p 154 = true ∨ p 47 = true ∨ p 50 = true ∨ p 51 = true
  clause159 : p 48 = false ∨ p 154 = true ∨ p 38 = true ∨ p 50 = true ∨ p 51 = true
  clause160 : p 48 = false ∨ p 154 = true ∨ p 38 = true ∨ p 47 = true ∨ p 50 = true
structure Block5 (p : Nat → Bool) : Prop where
  clause161 : p 49 = false ∨ p 155 = true ∨ p 47 = true ∨ p 50 = true
  clause162 : p 49 = false ∨ p 155 = true ∨ p 39 = true ∨ p 50 = true
  clause163 : p 49 = false ∨ p 155 = true ∨ p 39 = true ∨ p 47 = true
  clause164 : p 50 = false ∨ p 40 = false ∨ p 42 = false ∨ p 48 = false
  clause165 : p 50 = false ∨ p 40 = false ∨ p 42 = false ∨ p 49 = false
  clause166 : p 50 = false ∨ p 40 = false ∨ p 42 = false ∨ p 63 = false
  clause167 : p 50 = false ∨ p 40 = false ∨ p 48 = false ∨ p 49 = false
  clause168 : p 50 = false ∨ p 40 = false ∨ p 48 = false ∨ p 63 = false
  clause169 : p 50 = false ∨ p 40 = false ∨ p 49 = false ∨ p 63 = false
  clause170 : p 50 = false ∨ p 42 = false ∨ p 48 = false ∨ p 49 = false
  clause171 : p 50 = false ∨ p 42 = false ∨ p 48 = false ∨ p 63 = false
  clause172 : p 50 = false ∨ p 42 = false ∨ p 49 = false ∨ p 63 = false
  clause173 : p 50 = false ∨ p 48 = false ∨ p 49 = false ∨ p 63 = false
  clause174 : p 51 = false ∨ p 157 = true ∨ p 48 = true
  clause175 : p 51 = false ∨ p 157 = true ∨ p 44 = true
  clause176 : p 52 = false ∨ p 158 = true ∨ p 22 = true ∨ p 58 = true ∨ p 95 = true
  clause177 : p 52 = false ∨ p 158 = true ∨ p 22 = true ∨ p 54 = true ∨ p 58 = true
  clause178 : p 159 = false ∨ p 53 = true
  clause179 : p 53 = false ∨ p 56 = true
  clause180 : p 53 = false ∨ p 159 = true
  clause181 : p 54 = false ∨ p 160 = true ∨ p 55 = true
  clause182 : p 54 = false ∨ p 160 = true ∨ p 52 = true
  clause183 : p 161 = false ∨ p 55 = true
  clause184 : p 55 = false ∨ p 54 = true ∨ p 56 = true
  clause185 : p 55 = false ∨ p 161 = true ∨ p 56 = true
  clause186 : p 55 = false ∨ p 161 = true ∨ p 54 = true
  clause187 : p 56 = false ∨ p 30 = false ∨ p 53 = false ∨ p 55 = false
  clause188 : p 56 = false ∨ p 30 = false ∨ p 53 = false ∨ p 63 = false
  clause189 : p 56 = false ∨ p 30 = false ∨ p 53 = false ∨ p 103 = false
  clause190 : p 56 = false ∨ p 30 = false ∨ p 55 = false ∨ p 63 = false
  clause191 : p 56 = false ∨ p 30 = false ∨ p 55 = false ∨ p 103 = false
  clause192 : p 56 = false ∨ p 30 = false ∨ p 63 = false ∨ p 103 = false
structure Block6 (p : Nat → Bool) : Prop where
  clause193 : p 56 = false ∨ p 53 = false ∨ p 55 = false ∨ p 63 = false
  clause194 : p 56 = false ∨ p 53 = false ∨ p 55 = false ∨ p 103 = false
  clause195 : p 56 = false ∨ p 53 = false ∨ p 63 = false ∨ p 103 = false
  clause196 : p 56 = false ∨ p 55 = false ∨ p 63 = false ∨ p 103 = false
  clause197 : p 56 = false ∨ p 162 = true ∨ p 53 = true ∨ p 55 = true ∨ p 63 = true ∨ p 103 = true
  clause198 : p 56 = false ∨ p 162 = true ∨ p 30 = true ∨ p 53 = true ∨ p 63 = true ∨ p 103 = true
  clause199 : p 56 = false ∨ p 162 = true ∨ p 30 = true ∨ p 53 = true ∨ p 55 = true ∨ p 103 = true
  clause200 : p 56 = false ∨ p 162 = true ∨ p 30 = true ∨ p 53 = true ∨ p 55 = true ∨ p 63 = true
  clause201 : p 57 = false ∨ p 34 = false ∨ p 58 = false ∨ p 60 = false
  clause202 : p 57 = false ∨ p 163 = true ∨ p 58 = true ∨ p 60 = true
  clause203 : p 57 = false ∨ p 163 = true ∨ p 34 = true ∨ p 60 = true
  clause204 : p 57 = false ∨ p 163 = true ∨ p 34 = true ∨ p 58 = true
  clause205 : p 58 = false ∨ p 37 = false ∨ p 52 = false ∨ p 57 = false
  clause206 : p 58 = false ∨ p 164 = true ∨ p 52 = true ∨ p 57 = true
  clause207 : p 58 = false ∨ p 164 = true ∨ p 37 = true ∨ p 57 = true
  clause208 : p 58 = false ∨ p 164 = true ∨ p 37 = true ∨ p 52 = true
  clause209 : p 59 = false ∨ p 165 = true ∨ p 41 = true
  clause210 : p 60 = false ∨ p 57 = false ∨ p 61 = false ∨ p 62 = false
  clause211 : p 60 = false ∨ p 166 = true ∨ p 61 = true ∨ p 62 = true
  clause212 : p 60 = false ∨ p 166 = true ∨ p 57 = true ∨ p 61 = true
  clause213 : p 61 = false ∨ p 60 = true
  clause214 : p 61 = false ∨ p 167 = true
  clause215 : p 62 = false ∨ p 43 = false ∨ p 60 = false ∨ p 64 = false
  clause216 : p 62 = false ∨ p 168 = true ∨ p 43 = true ∨ p 64 = true
  clause217 : p 62 = false ∨ p 168 = true ∨ p 43 = true ∨ p 60 = true
  clause218 : p 63 = false ∨ p 169 = true ∨ p 50 = true ∨ p 66 = true
  clause219 : p 63 = false ∨ p 169 = true ∨ p 50 = true ∨ p 56 = true
  clause220 : p 64 = false ∨ p 170 = true ∨ p 65 = true
  clause221 : p 64 = false ∨ p 170 = true ∨ p 62 = true
  clause222 : p 65 = false ∨ p 59 = false ∨ p 64 = false ∨ p 66 = false
  clause223 : p 65 = false ∨ p 171 = true ∨ p 64 = true ∨ p 66 = true
  clause224 : p 65 = false ∨ p 171 = true ∨ p 59 = true ∨ p 66 = true
structure Block7 (p : Nat → Bool) : Prop where
  clause225 : p 65 = false ∨ p 171 = true ∨ p 59 = true ∨ p 64 = true
  clause226 : p 66 = false ∨ p 172 = true ∨ p 65 = true
  clause227 : p 66 = false ∨ p 172 = true ∨ p 63 = true
  clause228 : p 67 = false ∨ p 173 = true ∨ p 4 = true
  clause229 : p 174 = false ∨ p 68 = true
  clause230 : p 174 = false ∨ p 72 = false ∨ p 80 = false
  clause231 : p 68 = false ∨ p 174 = true ∨ p 67 = true ∨ p 80 = true
  clause232 : p 69 = false ∨ p 175 = true ∨ p 73 = true
  clause233 : p 70 = false ∨ p 176 = true ∨ p 69 = true
  clause234 : p 71 = false ∨ p 177 = true ∨ p 70 = true
  clause235 : p 72 = false ∨ p 178 = true ∨ p 68 = true
  clause236 : p 73 = false ∨ p 179 = true ∨ p 72 = true
  clause237 : p 74 = false ∨ p 75 = true
  clause238 : p 74 = true
  clause239 : p 75 = false ∨ p 181 = true ∨ p 71 = true
  clause240 : p 76 = false ∨ p 34 = false ∨ p 80 = false ∨ p 84 = false
  clause241 : p 76 = false ∨ p 77 = false ∨ p 80 = false ∨ p 84 = false
  clause242 : p 76 = false ∨ p 182 = true ∨ p 77 = true ∨ p 80 = true ∨ p 84 = true
  clause243 : p 76 = false ∨ p 182 = true ∨ p 34 = true ∨ p 80 = true ∨ p 84 = true
  clause244 : p 77 = false ∨ p 76 = false ∨ p 78 = false ∨ p 81 = false
  clause245 : p 77 = false ∨ p 183 = true ∨ p 76 = true ∨ p 81 = true
  clause246 : p 78 = false ∨ p 184 = true ∨ p 77 = true
  clause247 : p 79 = false ∨ p 185 = true ∨ p 78 = true
  clause248 : p 80 = false ∨ p 37 = false ∨ p 68 = false ∨ p 76 = false
  clause249 : p 80 = false ∨ p 37 = false ∨ p 68 = false ∨ p 81 = false
  clause250 : p 80 = false ∨ p 68 = false ∨ p 76 = false ∨ p 81 = false
  clause251 : p 81 = false ∨ p 38 = false ∨ p 77 = false ∨ p 80 = false
  clause252 : p 81 = false ∨ p 187 = true ∨ p 77 = true ∨ p 80 = true
  clause253 : p 81 = false ∨ p 187 = true ∨ p 38 = true ∨ p 80 = true
  clause254 : p 82 = false ∨ p 41 = false ∨ p 83 = false ∨ p 89 = false
  clause255 : p 83 = false ∨ p 189 = true ∨ p 79 = true ∨ p 90 = true
  clause256 : p 83 = false ∨ p 189 = true ∨ p 79 = true ∨ p 82 = true
structure Block8 (p : Nat → Bool) : Prop where
  clause257 : p 84 = false ∨ p 76 = false ∨ p 85 = false ∨ p 87 = false
  clause258 : p 84 = false ∨ p 190 = true ∨ p 76 = true ∨ p 87 = true
  clause259 : p 84 = false ∨ p 190 = true ∨ p 76 = true ∨ p 85 = true
  clause260 : p 85 = false ∨ p 84 = true ∨ p 86 = true
  clause261 : p 191 = false ∨ p 84 = false ∨ p 86 = false
  clause262 : p 85 = false ∨ p 191 = true ∨ p 86 = true
  clause263 : p 85 = false ∨ p 191 = true ∨ p 84 = true
  clause264 : p 86 = false ∨ p 192 = true ∨ p 85 = true
  clause265 : p 86 = false ∨ p 192 = true ∨ p 42 = true
  clause266 : p 87 = false ∨ p 43 = false ∨ p 84 = false ∨ p 88 = false
  clause267 : p 87 = false ∨ p 193 = true ∨ p 43 = true ∨ p 84 = true
  clause268 : p 88 = false ∨ p 194 = true ∨ p 87 = true
  clause269 : p 89 = false ∨ p 195 = true ∨ p 88 = true ∨ p 90 = true
  clause270 : p 89 = false ∨ p 195 = true ∨ p 82 = true ∨ p 88 = true
  clause271 : p 90 = false ∨ p 196 = true ∨ p 83 = true
  clause272 : p 91 = false ∨ p 92 = false ∨ p 95 = false ∨ p 99 = false
  clause273 : p 92 = false ∨ p 91 = false ∨ p 93 = false ∨ p 96 = false
  clause274 : p 92 = false ∨ p 198 = true ∨ p 91 = true ∨ p 96 = true
  clause275 : p 92 = false ∨ p 198 = true ∨ p 91 = true ∨ p 93 = true
  clause276 : p 93 = false ∨ p 199 = true ∨ p 94 = true
  clause277 : p 93 = false ∨ p 199 = true ∨ p 92 = true
  clause278 : p 94 = false ∨ p 200 = true ∨ p 98 = true
  clause279 : p 94 = false ∨ p 200 = true ∨ p 93 = true
  clause280 : p 95 = false ∨ p 52 = false ∨ p 91 = false ∨ p 96 = false
  clause281 : p 95 = false ∨ p 201 = true ∨ p 52 = true ∨ p 91 = true
  clause282 : p 96 = false ∨ p 202 = true ∨ p 95 = true
  clause283 : p 96 = false ∨ p 202 = true ∨ p 92 = true
  clause284 : p 97 = false ∨ p 203 = true ∨ p 98 = true
  clause285 : p 98 = false ∨ p 204 = true ∨ p 94 = true ∨ p 106 = true
  clause286 : p 99 = false ∨ p 91 = false ∨ p 100 = false ∨ p 102 = false
  clause287 : p 99 = false ∨ p 205 = true ∨ p 91 = true ∨ p 102 = true
  clause288 : p 99 = false ∨ p 205 = true ∨ p 91 = true ∨ p 100 = true
structure Block9 (p : Nat → Bool) : Prop where
  clause289 : p 100 = false ∨ p 206 = true ∨ p 101 = true
  clause290 : p 100 = false ∨ p 206 = true ∨ p 99 = true
  clause291 : p 101 = false ∨ p 207 = true ∨ p 103 = true
  clause292 : p 101 = false ∨ p 207 = true ∨ p 100 = true
  clause293 : p 102 = false ∨ p 208 = true ∨ p 104 = true
  clause294 : p 102 = false ∨ p 208 = true ∨ p 99 = true
  clause295 : p 103 = false ∨ p 209 = true ∨ p 56 = true ∨ p 106 = true
  clause296 : p 103 = false ∨ p 209 = true ∨ p 56 = true ∨ p 101 = true
  clause297 : p 104 = false ∨ p 210 = true ∨ p 105 = true
  clause298 : p 104 = false ∨ p 210 = true ∨ p 102 = true
  clause299 : p 105 = false ∨ p 211 = true ∨ p 97 = true ∨ p 104 = true
  clause300 : p 106 = false ∨ p 98 = false ∨ p 103 = false ∨ p 105 = false
  clause301 : p 107 = false
  clause302 : p 109 = false
  clause303 : p 111 = false
  clause304 : p 112 = false
  clause305 : p 118 = false
  clause306 : p 119 = false
  clause307 : p 122 = false
  clause308 : p 123 = false
  clause309 : p 125 = false
  clause310 : p 127 = false
  clause311 : p 128 = false
  clause312 : p 130 = false
  clause313 : p 132 = false
  clause314 : p 134 = false
  clause315 : p 137 = false
  clause316 : p 139 = false
  clause317 : p 140 = false
  clause318 : p 142 = false
  clause319 : p 144 = false
  clause320 : p 145 = false
structure Block10 (p : Nat → Bool) : Prop where
  clause321 : p 149 = false
  clause322 : p 152 = false
  clause323 : p 153 = false
  clause324 : p 156 = false
  clause325 : p 157 = false
  clause326 : p 160 = false
  clause327 : p 162 = false
  clause328 : p 164 = false
  clause329 : p 165 = false
  clause330 : p 166 = false
  clause331 : p 170 = false
  clause332 : p 172 = false
  clause333 : p 173 = false
  clause334 : p 175 = false
  clause335 : p 177 = false
  clause336 : p 178 = false
  clause337 : p 183 = false
  clause338 : p 185 = false
  clause339 : p 186 = false
  clause340 : p 188 = false
  clause341 : p 190 = false
  clause342 : p 192 = false
  clause343 : p 194 = false
  clause344 : p 196 = false
  clause345 : p 198 = false
  clause346 : p 200 = false
  clause347 : p 201 = false
  clause348 : p 203 = false
  clause349 : p 205 = false
  clause350 : p 207 = false
  clause351 : p 210 = false
  clause352 : p 212 = false
structure Block11 (p : Nat → Bool) : Prop where
  clause353 : p 108 = false ∨ p 213 = true
  clause354 : p 213 = false ∨ p 215 = true
  clause355 : p 110 = false ∨ p 219 = true
  clause356 : p 219 = false ∨ p 221 = true
  clause357 : p 215 = false ∨ p 221 = true
  clause358 : p 115 = false ∨ p 223 = true
  clause359 : p 114 = false ∨ p 223 = true
  clause360 : p 223 = false ∨ p 225 = true
  clause361 : p 113 = false ∨ p 225 = true
  clause362 : p 117 = false ∨ p 227 = true
  clause363 : p 116 = false ∨ p 227 = true
  clause364 : p 116 = false ∨ p 117 = false ∨ p 228 = true
  clause365 : p 227 = false ∨ p 231 = true
  clause366 : p 228 = false ∨ p 232 = true
  clause367 : p 231 = false ∨ p 233 = true
  clause368 : p 232 = false ∨ p 234 = true
  clause369 : p 225 = false ∨ p 233 = true
  clause370 : p 225 = false ∨ p 231 = false ∨ p 234 = true
  clause371 : p 233 = false ∨ p 235 = true
  clause372 : p 234 = false ∨ p 236 = true
  clause373 : p 221 = false ∨ p 235 = true
  clause374 : p 221 = false ∨ p 233 = false ∨ p 236 = true
  clause375 : p 121 = false ∨ p 237 = true
  clause376 : p 237 = false ∨ p 239 = true
  clause377 : p 120 = false ∨ p 239 = true
  clause378 : p 120 = false ∨ p 237 = false ∨ p 240 = true
  clause379 : p 124 = false ∨ p 241 = true
  clause380 : p 241 = false ∨ p 243 = true
  clause381 : p 243 = false ∨ p 245 = true
  clause382 : p 239 = false ∨ p 245 = true
  clause383 : p 240 = false ∨ p 246 = true
  clause384 : p 126 = false ∨ p 249 = true
structure Block12 (p : Nat → Bool) : Prop where
  clause385 : p 129 = false ∨ p 251 = true
  clause386 : p 131 = false ∨ p 253 = true
  clause387 : p 253 = false ∨ p 255 = true
  clause388 : p 251 = false ∨ p 255 = true
  clause389 : p 255 = false ∨ p 257 = true
  clause390 : p 249 = false ∨ p 257 = true
  clause391 : p 249 = false ∨ p 255 = false ∨ p 258 = true
  clause392 : p 257 = false ∨ p 259 = true
  clause393 : p 258 = false ∨ p 260 = true
  clause394 : p 245 = false ∨ p 259 = true
  clause395 : p 245 = false ∨ p 257 = false ∨ p 260 = true
  clause396 : p 246 = false ∨ p 260 = true
  clause397 : p 259 = false ∨ p 261 = true
  clause398 : p 260 = false ∨ p 262 = true
  clause399 : p 235 = false ∨ p 261 = true
  clause400 : p 235 = false ∨ p 259 = false ∨ p 262 = true
  clause401 : p 236 = false ∨ p 262 = true
  clause402 : p 135 = false ∨ p 263 = true
  clause403 : p 263 = false ∨ p 265 = true
  clause404 : p 133 = false ∨ p 265 = true
  clause405 : p 133 = false ∨ p 263 = false ∨ p 266 = true
  clause406 : p 138 = false ∨ p 267 = true
  clause407 : p 267 = false ∨ p 269 = true
  clause408 : p 269 = false ∨ p 271 = true
  clause409 : p 265 = false ∨ p 271 = true
  clause410 : p 265 = false ∨ p 269 = false ∨ p 272 = true
  clause411 : p 266 = false ∨ p 272 = true
  clause412 : p 141 = false ∨ p 273 = true
  clause413 : p 273 = false ∨ p 275 = true
  clause414 : p 143 = false ∨ p 277 = true
  clause415 : p 277 = false ∨ p 281 = true
  clause416 : p 281 = false ∨ p 283 = true
structure Block13 (p : Nat → Bool) : Prop where
  clause417 : p 275 = false ∨ p 283 = true
  clause418 : p 283 = false ∨ p 285 = true
  clause419 : p 271 = false ∨ p 285 = true
  clause420 : p 271 = false ∨ p 283 = false ∨ p 286 = true
  clause421 : p 272 = false ∨ p 286 = true
  clause422 : p 148 = false ∨ p 287 = true
  clause423 : p 147 = false ∨ p 287 = true
  clause424 : p 287 = false ∨ p 289 = true
  clause425 : p 146 = false ∨ p 289 = true
  clause426 : p 146 = false ∨ p 287 = false ∨ p 290 = true
  clause427 : p 151 = false ∨ p 291 = true
  clause428 : p 150 = false ∨ p 291 = true
  clause429 : p 150 = false ∨ p 151 = false ∨ p 292 = true
  clause430 : p 291 = false ∨ p 293 = true
  clause431 : p 292 = false ∨ p 294 = true
  clause432 : p 293 = false ∨ p 295 = true
  clause433 : p 294 = false ∨ p 296 = true
  clause434 : p 289 = false ∨ p 295 = true
  clause435 : p 289 = false ∨ p 293 = false ∨ p 296 = true
  clause436 : p 290 = false ∨ p 296 = true
  clause437 : p 154 = false ∨ p 297 = true
  clause438 : p 297 = false ∨ p 299 = true
  clause439 : p 155 = false ∨ p 301 = true
  clause440 : p 158 = false ∨ p 303 = true
  clause441 : p 303 = false ∨ p 305 = true
  clause442 : p 301 = false ∨ p 305 = true
  clause443 : p 305 = false ∨ p 307 = true
  clause444 : p 299 = false ∨ p 307 = true
  clause445 : p 307 = false ∨ p 309 = true
  clause446 : p 295 = false ∨ p 309 = true
  clause447 : p 295 = false ∨ p 307 = false ∨ p 310 = true
  clause448 : p 296 = false ∨ p 310 = true
structure Block14 (p : Nat → Bool) : Prop where
  clause449 : p 309 = false ∨ p 311 = true
  clause450 : p 310 = false ∨ p 312 = true
  clause451 : p 285 = false ∨ p 311 = true
  clause452 : p 285 = false ∨ p 309 = false ∨ p 312 = true
  clause453 : p 286 = false ∨ p 312 = true
  clause454 : p 311 = false ∨ p 313 = true
  clause455 : p 312 = false ∨ p 314 = true
  clause456 : p 261 = false ∨ p 313 = true
  clause457 : p 261 = false ∨ p 311 = false ∨ p 314 = true
  clause458 : p 262 = false ∨ p 314 = true
  clause459 : p 161 = false ∨ p 315 = true
  clause460 : p 315 = false ∨ p 317 = true
  clause461 : p 159 = false ∨ p 317 = true
  clause462 : p 159 = false ∨ p 315 = false ∨ p 318 = true
  clause463 : p 163 = false ∨ p 319 = true
  clause464 : p 319 = false ∨ p 321 = true
  clause465 : p 321 = false ∨ p 323 = true
  clause466 : p 317 = false ∨ p 323 = true
  clause467 : p 318 = false ∨ p 324 = true
  clause468 : p 167 = false ∨ p 325 = true
  clause469 : p 325 = false ∨ p 327 = true
  clause470 : p 169 = false ∨ p 329 = true
  clause471 : p 168 = false ∨ p 329 = true
  clause472 : p 171 = false ∨ p 331 = true
  clause473 : p 331 = false ∨ p 333 = true
  clause474 : p 329 = false ∨ p 333 = true
  clause475 : p 333 = false ∨ p 335 = true
  clause476 : p 327 = false ∨ p 335 = true
  clause477 : p 335 = false ∨ p 337 = true
  clause478 : p 323 = false ∨ p 337 = true
  clause479 : p 323 = false ∨ p 335 = false ∨ p 338 = true
  clause480 : p 324 = false ∨ p 338 = true
structure Block15 (p : Nat → Bool) : Prop where
  clause481 : p 174 = false ∨ p 339 = true
  clause482 : p 339 = false ∨ p 341 = true
  clause483 : p 176 = false ∨ p 343 = true
  clause484 : p 343 = false ∨ p 345 = true
  clause485 : p 345 = false ∨ p 347 = true
  clause486 : p 341 = false ∨ p 347 = true
  clause487 : p 341 = false ∨ p 345 = false ∨ p 348 = true
  clause488 : p 181 = false ∨ p 349 = true
  clause489 : p 179 = false ∨ p 349 = true
  clause490 : p 349 = false ∨ p 351 = true
  clause491 : p 182 = false ∨ p 353 = true
  clause492 : p 184 = false ∨ p 355 = true
  clause493 : p 355 = false ∨ p 357 = true
  clause494 : p 353 = false ∨ p 357 = true
  clause495 : p 353 = false ∨ p 355 = false ∨ p 358 = true
  clause496 : p 357 = false ∨ p 359 = true
  clause497 : p 358 = false ∨ p 360 = true
  clause498 : p 351 = false ∨ p 359 = true
  clause499 : p 351 = false ∨ p 357 = false ∨ p 360 = true
  clause500 : p 359 = false ∨ p 361 = true
  clause501 : p 360 = false ∨ p 362 = true
  clause502 : p 347 = false ∨ p 361 = true
  clause503 : p 347 = false ∨ p 359 = false ∨ p 362 = true
  clause504 : p 348 = false ∨ p 362 = true
  clause505 : p 361 = false ∨ p 363 = true
  clause506 : p 362 = false ∨ p 364 = true
  clause507 : p 337 = false ∨ p 363 = true
  clause508 : p 337 = false ∨ p 361 = false ∨ p 364 = true
  clause509 : p 338 = false ∨ p 364 = true
  clause510 : p 187 = false ∨ p 365 = true
  clause511 : p 365 = false ∨ p 367 = true
  clause512 : p 191 = false ∨ p 369 = true
structure Block16 (p : Nat → Bool) : Prop where
  clause513 : p 369 = false ∨ p 371 = true
  clause514 : p 189 = false ∨ p 371 = true
  clause515 : p 189 = false ∨ p 369 = false ∨ p 372 = true
  clause516 : p 371 = false ∨ p 373 = true
  clause517 : p 372 = false ∨ p 374 = true
  clause518 : p 367 = false ∨ p 373 = true
  clause519 : p 367 = false ∨ p 371 = false ∨ p 374 = true
  clause520 : p 193 = false ∨ p 375 = true
  clause521 : p 375 = false ∨ p 377 = true
  clause522 : p 195 = false ∨ p 379 = true
  clause523 : p 197 = false ∨ p 381 = true
  clause524 : p 381 = false ∨ p 383 = true
  clause525 : p 379 = false ∨ p 383 = true
  clause526 : p 383 = false ∨ p 385 = true
  clause527 : p 377 = false ∨ p 385 = true
  clause528 : p 385 = false ∨ p 387 = true
  clause529 : p 373 = false ∨ p 387 = true
  clause530 : p 373 = false ∨ p 385 = false ∨ p 388 = true
  clause531 : p 374 = false ∨ p 388 = true
  clause532 : p 199 = false ∨ p 391 = true
  clause533 : p 202 = false ∨ p 393 = true
  clause534 : p 204 = false ∨ p 395 = true
  clause535 : p 395 = false ∨ p 397 = true
  clause536 : p 393 = false ∨ p 397 = true
  clause537 : p 397 = false ∨ p 399 = true
  clause538 : p 391 = false ∨ p 399 = true
  clause539 : p 391 = false ∨ p 397 = false ∨ p 400 = true
  clause540 : p 208 = false ∨ p 401 = true
  clause541 : p 401 = false ∨ p 403 = true
  clause542 : p 206 = false ∨ p 403 = true
  clause543 : p 206 = false ∨ p 401 = false ∨ p 404 = true
  clause544 : p 209 = false ∨ p 405 = true
structure Block17 (p : Nat → Bool) : Prop where
  clause545 : p 211 = false ∨ p 407 = true
  clause546 : p 407 = false ∨ p 409 = true
  clause547 : p 405 = false ∨ p 409 = true
  clause548 : p 409 = false ∨ p 411 = true
  clause549 : p 403 = false ∨ p 411 = true
  clause550 : p 404 = false ∨ p 412 = true
  clause551 : p 411 = false ∨ p 413 = true
  clause552 : p 412 = false ∨ p 414 = true
  clause553 : p 399 = false ∨ p 413 = true
  clause554 : p 399 = false ∨ p 411 = false ∨ p 414 = true
  clause555 : p 400 = false ∨ p 414 = true
  clause556 : p 413 = false ∨ p 415 = true
  clause557 : p 414 = false ∨ p 416 = true
  clause558 : p 387 = false ∨ p 415 = true
  clause559 : p 387 = false ∨ p 413 = false ∨ p 416 = true
  clause560 : p 388 = false ∨ p 416 = true
  clause561 : p 415 = false ∨ p 417 = true
  clause562 : p 416 = false ∨ p 418 = true
  clause563 : p 363 = false ∨ p 417 = true
  clause564 : p 363 = false ∨ p 415 = false ∨ p 418 = true
  clause565 : p 364 = false ∨ p 418 = true
  clause566 : p 418 = false ∨ p 420 = true
  clause567 : p 313 = false ∨ p 417 = false ∨ p 420 = true
  clause568 : p 314 = false ∨ p 420 = true
  clause569 : p 420 = false
  clause570 : p 107 = true ∨ p 108 = true ∨ p 109 = true ∨ p 110 = true ∨ p 111 = true ∨ p 112 = true ∨ p 113 = true ∨ p 114 = true ∨ p 115 = true ∨ p 116 = true ∨ p 117 = true ∨ p 118 = true ∨ p 119 = true ∨ p 120 = true ∨ p 121 = true ∨ p 122 = true ∨ p 123 = true ∨ p 124 = true ∨ p 125 = true ∨ p 126 = true ∨ p 127 = true ∨ p 128 = true ∨ p 129 = true ∨ p 130 = true ∨ p 131 = true ∨ p 132 = true ∨ p 133 = true ∨ p 134 = true ∨ p 135 = true ∨ p 136 = true ∨ p 137 = true ∨ p 138 = true ∨ p 139 = true ∨ p 140 = true ∨ p 141 = true ∨ p 142 = true ∨ p 143 = true ∨ p 144 = true ∨ p 145 = true ∨ p 146 = true ∨ p 147 = true ∨ p 148 = true ∨ p 149 = true ∨ p 150 = true ∨ p 151 = true ∨ p 152 = true ∨ p 153 = true ∨ p 154 = true ∨ p 155 = true ∨ p 156 = true ∨ p 157 = true ∨ p 158 = true ∨ p 159 = true ∨ p 160 = true ∨ p 161 = true ∨ p 162 = true ∨ p 163 = true ∨ p 164 = true ∨ p 165 = true ∨ p 166 = true ∨ p 167 = true ∨ p 168 = true ∨ p 169 = true ∨ p 170 = true ∨ p 171 = true ∨ p 172 = true ∨ p 173 = true ∨ p 174 = true ∨ p 175 = true ∨ p 176 = true ∨ p 177 = true ∨ p 178 = true ∨ p 179 = true ∨ p 181 = true ∨ p 182 = true ∨ p 183 = true ∨ p 184 = true ∨ p 185 = true ∨ p 186 = true ∨ p 187 = true ∨ p 188 = true ∨ p 189 = true ∨ p 190 = true ∨ p 191 = true ∨ p 192 = true ∨ p 193 = true ∨ p 194 = true ∨ p 195 = true ∨ p 196 = true ∨ p 197 = true ∨ p 198 = true ∨ p 199 = true ∨ p 200 = true ∨ p 201 = true ∨ p 202 = true ∨ p 203 = true ∨ p 204 = true ∨ p 205 = true ∨ p 206 = true ∨ p 207 = true ∨ p 208 = true ∨ p 209 = true ∨ p 210 = true ∨ p 211 = true ∨ p 212 = true
  clause571 : p 7 = true ∨ p 1252 = true
  clause572 : p 4 = true ∨ p 1252 = true
  clause573 : p 4 = true ∨ p 7 = true ∨ p 1253 = true
  clause574 : p 1252 = false ∨ p 1254 = true
  clause575 : p 1253 = false ∨ p 1255 = true
  clause576 : p 2 = true ∨ p 1254 = true
structure Block18 (p : Nat → Bool) : Prop where
  clause577 : p 2 = true ∨ p 1252 = false ∨ p 1255 = true
  clause578 : p 2 = true ∨ p 1253 = false ∨ p 1256 = true
  clause579 : p 10 = true ∨ p 1257 = true
  clause580 : p 9 = true ∨ p 1257 = true
  clause581 : p 1257 = false ∨ p 1259 = true
  clause582 : p 8 = true ∨ p 1259 = true
  clause583 : p 8 = true ∨ p 1257 = false ∨ p 1260 = true
  clause584 : p 1259 = false ∨ p 1262 = true
  clause585 : p 1260 = false ∨ p 1263 = true
  clause586 : p 1254 = false ∨ p 1262 = true
  clause587 : p 1254 = false ∨ p 1259 = false ∨ p 1263 = true
  clause588 : p 1254 = false ∨ p 1260 = false ∨ p 1264 = true
  clause589 : p 1255 = false ∨ p 1263 = true
  clause590 : p 1255 = false ∨ p 1259 = false ∨ p 1264 = true
  clause591 : p 1256 = false ∨ p 1264 = true
  clause592 : p 15 = true ∨ p 1268 = true
  clause593 : p 14 = true ∨ p 1268 = true
  clause594 : p 14 = true ∨ p 15 = true ∨ p 1269 = true
  clause595 : p 1268 = false ∨ p 1270 = true
  clause596 : p 1269 = false ∨ p 1271 = true
  clause597 : p 11 = true ∨ p 1270 = true
  clause598 : p 11 = true ∨ p 1268 = false ∨ p 1271 = true
  clause599 : p 11 = true ∨ p 1269 = false ∨ p 1272 = true
  clause600 : p 20 = true ∨ p 1273 = true
  clause601 : p 18 = true ∨ p 1273 = true
  clause602 : p 18 = true ∨ p 20 = true ∨ p 1274 = true
  clause603 : p 25 = true ∨ p 1275 = true
  clause604 : p 23 = true ∨ p 1275 = true
  clause605 : p 1275 = false ∨ p 1277 = true
  clause606 : p 1273 = false ∨ p 1277 = true
  clause607 : p 1273 = false ∨ p 1275 = false ∨ p 1278 = true
  clause608 : p 1274 = false ∨ p 1275 = false ∨ p 1279 = true
structure Block19 (p : Nat → Bool) : Prop where
  clause609 : p 1277 = false ∨ p 1281 = true
  clause610 : p 1278 = false ∨ p 1282 = true
  clause611 : p 1279 = false ∨ p 1283 = true
  clause612 : p 1270 = false ∨ p 1281 = true
  clause613 : p 1270 = false ∨ p 1277 = false ∨ p 1282 = true
  clause614 : p 1270 = false ∨ p 1278 = false ∨ p 1283 = true
  clause615 : p 1270 = false ∨ p 1279 = false ∨ p 1284 = true
  clause616 : p 1271 = false ∨ p 1282 = true
  clause617 : p 1271 = false ∨ p 1277 = false ∨ p 1283 = true
  clause618 : p 1271 = false ∨ p 1278 = false ∨ p 1284 = true
  clause619 : p 1271 = false ∨ p 1279 = false ∨ p 1285 = true
  clause620 : p 1272 = false ∨ p 1277 = false ∨ p 1284 = true
  clause621 : p 1281 = false ∨ p 1288 = true
  clause622 : p 1282 = false ∨ p 1289 = true
  clause623 : p 1283 = false ∨ p 1290 = true
  clause624 : p 1284 = false ∨ p 1291 = true
  clause625 : p 1285 = false ∨ p 1292 = true
  clause626 : p 1262 = false ∨ p 1288 = true
  clause627 : p 1262 = false ∨ p 1281 = false ∨ p 1289 = true
  clause628 : p 1262 = false ∨ p 1282 = false ∨ p 1290 = true
  clause629 : p 1262 = false ∨ p 1283 = false ∨ p 1291 = true
  clause630 : p 1263 = false ∨ p 1289 = true
  clause631 : p 1263 = false ∨ p 1281 = false ∨ p 1290 = true
  clause632 : p 1263 = false ∨ p 1282 = false ∨ p 1291 = true
  clause633 : p 1263 = false ∨ p 1283 = false ∨ p 1292 = true
  clause634 : p 1264 = false ∨ p 1290 = true
  clause635 : p 1264 = false ∨ p 1281 = false ∨ p 1291 = true
  clause636 : p 30 = true ∨ p 1301 = true
  clause637 : p 29 = true ∨ p 1301 = true
  clause638 : p 29 = true ∨ p 30 = true ∨ p 1302 = true
  clause639 : p 1301 = false ∨ p 1303 = true
  clause640 : p 1302 = false ∨ p 1304 = true
structure Block20 (p : Nat → Bool) : Prop where
  clause641 : p 27 = true ∨ p 1303 = true
  clause642 : p 27 = true ∨ p 1301 = false ∨ p 1304 = true
  clause643 : p 27 = true ∨ p 1302 = false ∨ p 1305 = true
  clause644 : p 37 = true ∨ p 1306 = true
  clause645 : p 35 = true ∨ p 1306 = true
  clause646 : p 35 = true ∨ p 37 = true ∨ p 1307 = true
  clause647 : p 1306 = false ∨ p 1308 = true
  clause648 : p 1307 = false ∨ p 1309 = true
  clause649 : p 32 = true ∨ p 1308 = true
  clause650 : p 32 = true ∨ p 1306 = false ∨ p 1309 = true
  clause651 : p 1308 = false ∨ p 1311 = true
  clause652 : p 1309 = false ∨ p 1312 = true
  clause653 : p 1303 = false ∨ p 1311 = true
  clause654 : p 1303 = false ∨ p 1308 = false ∨ p 1312 = true
  clause655 : p 1303 = false ∨ p 1309 = false ∨ p 1313 = true
  clause656 : p 1304 = false ∨ p 1312 = true
  clause657 : p 1304 = false ∨ p 1308 = false ∨ p 1313 = true
  clause658 : p 1304 = false ∨ p 1309 = false ∨ p 1314 = true
  clause659 : p 1305 = false ∨ p 1308 = false ∨ p 1314 = true
  clause660 : p 42 = true ∨ p 1317 = true
  clause661 : p 41 = true ∨ p 1317 = true
  clause662 : p 41 = true ∨ p 42 = true ∨ p 1318 = true
  clause663 : p 1317 = false ∨ p 1319 = true
  clause664 : p 1318 = false ∨ p 1320 = true
  clause665 : p 40 = true ∨ p 1319 = true
  clause666 : p 40 = true ∨ p 1317 = false ∨ p 1320 = true
  clause667 : p 45 = true ∨ p 1322 = true
  clause668 : p 44 = true ∨ p 1322 = true
  clause669 : p 44 = true ∨ p 45 = true ∨ p 1323 = true
  clause670 : p 49 = true ∨ p 1324 = true
  clause671 : p 48 = true ∨ p 1324 = true
  clause672 : p 48 = true ∨ p 49 = true ∨ p 1325 = true
structure Block21 (p : Nat → Bool) : Prop where
  clause673 : p 1324 = false ∨ p 1326 = true
  clause674 : p 1325 = false ∨ p 1327 = true
  clause675 : p 1322 = false ∨ p 1326 = true
  clause676 : p 1322 = false ∨ p 1324 = false ∨ p 1327 = true
  clause677 : p 1322 = false ∨ p 1325 = false ∨ p 1328 = true
  clause678 : p 1323 = false ∨ p 1327 = true
  clause679 : p 1323 = false ∨ p 1324 = false ∨ p 1328 = true
  clause680 : p 1323 = false ∨ p 1325 = false ∨ p 1329 = true
  clause681 : p 1326 = false ∨ p 1330 = true
  clause682 : p 1327 = false ∨ p 1331 = true
  clause683 : p 1328 = false ∨ p 1332 = true
  clause684 : p 1329 = false ∨ p 1333 = true
  clause685 : p 1319 = false ∨ p 1330 = true
  clause686 : p 1319 = false ∨ p 1326 = false ∨ p 1331 = true
  clause687 : p 1319 = false ∨ p 1327 = false ∨ p 1332 = true
  clause688 : p 1319 = false ∨ p 1328 = false ∨ p 1333 = true
  clause689 : p 1319 = false ∨ p 1329 = false ∨ p 1334 = true
  clause690 : p 1320 = false ∨ p 1331 = true
  clause691 : p 1320 = false ∨ p 1326 = false ∨ p 1332 = true
  clause692 : p 1320 = false ∨ p 1327 = false ∨ p 1333 = true
  clause693 : p 1330 = false ∨ p 1337 = true
  clause694 : p 1331 = false ∨ p 1338 = true
  clause695 : p 1332 = false ∨ p 1339 = true
  clause696 : p 1333 = false ∨ p 1340 = true
  clause697 : p 1334 = false ∨ p 1341 = true
  clause698 : p 1311 = false ∨ p 1337 = true
  clause699 : p 1311 = false ∨ p 1330 = false ∨ p 1338 = true
  clause700 : p 1311 = false ∨ p 1331 = false ∨ p 1339 = true
  clause701 : p 1311 = false ∨ p 1332 = false ∨ p 1340 = true
  clause702 : p 1311 = false ∨ p 1333 = false ∨ p 1341 = true
  clause703 : p 1312 = false ∨ p 1330 = false ∨ p 1339 = true
  clause704 : p 1312 = false ∨ p 1331 = false ∨ p 1340 = true
structure Block22 (p : Nat → Bool) : Prop where
  clause705 : p 1312 = false ∨ p 1332 = false ∨ p 1341 = true
  clause706 : p 1312 = false ∨ p 1333 = false ∨ p 1342 = true
  clause707 : p 1313 = false ∨ p 1330 = false ∨ p 1340 = true
  clause708 : p 1313 = false ∨ p 1331 = false ∨ p 1341 = true
  clause709 : p 1313 = false ∨ p 1332 = false ∨ p 1342 = true
  clause710 : p 1314 = false ∨ p 1330 = false ∨ p 1341 = true
  clause711 : p 1314 = false ∨ p 1331 = false ∨ p 1342 = true
  clause712 : p 1288 = false ∨ p 1340 = false ∨ p 1354 = true
  clause713 : p 1288 = false ∨ p 1341 = false ∨ p 1355 = true
  clause714 : p 1289 = false ∨ p 1337 = false ∨ p 1352 = true
  clause715 : p 1289 = false ∨ p 1338 = false ∨ p 1353 = true
  clause716 : p 1289 = false ∨ p 1339 = false ∨ p 1354 = true
  clause717 : p 1289 = false ∨ p 1340 = false ∨ p 1355 = true
  clause718 : p 1289 = false ∨ p 1341 = false ∨ p 1356 = true
  clause719 : p 1289 = false ∨ p 1342 = false ∨ p 1357 = true
  clause720 : p 1290 = false ∨ p 1337 = false ∨ p 1353 = true
  clause721 : p 1290 = false ∨ p 1338 = false ∨ p 1354 = true
  clause722 : p 1290 = false ∨ p 1339 = false ∨ p 1355 = true
  clause723 : p 1290 = false ∨ p 1340 = false ∨ p 1356 = true
  clause724 : p 1290 = false ∨ p 1341 = false ∨ p 1357 = true
  clause725 : p 1291 = false ∨ p 1353 = true
  clause726 : p 1291 = false ∨ p 1337 = false ∨ p 1354 = true
  clause727 : p 1291 = false ∨ p 1338 = false ∨ p 1355 = true
  clause728 : p 1291 = false ∨ p 1339 = false ∨ p 1356 = true
  clause729 : p 1291 = false ∨ p 1340 = false ∨ p 1357 = true
  clause730 : p 1291 = false ∨ p 1341 = false ∨ p 1358 = true
  clause731 : p 1291 = false ∨ p 1342 = false ∨ p 1359 = true
  clause732 : p 1292 = false ∨ p 1337 = false ∨ p 1355 = true
  clause733 : p 1292 = false ∨ p 1338 = false ∨ p 1356 = true
  clause734 : p 1292 = false ∨ p 1339 = false ∨ p 1357 = true
  clause735 : p 1292 = false ∨ p 1340 = false ∨ p 1358 = true
  clause736 : p 55 = true ∨ p 1363 = true
structure Block23 (p : Nat → Bool) : Prop where
  clause737 : p 53 = true ∨ p 1363 = true
  clause738 : p 53 = true ∨ p 55 = true ∨ p 1364 = true
  clause739 : p 1363 = false ∨ p 1365 = true
  clause740 : p 1364 = false ∨ p 1366 = true
  clause741 : p 52 = true ∨ p 1365 = true
  clause742 : p 52 = true ∨ p 1363 = false ∨ p 1366 = true
  clause743 : p 52 = true ∨ p 1364 = false ∨ p 1367 = true
  clause744 : p 62 = true ∨ p 1368 = true
  clause745 : p 61 = true ∨ p 1368 = true
  clause746 : p 61 = true ∨ p 62 = true ∨ p 1369 = true
  clause747 : p 1368 = false ∨ p 1370 = true
  clause748 : p 1369 = false ∨ p 1371 = true
  clause749 : p 57 = true ∨ p 1370 = true
  clause750 : p 57 = true ∨ p 1368 = false ∨ p 1371 = true
  clause751 : p 57 = true ∨ p 1369 = false ∨ p 1372 = true
  clause752 : p 1370 = false ∨ p 1373 = true
  clause753 : p 1365 = false ∨ p 1370 = false ∨ p 1374 = true
  clause754 : p 1365 = false ∨ p 1371 = false ∨ p 1375 = true
  clause755 : p 1365 = false ∨ p 1372 = false ∨ p 1376 = true
  clause756 : p 1366 = false ∨ p 1370 = false ∨ p 1375 = true
  clause757 : p 1366 = false ∨ p 1371 = false ∨ p 1376 = true
  clause758 : p 1366 = false ∨ p 1372 = false ∨ p 1377 = true
  clause759 : p 1367 = false ∨ p 1370 = false ∨ p 1376 = true
  clause760 : p 1367 = false ∨ p 1371 = false ∨ p 1377 = true
  clause761 : p 1367 = false ∨ p 1372 = false ∨ p 1378 = true
  clause762 : p 68 = true ∨ p 1379 = true
  clause763 : p 65 = true ∨ p 1379 = true
  clause764 : p 1379 = false ∨ p 1381 = true
  clause765 : p 63 = true ∨ p 1381 = true
  clause766 : p 63 = true ∨ p 1379 = false ∨ p 1382 = true
  clause767 : p 73 = true ∨ p 1384 = true
  clause768 : p 76 = true ∨ p 1386 = true
structure Block24 (p : Nat → Bool) : Prop where
  clause769 : p 1386 = false ∨ p 1388 = true
  clause770 : p 1384 = false ∨ p 1388 = true
  clause771 : p 1384 = false ∨ p 1386 = false ∨ p 1389 = true
  clause772 : p 1388 = false ∨ p 1392 = true
  clause773 : p 1381 = false ∨ p 1392 = true
  clause774 : p 1381 = false ∨ p 1388 = false ∨ p 1393 = true
  clause775 : p 1381 = false ∨ p 1389 = false ∨ p 1394 = true
  clause776 : p 1382 = false ∨ p 1393 = true
  clause777 : p 1382 = false ∨ p 1388 = false ∨ p 1394 = true
  clause778 : p 1373 = false ∨ p 1399 = true
  clause779 : p 1373 = false ∨ p 1392 = false ∨ p 1400 = true
  clause780 : p 1373 = false ∨ p 1393 = false ∨ p 1401 = true
  clause781 : p 1374 = false ∨ p 1400 = true
  clause782 : p 1374 = false ∨ p 1392 = false ∨ p 1401 = true
  clause783 : p 1374 = false ∨ p 1393 = false ∨ p 1402 = true
  clause784 : p 1374 = false ∨ p 1394 = false ∨ p 1403 = true
  clause785 : p 1375 = false ∨ p 1401 = true
  clause786 : p 1375 = false ∨ p 1392 = false ∨ p 1402 = true
  clause787 : p 1375 = false ∨ p 1393 = false ∨ p 1403 = true
  clause788 : p 1375 = false ∨ p 1394 = false ∨ p 1404 = true
  clause789 : p 1376 = false ∨ p 1402 = true
  clause790 : p 1376 = false ∨ p 1392 = false ∨ p 1403 = true
  clause791 : p 1376 = false ∨ p 1393 = false ∨ p 1404 = true
  clause792 : p 1376 = false ∨ p 1394 = false ∨ p 1405 = true
  clause793 : p 1377 = false ∨ p 1403 = true
  clause794 : p 1377 = false ∨ p 1392 = false ∨ p 1404 = true
  clause795 : p 1377 = false ∨ p 1393 = false ∨ p 1405 = true
  clause796 : p 1378 = false ∨ p 1404 = true
  clause797 : p 1378 = false ∨ p 1392 = false ∨ p 1405 = true
  clause798 : p 1378 = false ∨ p 1393 = false ∨ p 1406 = true
  clause799 : p 83 = true ∨ p 1412 = true
  clause800 : p 81 = true ∨ p 1412 = true
structure Block25 (p : Nat → Bool) : Prop where
  clause801 : p 1412 = false ∨ p 1414 = true
  clause802 : p 78 = true ∨ p 1414 = true
  clause803 : p 78 = true ∨ p 1412 = false ∨ p 1415 = true
  clause804 : p 87 = true ∨ p 1417 = true
  clause805 : p 85 = true ∨ p 1417 = true
  clause806 : p 85 = true ∨ p 87 = true ∨ p 1418 = true
  clause807 : p 91 = true ∨ p 1419 = true
  clause808 : p 89 = true ∨ p 1419 = true
  clause809 : p 89 = true ∨ p 91 = true ∨ p 1420 = true
  clause810 : p 1419 = false ∨ p 1421 = true
  clause811 : p 1420 = false ∨ p 1422 = true
  clause812 : p 1417 = false ∨ p 1421 = true
  clause813 : p 1417 = false ∨ p 1419 = false ∨ p 1422 = true
  clause814 : p 1417 = false ∨ p 1420 = false ∨ p 1423 = true
  clause815 : p 1418 = false ∨ p 1422 = true
  clause816 : p 1418 = false ∨ p 1419 = false ∨ p 1423 = true
  clause817 : p 1421 = false ∨ p 1425 = true
  clause818 : p 1422 = false ∨ p 1426 = true
  clause819 : p 1423 = false ∨ p 1427 = true
  clause820 : p 1414 = false ∨ p 1425 = true
  clause821 : p 1414 = false ∨ p 1421 = false ∨ p 1426 = true
  clause822 : p 1414 = false ∨ p 1422 = false ∨ p 1427 = true
  clause823 : p 1414 = false ∨ p 1423 = false ∨ p 1428 = true
  clause824 : p 1415 = false ∨ p 1426 = true
  clause825 : p 1415 = false ∨ p 1421 = false ∨ p 1427 = true
  clause826 : p 98 = true ∨ p 1432 = true
  clause827 : p 96 = true ∨ p 1432 = true
  clause828 : p 96 = true ∨ p 98 = true ∨ p 1433 = true
  clause829 : p 1432 = false ∨ p 1434 = true
  clause830 : p 93 = true ∨ p 1434 = true
  clause831 : p 93 = true ∨ p 1432 = false ∨ p 1435 = true
  clause832 : p 93 = true ∨ p 1433 = false ∨ p 1436 = true
structure Block26 (p : Nat → Bool) : Prop where
  clause833 : p 102 = true ∨ p 1437 = true
  clause834 : p 100 = true ∨ p 1437 = true
  clause835 : p 100 = true ∨ p 102 = true ∨ p 1438 = true
  clause836 : p 105 = true ∨ p 1439 = true
  clause837 : p 103 = true ∨ p 1439 = true
  clause838 : p 1439 = false ∨ p 1441 = true
  clause839 : p 1437 = false ∨ p 1441 = true
  clause840 : p 1437 = false ∨ p 1439 = false ∨ p 1442 = true
  clause841 : p 1438 = false ∨ p 1439 = false ∨ p 1443 = true
  clause842 : p 1441 = false ∨ p 1445 = true
  clause843 : p 1442 = false ∨ p 1446 = true
  clause844 : p 1443 = false ∨ p 1447 = true
  clause845 : p 1434 = false ∨ p 1445 = true
  clause846 : p 1434 = false ∨ p 1441 = false ∨ p 1446 = true
  clause847 : p 1434 = false ∨ p 1442 = false ∨ p 1447 = true
  clause848 : p 1434 = false ∨ p 1443 = false ∨ p 1448 = true
  clause849 : p 1435 = false ∨ p 1446 = true
  clause850 : p 1435 = false ∨ p 1441 = false ∨ p 1447 = true
  clause851 : p 1435 = false ∨ p 1442 = false ∨ p 1448 = true
  clause852 : p 1436 = false ∨ p 1447 = true
  clause853 : p 1445 = false ∨ p 1452 = true
  clause854 : p 1446 = false ∨ p 1453 = true
  clause855 : p 1447 = false ∨ p 1454 = true
  clause856 : p 1448 = false ∨ p 1455 = true
  clause857 : p 1425 = false ∨ p 1452 = true
  clause858 : p 1425 = false ∨ p 1445 = false ∨ p 1453 = true
  clause859 : p 1425 = false ∨ p 1446 = false ∨ p 1454 = true
  clause860 : p 1425 = false ∨ p 1447 = false ∨ p 1455 = true
  clause861 : p 1426 = false ∨ p 1453 = true
  clause862 : p 1426 = false ∨ p 1445 = false ∨ p 1454 = true
  clause863 : p 1426 = false ∨ p 1446 = false ∨ p 1455 = true
  clause864 : p 1426 = false ∨ p 1447 = false ∨ p 1456 = true
structure Block27 (p : Nat → Bool) : Prop where
  clause865 : p 1427 = false ∨ p 1454 = true
  clause866 : p 1427 = false ∨ p 1445 = false ∨ p 1455 = true
  clause867 : p 1427 = false ∨ p 1446 = false ∨ p 1456 = true
  clause868 : p 1427 = false ∨ p 1447 = false ∨ p 1457 = true
  clause869 : p 1428 = false ∨ p 1455 = true
  clause870 : p 1399 = false ∨ p 1457 = false ∨ p 1471 = true
  clause871 : p 1400 = false ∨ p 1453 = false ∨ p 1468 = true
  clause872 : p 1400 = false ∨ p 1454 = false ∨ p 1469 = true
  clause873 : p 1400 = false ∨ p 1455 = false ∨ p 1470 = true
  clause874 : p 1400 = false ∨ p 1456 = false ∨ p 1471 = true
  clause875 : p 1400 = false ∨ p 1457 = false ∨ p 1472 = true
  clause876 : p 1401 = false ∨ p 1467 = true
  clause877 : p 1401 = false ∨ p 1452 = false ∨ p 1468 = true
  clause878 : p 1401 = false ∨ p 1453 = false ∨ p 1469 = true
  clause879 : p 1401 = false ∨ p 1454 = false ∨ p 1470 = true
  clause880 : p 1401 = false ∨ p 1455 = false ∨ p 1471 = true
  clause881 : p 1401 = false ∨ p 1456 = false ∨ p 1472 = true
  clause882 : p 1401 = false ∨ p 1457 = false ∨ p 1473 = true
  clause883 : p 1402 = false ∨ p 1452 = false ∨ p 1469 = true
  clause884 : p 1402 = false ∨ p 1453 = false ∨ p 1470 = true
  clause885 : p 1402 = false ∨ p 1454 = false ∨ p 1471 = true
  clause886 : p 1402 = false ∨ p 1455 = false ∨ p 1472 = true
  clause887 : p 1402 = false ∨ p 1456 = false ∨ p 1473 = true
  clause888 : p 1402 = false ∨ p 1457 = false ∨ p 1474 = true
  clause889 : p 1403 = false ∨ p 1469 = true
  clause890 : p 1403 = false ∨ p 1452 = false ∨ p 1470 = true
  clause891 : p 1403 = false ∨ p 1453 = false ∨ p 1471 = true
  clause892 : p 1403 = false ∨ p 1454 = false ∨ p 1472 = true
  clause893 : p 1403 = false ∨ p 1455 = false ∨ p 1473 = true
  clause894 : p 1404 = false ∨ p 1452 = false ∨ p 1471 = true
  clause895 : p 1404 = false ∨ p 1453 = false ∨ p 1472 = true
  clause896 : p 1404 = false ∨ p 1454 = false ∨ p 1473 = true
structure Block28 (p : Nat → Bool) : Prop where
  clause897 : p 1404 = false ∨ p 1455 = false ∨ p 1474 = true
  clause898 : p 1405 = false ∨ p 1452 = false ∨ p 1472 = true
  clause899 : p 1405 = false ∨ p 1453 = false ∨ p 1473 = true
  clause900 : p 1406 = false ∨ p 1472 = true
  clause901 : p 1406 = false ∨ p 1452 = false ∨ p 1473 = true
  clause902 : p 1352 = false ∨ p 1474 = false ∨ p 1490 = true
  clause903 : p 1353 = false ∨ p 1473 = false ∨ p 1490 = true
  clause904 : p 1354 = false ∨ p 1472 = false ∨ p 1490 = true
  clause905 : p 1355 = false ∨ p 1471 = false ∨ p 1490 = true
  clause906 : p 1356 = false ∨ p 1470 = false ∨ p 1490 = true
  clause907 : p 1357 = false ∨ p 1469 = false ∨ p 1490 = true
  clause908 : p 1358 = false ∨ p 1468 = false ∨ p 1490 = true
  clause909 : p 1359 = false ∨ p 1467 = false ∨ p 1490 = true
  clause910 : p 1490 = false
  clause911 : p 4 = false ∨ p 5 = false ∨ p 6 = false ∨ p 7 = false
  clause912 : p 4 = false ∨ p 5 = false ∨ p 22 = false ∨ p 23 = false
  clause913 : p 5 = false ∨ p 7 = false ∨ p 14 = false ∨ p 16 = false
  clause914 : p 24 = false ∨ p 25 = false ∨ p 32 = false ∨ p 33 = false
  clause915 : p 34 = false ∨ p 37 = false ∨ p 57 = false ∨ p 58 = false
  clause916 : p 35 = false ∨ p 36 = false ∨ p 43 = false ∨ p 45 = false
  clause917 : p 37 = false ∨ p 39 = false ∨ p 47 = false ∨ p 49 = false
  clause918 : p 82 = false ∨ p 83 = false ∨ p 89 = false ∨ p 90 = false
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
def c1 : List Lit := [(1, false), (2, false), (4, false), (18, false)]
theorem step1 (p : Nat → Bool) (h : Constraints p) : clause p c1 = true := by
  simpa only [c1,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause1
def c2 : List Lit := [(1, false), (107, true), (4, true), (18, true)]
theorem step2 (p : Nat → Bool) (h : Constraints p) : clause p c2 = true := by
  simpa only [c2,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause2
def c3 : List Lit := [(108, false), (2, true)]
theorem step3 (p : Nat → Bool) (h : Constraints p) : clause p c3 = true := by
  simpa only [c3,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause3
def c4 : List Lit := [(2, false), (1, true), (3, true)]
theorem step4 (p : Nat → Bool) (h : Constraints p) : clause p c4 = true := by
  simpa only [c4,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause4
def c5 : List Lit := [(2, false), (108, true), (3, true)]
theorem step5 (p : Nat → Bool) (h : Constraints p) : clause p c5 = true := by
  simpa only [c5,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause5
def c6 : List Lit := [(2, false), (108, true), (1, true)]
theorem step6 (p : Nat → Bool) (h : Constraints p) : clause p c6 = true := by
  simpa only [c6,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause6
def c7 : List Lit := [(3, false), (2, false), (8, false), (11, false)]
theorem step7 (p : Nat → Bool) (h : Constraints p) : clause p c7 = true := by
  simpa only [c7,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause7
def c8 : List Lit := [(3, false), (109, true), (2, true), (8, true)]
theorem step8 (p : Nat → Bool) (h : Constraints p) : clause p c8 = true := by
  simpa only [c8,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause8
def c9 : List Lit := [(4, false), (1, false), (5, false), (6, false)]
theorem step9 (p : Nat → Bool) (h : Constraints p) : clause p c9 = true := by
  simpa only [c9,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause9
def c10 : List Lit := [(4, false), (1, false), (5, false), (13, false)]
theorem step10 (p : Nat → Bool) (h : Constraints p) : clause p c10 = true := by
  simpa only [c10,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause10
def c11 : List Lit := [(4, false), (1, false), (5, false), (22, false)]
theorem step11 (p : Nat → Bool) (h : Constraints p) : clause p c11 = true := by
  simpa only [c11,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause11
def c12 : List Lit := [(4, false), (1, false), (5, false), (67, false)]
theorem step12 (p : Nat → Bool) (h : Constraints p) : clause p c12 = true := by
  simpa only [c12,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause12
def c13 : List Lit := [(4, false), (1, false), (6, false), (13, false)]
theorem step13 (p : Nat → Bool) (h : Constraints p) : clause p c13 = true := by
  simpa only [c13,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause13
def c14 : List Lit := [(4, false), (1, false), (6, false), (22, false)]
theorem step14 (p : Nat → Bool) (h : Constraints p) : clause p c14 = true := by
  simpa only [c14,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause14
def c15 : List Lit := [(4, false), (1, false), (6, false), (67, false)]
theorem step15 (p : Nat → Bool) (h : Constraints p) : clause p c15 = true := by
  simpa only [c15,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause15
def c16 : List Lit := [(4, false), (1, false), (13, false), (22, false)]
theorem step16 (p : Nat → Bool) (h : Constraints p) : clause p c16 = true := by
  simpa only [c16,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause16
def c17 : List Lit := [(4, false), (1, false), (13, false), (67, false)]
theorem step17 (p : Nat → Bool) (h : Constraints p) : clause p c17 = true := by
  simpa only [c17,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause17
def c18 : List Lit := [(4, false), (1, false), (22, false), (67, false)]
theorem step18 (p : Nat → Bool) (h : Constraints p) : clause p c18 = true := by
  simpa only [c18,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause18
def c19 : List Lit := [(4, false), (5, false), (6, false), (67, false)]
theorem step19 (p : Nat → Bool) (h : Constraints p) : clause p c19 = true := by
  simpa only [c19,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause19
def c20 : List Lit := [(4, false), (5, false), (13, false), (67, false)]
theorem step20 (p : Nat → Bool) (h : Constraints p) : clause p c20 = true := by
  simpa only [c20,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause20
def c21 : List Lit := [(4, false), (5, false), (22, false), (67, false)]
theorem step21 (p : Nat → Bool) (h : Constraints p) : clause p c21 = true := by
  simpa only [c21,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause21
def c22 : List Lit := [(4, false), (6, false), (22, false), (67, false)]
theorem step22 (p : Nat → Bool) (h : Constraints p) : clause p c22 = true := by
  simpa only [c22,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause22
def c23 : List Lit := [(5, false), (4, false), (7, false), (14, false)]
theorem step23 (p : Nat → Bool) (h : Constraints p) : clause p c23 = true := by
  simpa only [c23,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause23
def c24 : List Lit := [(5, false), (4, false), (7, false), (23, false)]
theorem step24 (p : Nat → Bool) (h : Constraints p) : clause p c24 = true := by
  simpa only [c24,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause24
def c25 : List Lit := [(5, false), (4, false), (14, false), (23, false)]
theorem step25 (p : Nat → Bool) (h : Constraints p) : clause p c25 = true := by
  simpa only [c25,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause25
def c26 : List Lit := [(5, false), (7, false), (14, false), (23, false)]
theorem step26 (p : Nat → Bool) (h : Constraints p) : clause p c26 = true := by
  simpa only [c26,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause26
def c27 : List Lit := [(6, false), (4, false), (7, false), (8, false)]
theorem step27 (p : Nat → Bool) (h : Constraints p) : clause p c27 = true := by
  simpa only [c27,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause27
def c28 : List Lit := [(6, false), (4, false), (7, false), (15, false)]
theorem step28 (p : Nat → Bool) (h : Constraints p) : clause p c28 = true := by
  simpa only [c28,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause28
def c29 : List Lit := [(6, false), (4, false), (8, false), (15, false)]
theorem step29 (p : Nat → Bool) (h : Constraints p) : clause p c29 = true := by
  simpa only [c29,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause29
def c30 : List Lit := [(6, false), (7, false), (8, false), (15, false)]
theorem step30 (p : Nat → Bool) (h : Constraints p) : clause p c30 = true := by
  simpa only [c30,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause30
def c31 : List Lit := [(113, false), (7, true)]
theorem step31 (p : Nat → Bool) (h : Constraints p) : clause p c31 = true := by
  simpa only [c31,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause31
def c32 : List Lit := [(7, false), (5, true), (6, true), (16, true)]
theorem step32 (p : Nat → Bool) (h : Constraints p) : clause p c32 = true := by
  simpa only [c32,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block0.clause32
def c33 : List Lit := [(7, false), (113, true), (6, true), (16, true)]
theorem step33 (p : Nat → Bool) (h : Constraints p) : clause p c33 = true := by
  simpa only [c33,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause33
def c34 : List Lit := [(7, false), (113, true), (5, true), (16, true)]
theorem step34 (p : Nat → Bool) (h : Constraints p) : clause p c34 = true := by
  simpa only [c34,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause34
def c35 : List Lit := [(7, false), (113, true), (5, true), (6, true)]
theorem step35 (p : Nat → Bool) (h : Constraints p) : clause p c35 = true := by
  simpa only [c35,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause35
def c36 : List Lit := [(8, false), (3, true), (6, true), (24, true)]
theorem step36 (p : Nat → Bool) (h : Constraints p) : clause p c36 = true := by
  simpa only [c36,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause36
def c37 : List Lit := [(8, false), (114, true), (6, true), (24, true)]
theorem step37 (p : Nat → Bool) (h : Constraints p) : clause p c37 = true := by
  simpa only [c37,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause37
def c38 : List Lit := [(8, false), (114, true), (3, true), (6, true)]
theorem step38 (p : Nat → Bool) (h : Constraints p) : clause p c38 = true := by
  simpa only [c38,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause38
def c39 : List Lit := [(9, false), (12, false), (16, false), (28, false)]
theorem step39 (p : Nat → Bool) (h : Constraints p) : clause p c39 = true := by
  simpa only [c39,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause39
def c40 : List Lit := [(10, false), (116, true), (17, true)]
theorem step40 (p : Nat → Bool) (h : Constraints p) : clause p c40 = true := by
  simpa only [c40,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause40
def c41 : List Lit := [(10, false), (116, true), (12, true)]
theorem step41 (p : Nat → Bool) (h : Constraints p) : clause p c41 = true := by
  simpa only [c41,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause41
def c42 : List Lit := [(11, false), (3, true), (12, true)]
theorem step42 (p : Nat → Bool) (h : Constraints p) : clause p c42 = true := by
  simpa only [c42,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause42
def c43 : List Lit := [(11, false), (117, true), (12, true)]
theorem step43 (p : Nat → Bool) (h : Constraints p) : clause p c43 = true := by
  simpa only [c43,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause43
def c44 : List Lit := [(11, false), (117, true), (3, true)]
theorem step44 (p : Nat → Bool) (h : Constraints p) : clause p c44 = true := by
  simpa only [c44,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause44
def c45 : List Lit := [(12, false), (9, false), (10, false), (11, false)]
theorem step45 (p : Nat → Bool) (h : Constraints p) : clause p c45 = true := by
  simpa only [c45,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause45
def c46 : List Lit := [(13, false), (4, false), (14, false), (15, false)]
theorem step46 (p : Nat → Bool) (h : Constraints p) : clause p c46 = true := by
  simpa only [c46,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause46
def c47 : List Lit := [(13, false), (119, true), (4, true), (15, true)]
theorem step47 (p : Nat → Bool) (h : Constraints p) : clause p c47 = true := by
  simpa only [c47,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause47
def c48 : List Lit := [(13, false), (119, true), (4, true), (14, true)]
theorem step48 (p : Nat → Bool) (h : Constraints p) : clause p c48 = true := by
  simpa only [c48,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause48
def c49 : List Lit := [(14, false), (5, true), (13, true), (16, true), (17, true)]
theorem step49 (p : Nat → Bool) (h : Constraints p) : clause p c49 = true := by
  simpa only [c49,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause49
def c50 : List Lit := [(14, false), (120, true), (13, true), (16, true), (17, true)]
theorem step50 (p : Nat → Bool) (h : Constraints p) : clause p c50 = true := by
  simpa only [c50,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause50
def c51 : List Lit := [(14, false), (120, true), (5, true), (13, true), (16, true)]
theorem step51 (p : Nat → Bool) (h : Constraints p) : clause p c51 = true := by
  simpa only [c51,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause51
def c52 : List Lit := [(15, false), (6, true), (13, true), (16, true)]
theorem step52 (p : Nat → Bool) (h : Constraints p) : clause p c52 = true := by
  simpa only [c52,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause52
def c53 : List Lit := [(15, false), (121, true), (13, true), (16, true)]
theorem step53 (p : Nat → Bool) (h : Constraints p) : clause p c53 = true := by
  simpa only [c53,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause53
def c54 : List Lit := [(15, false), (121, true), (6, true), (16, true)]
theorem step54 (p : Nat → Bool) (h : Constraints p) : clause p c54 = true := by
  simpa only [c54,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause54
def c55 : List Lit := [(15, false), (121, true), (6, true), (13, true)]
theorem step55 (p : Nat → Bool) (h : Constraints p) : clause p c55 = true := by
  simpa only [c55,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause55
def c56 : List Lit := [(16, false), (7, false), (9, false), (14, false)]
theorem step56 (p : Nat → Bool) (h : Constraints p) : clause p c56 = true := by
  simpa only [c56,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause56
def c57 : List Lit := [(16, false), (7, false), (9, false), (15, false)]
theorem step57 (p : Nat → Bool) (h : Constraints p) : clause p c57 = true := by
  simpa only [c57,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause57
def c58 : List Lit := [(16, false), (7, false), (14, false), (15, false)]
theorem step58 (p : Nat → Bool) (h : Constraints p) : clause p c58 = true := by
  simpa only [c58,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause58
def c59 : List Lit := [(16, false), (9, false), (14, false), (15, false)]
theorem step59 (p : Nat → Bool) (h : Constraints p) : clause p c59 = true := by
  simpa only [c59,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause59
def c60 : List Lit := [(17, false), (123, true), (14, true)]
theorem step60 (p : Nat → Bool) (h : Constraints p) : clause p c60 = true := by
  simpa only [c60,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause60
def c61 : List Lit := [(17, false), (123, true), (10, true)]
theorem step61 (p : Nat → Bool) (h : Constraints p) : clause p c61 = true := by
  simpa only [c61,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause61
def c62 : List Lit := [(18, false), (1, false), (22, false), (26, false)]
theorem step62 (p : Nat → Bool) (h : Constraints p) : clause p c62 = true := by
  simpa only [c62,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause62
def c63 : List Lit := [(19, false), (18, false), (20, false), (23, false)]
theorem step63 (p : Nat → Bool) (h : Constraints p) : clause p c63 = true := by
  simpa only [c63,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause63
def c64 : List Lit := [(19, false), (125, true), (18, true), (23, true)]
theorem step64 (p : Nat → Bool) (h : Constraints p) : clause p c64 = true := by
  simpa only [c64,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block1.clause64
def c65 : List Lit := [(19, false), (125, true), (18, true), (20, true)]
theorem step65 (p : Nat → Bool) (h : Constraints p) : clause p c65 = true := by
  simpa only [c65,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause65
def c66 : List Lit := [(20, false), (126, true), (21, true)]
theorem step66 (p : Nat → Bool) (h : Constraints p) : clause p c66 = true := by
  simpa only [c66,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause66
def c67 : List Lit := [(20, false), (126, true), (19, true)]
theorem step67 (p : Nat → Bool) (h : Constraints p) : clause p c67 = true := by
  simpa only [c67,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause67
def c68 : List Lit := [(21, false), (127, true), (25, true)]
theorem step68 (p : Nat → Bool) (h : Constraints p) : clause p c68 = true := by
  simpa only [c68,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause68
def c69 : List Lit := [(22, false), (4, false), (18, false), (52, false)]
theorem step69 (p : Nat → Bool) (h : Constraints p) : clause p c69 = true := by
  simpa only [c69,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause69
def c70 : List Lit := [(22, false), (4, false), (23, false), (52, false)]
theorem step70 (p : Nat → Bool) (h : Constraints p) : clause p c70 = true := by
  simpa only [c70,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause70
def c71 : List Lit := [(22, false), (18, false), (23, false), (52, false)]
theorem step71 (p : Nat → Bool) (h : Constraints p) : clause p c71 = true := by
  simpa only [c71,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause71
def c72 : List Lit := [(22, false), (128, true), (4, true), (18, true), (23, true)]
theorem step72 (p : Nat → Bool) (h : Constraints p) : clause p c72 = true := by
  simpa only [c72,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause72
def c73 : List Lit := [(23, false), (5, true), (19, true), (22, true)]
theorem step73 (p : Nat → Bool) (h : Constraints p) : clause p c73 = true := by
  simpa only [c73,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause73
def c74 : List Lit := [(23, false), (129, true), (19, true), (22, true)]
theorem step74 (p : Nat → Bool) (h : Constraints p) : clause p c74 = true := by
  simpa only [c74,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause74
def c75 : List Lit := [(23, false), (129, true), (5, true), (22, true)]
theorem step75 (p : Nat → Bool) (h : Constraints p) : clause p c75 = true := by
  simpa only [c75,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause75
def c76 : List Lit := [(23, false), (129, true), (5, true), (19, true)]
theorem step76 (p : Nat → Bool) (h : Constraints p) : clause p c76 = true := by
  simpa only [c76,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause76
def c77 : List Lit := [(24, false), (8, false), (25, false), (32, false)]
theorem step77 (p : Nat → Bool) (h : Constraints p) : clause p c77 = true := by
  simpa only [c77,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause77
def c78 : List Lit := [(26, false), (18, false), (27, false), (29, false)]
theorem step78 (p : Nat → Bool) (h : Constraints p) : clause p c78 = true := by
  simpa only [c78,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause78
def c79 : List Lit := [(26, false), (132, true), (18, true), (29, true)]
theorem step79 (p : Nat → Bool) (h : Constraints p) : clause p c79 = true := by
  simpa only [c79,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause79
def c80 : List Lit := [(26, false), (132, true), (18, true), (27, true)]
theorem step80 (p : Nat → Bool) (h : Constraints p) : clause p c80 = true := by
  simpa only [c80,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause80
def c81 : List Lit := [(133, false), (27, true)]
theorem step81 (p : Nat → Bool) (h : Constraints p) : clause p c81 = true := by
  simpa only [c81,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause81
def c82 : List Lit := [(27, false), (133, true), (28, true)]
theorem step82 (p : Nat → Bool) (h : Constraints p) : clause p c82 = true := by
  simpa only [c82,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause82
def c83 : List Lit := [(27, false), (133, true), (26, true)]
theorem step83 (p : Nat → Bool) (h : Constraints p) : clause p c83 = true := by
  simpa only [c83,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause83
def c84 : List Lit := [(28, false), (9, false), (27, false), (30, false)]
theorem step84 (p : Nat → Bool) (h : Constraints p) : clause p c84 = true := by
  simpa only [c84,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause84
def c85 : List Lit := [(28, false), (134, true), (9, true), (30, true)]
theorem step85 (p : Nat → Bool) (h : Constraints p) : clause p c85 = true := by
  simpa only [c85,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause85
def c86 : List Lit := [(135, false), (29, true)]
theorem step86 (p : Nat → Bool) (h : Constraints p) : clause p c86 = true := by
  simpa only [c86,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause86
def c87 : List Lit := [(29, false), (135, true), (31, true)]
theorem step87 (p : Nat → Bool) (h : Constraints p) : clause p c87 = true := by
  simpa only [c87,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause87
def c88 : List Lit := [(29, false), (135, true), (26, true)]
theorem step88 (p : Nat → Bool) (h : Constraints p) : clause p c88 = true := by
  simpa only [c88,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause88
def c89 : List Lit := [(136, false), (30, true)]
theorem step89 (p : Nat → Bool) (h : Constraints p) : clause p c89 = true := by
  simpa only [c89,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause89
def c90 : List Lit := [(30, false), (28, false), (33, false), (56, false)]
theorem step90 (p : Nat → Bool) (h : Constraints p) : clause p c90 = true := by
  simpa only [c90,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause90
def c91 : List Lit := [(31, false), (137, true), (32, true)]
theorem step91 (p : Nat → Bool) (h : Constraints p) : clause p c91 = true := by
  simpa only [c91,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause91
def c92 : List Lit := [(31, false), (137, true), (29, true)]
theorem step92 (p : Nat → Bool) (h : Constraints p) : clause p c92 = true := by
  simpa only [c92,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause92
def c93 : List Lit := [(32, false), (138, true), (31, true), (33, true)]
theorem step93 (p : Nat → Bool) (h : Constraints p) : clause p c93 = true := by
  simpa only [c93,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause93
def c94 : List Lit := [(32, false), (138, true), (24, true), (33, true)]
theorem step94 (p : Nat → Bool) (h : Constraints p) : clause p c94 = true := by
  simpa only [c94,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause94
def c95 : List Lit := [(32, false), (138, true), (24, true), (31, true)]
theorem step95 (p : Nat → Bool) (h : Constraints p) : clause p c95 = true := by
  simpa only [c95,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause95
def c96 : List Lit := [(33, false), (139, true), (25, true), (30, true)]
theorem step96 (p : Nat → Bool) (h : Constraints p) : clause p c96 = true := by
  simpa only [c96,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block2.clause96
def c97 : List Lit := [(34, false), (35, false), (37, false), (57, false)]
theorem step97 (p : Nat → Bool) (h : Constraints p) : clause p c97 = true := by
  simpa only [c97,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause97
def c98 : List Lit := [(34, false), (35, false), (37, false), (76, false)]
theorem step98 (p : Nat → Bool) (h : Constraints p) : clause p c98 = true := by
  simpa only [c98,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause98
def c99 : List Lit := [(34, false), (35, false), (57, false), (76, false)]
theorem step99 (p : Nat → Bool) (h : Constraints p) : clause p c99 = true := by
  simpa only [c99,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause99
def c100 : List Lit := [(34, false), (37, false), (57, false), (76, false)]
theorem step100 (p : Nat → Bool) (h : Constraints p) : clause p c100 = true := by
  simpa only [c100,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause100
def c101 : List Lit := [(34, false), (140, true), (37, true), (57, true), (76, true)]
theorem step101 (p : Nat → Bool) (h : Constraints p) : clause p c101 = true := by
  simpa only [c101,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause101
def c102 : List Lit := [(34, false), (140, true), (35, true), (37, true), (76, true)]
theorem step102 (p : Nat → Bool) (h : Constraints p) : clause p c102 = true := by
  simpa only [c102,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause102
def c103 : List Lit := [(35, false), (34, true), (36, true), (43, true)]
theorem step103 (p : Nat → Bool) (h : Constraints p) : clause p c103 = true := by
  simpa only [c103,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause103
def c104 : List Lit := [(35, false), (141, true), (36, true), (43, true)]
theorem step104 (p : Nat → Bool) (h : Constraints p) : clause p c104 = true := by
  simpa only [c104,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause104
def c105 : List Lit := [(35, false), (141, true), (34, true), (43, true)]
theorem step105 (p : Nat → Bool) (h : Constraints p) : clause p c105 = true := by
  simpa only [c105,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause105
def c106 : List Lit := [(36, false), (35, false), (41, false), (45, false)]
theorem step106 (p : Nat → Bool) (h : Constraints p) : clause p c106 = true := by
  simpa only [c106,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause106
def c107 : List Lit := [(36, false), (142, true), (41, true), (45, true)]
theorem step107 (p : Nat → Bool) (h : Constraints p) : clause p c107 = true := by
  simpa only [c107,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause107
def c108 : List Lit := [(36, false), (142, true), (35, true), (45, true)]
theorem step108 (p : Nat → Bool) (h : Constraints p) : clause p c108 = true := by
  simpa only [c108,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause108
def c109 : List Lit := [(36, false), (142, true), (35, true), (41, true)]
theorem step109 (p : Nat → Bool) (h : Constraints p) : clause p c109 = true := by
  simpa only [c109,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause109
def c110 : List Lit := [(37, false), (34, false), (38, false), (39, false)]
theorem step110 (p : Nat → Bool) (h : Constraints p) : clause p c110 = true := by
  simpa only [c110,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause110
def c111 : List Lit := [(37, false), (34, false), (38, false), (47, false)]
theorem step111 (p : Nat → Bool) (h : Constraints p) : clause p c111 = true := by
  simpa only [c111,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause111
def c112 : List Lit := [(37, false), (38, false), (39, false), (58, false)]
theorem step112 (p : Nat → Bool) (h : Constraints p) : clause p c112 = true := by
  simpa only [c112,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause112
def c113 : List Lit := [(37, false), (38, false), (47, false), (58, false)]
theorem step113 (p : Nat → Bool) (h : Constraints p) : clause p c113 = true := by
  simpa only [c113,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause113
def c114 : List Lit := [(38, false), (37, false), (40, false), (48, false)]
theorem step114 (p : Nat → Bool) (h : Constraints p) : clause p c114 = true := by
  simpa only [c114,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause114
def c115 : List Lit := [(38, false), (37, false), (40, false), (81, false)]
theorem step115 (p : Nat → Bool) (h : Constraints p) : clause p c115 = true := by
  simpa only [c115,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause115
def c116 : List Lit := [(38, false), (37, false), (48, false), (81, false)]
theorem step116 (p : Nat → Bool) (h : Constraints p) : clause p c116 = true := by
  simpa only [c116,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause116
def c117 : List Lit := [(38, false), (40, false), (48, false), (81, false)]
theorem step117 (p : Nat → Bool) (h : Constraints p) : clause p c117 = true := by
  simpa only [c117,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause117
def c118 : List Lit := [(39, false), (37, false), (40, false), (41, false)]
theorem step118 (p : Nat → Bool) (h : Constraints p) : clause p c118 = true := by
  simpa only [c118,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause118
def c119 : List Lit := [(39, false), (37, false), (41, false), (49, false)]
theorem step119 (p : Nat → Bool) (h : Constraints p) : clause p c119 = true := by
  simpa only [c119,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause119
def c120 : List Lit := [(39, false), (40, false), (41, false), (49, false)]
theorem step120 (p : Nat → Bool) (h : Constraints p) : clause p c120 = true := by
  simpa only [c120,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause120
def c121 : List Lit := [(39, false), (145, true), (37, true), (40, true), (41, true)]
theorem step121 (p : Nat → Bool) (h : Constraints p) : clause p c121 = true := by
  simpa only [c121,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause121
def c122 : List Lit := [(146, false), (40, true)]
theorem step122 (p : Nat → Bool) (h : Constraints p) : clause p c122 = true := by
  simpa only [c122,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause122
def c123 : List Lit := [(40, false), (38, true), (39, true), (50, true)]
theorem step123 (p : Nat → Bool) (h : Constraints p) : clause p c123 = true := by
  simpa only [c123,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause123
def c124 : List Lit := [(146, false), (38, false), (39, false)]
theorem step124 (p : Nat → Bool) (h : Constraints p) : clause p c124 = true := by
  simpa only [c124,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause124
def c125 : List Lit := [(40, false), (146, true), (39, true), (50, true)]
theorem step125 (p : Nat → Bool) (h : Constraints p) : clause p c125 = true := by
  simpa only [c125,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause125
def c126 : List Lit := [(40, false), (146, true), (38, true), (50, true)]
theorem step126 (p : Nat → Bool) (h : Constraints p) : clause p c126 = true := by
  simpa only [c126,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause126
def c127 : List Lit := [(40, false), (146, true), (38, true), (39, true)]
theorem step127 (p : Nat → Bool) (h : Constraints p) : clause p c127 = true := by
  simpa only [c127,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause127
def c128 : List Lit := [(41, false), (36, false), (39, false), (59, false)]
theorem step128 (p : Nat → Bool) (h : Constraints p) : clause p c128 = true := by
  simpa only [c128,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block3.clause128
def c129 : List Lit := [(41, false), (147, true), (39, true), (59, true), (82, true)]
theorem step129 (p : Nat → Bool) (h : Constraints p) : clause p c129 = true := by
  simpa only [c129,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause129
def c130 : List Lit := [(41, false), (147, true), (36, true), (59, true), (82, true)]
theorem step130 (p : Nat → Bool) (h : Constraints p) : clause p c130 = true := by
  simpa only [c130,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause130
def c131 : List Lit := [(42, false), (46, false), (50, false), (86, false)]
theorem step131 (p : Nat → Bool) (h : Constraints p) : clause p c131 = true := by
  simpa only [c131,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause131
def c132 : List Lit := [(42, false), (148, true), (50, true), (86, true)]
theorem step132 (p : Nat → Bool) (h : Constraints p) : clause p c132 = true := by
  simpa only [c132,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause132
def c133 : List Lit := [(42, false), (148, true), (46, true), (50, true)]
theorem step133 (p : Nat → Bool) (h : Constraints p) : clause p c133 = true := by
  simpa only [c133,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause133
def c134 : List Lit := [(43, false), (35, false), (44, false), (45, false)]
theorem step134 (p : Nat → Bool) (h : Constraints p) : clause p c134 = true := by
  simpa only [c134,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause134
def c135 : List Lit := [(43, false), (35, false), (44, false), (62, false)]
theorem step135 (p : Nat → Bool) (h : Constraints p) : clause p c135 = true := by
  simpa only [c135,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause135
def c136 : List Lit := [(43, false), (35, false), (44, false), (87, false)]
theorem step136 (p : Nat → Bool) (h : Constraints p) : clause p c136 = true := by
  simpa only [c136,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause136
def c137 : List Lit := [(43, false), (35, false), (45, false), (62, false)]
theorem step137 (p : Nat → Bool) (h : Constraints p) : clause p c137 = true := by
  simpa only [c137,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause137
def c138 : List Lit := [(43, false), (35, false), (45, false), (87, false)]
theorem step138 (p : Nat → Bool) (h : Constraints p) : clause p c138 = true := by
  simpa only [c138,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause138
def c139 : List Lit := [(43, false), (35, false), (62, false), (87, false)]
theorem step139 (p : Nat → Bool) (h : Constraints p) : clause p c139 = true := by
  simpa only [c139,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause139
def c140 : List Lit := [(43, false), (44, false), (45, false), (62, false)]
theorem step140 (p : Nat → Bool) (h : Constraints p) : clause p c140 = true := by
  simpa only [c140,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause140
def c141 : List Lit := [(43, false), (44, false), (45, false), (87, false)]
theorem step141 (p : Nat → Bool) (h : Constraints p) : clause p c141 = true := by
  simpa only [c141,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause141
def c142 : List Lit := [(43, false), (45, false), (62, false), (87, false)]
theorem step142 (p : Nat → Bool) (h : Constraints p) : clause p c142 = true := by
  simpa only [c142,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause142
def c143 : List Lit := [(44, false), (43, false), (46, false), (51, false)]
theorem step143 (p : Nat → Bool) (h : Constraints p) : clause p c143 = true := by
  simpa only [c143,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause143
def c144 : List Lit := [(44, false), (150, true), (46, true), (51, true)]
theorem step144 (p : Nat → Bool) (h : Constraints p) : clause p c144 = true := by
  simpa only [c144,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause144
def c145 : List Lit := [(44, false), (150, true), (43, true), (51, true)]
theorem step145 (p : Nat → Bool) (h : Constraints p) : clause p c145 = true := by
  simpa only [c145,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause145
def c146 : List Lit := [(44, false), (150, true), (43, true), (46, true)]
theorem step146 (p : Nat → Bool) (h : Constraints p) : clause p c146 = true := by
  simpa only [c146,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause146
def c147 : List Lit := [(45, false), (151, true), (43, true), (46, true)]
theorem step147 (p : Nat → Bool) (h : Constraints p) : clause p c147 = true := by
  simpa only [c147,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause147
def c148 : List Lit := [(45, false), (151, true), (36, true), (46, true)]
theorem step148 (p : Nat → Bool) (h : Constraints p) : clause p c148 = true := by
  simpa only [c148,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause148
def c149 : List Lit := [(45, false), (151, true), (36, true), (43, true)]
theorem step149 (p : Nat → Bool) (h : Constraints p) : clause p c149 = true := by
  simpa only [c149,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause149
def c150 : List Lit := [(46, false), (42, false), (44, false), (45, false)]
theorem step150 (p : Nat → Bool) (h : Constraints p) : clause p c150 = true := by
  simpa only [c150,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause150
def c151 : List Lit := [(46, false), (152, true), (44, true), (45, true)]
theorem step151 (p : Nat → Bool) (h : Constraints p) : clause p c151 = true := by
  simpa only [c151,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause151
def c152 : List Lit := [(47, false), (37, false), (48, false), (49, false)]
theorem step152 (p : Nat → Bool) (h : Constraints p) : clause p c152 = true := by
  simpa only [c152,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause152
def c153 : List Lit := [(47, false), (153, true), (37, true), (49, true)]
theorem step153 (p : Nat → Bool) (h : Constraints p) : clause p c153 = true := by
  simpa only [c153,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause153
def c154 : List Lit := [(47, false), (153, true), (37, true), (48, true)]
theorem step154 (p : Nat → Bool) (h : Constraints p) : clause p c154 = true := by
  simpa only [c154,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause154
def c155 : List Lit := [(48, false), (38, true), (47, true), (50, true), (51, true)]
theorem step155 (p : Nat → Bool) (h : Constraints p) : clause p c155 = true := by
  simpa only [c155,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause155
def c156 : List Lit := [(48, false), (38, false), (47, false), (51, false)]
theorem step156 (p : Nat → Bool) (h : Constraints p) : clause p c156 = true := by
  simpa only [c156,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause156
def c157 : List Lit := [(48, false), (38, false), (50, false), (51, false)]
theorem step157 (p : Nat → Bool) (h : Constraints p) : clause p c157 = true := by
  simpa only [c157,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause157
def c158 : List Lit := [(48, false), (154, true), (47, true), (50, true), (51, true)]
theorem step158 (p : Nat → Bool) (h : Constraints p) : clause p c158 = true := by
  simpa only [c158,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause158
def c159 : List Lit := [(48, false), (154, true), (38, true), (50, true), (51, true)]
theorem step159 (p : Nat → Bool) (h : Constraints p) : clause p c159 = true := by
  simpa only [c159,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause159
def c160 : List Lit := [(48, false), (154, true), (38, true), (47, true), (50, true)]
theorem step160 (p : Nat → Bool) (h : Constraints p) : clause p c160 = true := by
  simpa only [c160,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block4.clause160
def c161 : List Lit := [(49, false), (155, true), (47, true), (50, true)]
theorem step161 (p : Nat → Bool) (h : Constraints p) : clause p c161 = true := by
  simpa only [c161,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause161
def c162 : List Lit := [(49, false), (155, true), (39, true), (50, true)]
theorem step162 (p : Nat → Bool) (h : Constraints p) : clause p c162 = true := by
  simpa only [c162,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause162
def c163 : List Lit := [(49, false), (155, true), (39, true), (47, true)]
theorem step163 (p : Nat → Bool) (h : Constraints p) : clause p c163 = true := by
  simpa only [c163,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause163
def c164 : List Lit := [(50, false), (40, false), (42, false), (48, false)]
theorem step164 (p : Nat → Bool) (h : Constraints p) : clause p c164 = true := by
  simpa only [c164,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause164
def c165 : List Lit := [(50, false), (40, false), (42, false), (49, false)]
theorem step165 (p : Nat → Bool) (h : Constraints p) : clause p c165 = true := by
  simpa only [c165,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause165
def c166 : List Lit := [(50, false), (40, false), (42, false), (63, false)]
theorem step166 (p : Nat → Bool) (h : Constraints p) : clause p c166 = true := by
  simpa only [c166,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause166
def c167 : List Lit := [(50, false), (40, false), (48, false), (49, false)]
theorem step167 (p : Nat → Bool) (h : Constraints p) : clause p c167 = true := by
  simpa only [c167,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause167
def c168 : List Lit := [(50, false), (40, false), (48, false), (63, false)]
theorem step168 (p : Nat → Bool) (h : Constraints p) : clause p c168 = true := by
  simpa only [c168,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause168
def c169 : List Lit := [(50, false), (40, false), (49, false), (63, false)]
theorem step169 (p : Nat → Bool) (h : Constraints p) : clause p c169 = true := by
  simpa only [c169,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause169
def c170 : List Lit := [(50, false), (42, false), (48, false), (49, false)]
theorem step170 (p : Nat → Bool) (h : Constraints p) : clause p c170 = true := by
  simpa only [c170,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause170
def c171 : List Lit := [(50, false), (42, false), (48, false), (63, false)]
theorem step171 (p : Nat → Bool) (h : Constraints p) : clause p c171 = true := by
  simpa only [c171,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause171
def c172 : List Lit := [(50, false), (42, false), (49, false), (63, false)]
theorem step172 (p : Nat → Bool) (h : Constraints p) : clause p c172 = true := by
  simpa only [c172,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause172
def c173 : List Lit := [(50, false), (48, false), (49, false), (63, false)]
theorem step173 (p : Nat → Bool) (h : Constraints p) : clause p c173 = true := by
  simpa only [c173,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause173
def c174 : List Lit := [(51, false), (157, true), (48, true)]
theorem step174 (p : Nat → Bool) (h : Constraints p) : clause p c174 = true := by
  simpa only [c174,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause174
def c175 : List Lit := [(51, false), (157, true), (44, true)]
theorem step175 (p : Nat → Bool) (h : Constraints p) : clause p c175 = true := by
  simpa only [c175,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause175
def c176 : List Lit := [(52, false), (158, true), (22, true), (58, true), (95, true)]
theorem step176 (p : Nat → Bool) (h : Constraints p) : clause p c176 = true := by
  simpa only [c176,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause176
def c177 : List Lit := [(52, false), (158, true), (22, true), (54, true), (58, true)]
theorem step177 (p : Nat → Bool) (h : Constraints p) : clause p c177 = true := by
  simpa only [c177,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause177
def c178 : List Lit := [(159, false), (53, true)]
theorem step178 (p : Nat → Bool) (h : Constraints p) : clause p c178 = true := by
  simpa only [c178,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause178
def c179 : List Lit := [(53, false), (56, true)]
theorem step179 (p : Nat → Bool) (h : Constraints p) : clause p c179 = true := by
  simpa only [c179,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause179
def c180 : List Lit := [(53, false), (159, true)]
theorem step180 (p : Nat → Bool) (h : Constraints p) : clause p c180 = true := by
  simpa only [c180,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause180
def c181 : List Lit := [(54, false), (160, true), (55, true)]
theorem step181 (p : Nat → Bool) (h : Constraints p) : clause p c181 = true := by
  simpa only [c181,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause181
def c182 : List Lit := [(54, false), (160, true), (52, true)]
theorem step182 (p : Nat → Bool) (h : Constraints p) : clause p c182 = true := by
  simpa only [c182,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause182
def c183 : List Lit := [(161, false), (55, true)]
theorem step183 (p : Nat → Bool) (h : Constraints p) : clause p c183 = true := by
  simpa only [c183,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause183
def c184 : List Lit := [(55, false), (54, true), (56, true)]
theorem step184 (p : Nat → Bool) (h : Constraints p) : clause p c184 = true := by
  simpa only [c184,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause184
def c185 : List Lit := [(55, false), (161, true), (56, true)]
theorem step185 (p : Nat → Bool) (h : Constraints p) : clause p c185 = true := by
  simpa only [c185,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause185
def c186 : List Lit := [(55, false), (161, true), (54, true)]
theorem step186 (p : Nat → Bool) (h : Constraints p) : clause p c186 = true := by
  simpa only [c186,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause186
def c187 : List Lit := [(56, false), (30, false), (53, false), (55, false)]
theorem step187 (p : Nat → Bool) (h : Constraints p) : clause p c187 = true := by
  simpa only [c187,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause187
def c188 : List Lit := [(56, false), (30, false), (53, false), (63, false)]
theorem step188 (p : Nat → Bool) (h : Constraints p) : clause p c188 = true := by
  simpa only [c188,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause188
def c189 : List Lit := [(56, false), (30, false), (53, false), (103, false)]
theorem step189 (p : Nat → Bool) (h : Constraints p) : clause p c189 = true := by
  simpa only [c189,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause189
def c190 : List Lit := [(56, false), (30, false), (55, false), (63, false)]
theorem step190 (p : Nat → Bool) (h : Constraints p) : clause p c190 = true := by
  simpa only [c190,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause190
def c191 : List Lit := [(56, false), (30, false), (55, false), (103, false)]
theorem step191 (p : Nat → Bool) (h : Constraints p) : clause p c191 = true := by
  simpa only [c191,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause191
def c192 : List Lit := [(56, false), (30, false), (63, false), (103, false)]
theorem step192 (p : Nat → Bool) (h : Constraints p) : clause p c192 = true := by
  simpa only [c192,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block5.clause192
def c193 : List Lit := [(56, false), (53, false), (55, false), (63, false)]
theorem step193 (p : Nat → Bool) (h : Constraints p) : clause p c193 = true := by
  simpa only [c193,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause193
def c194 : List Lit := [(56, false), (53, false), (55, false), (103, false)]
theorem step194 (p : Nat → Bool) (h : Constraints p) : clause p c194 = true := by
  simpa only [c194,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause194
def c195 : List Lit := [(56, false), (53, false), (63, false), (103, false)]
theorem step195 (p : Nat → Bool) (h : Constraints p) : clause p c195 = true := by
  simpa only [c195,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause195
def c196 : List Lit := [(56, false), (55, false), (63, false), (103, false)]
theorem step196 (p : Nat → Bool) (h : Constraints p) : clause p c196 = true := by
  simpa only [c196,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause196
def c197 : List Lit := [(56, false), (162, true), (53, true), (55, true), (63, true), (103, true)]
theorem step197 (p : Nat → Bool) (h : Constraints p) : clause p c197 = true := by
  simpa only [c197,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause197
def c198 : List Lit := [(56, false), (162, true), (30, true), (53, true), (63, true), (103, true)]
theorem step198 (p : Nat → Bool) (h : Constraints p) : clause p c198 = true := by
  simpa only [c198,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause198
def c199 : List Lit := [(56, false), (162, true), (30, true), (53, true), (55, true), (103, true)]
theorem step199 (p : Nat → Bool) (h : Constraints p) : clause p c199 = true := by
  simpa only [c199,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause199
def c200 : List Lit := [(56, false), (162, true), (30, true), (53, true), (55, true), (63, true)]
theorem step200 (p : Nat → Bool) (h : Constraints p) : clause p c200 = true := by
  simpa only [c200,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause200
def c201 : List Lit := [(57, false), (34, false), (58, false), (60, false)]
theorem step201 (p : Nat → Bool) (h : Constraints p) : clause p c201 = true := by
  simpa only [c201,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause201
def c202 : List Lit := [(57, false), (163, true), (58, true), (60, true)]
theorem step202 (p : Nat → Bool) (h : Constraints p) : clause p c202 = true := by
  simpa only [c202,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause202
def c203 : List Lit := [(57, false), (163, true), (34, true), (60, true)]
theorem step203 (p : Nat → Bool) (h : Constraints p) : clause p c203 = true := by
  simpa only [c203,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause203
def c204 : List Lit := [(57, false), (163, true), (34, true), (58, true)]
theorem step204 (p : Nat → Bool) (h : Constraints p) : clause p c204 = true := by
  simpa only [c204,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause204
def c205 : List Lit := [(58, false), (37, false), (52, false), (57, false)]
theorem step205 (p : Nat → Bool) (h : Constraints p) : clause p c205 = true := by
  simpa only [c205,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause205
def c206 : List Lit := [(58, false), (164, true), (52, true), (57, true)]
theorem step206 (p : Nat → Bool) (h : Constraints p) : clause p c206 = true := by
  simpa only [c206,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause206
def c207 : List Lit := [(58, false), (164, true), (37, true), (57, true)]
theorem step207 (p : Nat → Bool) (h : Constraints p) : clause p c207 = true := by
  simpa only [c207,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause207
def c208 : List Lit := [(58, false), (164, true), (37, true), (52, true)]
theorem step208 (p : Nat → Bool) (h : Constraints p) : clause p c208 = true := by
  simpa only [c208,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause208
def c209 : List Lit := [(59, false), (165, true), (41, true)]
theorem step209 (p : Nat → Bool) (h : Constraints p) : clause p c209 = true := by
  simpa only [c209,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause209
def c210 : List Lit := [(60, false), (57, false), (61, false), (62, false)]
theorem step210 (p : Nat → Bool) (h : Constraints p) : clause p c210 = true := by
  simpa only [c210,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause210
def c211 : List Lit := [(60, false), (166, true), (61, true), (62, true)]
theorem step211 (p : Nat → Bool) (h : Constraints p) : clause p c211 = true := by
  simpa only [c211,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause211
def c212 : List Lit := [(60, false), (166, true), (57, true), (61, true)]
theorem step212 (p : Nat → Bool) (h : Constraints p) : clause p c212 = true := by
  simpa only [c212,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause212
def c213 : List Lit := [(61, false), (60, true)]
theorem step213 (p : Nat → Bool) (h : Constraints p) : clause p c213 = true := by
  simpa only [c213,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause213
def c214 : List Lit := [(61, false), (167, true)]
theorem step214 (p : Nat → Bool) (h : Constraints p) : clause p c214 = true := by
  simpa only [c214,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause214
def c215 : List Lit := [(62, false), (43, false), (60, false), (64, false)]
theorem step215 (p : Nat → Bool) (h : Constraints p) : clause p c215 = true := by
  simpa only [c215,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause215
def c216 : List Lit := [(62, false), (168, true), (43, true), (64, true)]
theorem step216 (p : Nat → Bool) (h : Constraints p) : clause p c216 = true := by
  simpa only [c216,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause216
def c217 : List Lit := [(62, false), (168, true), (43, true), (60, true)]
theorem step217 (p : Nat → Bool) (h : Constraints p) : clause p c217 = true := by
  simpa only [c217,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause217
def c218 : List Lit := [(63, false), (169, true), (50, true), (66, true)]
theorem step218 (p : Nat → Bool) (h : Constraints p) : clause p c218 = true := by
  simpa only [c218,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause218
def c219 : List Lit := [(63, false), (169, true), (50, true), (56, true)]
theorem step219 (p : Nat → Bool) (h : Constraints p) : clause p c219 = true := by
  simpa only [c219,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause219
def c220 : List Lit := [(64, false), (170, true), (65, true)]
theorem step220 (p : Nat → Bool) (h : Constraints p) : clause p c220 = true := by
  simpa only [c220,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause220
def c221 : List Lit := [(64, false), (170, true), (62, true)]
theorem step221 (p : Nat → Bool) (h : Constraints p) : clause p c221 = true := by
  simpa only [c221,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause221
def c222 : List Lit := [(65, false), (59, false), (64, false), (66, false)]
theorem step222 (p : Nat → Bool) (h : Constraints p) : clause p c222 = true := by
  simpa only [c222,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause222
def c223 : List Lit := [(65, false), (171, true), (64, true), (66, true)]
theorem step223 (p : Nat → Bool) (h : Constraints p) : clause p c223 = true := by
  simpa only [c223,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause223
def c224 : List Lit := [(65, false), (171, true), (59, true), (66, true)]
theorem step224 (p : Nat → Bool) (h : Constraints p) : clause p c224 = true := by
  simpa only [c224,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block6.clause224
def c225 : List Lit := [(65, false), (171, true), (59, true), (64, true)]
theorem step225 (p : Nat → Bool) (h : Constraints p) : clause p c225 = true := by
  simpa only [c225,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause225
def c226 : List Lit := [(66, false), (172, true), (65, true)]
theorem step226 (p : Nat → Bool) (h : Constraints p) : clause p c226 = true := by
  simpa only [c226,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause226
def c227 : List Lit := [(66, false), (172, true), (63, true)]
theorem step227 (p : Nat → Bool) (h : Constraints p) : clause p c227 = true := by
  simpa only [c227,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause227
def c228 : List Lit := [(67, false), (173, true), (4, true)]
theorem step228 (p : Nat → Bool) (h : Constraints p) : clause p c228 = true := by
  simpa only [c228,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause228
def c229 : List Lit := [(174, false), (68, true)]
theorem step229 (p : Nat → Bool) (h : Constraints p) : clause p c229 = true := by
  simpa only [c229,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause229
def c230 : List Lit := [(174, false), (72, false), (80, false)]
theorem step230 (p : Nat → Bool) (h : Constraints p) : clause p c230 = true := by
  simpa only [c230,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause230
def c231 : List Lit := [(68, false), (174, true), (67, true), (80, true)]
theorem step231 (p : Nat → Bool) (h : Constraints p) : clause p c231 = true := by
  simpa only [c231,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause231
def c232 : List Lit := [(69, false), (175, true), (73, true)]
theorem step232 (p : Nat → Bool) (h : Constraints p) : clause p c232 = true := by
  simpa only [c232,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause232
def c233 : List Lit := [(70, false), (176, true), (69, true)]
theorem step233 (p : Nat → Bool) (h : Constraints p) : clause p c233 = true := by
  simpa only [c233,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause233
def c234 : List Lit := [(71, false), (177, true), (70, true)]
theorem step234 (p : Nat → Bool) (h : Constraints p) : clause p c234 = true := by
  simpa only [c234,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause234
def c235 : List Lit := [(72, false), (178, true), (68, true)]
theorem step235 (p : Nat → Bool) (h : Constraints p) : clause p c235 = true := by
  simpa only [c235,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause235
def c236 : List Lit := [(73, false), (179, true), (72, true)]
theorem step236 (p : Nat → Bool) (h : Constraints p) : clause p c236 = true := by
  simpa only [c236,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause236
def c237 : List Lit := [(74, false), (75, true)]
theorem step237 (p : Nat → Bool) (h : Constraints p) : clause p c237 = true := by
  simpa only [c237,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause237
def c238 : List Lit := [(74, true)]
theorem step238 (p : Nat → Bool) (h : Constraints p) : clause p c238 = true := by
  simpa only [c238,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause238
def c239 : List Lit := [(75, false), (181, true), (71, true)]
theorem step239 (p : Nat → Bool) (h : Constraints p) : clause p c239 = true := by
  simpa only [c239,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause239
def c240 : List Lit := [(76, false), (34, false), (80, false), (84, false)]
theorem step240 (p : Nat → Bool) (h : Constraints p) : clause p c240 = true := by
  simpa only [c240,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause240
def c241 : List Lit := [(76, false), (77, false), (80, false), (84, false)]
theorem step241 (p : Nat → Bool) (h : Constraints p) : clause p c241 = true := by
  simpa only [c241,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause241
def c242 : List Lit := [(76, false), (182, true), (77, true), (80, true), (84, true)]
theorem step242 (p : Nat → Bool) (h : Constraints p) : clause p c242 = true := by
  simpa only [c242,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause242
def c243 : List Lit := [(76, false), (182, true), (34, true), (80, true), (84, true)]
theorem step243 (p : Nat → Bool) (h : Constraints p) : clause p c243 = true := by
  simpa only [c243,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause243
def c244 : List Lit := [(77, false), (76, false), (78, false), (81, false)]
theorem step244 (p : Nat → Bool) (h : Constraints p) : clause p c244 = true := by
  simpa only [c244,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause244
def c245 : List Lit := [(77, false), (183, true), (76, true), (81, true)]
theorem step245 (p : Nat → Bool) (h : Constraints p) : clause p c245 = true := by
  simpa only [c245,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause245
def c246 : List Lit := [(78, false), (184, true), (77, true)]
theorem step246 (p : Nat → Bool) (h : Constraints p) : clause p c246 = true := by
  simpa only [c246,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause246
def c247 : List Lit := [(79, false), (185, true), (78, true)]
theorem step247 (p : Nat → Bool) (h : Constraints p) : clause p c247 = true := by
  simpa only [c247,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause247
def c248 : List Lit := [(80, false), (37, false), (68, false), (76, false)]
theorem step248 (p : Nat → Bool) (h : Constraints p) : clause p c248 = true := by
  simpa only [c248,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause248
def c249 : List Lit := [(80, false), (37, false), (68, false), (81, false)]
theorem step249 (p : Nat → Bool) (h : Constraints p) : clause p c249 = true := by
  simpa only [c249,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause249
def c250 : List Lit := [(80, false), (68, false), (76, false), (81, false)]
theorem step250 (p : Nat → Bool) (h : Constraints p) : clause p c250 = true := by
  simpa only [c250,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause250
def c251 : List Lit := [(81, false), (38, false), (77, false), (80, false)]
theorem step251 (p : Nat → Bool) (h : Constraints p) : clause p c251 = true := by
  simpa only [c251,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause251
def c252 : List Lit := [(81, false), (187, true), (77, true), (80, true)]
theorem step252 (p : Nat → Bool) (h : Constraints p) : clause p c252 = true := by
  simpa only [c252,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause252
def c253 : List Lit := [(81, false), (187, true), (38, true), (80, true)]
theorem step253 (p : Nat → Bool) (h : Constraints p) : clause p c253 = true := by
  simpa only [c253,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause253
def c254 : List Lit := [(82, false), (41, false), (83, false), (89, false)]
theorem step254 (p : Nat → Bool) (h : Constraints p) : clause p c254 = true := by
  simpa only [c254,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause254
def c255 : List Lit := [(83, false), (189, true), (79, true), (90, true)]
theorem step255 (p : Nat → Bool) (h : Constraints p) : clause p c255 = true := by
  simpa only [c255,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause255
def c256 : List Lit := [(83, false), (189, true), (79, true), (82, true)]
theorem step256 (p : Nat → Bool) (h : Constraints p) : clause p c256 = true := by
  simpa only [c256,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block7.clause256
def c257 : List Lit := [(84, false), (76, false), (85, false), (87, false)]
theorem step257 (p : Nat → Bool) (h : Constraints p) : clause p c257 = true := by
  simpa only [c257,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause257
def c258 : List Lit := [(84, false), (190, true), (76, true), (87, true)]
theorem step258 (p : Nat → Bool) (h : Constraints p) : clause p c258 = true := by
  simpa only [c258,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause258
def c259 : List Lit := [(84, false), (190, true), (76, true), (85, true)]
theorem step259 (p : Nat → Bool) (h : Constraints p) : clause p c259 = true := by
  simpa only [c259,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause259
def c260 : List Lit := [(85, false), (84, true), (86, true)]
theorem step260 (p : Nat → Bool) (h : Constraints p) : clause p c260 = true := by
  simpa only [c260,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause260
def c261 : List Lit := [(191, false), (84, false), (86, false)]
theorem step261 (p : Nat → Bool) (h : Constraints p) : clause p c261 = true := by
  simpa only [c261,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause261
def c262 : List Lit := [(85, false), (191, true), (86, true)]
theorem step262 (p : Nat → Bool) (h : Constraints p) : clause p c262 = true := by
  simpa only [c262,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause262
def c263 : List Lit := [(85, false), (191, true), (84, true)]
theorem step263 (p : Nat → Bool) (h : Constraints p) : clause p c263 = true := by
  simpa only [c263,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause263
def c264 : List Lit := [(86, false), (192, true), (85, true)]
theorem step264 (p : Nat → Bool) (h : Constraints p) : clause p c264 = true := by
  simpa only [c264,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause264
def c265 : List Lit := [(86, false), (192, true), (42, true)]
theorem step265 (p : Nat → Bool) (h : Constraints p) : clause p c265 = true := by
  simpa only [c265,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause265
def c266 : List Lit := [(87, false), (43, false), (84, false), (88, false)]
theorem step266 (p : Nat → Bool) (h : Constraints p) : clause p c266 = true := by
  simpa only [c266,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause266
def c267 : List Lit := [(87, false), (193, true), (43, true), (84, true)]
theorem step267 (p : Nat → Bool) (h : Constraints p) : clause p c267 = true := by
  simpa only [c267,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause267
def c268 : List Lit := [(88, false), (194, true), (87, true)]
theorem step268 (p : Nat → Bool) (h : Constraints p) : clause p c268 = true := by
  simpa only [c268,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause268
def c269 : List Lit := [(89, false), (195, true), (88, true), (90, true)]
theorem step269 (p : Nat → Bool) (h : Constraints p) : clause p c269 = true := by
  simpa only [c269,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause269
def c270 : List Lit := [(89, false), (195, true), (82, true), (88, true)]
theorem step270 (p : Nat → Bool) (h : Constraints p) : clause p c270 = true := by
  simpa only [c270,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause270
def c271 : List Lit := [(90, false), (196, true), (83, true)]
theorem step271 (p : Nat → Bool) (h : Constraints p) : clause p c271 = true := by
  simpa only [c271,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause271
def c272 : List Lit := [(91, false), (92, false), (95, false), (99, false)]
theorem step272 (p : Nat → Bool) (h : Constraints p) : clause p c272 = true := by
  simpa only [c272,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause272
def c273 : List Lit := [(92, false), (91, false), (93, false), (96, false)]
theorem step273 (p : Nat → Bool) (h : Constraints p) : clause p c273 = true := by
  simpa only [c273,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause273
def c274 : List Lit := [(92, false), (198, true), (91, true), (96, true)]
theorem step274 (p : Nat → Bool) (h : Constraints p) : clause p c274 = true := by
  simpa only [c274,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause274
def c275 : List Lit := [(92, false), (198, true), (91, true), (93, true)]
theorem step275 (p : Nat → Bool) (h : Constraints p) : clause p c275 = true := by
  simpa only [c275,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause275
def c276 : List Lit := [(93, false), (199, true), (94, true)]
theorem step276 (p : Nat → Bool) (h : Constraints p) : clause p c276 = true := by
  simpa only [c276,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause276
def c277 : List Lit := [(93, false), (199, true), (92, true)]
theorem step277 (p : Nat → Bool) (h : Constraints p) : clause p c277 = true := by
  simpa only [c277,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause277
def c278 : List Lit := [(94, false), (200, true), (98, true)]
theorem step278 (p : Nat → Bool) (h : Constraints p) : clause p c278 = true := by
  simpa only [c278,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause278
def c279 : List Lit := [(94, false), (200, true), (93, true)]
theorem step279 (p : Nat → Bool) (h : Constraints p) : clause p c279 = true := by
  simpa only [c279,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause279
def c280 : List Lit := [(95, false), (52, false), (91, false), (96, false)]
theorem step280 (p : Nat → Bool) (h : Constraints p) : clause p c280 = true := by
  simpa only [c280,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause280
def c281 : List Lit := [(95, false), (201, true), (52, true), (91, true)]
theorem step281 (p : Nat → Bool) (h : Constraints p) : clause p c281 = true := by
  simpa only [c281,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause281
def c282 : List Lit := [(96, false), (202, true), (95, true)]
theorem step282 (p : Nat → Bool) (h : Constraints p) : clause p c282 = true := by
  simpa only [c282,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause282
def c283 : List Lit := [(96, false), (202, true), (92, true)]
theorem step283 (p : Nat → Bool) (h : Constraints p) : clause p c283 = true := by
  simpa only [c283,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause283
def c284 : List Lit := [(97, false), (203, true), (98, true)]
theorem step284 (p : Nat → Bool) (h : Constraints p) : clause p c284 = true := by
  simpa only [c284,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause284
def c285 : List Lit := [(98, false), (204, true), (94, true), (106, true)]
theorem step285 (p : Nat → Bool) (h : Constraints p) : clause p c285 = true := by
  simpa only [c285,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause285
def c286 : List Lit := [(99, false), (91, false), (100, false), (102, false)]
theorem step286 (p : Nat → Bool) (h : Constraints p) : clause p c286 = true := by
  simpa only [c286,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause286
def c287 : List Lit := [(99, false), (205, true), (91, true), (102, true)]
theorem step287 (p : Nat → Bool) (h : Constraints p) : clause p c287 = true := by
  simpa only [c287,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause287
def c288 : List Lit := [(99, false), (205, true), (91, true), (100, true)]
theorem step288 (p : Nat → Bool) (h : Constraints p) : clause p c288 = true := by
  simpa only [c288,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block8.clause288
def c289 : List Lit := [(100, false), (206, true), (101, true)]
theorem step289 (p : Nat → Bool) (h : Constraints p) : clause p c289 = true := by
  simpa only [c289,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause289
def c290 : List Lit := [(100, false), (206, true), (99, true)]
theorem step290 (p : Nat → Bool) (h : Constraints p) : clause p c290 = true := by
  simpa only [c290,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause290
def c291 : List Lit := [(101, false), (207, true), (103, true)]
theorem step291 (p : Nat → Bool) (h : Constraints p) : clause p c291 = true := by
  simpa only [c291,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause291
def c292 : List Lit := [(101, false), (207, true), (100, true)]
theorem step292 (p : Nat → Bool) (h : Constraints p) : clause p c292 = true := by
  simpa only [c292,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause292
def c293 : List Lit := [(102, false), (208, true), (104, true)]
theorem step293 (p : Nat → Bool) (h : Constraints p) : clause p c293 = true := by
  simpa only [c293,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause293
def c294 : List Lit := [(102, false), (208, true), (99, true)]
theorem step294 (p : Nat → Bool) (h : Constraints p) : clause p c294 = true := by
  simpa only [c294,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause294
def c295 : List Lit := [(103, false), (209, true), (56, true), (106, true)]
theorem step295 (p : Nat → Bool) (h : Constraints p) : clause p c295 = true := by
  simpa only [c295,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause295
def c296 : List Lit := [(103, false), (209, true), (56, true), (101, true)]
theorem step296 (p : Nat → Bool) (h : Constraints p) : clause p c296 = true := by
  simpa only [c296,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause296
def c297 : List Lit := [(104, false), (210, true), (105, true)]
theorem step297 (p : Nat → Bool) (h : Constraints p) : clause p c297 = true := by
  simpa only [c297,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause297
def c298 : List Lit := [(104, false), (210, true), (102, true)]
theorem step298 (p : Nat → Bool) (h : Constraints p) : clause p c298 = true := by
  simpa only [c298,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause298
def c299 : List Lit := [(105, false), (211, true), (97, true), (104, true)]
theorem step299 (p : Nat → Bool) (h : Constraints p) : clause p c299 = true := by
  simpa only [c299,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause299
def c300 : List Lit := [(106, false), (98, false), (103, false), (105, false)]
theorem step300 (p : Nat → Bool) (h : Constraints p) : clause p c300 = true := by
  simpa only [c300,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause300
def c301 : List Lit := [(107, false)]
theorem step301 (p : Nat → Bool) (h : Constraints p) : clause p c301 = true := by
  simpa only [c301,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause301
def c302 : List Lit := [(109, false)]
theorem step302 (p : Nat → Bool) (h : Constraints p) : clause p c302 = true := by
  simpa only [c302,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause302
def c303 : List Lit := [(111, false)]
theorem step303 (p : Nat → Bool) (h : Constraints p) : clause p c303 = true := by
  simpa only [c303,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause303
def c304 : List Lit := [(112, false)]
theorem step304 (p : Nat → Bool) (h : Constraints p) : clause p c304 = true := by
  simpa only [c304,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause304
def c305 : List Lit := [(118, false)]
theorem step305 (p : Nat → Bool) (h : Constraints p) : clause p c305 = true := by
  simpa only [c305,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause305
def c306 : List Lit := [(119, false)]
theorem step306 (p : Nat → Bool) (h : Constraints p) : clause p c306 = true := by
  simpa only [c306,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause306
def c307 : List Lit := [(122, false)]
theorem step307 (p : Nat → Bool) (h : Constraints p) : clause p c307 = true := by
  simpa only [c307,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause307
def c308 : List Lit := [(123, false)]
theorem step308 (p : Nat → Bool) (h : Constraints p) : clause p c308 = true := by
  simpa only [c308,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause308
def c309 : List Lit := [(125, false)]
theorem step309 (p : Nat → Bool) (h : Constraints p) : clause p c309 = true := by
  simpa only [c309,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause309
def c310 : List Lit := [(127, false)]
theorem step310 (p : Nat → Bool) (h : Constraints p) : clause p c310 = true := by
  simpa only [c310,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause310
def c311 : List Lit := [(128, false)]
theorem step311 (p : Nat → Bool) (h : Constraints p) : clause p c311 = true := by
  simpa only [c311,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause311
def c312 : List Lit := [(130, false)]
theorem step312 (p : Nat → Bool) (h : Constraints p) : clause p c312 = true := by
  simpa only [c312,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause312
def c313 : List Lit := [(132, false)]
theorem step313 (p : Nat → Bool) (h : Constraints p) : clause p c313 = true := by
  simpa only [c313,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause313
def c314 : List Lit := [(134, false)]
theorem step314 (p : Nat → Bool) (h : Constraints p) : clause p c314 = true := by
  simpa only [c314,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause314
def c315 : List Lit := [(137, false)]
theorem step315 (p : Nat → Bool) (h : Constraints p) : clause p c315 = true := by
  simpa only [c315,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause315
def c316 : List Lit := [(139, false)]
theorem step316 (p : Nat → Bool) (h : Constraints p) : clause p c316 = true := by
  simpa only [c316,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause316
def c317 : List Lit := [(140, false)]
theorem step317 (p : Nat → Bool) (h : Constraints p) : clause p c317 = true := by
  simpa only [c317,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause317
def c318 : List Lit := [(142, false)]
theorem step318 (p : Nat → Bool) (h : Constraints p) : clause p c318 = true := by
  simpa only [c318,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause318
def c319 : List Lit := [(144, false)]
theorem step319 (p : Nat → Bool) (h : Constraints p) : clause p c319 = true := by
  simpa only [c319,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause319
def c320 : List Lit := [(145, false)]
theorem step320 (p : Nat → Bool) (h : Constraints p) : clause p c320 = true := by
  simpa only [c320,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block9.clause320
def c321 : List Lit := [(149, false)]
theorem step321 (p : Nat → Bool) (h : Constraints p) : clause p c321 = true := by
  simpa only [c321,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause321
def c322 : List Lit := [(152, false)]
theorem step322 (p : Nat → Bool) (h : Constraints p) : clause p c322 = true := by
  simpa only [c322,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause322
def c323 : List Lit := [(153, false)]
theorem step323 (p : Nat → Bool) (h : Constraints p) : clause p c323 = true := by
  simpa only [c323,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause323
def c324 : List Lit := [(156, false)]
theorem step324 (p : Nat → Bool) (h : Constraints p) : clause p c324 = true := by
  simpa only [c324,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause324
def c325 : List Lit := [(157, false)]
theorem step325 (p : Nat → Bool) (h : Constraints p) : clause p c325 = true := by
  simpa only [c325,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause325
def c326 : List Lit := [(160, false)]
theorem step326 (p : Nat → Bool) (h : Constraints p) : clause p c326 = true := by
  simpa only [c326,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause326
def c327 : List Lit := [(162, false)]
theorem step327 (p : Nat → Bool) (h : Constraints p) : clause p c327 = true := by
  simpa only [c327,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause327
def c328 : List Lit := [(164, false)]
theorem step328 (p : Nat → Bool) (h : Constraints p) : clause p c328 = true := by
  simpa only [c328,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause328
def c329 : List Lit := [(165, false)]
theorem step329 (p : Nat → Bool) (h : Constraints p) : clause p c329 = true := by
  simpa only [c329,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause329
def c330 : List Lit := [(166, false)]
theorem step330 (p : Nat → Bool) (h : Constraints p) : clause p c330 = true := by
  simpa only [c330,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause330
def c331 : List Lit := [(170, false)]
theorem step331 (p : Nat → Bool) (h : Constraints p) : clause p c331 = true := by
  simpa only [c331,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause331
def c332 : List Lit := [(172, false)]
theorem step332 (p : Nat → Bool) (h : Constraints p) : clause p c332 = true := by
  simpa only [c332,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause332
def c333 : List Lit := [(173, false)]
theorem step333 (p : Nat → Bool) (h : Constraints p) : clause p c333 = true := by
  simpa only [c333,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause333
def c334 : List Lit := [(175, false)]
theorem step334 (p : Nat → Bool) (h : Constraints p) : clause p c334 = true := by
  simpa only [c334,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause334
def c335 : List Lit := [(177, false)]
theorem step335 (p : Nat → Bool) (h : Constraints p) : clause p c335 = true := by
  simpa only [c335,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause335
def c336 : List Lit := [(178, false)]
theorem step336 (p : Nat → Bool) (h : Constraints p) : clause p c336 = true := by
  simpa only [c336,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause336
def c337 : List Lit := [(183, false)]
theorem step337 (p : Nat → Bool) (h : Constraints p) : clause p c337 = true := by
  simpa only [c337,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause337
def c338 : List Lit := [(185, false)]
theorem step338 (p : Nat → Bool) (h : Constraints p) : clause p c338 = true := by
  simpa only [c338,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause338
def c339 : List Lit := [(186, false)]
theorem step339 (p : Nat → Bool) (h : Constraints p) : clause p c339 = true := by
  simpa only [c339,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause339
def c340 : List Lit := [(188, false)]
theorem step340 (p : Nat → Bool) (h : Constraints p) : clause p c340 = true := by
  simpa only [c340,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause340
def c341 : List Lit := [(190, false)]
theorem step341 (p : Nat → Bool) (h : Constraints p) : clause p c341 = true := by
  simpa only [c341,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause341
def c342 : List Lit := [(192, false)]
theorem step342 (p : Nat → Bool) (h : Constraints p) : clause p c342 = true := by
  simpa only [c342,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause342
def c343 : List Lit := [(194, false)]
theorem step343 (p : Nat → Bool) (h : Constraints p) : clause p c343 = true := by
  simpa only [c343,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause343
def c344 : List Lit := [(196, false)]
theorem step344 (p : Nat → Bool) (h : Constraints p) : clause p c344 = true := by
  simpa only [c344,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause344
def c345 : List Lit := [(198, false)]
theorem step345 (p : Nat → Bool) (h : Constraints p) : clause p c345 = true := by
  simpa only [c345,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause345
def c346 : List Lit := [(200, false)]
theorem step346 (p : Nat → Bool) (h : Constraints p) : clause p c346 = true := by
  simpa only [c346,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause346
def c347 : List Lit := [(201, false)]
theorem step347 (p : Nat → Bool) (h : Constraints p) : clause p c347 = true := by
  simpa only [c347,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause347
def c348 : List Lit := [(203, false)]
theorem step348 (p : Nat → Bool) (h : Constraints p) : clause p c348 = true := by
  simpa only [c348,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause348
def c349 : List Lit := [(205, false)]
theorem step349 (p : Nat → Bool) (h : Constraints p) : clause p c349 = true := by
  simpa only [c349,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause349
def c350 : List Lit := [(207, false)]
theorem step350 (p : Nat → Bool) (h : Constraints p) : clause p c350 = true := by
  simpa only [c350,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause350
def c351 : List Lit := [(210, false)]
theorem step351 (p : Nat → Bool) (h : Constraints p) : clause p c351 = true := by
  simpa only [c351,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause351
def c352 : List Lit := [(212, false)]
theorem step352 (p : Nat → Bool) (h : Constraints p) : clause p c352 = true := by
  simpa only [c352,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block10.clause352
def c353 : List Lit := [(108, false), (213, true)]
theorem step353 (p : Nat → Bool) (h : Constraints p) : clause p c353 = true := by
  simpa only [c353,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause353
def c354 : List Lit := [(213, false), (215, true)]
theorem step354 (p : Nat → Bool) (h : Constraints p) : clause p c354 = true := by
  simpa only [c354,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause354
def c355 : List Lit := [(110, false), (219, true)]
theorem step355 (p : Nat → Bool) (h : Constraints p) : clause p c355 = true := by
  simpa only [c355,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause355
def c356 : List Lit := [(219, false), (221, true)]
theorem step356 (p : Nat → Bool) (h : Constraints p) : clause p c356 = true := by
  simpa only [c356,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause356
def c357 : List Lit := [(215, false), (221, true)]
theorem step357 (p : Nat → Bool) (h : Constraints p) : clause p c357 = true := by
  simpa only [c357,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause357
def c358 : List Lit := [(115, false), (223, true)]
theorem step358 (p : Nat → Bool) (h : Constraints p) : clause p c358 = true := by
  simpa only [c358,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause358
def c359 : List Lit := [(114, false), (223, true)]
theorem step359 (p : Nat → Bool) (h : Constraints p) : clause p c359 = true := by
  simpa only [c359,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause359
def c360 : List Lit := [(223, false), (225, true)]
theorem step360 (p : Nat → Bool) (h : Constraints p) : clause p c360 = true := by
  simpa only [c360,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause360
def c361 : List Lit := [(113, false), (225, true)]
theorem step361 (p : Nat → Bool) (h : Constraints p) : clause p c361 = true := by
  simpa only [c361,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause361
def c362 : List Lit := [(117, false), (227, true)]
theorem step362 (p : Nat → Bool) (h : Constraints p) : clause p c362 = true := by
  simpa only [c362,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause362
def c363 : List Lit := [(116, false), (227, true)]
theorem step363 (p : Nat → Bool) (h : Constraints p) : clause p c363 = true := by
  simpa only [c363,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause363
def c364 : List Lit := [(116, false), (117, false), (228, true)]
theorem step364 (p : Nat → Bool) (h : Constraints p) : clause p c364 = true := by
  simpa only [c364,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause364
def c365 : List Lit := [(227, false), (231, true)]
theorem step365 (p : Nat → Bool) (h : Constraints p) : clause p c365 = true := by
  simpa only [c365,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause365
def c366 : List Lit := [(228, false), (232, true)]
theorem step366 (p : Nat → Bool) (h : Constraints p) : clause p c366 = true := by
  simpa only [c366,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause366
def c367 : List Lit := [(231, false), (233, true)]
theorem step367 (p : Nat → Bool) (h : Constraints p) : clause p c367 = true := by
  simpa only [c367,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause367
def c368 : List Lit := [(232, false), (234, true)]
theorem step368 (p : Nat → Bool) (h : Constraints p) : clause p c368 = true := by
  simpa only [c368,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause368
def c369 : List Lit := [(225, false), (233, true)]
theorem step369 (p : Nat → Bool) (h : Constraints p) : clause p c369 = true := by
  simpa only [c369,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause369
def c370 : List Lit := [(225, false), (231, false), (234, true)]
theorem step370 (p : Nat → Bool) (h : Constraints p) : clause p c370 = true := by
  simpa only [c370,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause370
def c371 : List Lit := [(233, false), (235, true)]
theorem step371 (p : Nat → Bool) (h : Constraints p) : clause p c371 = true := by
  simpa only [c371,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause371
def c372 : List Lit := [(234, false), (236, true)]
theorem step372 (p : Nat → Bool) (h : Constraints p) : clause p c372 = true := by
  simpa only [c372,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause372
def c373 : List Lit := [(221, false), (235, true)]
theorem step373 (p : Nat → Bool) (h : Constraints p) : clause p c373 = true := by
  simpa only [c373,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause373
def c374 : List Lit := [(221, false), (233, false), (236, true)]
theorem step374 (p : Nat → Bool) (h : Constraints p) : clause p c374 = true := by
  simpa only [c374,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause374
def c375 : List Lit := [(121, false), (237, true)]
theorem step375 (p : Nat → Bool) (h : Constraints p) : clause p c375 = true := by
  simpa only [c375,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause375
def c376 : List Lit := [(237, false), (239, true)]
theorem step376 (p : Nat → Bool) (h : Constraints p) : clause p c376 = true := by
  simpa only [c376,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause376
def c377 : List Lit := [(120, false), (239, true)]
theorem step377 (p : Nat → Bool) (h : Constraints p) : clause p c377 = true := by
  simpa only [c377,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause377
def c378 : List Lit := [(120, false), (237, false), (240, true)]
theorem step378 (p : Nat → Bool) (h : Constraints p) : clause p c378 = true := by
  simpa only [c378,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause378
def c379 : List Lit := [(124, false), (241, true)]
theorem step379 (p : Nat → Bool) (h : Constraints p) : clause p c379 = true := by
  simpa only [c379,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause379
def c380 : List Lit := [(241, false), (243, true)]
theorem step380 (p : Nat → Bool) (h : Constraints p) : clause p c380 = true := by
  simpa only [c380,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause380
def c381 : List Lit := [(243, false), (245, true)]
theorem step381 (p : Nat → Bool) (h : Constraints p) : clause p c381 = true := by
  simpa only [c381,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause381
def c382 : List Lit := [(239, false), (245, true)]
theorem step382 (p : Nat → Bool) (h : Constraints p) : clause p c382 = true := by
  simpa only [c382,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause382
def c383 : List Lit := [(240, false), (246, true)]
theorem step383 (p : Nat → Bool) (h : Constraints p) : clause p c383 = true := by
  simpa only [c383,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause383
def c384 : List Lit := [(126, false), (249, true)]
theorem step384 (p : Nat → Bool) (h : Constraints p) : clause p c384 = true := by
  simpa only [c384,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block11.clause384
def c385 : List Lit := [(129, false), (251, true)]
theorem step385 (p : Nat → Bool) (h : Constraints p) : clause p c385 = true := by
  simpa only [c385,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause385
def c386 : List Lit := [(131, false), (253, true)]
theorem step386 (p : Nat → Bool) (h : Constraints p) : clause p c386 = true := by
  simpa only [c386,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause386
def c387 : List Lit := [(253, false), (255, true)]
theorem step387 (p : Nat → Bool) (h : Constraints p) : clause p c387 = true := by
  simpa only [c387,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause387
def c388 : List Lit := [(251, false), (255, true)]
theorem step388 (p : Nat → Bool) (h : Constraints p) : clause p c388 = true := by
  simpa only [c388,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause388
def c389 : List Lit := [(255, false), (257, true)]
theorem step389 (p : Nat → Bool) (h : Constraints p) : clause p c389 = true := by
  simpa only [c389,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause389
def c390 : List Lit := [(249, false), (257, true)]
theorem step390 (p : Nat → Bool) (h : Constraints p) : clause p c390 = true := by
  simpa only [c390,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause390
def c391 : List Lit := [(249, false), (255, false), (258, true)]
theorem step391 (p : Nat → Bool) (h : Constraints p) : clause p c391 = true := by
  simpa only [c391,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause391
def c392 : List Lit := [(257, false), (259, true)]
theorem step392 (p : Nat → Bool) (h : Constraints p) : clause p c392 = true := by
  simpa only [c392,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause392
def c393 : List Lit := [(258, false), (260, true)]
theorem step393 (p : Nat → Bool) (h : Constraints p) : clause p c393 = true := by
  simpa only [c393,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause393
def c394 : List Lit := [(245, false), (259, true)]
theorem step394 (p : Nat → Bool) (h : Constraints p) : clause p c394 = true := by
  simpa only [c394,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause394
def c395 : List Lit := [(245, false), (257, false), (260, true)]
theorem step395 (p : Nat → Bool) (h : Constraints p) : clause p c395 = true := by
  simpa only [c395,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause395
def c396 : List Lit := [(246, false), (260, true)]
theorem step396 (p : Nat → Bool) (h : Constraints p) : clause p c396 = true := by
  simpa only [c396,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause396
def c397 : List Lit := [(259, false), (261, true)]
theorem step397 (p : Nat → Bool) (h : Constraints p) : clause p c397 = true := by
  simpa only [c397,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause397
def c398 : List Lit := [(260, false), (262, true)]
theorem step398 (p : Nat → Bool) (h : Constraints p) : clause p c398 = true := by
  simpa only [c398,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause398
def c399 : List Lit := [(235, false), (261, true)]
theorem step399 (p : Nat → Bool) (h : Constraints p) : clause p c399 = true := by
  simpa only [c399,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause399
def c400 : List Lit := [(235, false), (259, false), (262, true)]
theorem step400 (p : Nat → Bool) (h : Constraints p) : clause p c400 = true := by
  simpa only [c400,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause400
def c401 : List Lit := [(236, false), (262, true)]
theorem step401 (p : Nat → Bool) (h : Constraints p) : clause p c401 = true := by
  simpa only [c401,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause401
def c402 : List Lit := [(135, false), (263, true)]
theorem step402 (p : Nat → Bool) (h : Constraints p) : clause p c402 = true := by
  simpa only [c402,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause402
def c403 : List Lit := [(263, false), (265, true)]
theorem step403 (p : Nat → Bool) (h : Constraints p) : clause p c403 = true := by
  simpa only [c403,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause403
def c404 : List Lit := [(133, false), (265, true)]
theorem step404 (p : Nat → Bool) (h : Constraints p) : clause p c404 = true := by
  simpa only [c404,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause404
def c405 : List Lit := [(133, false), (263, false), (266, true)]
theorem step405 (p : Nat → Bool) (h : Constraints p) : clause p c405 = true := by
  simpa only [c405,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause405
def c406 : List Lit := [(138, false), (267, true)]
theorem step406 (p : Nat → Bool) (h : Constraints p) : clause p c406 = true := by
  simpa only [c406,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause406
def c407 : List Lit := [(267, false), (269, true)]
theorem step407 (p : Nat → Bool) (h : Constraints p) : clause p c407 = true := by
  simpa only [c407,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause407
def c408 : List Lit := [(269, false), (271, true)]
theorem step408 (p : Nat → Bool) (h : Constraints p) : clause p c408 = true := by
  simpa only [c408,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause408
def c409 : List Lit := [(265, false), (271, true)]
theorem step409 (p : Nat → Bool) (h : Constraints p) : clause p c409 = true := by
  simpa only [c409,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause409
def c410 : List Lit := [(265, false), (269, false), (272, true)]
theorem step410 (p : Nat → Bool) (h : Constraints p) : clause p c410 = true := by
  simpa only [c410,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause410
def c411 : List Lit := [(266, false), (272, true)]
theorem step411 (p : Nat → Bool) (h : Constraints p) : clause p c411 = true := by
  simpa only [c411,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause411
def c412 : List Lit := [(141, false), (273, true)]
theorem step412 (p : Nat → Bool) (h : Constraints p) : clause p c412 = true := by
  simpa only [c412,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause412
def c413 : List Lit := [(273, false), (275, true)]
theorem step413 (p : Nat → Bool) (h : Constraints p) : clause p c413 = true := by
  simpa only [c413,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause413
def c414 : List Lit := [(143, false), (277, true)]
theorem step414 (p : Nat → Bool) (h : Constraints p) : clause p c414 = true := by
  simpa only [c414,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause414
def c415 : List Lit := [(277, false), (281, true)]
theorem step415 (p : Nat → Bool) (h : Constraints p) : clause p c415 = true := by
  simpa only [c415,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause415
def c416 : List Lit := [(281, false), (283, true)]
theorem step416 (p : Nat → Bool) (h : Constraints p) : clause p c416 = true := by
  simpa only [c416,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block12.clause416
def c417 : List Lit := [(275, false), (283, true)]
theorem step417 (p : Nat → Bool) (h : Constraints p) : clause p c417 = true := by
  simpa only [c417,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause417
def c418 : List Lit := [(283, false), (285, true)]
theorem step418 (p : Nat → Bool) (h : Constraints p) : clause p c418 = true := by
  simpa only [c418,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause418
def c419 : List Lit := [(271, false), (285, true)]
theorem step419 (p : Nat → Bool) (h : Constraints p) : clause p c419 = true := by
  simpa only [c419,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause419
def c420 : List Lit := [(271, false), (283, false), (286, true)]
theorem step420 (p : Nat → Bool) (h : Constraints p) : clause p c420 = true := by
  simpa only [c420,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause420
def c421 : List Lit := [(272, false), (286, true)]
theorem step421 (p : Nat → Bool) (h : Constraints p) : clause p c421 = true := by
  simpa only [c421,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause421
def c422 : List Lit := [(148, false), (287, true)]
theorem step422 (p : Nat → Bool) (h : Constraints p) : clause p c422 = true := by
  simpa only [c422,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause422
def c423 : List Lit := [(147, false), (287, true)]
theorem step423 (p : Nat → Bool) (h : Constraints p) : clause p c423 = true := by
  simpa only [c423,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause423
def c424 : List Lit := [(287, false), (289, true)]
theorem step424 (p : Nat → Bool) (h : Constraints p) : clause p c424 = true := by
  simpa only [c424,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause424
def c425 : List Lit := [(146, false), (289, true)]
theorem step425 (p : Nat → Bool) (h : Constraints p) : clause p c425 = true := by
  simpa only [c425,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause425
def c426 : List Lit := [(146, false), (287, false), (290, true)]
theorem step426 (p : Nat → Bool) (h : Constraints p) : clause p c426 = true := by
  simpa only [c426,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause426
def c427 : List Lit := [(151, false), (291, true)]
theorem step427 (p : Nat → Bool) (h : Constraints p) : clause p c427 = true := by
  simpa only [c427,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause427
def c428 : List Lit := [(150, false), (291, true)]
theorem step428 (p : Nat → Bool) (h : Constraints p) : clause p c428 = true := by
  simpa only [c428,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause428
def c429 : List Lit := [(150, false), (151, false), (292, true)]
theorem step429 (p : Nat → Bool) (h : Constraints p) : clause p c429 = true := by
  simpa only [c429,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause429
def c430 : List Lit := [(291, false), (293, true)]
theorem step430 (p : Nat → Bool) (h : Constraints p) : clause p c430 = true := by
  simpa only [c430,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause430
def c431 : List Lit := [(292, false), (294, true)]
theorem step431 (p : Nat → Bool) (h : Constraints p) : clause p c431 = true := by
  simpa only [c431,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause431
def c432 : List Lit := [(293, false), (295, true)]
theorem step432 (p : Nat → Bool) (h : Constraints p) : clause p c432 = true := by
  simpa only [c432,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause432
def c433 : List Lit := [(294, false), (296, true)]
theorem step433 (p : Nat → Bool) (h : Constraints p) : clause p c433 = true := by
  simpa only [c433,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause433
def c434 : List Lit := [(289, false), (295, true)]
theorem step434 (p : Nat → Bool) (h : Constraints p) : clause p c434 = true := by
  simpa only [c434,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause434
def c435 : List Lit := [(289, false), (293, false), (296, true)]
theorem step435 (p : Nat → Bool) (h : Constraints p) : clause p c435 = true := by
  simpa only [c435,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause435
def c436 : List Lit := [(290, false), (296, true)]
theorem step436 (p : Nat → Bool) (h : Constraints p) : clause p c436 = true := by
  simpa only [c436,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause436
def c437 : List Lit := [(154, false), (297, true)]
theorem step437 (p : Nat → Bool) (h : Constraints p) : clause p c437 = true := by
  simpa only [c437,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause437
def c438 : List Lit := [(297, false), (299, true)]
theorem step438 (p : Nat → Bool) (h : Constraints p) : clause p c438 = true := by
  simpa only [c438,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause438
def c439 : List Lit := [(155, false), (301, true)]
theorem step439 (p : Nat → Bool) (h : Constraints p) : clause p c439 = true := by
  simpa only [c439,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause439
def c440 : List Lit := [(158, false), (303, true)]
theorem step440 (p : Nat → Bool) (h : Constraints p) : clause p c440 = true := by
  simpa only [c440,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause440
def c441 : List Lit := [(303, false), (305, true)]
theorem step441 (p : Nat → Bool) (h : Constraints p) : clause p c441 = true := by
  simpa only [c441,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause441
def c442 : List Lit := [(301, false), (305, true)]
theorem step442 (p : Nat → Bool) (h : Constraints p) : clause p c442 = true := by
  simpa only [c442,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause442
def c443 : List Lit := [(305, false), (307, true)]
theorem step443 (p : Nat → Bool) (h : Constraints p) : clause p c443 = true := by
  simpa only [c443,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause443
def c444 : List Lit := [(299, false), (307, true)]
theorem step444 (p : Nat → Bool) (h : Constraints p) : clause p c444 = true := by
  simpa only [c444,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause444
def c445 : List Lit := [(307, false), (309, true)]
theorem step445 (p : Nat → Bool) (h : Constraints p) : clause p c445 = true := by
  simpa only [c445,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause445
def c446 : List Lit := [(295, false), (309, true)]
theorem step446 (p : Nat → Bool) (h : Constraints p) : clause p c446 = true := by
  simpa only [c446,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause446
def c447 : List Lit := [(295, false), (307, false), (310, true)]
theorem step447 (p : Nat → Bool) (h : Constraints p) : clause p c447 = true := by
  simpa only [c447,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause447
def c448 : List Lit := [(296, false), (310, true)]
theorem step448 (p : Nat → Bool) (h : Constraints p) : clause p c448 = true := by
  simpa only [c448,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block13.clause448
def c449 : List Lit := [(309, false), (311, true)]
theorem step449 (p : Nat → Bool) (h : Constraints p) : clause p c449 = true := by
  simpa only [c449,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause449
def c450 : List Lit := [(310, false), (312, true)]
theorem step450 (p : Nat → Bool) (h : Constraints p) : clause p c450 = true := by
  simpa only [c450,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause450
def c451 : List Lit := [(285, false), (311, true)]
theorem step451 (p : Nat → Bool) (h : Constraints p) : clause p c451 = true := by
  simpa only [c451,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause451
def c452 : List Lit := [(285, false), (309, false), (312, true)]
theorem step452 (p : Nat → Bool) (h : Constraints p) : clause p c452 = true := by
  simpa only [c452,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause452
def c453 : List Lit := [(286, false), (312, true)]
theorem step453 (p : Nat → Bool) (h : Constraints p) : clause p c453 = true := by
  simpa only [c453,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause453
def c454 : List Lit := [(311, false), (313, true)]
theorem step454 (p : Nat → Bool) (h : Constraints p) : clause p c454 = true := by
  simpa only [c454,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause454
def c455 : List Lit := [(312, false), (314, true)]
theorem step455 (p : Nat → Bool) (h : Constraints p) : clause p c455 = true := by
  simpa only [c455,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause455
def c456 : List Lit := [(261, false), (313, true)]
theorem step456 (p : Nat → Bool) (h : Constraints p) : clause p c456 = true := by
  simpa only [c456,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause456
def c457 : List Lit := [(261, false), (311, false), (314, true)]
theorem step457 (p : Nat → Bool) (h : Constraints p) : clause p c457 = true := by
  simpa only [c457,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause457
def c458 : List Lit := [(262, false), (314, true)]
theorem step458 (p : Nat → Bool) (h : Constraints p) : clause p c458 = true := by
  simpa only [c458,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause458
def c459 : List Lit := [(161, false), (315, true)]
theorem step459 (p : Nat → Bool) (h : Constraints p) : clause p c459 = true := by
  simpa only [c459,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause459
def c460 : List Lit := [(315, false), (317, true)]
theorem step460 (p : Nat → Bool) (h : Constraints p) : clause p c460 = true := by
  simpa only [c460,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause460
def c461 : List Lit := [(159, false), (317, true)]
theorem step461 (p : Nat → Bool) (h : Constraints p) : clause p c461 = true := by
  simpa only [c461,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause461
def c462 : List Lit := [(159, false), (315, false), (318, true)]
theorem step462 (p : Nat → Bool) (h : Constraints p) : clause p c462 = true := by
  simpa only [c462,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause462
def c463 : List Lit := [(163, false), (319, true)]
theorem step463 (p : Nat → Bool) (h : Constraints p) : clause p c463 = true := by
  simpa only [c463,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause463
def c464 : List Lit := [(319, false), (321, true)]
theorem step464 (p : Nat → Bool) (h : Constraints p) : clause p c464 = true := by
  simpa only [c464,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause464
def c465 : List Lit := [(321, false), (323, true)]
theorem step465 (p : Nat → Bool) (h : Constraints p) : clause p c465 = true := by
  simpa only [c465,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause465
def c466 : List Lit := [(317, false), (323, true)]
theorem step466 (p : Nat → Bool) (h : Constraints p) : clause p c466 = true := by
  simpa only [c466,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause466
def c467 : List Lit := [(318, false), (324, true)]
theorem step467 (p : Nat → Bool) (h : Constraints p) : clause p c467 = true := by
  simpa only [c467,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause467
def c468 : List Lit := [(167, false), (325, true)]
theorem step468 (p : Nat → Bool) (h : Constraints p) : clause p c468 = true := by
  simpa only [c468,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause468
def c469 : List Lit := [(325, false), (327, true)]
theorem step469 (p : Nat → Bool) (h : Constraints p) : clause p c469 = true := by
  simpa only [c469,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause469
def c470 : List Lit := [(169, false), (329, true)]
theorem step470 (p : Nat → Bool) (h : Constraints p) : clause p c470 = true := by
  simpa only [c470,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause470
def c471 : List Lit := [(168, false), (329, true)]
theorem step471 (p : Nat → Bool) (h : Constraints p) : clause p c471 = true := by
  simpa only [c471,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause471
def c472 : List Lit := [(171, false), (331, true)]
theorem step472 (p : Nat → Bool) (h : Constraints p) : clause p c472 = true := by
  simpa only [c472,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause472
def c473 : List Lit := [(331, false), (333, true)]
theorem step473 (p : Nat → Bool) (h : Constraints p) : clause p c473 = true := by
  simpa only [c473,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause473
def c474 : List Lit := [(329, false), (333, true)]
theorem step474 (p : Nat → Bool) (h : Constraints p) : clause p c474 = true := by
  simpa only [c474,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause474
def c475 : List Lit := [(333, false), (335, true)]
theorem step475 (p : Nat → Bool) (h : Constraints p) : clause p c475 = true := by
  simpa only [c475,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause475
def c476 : List Lit := [(327, false), (335, true)]
theorem step476 (p : Nat → Bool) (h : Constraints p) : clause p c476 = true := by
  simpa only [c476,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause476
def c477 : List Lit := [(335, false), (337, true)]
theorem step477 (p : Nat → Bool) (h : Constraints p) : clause p c477 = true := by
  simpa only [c477,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause477
def c478 : List Lit := [(323, false), (337, true)]
theorem step478 (p : Nat → Bool) (h : Constraints p) : clause p c478 = true := by
  simpa only [c478,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause478
def c479 : List Lit := [(323, false), (335, false), (338, true)]
theorem step479 (p : Nat → Bool) (h : Constraints p) : clause p c479 = true := by
  simpa only [c479,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause479
def c480 : List Lit := [(324, false), (338, true)]
theorem step480 (p : Nat → Bool) (h : Constraints p) : clause p c480 = true := by
  simpa only [c480,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block14.clause480
def c481 : List Lit := [(174, false), (339, true)]
theorem step481 (p : Nat → Bool) (h : Constraints p) : clause p c481 = true := by
  simpa only [c481,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause481
def c482 : List Lit := [(339, false), (341, true)]
theorem step482 (p : Nat → Bool) (h : Constraints p) : clause p c482 = true := by
  simpa only [c482,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause482
def c483 : List Lit := [(176, false), (343, true)]
theorem step483 (p : Nat → Bool) (h : Constraints p) : clause p c483 = true := by
  simpa only [c483,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause483
def c484 : List Lit := [(343, false), (345, true)]
theorem step484 (p : Nat → Bool) (h : Constraints p) : clause p c484 = true := by
  simpa only [c484,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause484
def c485 : List Lit := [(345, false), (347, true)]
theorem step485 (p : Nat → Bool) (h : Constraints p) : clause p c485 = true := by
  simpa only [c485,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause485
def c486 : List Lit := [(341, false), (347, true)]
theorem step486 (p : Nat → Bool) (h : Constraints p) : clause p c486 = true := by
  simpa only [c486,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause486
def c487 : List Lit := [(341, false), (345, false), (348, true)]
theorem step487 (p : Nat → Bool) (h : Constraints p) : clause p c487 = true := by
  simpa only [c487,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause487
def c488 : List Lit := [(181, false), (349, true)]
theorem step488 (p : Nat → Bool) (h : Constraints p) : clause p c488 = true := by
  simpa only [c488,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause488
def c489 : List Lit := [(179, false), (349, true)]
theorem step489 (p : Nat → Bool) (h : Constraints p) : clause p c489 = true := by
  simpa only [c489,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause489
def c490 : List Lit := [(349, false), (351, true)]
theorem step490 (p : Nat → Bool) (h : Constraints p) : clause p c490 = true := by
  simpa only [c490,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause490
def c491 : List Lit := [(182, false), (353, true)]
theorem step491 (p : Nat → Bool) (h : Constraints p) : clause p c491 = true := by
  simpa only [c491,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause491
def c492 : List Lit := [(184, false), (355, true)]
theorem step492 (p : Nat → Bool) (h : Constraints p) : clause p c492 = true := by
  simpa only [c492,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause492
def c493 : List Lit := [(355, false), (357, true)]
theorem step493 (p : Nat → Bool) (h : Constraints p) : clause p c493 = true := by
  simpa only [c493,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause493
def c494 : List Lit := [(353, false), (357, true)]
theorem step494 (p : Nat → Bool) (h : Constraints p) : clause p c494 = true := by
  simpa only [c494,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause494
def c495 : List Lit := [(353, false), (355, false), (358, true)]
theorem step495 (p : Nat → Bool) (h : Constraints p) : clause p c495 = true := by
  simpa only [c495,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause495
def c496 : List Lit := [(357, false), (359, true)]
theorem step496 (p : Nat → Bool) (h : Constraints p) : clause p c496 = true := by
  simpa only [c496,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause496
def c497 : List Lit := [(358, false), (360, true)]
theorem step497 (p : Nat → Bool) (h : Constraints p) : clause p c497 = true := by
  simpa only [c497,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause497
def c498 : List Lit := [(351, false), (359, true)]
theorem step498 (p : Nat → Bool) (h : Constraints p) : clause p c498 = true := by
  simpa only [c498,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause498
def c499 : List Lit := [(351, false), (357, false), (360, true)]
theorem step499 (p : Nat → Bool) (h : Constraints p) : clause p c499 = true := by
  simpa only [c499,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause499
def c500 : List Lit := [(359, false), (361, true)]
theorem step500 (p : Nat → Bool) (h : Constraints p) : clause p c500 = true := by
  simpa only [c500,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause500
def c501 : List Lit := [(360, false), (362, true)]
theorem step501 (p : Nat → Bool) (h : Constraints p) : clause p c501 = true := by
  simpa only [c501,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause501
def c502 : List Lit := [(347, false), (361, true)]
theorem step502 (p : Nat → Bool) (h : Constraints p) : clause p c502 = true := by
  simpa only [c502,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause502
def c503 : List Lit := [(347, false), (359, false), (362, true)]
theorem step503 (p : Nat → Bool) (h : Constraints p) : clause p c503 = true := by
  simpa only [c503,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause503
def c504 : List Lit := [(348, false), (362, true)]
theorem step504 (p : Nat → Bool) (h : Constraints p) : clause p c504 = true := by
  simpa only [c504,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause504
def c505 : List Lit := [(361, false), (363, true)]
theorem step505 (p : Nat → Bool) (h : Constraints p) : clause p c505 = true := by
  simpa only [c505,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause505
def c506 : List Lit := [(362, false), (364, true)]
theorem step506 (p : Nat → Bool) (h : Constraints p) : clause p c506 = true := by
  simpa only [c506,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause506
def c507 : List Lit := [(337, false), (363, true)]
theorem step507 (p : Nat → Bool) (h : Constraints p) : clause p c507 = true := by
  simpa only [c507,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause507
def c508 : List Lit := [(337, false), (361, false), (364, true)]
theorem step508 (p : Nat → Bool) (h : Constraints p) : clause p c508 = true := by
  simpa only [c508,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause508
def c509 : List Lit := [(338, false), (364, true)]
theorem step509 (p : Nat → Bool) (h : Constraints p) : clause p c509 = true := by
  simpa only [c509,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause509
def c510 : List Lit := [(187, false), (365, true)]
theorem step510 (p : Nat → Bool) (h : Constraints p) : clause p c510 = true := by
  simpa only [c510,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause510
def c511 : List Lit := [(365, false), (367, true)]
theorem step511 (p : Nat → Bool) (h : Constraints p) : clause p c511 = true := by
  simpa only [c511,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause511
def c512 : List Lit := [(191, false), (369, true)]
theorem step512 (p : Nat → Bool) (h : Constraints p) : clause p c512 = true := by
  simpa only [c512,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block15.clause512
def c513 : List Lit := [(369, false), (371, true)]
theorem step513 (p : Nat → Bool) (h : Constraints p) : clause p c513 = true := by
  simpa only [c513,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause513
def c514 : List Lit := [(189, false), (371, true)]
theorem step514 (p : Nat → Bool) (h : Constraints p) : clause p c514 = true := by
  simpa only [c514,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause514
def c515 : List Lit := [(189, false), (369, false), (372, true)]
theorem step515 (p : Nat → Bool) (h : Constraints p) : clause p c515 = true := by
  simpa only [c515,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause515
def c516 : List Lit := [(371, false), (373, true)]
theorem step516 (p : Nat → Bool) (h : Constraints p) : clause p c516 = true := by
  simpa only [c516,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause516
def c517 : List Lit := [(372, false), (374, true)]
theorem step517 (p : Nat → Bool) (h : Constraints p) : clause p c517 = true := by
  simpa only [c517,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause517
def c518 : List Lit := [(367, false), (373, true)]
theorem step518 (p : Nat → Bool) (h : Constraints p) : clause p c518 = true := by
  simpa only [c518,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause518
def c519 : List Lit := [(367, false), (371, false), (374, true)]
theorem step519 (p : Nat → Bool) (h : Constraints p) : clause p c519 = true := by
  simpa only [c519,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause519
def c520 : List Lit := [(193, false), (375, true)]
theorem step520 (p : Nat → Bool) (h : Constraints p) : clause p c520 = true := by
  simpa only [c520,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause520
def c521 : List Lit := [(375, false), (377, true)]
theorem step521 (p : Nat → Bool) (h : Constraints p) : clause p c521 = true := by
  simpa only [c521,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause521
def c522 : List Lit := [(195, false), (379, true)]
theorem step522 (p : Nat → Bool) (h : Constraints p) : clause p c522 = true := by
  simpa only [c522,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause522
def c523 : List Lit := [(197, false), (381, true)]
theorem step523 (p : Nat → Bool) (h : Constraints p) : clause p c523 = true := by
  simpa only [c523,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause523
def c524 : List Lit := [(381, false), (383, true)]
theorem step524 (p : Nat → Bool) (h : Constraints p) : clause p c524 = true := by
  simpa only [c524,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause524
def c525 : List Lit := [(379, false), (383, true)]
theorem step525 (p : Nat → Bool) (h : Constraints p) : clause p c525 = true := by
  simpa only [c525,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause525
def c526 : List Lit := [(383, false), (385, true)]
theorem step526 (p : Nat → Bool) (h : Constraints p) : clause p c526 = true := by
  simpa only [c526,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause526
def c527 : List Lit := [(377, false), (385, true)]
theorem step527 (p : Nat → Bool) (h : Constraints p) : clause p c527 = true := by
  simpa only [c527,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause527
def c528 : List Lit := [(385, false), (387, true)]
theorem step528 (p : Nat → Bool) (h : Constraints p) : clause p c528 = true := by
  simpa only [c528,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause528
def c529 : List Lit := [(373, false), (387, true)]
theorem step529 (p : Nat → Bool) (h : Constraints p) : clause p c529 = true := by
  simpa only [c529,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause529
def c530 : List Lit := [(373, false), (385, false), (388, true)]
theorem step530 (p : Nat → Bool) (h : Constraints p) : clause p c530 = true := by
  simpa only [c530,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause530
def c531 : List Lit := [(374, false), (388, true)]
theorem step531 (p : Nat → Bool) (h : Constraints p) : clause p c531 = true := by
  simpa only [c531,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause531
def c532 : List Lit := [(199, false), (391, true)]
theorem step532 (p : Nat → Bool) (h : Constraints p) : clause p c532 = true := by
  simpa only [c532,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause532
def c533 : List Lit := [(202, false), (393, true)]
theorem step533 (p : Nat → Bool) (h : Constraints p) : clause p c533 = true := by
  simpa only [c533,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause533
def c534 : List Lit := [(204, false), (395, true)]
theorem step534 (p : Nat → Bool) (h : Constraints p) : clause p c534 = true := by
  simpa only [c534,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause534
def c535 : List Lit := [(395, false), (397, true)]
theorem step535 (p : Nat → Bool) (h : Constraints p) : clause p c535 = true := by
  simpa only [c535,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause535
def c536 : List Lit := [(393, false), (397, true)]
theorem step536 (p : Nat → Bool) (h : Constraints p) : clause p c536 = true := by
  simpa only [c536,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause536
def c537 : List Lit := [(397, false), (399, true)]
theorem step537 (p : Nat → Bool) (h : Constraints p) : clause p c537 = true := by
  simpa only [c537,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause537
def c538 : List Lit := [(391, false), (399, true)]
theorem step538 (p : Nat → Bool) (h : Constraints p) : clause p c538 = true := by
  simpa only [c538,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause538
def c539 : List Lit := [(391, false), (397, false), (400, true)]
theorem step539 (p : Nat → Bool) (h : Constraints p) : clause p c539 = true := by
  simpa only [c539,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause539
def c540 : List Lit := [(208, false), (401, true)]
theorem step540 (p : Nat → Bool) (h : Constraints p) : clause p c540 = true := by
  simpa only [c540,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause540
def c541 : List Lit := [(401, false), (403, true)]
theorem step541 (p : Nat → Bool) (h : Constraints p) : clause p c541 = true := by
  simpa only [c541,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause541
def c542 : List Lit := [(206, false), (403, true)]
theorem step542 (p : Nat → Bool) (h : Constraints p) : clause p c542 = true := by
  simpa only [c542,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause542
def c543 : List Lit := [(206, false), (401, false), (404, true)]
theorem step543 (p : Nat → Bool) (h : Constraints p) : clause p c543 = true := by
  simpa only [c543,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause543
def c544 : List Lit := [(209, false), (405, true)]
theorem step544 (p : Nat → Bool) (h : Constraints p) : clause p c544 = true := by
  simpa only [c544,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block16.clause544
def c545 : List Lit := [(211, false), (407, true)]
theorem step545 (p : Nat → Bool) (h : Constraints p) : clause p c545 = true := by
  simpa only [c545,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause545
def c546 : List Lit := [(407, false), (409, true)]
theorem step546 (p : Nat → Bool) (h : Constraints p) : clause p c546 = true := by
  simpa only [c546,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause546
def c547 : List Lit := [(405, false), (409, true)]
theorem step547 (p : Nat → Bool) (h : Constraints p) : clause p c547 = true := by
  simpa only [c547,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause547
def c548 : List Lit := [(409, false), (411, true)]
theorem step548 (p : Nat → Bool) (h : Constraints p) : clause p c548 = true := by
  simpa only [c548,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause548
def c549 : List Lit := [(403, false), (411, true)]
theorem step549 (p : Nat → Bool) (h : Constraints p) : clause p c549 = true := by
  simpa only [c549,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause549
def c550 : List Lit := [(404, false), (412, true)]
theorem step550 (p : Nat → Bool) (h : Constraints p) : clause p c550 = true := by
  simpa only [c550,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause550
def c551 : List Lit := [(411, false), (413, true)]
theorem step551 (p : Nat → Bool) (h : Constraints p) : clause p c551 = true := by
  simpa only [c551,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause551
def c552 : List Lit := [(412, false), (414, true)]
theorem step552 (p : Nat → Bool) (h : Constraints p) : clause p c552 = true := by
  simpa only [c552,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause552
def c553 : List Lit := [(399, false), (413, true)]
theorem step553 (p : Nat → Bool) (h : Constraints p) : clause p c553 = true := by
  simpa only [c553,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause553
def c554 : List Lit := [(399, false), (411, false), (414, true)]
theorem step554 (p : Nat → Bool) (h : Constraints p) : clause p c554 = true := by
  simpa only [c554,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause554
def c555 : List Lit := [(400, false), (414, true)]
theorem step555 (p : Nat → Bool) (h : Constraints p) : clause p c555 = true := by
  simpa only [c555,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause555
def c556 : List Lit := [(413, false), (415, true)]
theorem step556 (p : Nat → Bool) (h : Constraints p) : clause p c556 = true := by
  simpa only [c556,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause556
def c557 : List Lit := [(414, false), (416, true)]
theorem step557 (p : Nat → Bool) (h : Constraints p) : clause p c557 = true := by
  simpa only [c557,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause557
def c558 : List Lit := [(387, false), (415, true)]
theorem step558 (p : Nat → Bool) (h : Constraints p) : clause p c558 = true := by
  simpa only [c558,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause558
def c559 : List Lit := [(387, false), (413, false), (416, true)]
theorem step559 (p : Nat → Bool) (h : Constraints p) : clause p c559 = true := by
  simpa only [c559,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause559
def c560 : List Lit := [(388, false), (416, true)]
theorem step560 (p : Nat → Bool) (h : Constraints p) : clause p c560 = true := by
  simpa only [c560,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause560
def c561 : List Lit := [(415, false), (417, true)]
theorem step561 (p : Nat → Bool) (h : Constraints p) : clause p c561 = true := by
  simpa only [c561,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause561
def c562 : List Lit := [(416, false), (418, true)]
theorem step562 (p : Nat → Bool) (h : Constraints p) : clause p c562 = true := by
  simpa only [c562,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause562
def c563 : List Lit := [(363, false), (417, true)]
theorem step563 (p : Nat → Bool) (h : Constraints p) : clause p c563 = true := by
  simpa only [c563,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause563
def c564 : List Lit := [(363, false), (415, false), (418, true)]
theorem step564 (p : Nat → Bool) (h : Constraints p) : clause p c564 = true := by
  simpa only [c564,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause564
def c565 : List Lit := [(364, false), (418, true)]
theorem step565 (p : Nat → Bool) (h : Constraints p) : clause p c565 = true := by
  simpa only [c565,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause565
def c566 : List Lit := [(418, false), (420, true)]
theorem step566 (p : Nat → Bool) (h : Constraints p) : clause p c566 = true := by
  simpa only [c566,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause566
def c567 : List Lit := [(313, false), (417, false), (420, true)]
theorem step567 (p : Nat → Bool) (h : Constraints p) : clause p c567 = true := by
  simpa only [c567,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause567
def c568 : List Lit := [(314, false), (420, true)]
theorem step568 (p : Nat → Bool) (h : Constraints p) : clause p c568 = true := by
  simpa only [c568,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause568
def c569 : List Lit := [(420, false)]
theorem step569 (p : Nat → Bool) (h : Constraints p) : clause p c569 = true := by
  simpa only [c569,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause569
def c570 : List Lit := [(107, true), (108, true), (109, true), (110, true), (111, true), (112, true), (113, true), (114, true), (115, true), (116, true), (117, true), (118, true), (119, true), (120, true), (121, true), (122, true), (123, true), (124, true), (125, true), (126, true), (127, true), (128, true), (129, true), (130, true), (131, true), (132, true), (133, true), (134, true), (135, true), (136, true), (137, true), (138, true), (139, true), (140, true), (141, true), (142, true), (143, true), (144, true), (145, true), (146, true), (147, true), (148, true), (149, true), (150, true), (151, true), (152, true), (153, true), (154, true), (155, true), (156, true), (157, true), (158, true), (159, true), (160, true), (161, true), (162, true), (163, true), (164, true), (165, true), (166, true), (167, true), (168, true), (169, true), (170, true), (171, true), (172, true), (173, true), (174, true), (175, true), (176, true), (177, true), (178, true), (179, true), (181, true), (182, true), (183, true), (184, true), (185, true), (186, true), (187, true), (188, true), (189, true), (190, true), (191, true), (192, true), (193, true), (194, true), (195, true), (196, true), (197, true), (198, true), (199, true), (200, true), (201, true), (202, true), (203, true), (204, true), (205, true), (206, true), (207, true), (208, true), (209, true), (210, true), (211, true), (212, true)]
theorem step570 (p : Nat → Bool) (h : Constraints p) : clause p c570 = true := by
  simpa only [c570,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause570
def c571 : List Lit := [(7, true), (1252, true)]
theorem step571 (p : Nat → Bool) (h : Constraints p) : clause p c571 = true := by
  simpa only [c571,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause571
def c572 : List Lit := [(4, true), (1252, true)]
theorem step572 (p : Nat → Bool) (h : Constraints p) : clause p c572 = true := by
  simpa only [c572,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause572
def c573 : List Lit := [(4, true), (7, true), (1253, true)]
theorem step573 (p : Nat → Bool) (h : Constraints p) : clause p c573 = true := by
  simpa only [c573,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause573
def c574 : List Lit := [(1252, false), (1254, true)]
theorem step574 (p : Nat → Bool) (h : Constraints p) : clause p c574 = true := by
  simpa only [c574,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause574
def c575 : List Lit := [(1253, false), (1255, true)]
theorem step575 (p : Nat → Bool) (h : Constraints p) : clause p c575 = true := by
  simpa only [c575,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause575
def c576 : List Lit := [(2, true), (1254, true)]
theorem step576 (p : Nat → Bool) (h : Constraints p) : clause p c576 = true := by
  simpa only [c576,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block17.clause576
def c577 : List Lit := [(2, true), (1252, false), (1255, true)]
theorem step577 (p : Nat → Bool) (h : Constraints p) : clause p c577 = true := by
  simpa only [c577,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause577
def c578 : List Lit := [(2, true), (1253, false), (1256, true)]
theorem step578 (p : Nat → Bool) (h : Constraints p) : clause p c578 = true := by
  simpa only [c578,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause578
def c579 : List Lit := [(10, true), (1257, true)]
theorem step579 (p : Nat → Bool) (h : Constraints p) : clause p c579 = true := by
  simpa only [c579,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause579
def c580 : List Lit := [(9, true), (1257, true)]
theorem step580 (p : Nat → Bool) (h : Constraints p) : clause p c580 = true := by
  simpa only [c580,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause580
def c581 : List Lit := [(1257, false), (1259, true)]
theorem step581 (p : Nat → Bool) (h : Constraints p) : clause p c581 = true := by
  simpa only [c581,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause581
def c582 : List Lit := [(8, true), (1259, true)]
theorem step582 (p : Nat → Bool) (h : Constraints p) : clause p c582 = true := by
  simpa only [c582,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause582
def c583 : List Lit := [(8, true), (1257, false), (1260, true)]
theorem step583 (p : Nat → Bool) (h : Constraints p) : clause p c583 = true := by
  simpa only [c583,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause583
def c584 : List Lit := [(1259, false), (1262, true)]
theorem step584 (p : Nat → Bool) (h : Constraints p) : clause p c584 = true := by
  simpa only [c584,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause584
def c585 : List Lit := [(1260, false), (1263, true)]
theorem step585 (p : Nat → Bool) (h : Constraints p) : clause p c585 = true := by
  simpa only [c585,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause585
def c586 : List Lit := [(1254, false), (1262, true)]
theorem step586 (p : Nat → Bool) (h : Constraints p) : clause p c586 = true := by
  simpa only [c586,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause586
def c587 : List Lit := [(1254, false), (1259, false), (1263, true)]
theorem step587 (p : Nat → Bool) (h : Constraints p) : clause p c587 = true := by
  simpa only [c587,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause587
def c588 : List Lit := [(1254, false), (1260, false), (1264, true)]
theorem step588 (p : Nat → Bool) (h : Constraints p) : clause p c588 = true := by
  simpa only [c588,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause588
def c589 : List Lit := [(1255, false), (1263, true)]
theorem step589 (p : Nat → Bool) (h : Constraints p) : clause p c589 = true := by
  simpa only [c589,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause589
def c590 : List Lit := [(1255, false), (1259, false), (1264, true)]
theorem step590 (p : Nat → Bool) (h : Constraints p) : clause p c590 = true := by
  simpa only [c590,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause590
def c591 : List Lit := [(1256, false), (1264, true)]
theorem step591 (p : Nat → Bool) (h : Constraints p) : clause p c591 = true := by
  simpa only [c591,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause591
def c592 : List Lit := [(15, true), (1268, true)]
theorem step592 (p : Nat → Bool) (h : Constraints p) : clause p c592 = true := by
  simpa only [c592,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause592
def c593 : List Lit := [(14, true), (1268, true)]
theorem step593 (p : Nat → Bool) (h : Constraints p) : clause p c593 = true := by
  simpa only [c593,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause593
def c594 : List Lit := [(14, true), (15, true), (1269, true)]
theorem step594 (p : Nat → Bool) (h : Constraints p) : clause p c594 = true := by
  simpa only [c594,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause594
def c595 : List Lit := [(1268, false), (1270, true)]
theorem step595 (p : Nat → Bool) (h : Constraints p) : clause p c595 = true := by
  simpa only [c595,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause595
def c596 : List Lit := [(1269, false), (1271, true)]
theorem step596 (p : Nat → Bool) (h : Constraints p) : clause p c596 = true := by
  simpa only [c596,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause596
def c597 : List Lit := [(11, true), (1270, true)]
theorem step597 (p : Nat → Bool) (h : Constraints p) : clause p c597 = true := by
  simpa only [c597,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause597
def c598 : List Lit := [(11, true), (1268, false), (1271, true)]
theorem step598 (p : Nat → Bool) (h : Constraints p) : clause p c598 = true := by
  simpa only [c598,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause598
def c599 : List Lit := [(11, true), (1269, false), (1272, true)]
theorem step599 (p : Nat → Bool) (h : Constraints p) : clause p c599 = true := by
  simpa only [c599,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause599
def c600 : List Lit := [(20, true), (1273, true)]
theorem step600 (p : Nat → Bool) (h : Constraints p) : clause p c600 = true := by
  simpa only [c600,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause600
def c601 : List Lit := [(18, true), (1273, true)]
theorem step601 (p : Nat → Bool) (h : Constraints p) : clause p c601 = true := by
  simpa only [c601,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause601
def c602 : List Lit := [(18, true), (20, true), (1274, true)]
theorem step602 (p : Nat → Bool) (h : Constraints p) : clause p c602 = true := by
  simpa only [c602,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause602
def c603 : List Lit := [(25, true), (1275, true)]
theorem step603 (p : Nat → Bool) (h : Constraints p) : clause p c603 = true := by
  simpa only [c603,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause603
def c604 : List Lit := [(23, true), (1275, true)]
theorem step604 (p : Nat → Bool) (h : Constraints p) : clause p c604 = true := by
  simpa only [c604,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause604
def c605 : List Lit := [(1275, false), (1277, true)]
theorem step605 (p : Nat → Bool) (h : Constraints p) : clause p c605 = true := by
  simpa only [c605,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause605
def c606 : List Lit := [(1273, false), (1277, true)]
theorem step606 (p : Nat → Bool) (h : Constraints p) : clause p c606 = true := by
  simpa only [c606,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause606
def c607 : List Lit := [(1273, false), (1275, false), (1278, true)]
theorem step607 (p : Nat → Bool) (h : Constraints p) : clause p c607 = true := by
  simpa only [c607,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause607
def c608 : List Lit := [(1274, false), (1275, false), (1279, true)]
theorem step608 (p : Nat → Bool) (h : Constraints p) : clause p c608 = true := by
  simpa only [c608,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block18.clause608
def c609 : List Lit := [(1277, false), (1281, true)]
theorem step609 (p : Nat → Bool) (h : Constraints p) : clause p c609 = true := by
  simpa only [c609,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause609
def c610 : List Lit := [(1278, false), (1282, true)]
theorem step610 (p : Nat → Bool) (h : Constraints p) : clause p c610 = true := by
  simpa only [c610,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause610
def c611 : List Lit := [(1279, false), (1283, true)]
theorem step611 (p : Nat → Bool) (h : Constraints p) : clause p c611 = true := by
  simpa only [c611,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause611
def c612 : List Lit := [(1270, false), (1281, true)]
theorem step612 (p : Nat → Bool) (h : Constraints p) : clause p c612 = true := by
  simpa only [c612,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause612
def c613 : List Lit := [(1270, false), (1277, false), (1282, true)]
theorem step613 (p : Nat → Bool) (h : Constraints p) : clause p c613 = true := by
  simpa only [c613,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause613
def c614 : List Lit := [(1270, false), (1278, false), (1283, true)]
theorem step614 (p : Nat → Bool) (h : Constraints p) : clause p c614 = true := by
  simpa only [c614,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause614
def c615 : List Lit := [(1270, false), (1279, false), (1284, true)]
theorem step615 (p : Nat → Bool) (h : Constraints p) : clause p c615 = true := by
  simpa only [c615,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause615
def c616 : List Lit := [(1271, false), (1282, true)]
theorem step616 (p : Nat → Bool) (h : Constraints p) : clause p c616 = true := by
  simpa only [c616,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause616
def c617 : List Lit := [(1271, false), (1277, false), (1283, true)]
theorem step617 (p : Nat → Bool) (h : Constraints p) : clause p c617 = true := by
  simpa only [c617,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause617
def c618 : List Lit := [(1271, false), (1278, false), (1284, true)]
theorem step618 (p : Nat → Bool) (h : Constraints p) : clause p c618 = true := by
  simpa only [c618,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause618
def c619 : List Lit := [(1271, false), (1279, false), (1285, true)]
theorem step619 (p : Nat → Bool) (h : Constraints p) : clause p c619 = true := by
  simpa only [c619,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause619
def c620 : List Lit := [(1272, false), (1277, false), (1284, true)]
theorem step620 (p : Nat → Bool) (h : Constraints p) : clause p c620 = true := by
  simpa only [c620,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause620
def c621 : List Lit := [(1281, false), (1288, true)]
theorem step621 (p : Nat → Bool) (h : Constraints p) : clause p c621 = true := by
  simpa only [c621,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause621
def c622 : List Lit := [(1282, false), (1289, true)]
theorem step622 (p : Nat → Bool) (h : Constraints p) : clause p c622 = true := by
  simpa only [c622,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause622
def c623 : List Lit := [(1283, false), (1290, true)]
theorem step623 (p : Nat → Bool) (h : Constraints p) : clause p c623 = true := by
  simpa only [c623,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause623
def c624 : List Lit := [(1284, false), (1291, true)]
theorem step624 (p : Nat → Bool) (h : Constraints p) : clause p c624 = true := by
  simpa only [c624,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause624
def c625 : List Lit := [(1285, false), (1292, true)]
theorem step625 (p : Nat → Bool) (h : Constraints p) : clause p c625 = true := by
  simpa only [c625,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause625
def c626 : List Lit := [(1262, false), (1288, true)]
theorem step626 (p : Nat → Bool) (h : Constraints p) : clause p c626 = true := by
  simpa only [c626,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause626
def c627 : List Lit := [(1262, false), (1281, false), (1289, true)]
theorem step627 (p : Nat → Bool) (h : Constraints p) : clause p c627 = true := by
  simpa only [c627,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause627
def c628 : List Lit := [(1262, false), (1282, false), (1290, true)]
theorem step628 (p : Nat → Bool) (h : Constraints p) : clause p c628 = true := by
  simpa only [c628,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause628
def c629 : List Lit := [(1262, false), (1283, false), (1291, true)]
theorem step629 (p : Nat → Bool) (h : Constraints p) : clause p c629 = true := by
  simpa only [c629,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause629
def c630 : List Lit := [(1263, false), (1289, true)]
theorem step630 (p : Nat → Bool) (h : Constraints p) : clause p c630 = true := by
  simpa only [c630,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause630
def c631 : List Lit := [(1263, false), (1281, false), (1290, true)]
theorem step631 (p : Nat → Bool) (h : Constraints p) : clause p c631 = true := by
  simpa only [c631,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause631
def c632 : List Lit := [(1263, false), (1282, false), (1291, true)]
theorem step632 (p : Nat → Bool) (h : Constraints p) : clause p c632 = true := by
  simpa only [c632,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause632
def c633 : List Lit := [(1263, false), (1283, false), (1292, true)]
theorem step633 (p : Nat → Bool) (h : Constraints p) : clause p c633 = true := by
  simpa only [c633,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause633
def c634 : List Lit := [(1264, false), (1290, true)]
theorem step634 (p : Nat → Bool) (h : Constraints p) : clause p c634 = true := by
  simpa only [c634,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause634
def c635 : List Lit := [(1264, false), (1281, false), (1291, true)]
theorem step635 (p : Nat → Bool) (h : Constraints p) : clause p c635 = true := by
  simpa only [c635,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause635
def c636 : List Lit := [(30, true), (1301, true)]
theorem step636 (p : Nat → Bool) (h : Constraints p) : clause p c636 = true := by
  simpa only [c636,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause636
def c637 : List Lit := [(29, true), (1301, true)]
theorem step637 (p : Nat → Bool) (h : Constraints p) : clause p c637 = true := by
  simpa only [c637,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause637
def c638 : List Lit := [(29, true), (30, true), (1302, true)]
theorem step638 (p : Nat → Bool) (h : Constraints p) : clause p c638 = true := by
  simpa only [c638,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause638
def c639 : List Lit := [(1301, false), (1303, true)]
theorem step639 (p : Nat → Bool) (h : Constraints p) : clause p c639 = true := by
  simpa only [c639,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause639
def c640 : List Lit := [(1302, false), (1304, true)]
theorem step640 (p : Nat → Bool) (h : Constraints p) : clause p c640 = true := by
  simpa only [c640,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block19.clause640
def c641 : List Lit := [(27, true), (1303, true)]
theorem step641 (p : Nat → Bool) (h : Constraints p) : clause p c641 = true := by
  simpa only [c641,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause641
def c642 : List Lit := [(27, true), (1301, false), (1304, true)]
theorem step642 (p : Nat → Bool) (h : Constraints p) : clause p c642 = true := by
  simpa only [c642,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause642
def c643 : List Lit := [(27, true), (1302, false), (1305, true)]
theorem step643 (p : Nat → Bool) (h : Constraints p) : clause p c643 = true := by
  simpa only [c643,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause643
def c644 : List Lit := [(37, true), (1306, true)]
theorem step644 (p : Nat → Bool) (h : Constraints p) : clause p c644 = true := by
  simpa only [c644,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause644
def c645 : List Lit := [(35, true), (1306, true)]
theorem step645 (p : Nat → Bool) (h : Constraints p) : clause p c645 = true := by
  simpa only [c645,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause645
def c646 : List Lit := [(35, true), (37, true), (1307, true)]
theorem step646 (p : Nat → Bool) (h : Constraints p) : clause p c646 = true := by
  simpa only [c646,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause646
def c647 : List Lit := [(1306, false), (1308, true)]
theorem step647 (p : Nat → Bool) (h : Constraints p) : clause p c647 = true := by
  simpa only [c647,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause647
def c648 : List Lit := [(1307, false), (1309, true)]
theorem step648 (p : Nat → Bool) (h : Constraints p) : clause p c648 = true := by
  simpa only [c648,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause648
def c649 : List Lit := [(32, true), (1308, true)]
theorem step649 (p : Nat → Bool) (h : Constraints p) : clause p c649 = true := by
  simpa only [c649,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause649
def c650 : List Lit := [(32, true), (1306, false), (1309, true)]
theorem step650 (p : Nat → Bool) (h : Constraints p) : clause p c650 = true := by
  simpa only [c650,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause650
def c651 : List Lit := [(1308, false), (1311, true)]
theorem step651 (p : Nat → Bool) (h : Constraints p) : clause p c651 = true := by
  simpa only [c651,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause651
def c652 : List Lit := [(1309, false), (1312, true)]
theorem step652 (p : Nat → Bool) (h : Constraints p) : clause p c652 = true := by
  simpa only [c652,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause652
def c653 : List Lit := [(1303, false), (1311, true)]
theorem step653 (p : Nat → Bool) (h : Constraints p) : clause p c653 = true := by
  simpa only [c653,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause653
def c654 : List Lit := [(1303, false), (1308, false), (1312, true)]
theorem step654 (p : Nat → Bool) (h : Constraints p) : clause p c654 = true := by
  simpa only [c654,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause654
def c655 : List Lit := [(1303, false), (1309, false), (1313, true)]
theorem step655 (p : Nat → Bool) (h : Constraints p) : clause p c655 = true := by
  simpa only [c655,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause655
def c656 : List Lit := [(1304, false), (1312, true)]
theorem step656 (p : Nat → Bool) (h : Constraints p) : clause p c656 = true := by
  simpa only [c656,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause656
def c657 : List Lit := [(1304, false), (1308, false), (1313, true)]
theorem step657 (p : Nat → Bool) (h : Constraints p) : clause p c657 = true := by
  simpa only [c657,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause657
def c658 : List Lit := [(1304, false), (1309, false), (1314, true)]
theorem step658 (p : Nat → Bool) (h : Constraints p) : clause p c658 = true := by
  simpa only [c658,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause658
def c659 : List Lit := [(1305, false), (1308, false), (1314, true)]
theorem step659 (p : Nat → Bool) (h : Constraints p) : clause p c659 = true := by
  simpa only [c659,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause659
def c660 : List Lit := [(42, true), (1317, true)]
theorem step660 (p : Nat → Bool) (h : Constraints p) : clause p c660 = true := by
  simpa only [c660,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause660
def c661 : List Lit := [(41, true), (1317, true)]
theorem step661 (p : Nat → Bool) (h : Constraints p) : clause p c661 = true := by
  simpa only [c661,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause661
def c662 : List Lit := [(41, true), (42, true), (1318, true)]
theorem step662 (p : Nat → Bool) (h : Constraints p) : clause p c662 = true := by
  simpa only [c662,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause662
def c663 : List Lit := [(1317, false), (1319, true)]
theorem step663 (p : Nat → Bool) (h : Constraints p) : clause p c663 = true := by
  simpa only [c663,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause663
def c664 : List Lit := [(1318, false), (1320, true)]
theorem step664 (p : Nat → Bool) (h : Constraints p) : clause p c664 = true := by
  simpa only [c664,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause664
def c665 : List Lit := [(40, true), (1319, true)]
theorem step665 (p : Nat → Bool) (h : Constraints p) : clause p c665 = true := by
  simpa only [c665,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause665
def c666 : List Lit := [(40, true), (1317, false), (1320, true)]
theorem step666 (p : Nat → Bool) (h : Constraints p) : clause p c666 = true := by
  simpa only [c666,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause666
def c667 : List Lit := [(45, true), (1322, true)]
theorem step667 (p : Nat → Bool) (h : Constraints p) : clause p c667 = true := by
  simpa only [c667,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause667
def c668 : List Lit := [(44, true), (1322, true)]
theorem step668 (p : Nat → Bool) (h : Constraints p) : clause p c668 = true := by
  simpa only [c668,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause668
def c669 : List Lit := [(44, true), (45, true), (1323, true)]
theorem step669 (p : Nat → Bool) (h : Constraints p) : clause p c669 = true := by
  simpa only [c669,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause669
def c670 : List Lit := [(49, true), (1324, true)]
theorem step670 (p : Nat → Bool) (h : Constraints p) : clause p c670 = true := by
  simpa only [c670,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause670
def c671 : List Lit := [(48, true), (1324, true)]
theorem step671 (p : Nat → Bool) (h : Constraints p) : clause p c671 = true := by
  simpa only [c671,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause671
def c672 : List Lit := [(48, true), (49, true), (1325, true)]
theorem step672 (p : Nat → Bool) (h : Constraints p) : clause p c672 = true := by
  simpa only [c672,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block20.clause672
def c673 : List Lit := [(1324, false), (1326, true)]
theorem step673 (p : Nat → Bool) (h : Constraints p) : clause p c673 = true := by
  simpa only [c673,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause673
def c674 : List Lit := [(1325, false), (1327, true)]
theorem step674 (p : Nat → Bool) (h : Constraints p) : clause p c674 = true := by
  simpa only [c674,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause674
def c675 : List Lit := [(1322, false), (1326, true)]
theorem step675 (p : Nat → Bool) (h : Constraints p) : clause p c675 = true := by
  simpa only [c675,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause675
def c676 : List Lit := [(1322, false), (1324, false), (1327, true)]
theorem step676 (p : Nat → Bool) (h : Constraints p) : clause p c676 = true := by
  simpa only [c676,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause676
def c677 : List Lit := [(1322, false), (1325, false), (1328, true)]
theorem step677 (p : Nat → Bool) (h : Constraints p) : clause p c677 = true := by
  simpa only [c677,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause677
def c678 : List Lit := [(1323, false), (1327, true)]
theorem step678 (p : Nat → Bool) (h : Constraints p) : clause p c678 = true := by
  simpa only [c678,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause678
def c679 : List Lit := [(1323, false), (1324, false), (1328, true)]
theorem step679 (p : Nat → Bool) (h : Constraints p) : clause p c679 = true := by
  simpa only [c679,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause679
def c680 : List Lit := [(1323, false), (1325, false), (1329, true)]
theorem step680 (p : Nat → Bool) (h : Constraints p) : clause p c680 = true := by
  simpa only [c680,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause680
def c681 : List Lit := [(1326, false), (1330, true)]
theorem step681 (p : Nat → Bool) (h : Constraints p) : clause p c681 = true := by
  simpa only [c681,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause681
def c682 : List Lit := [(1327, false), (1331, true)]
theorem step682 (p : Nat → Bool) (h : Constraints p) : clause p c682 = true := by
  simpa only [c682,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause682
def c683 : List Lit := [(1328, false), (1332, true)]
theorem step683 (p : Nat → Bool) (h : Constraints p) : clause p c683 = true := by
  simpa only [c683,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause683
def c684 : List Lit := [(1329, false), (1333, true)]
theorem step684 (p : Nat → Bool) (h : Constraints p) : clause p c684 = true := by
  simpa only [c684,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause684
def c685 : List Lit := [(1319, false), (1330, true)]
theorem step685 (p : Nat → Bool) (h : Constraints p) : clause p c685 = true := by
  simpa only [c685,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause685
def c686 : List Lit := [(1319, false), (1326, false), (1331, true)]
theorem step686 (p : Nat → Bool) (h : Constraints p) : clause p c686 = true := by
  simpa only [c686,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause686
def c687 : List Lit := [(1319, false), (1327, false), (1332, true)]
theorem step687 (p : Nat → Bool) (h : Constraints p) : clause p c687 = true := by
  simpa only [c687,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause687
def c688 : List Lit := [(1319, false), (1328, false), (1333, true)]
theorem step688 (p : Nat → Bool) (h : Constraints p) : clause p c688 = true := by
  simpa only [c688,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause688
def c689 : List Lit := [(1319, false), (1329, false), (1334, true)]
theorem step689 (p : Nat → Bool) (h : Constraints p) : clause p c689 = true := by
  simpa only [c689,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause689
def c690 : List Lit := [(1320, false), (1331, true)]
theorem step690 (p : Nat → Bool) (h : Constraints p) : clause p c690 = true := by
  simpa only [c690,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause690
def c691 : List Lit := [(1320, false), (1326, false), (1332, true)]
theorem step691 (p : Nat → Bool) (h : Constraints p) : clause p c691 = true := by
  simpa only [c691,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause691
def c692 : List Lit := [(1320, false), (1327, false), (1333, true)]
theorem step692 (p : Nat → Bool) (h : Constraints p) : clause p c692 = true := by
  simpa only [c692,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause692
def c693 : List Lit := [(1330, false), (1337, true)]
theorem step693 (p : Nat → Bool) (h : Constraints p) : clause p c693 = true := by
  simpa only [c693,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause693
def c694 : List Lit := [(1331, false), (1338, true)]
theorem step694 (p : Nat → Bool) (h : Constraints p) : clause p c694 = true := by
  simpa only [c694,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause694
def c695 : List Lit := [(1332, false), (1339, true)]
theorem step695 (p : Nat → Bool) (h : Constraints p) : clause p c695 = true := by
  simpa only [c695,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause695
def c696 : List Lit := [(1333, false), (1340, true)]
theorem step696 (p : Nat → Bool) (h : Constraints p) : clause p c696 = true := by
  simpa only [c696,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause696
def c697 : List Lit := [(1334, false), (1341, true)]
theorem step697 (p : Nat → Bool) (h : Constraints p) : clause p c697 = true := by
  simpa only [c697,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause697
def c698 : List Lit := [(1311, false), (1337, true)]
theorem step698 (p : Nat → Bool) (h : Constraints p) : clause p c698 = true := by
  simpa only [c698,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause698
def c699 : List Lit := [(1311, false), (1330, false), (1338, true)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true := by
  simpa only [c699,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause699
def c700 : List Lit := [(1311, false), (1331, false), (1339, true)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true := by
  simpa only [c700,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause700
def c701 : List Lit := [(1311, false), (1332, false), (1340, true)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true := by
  simpa only [c701,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause701
def c702 : List Lit := [(1311, false), (1333, false), (1341, true)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true := by
  simpa only [c702,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause702
def c703 : List Lit := [(1312, false), (1330, false), (1339, true)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true := by
  simpa only [c703,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause703
def c704 : List Lit := [(1312, false), (1331, false), (1340, true)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true := by
  simpa only [c704,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block21.clause704
def c705 : List Lit := [(1312, false), (1332, false), (1341, true)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true := by
  simpa only [c705,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause705
def c706 : List Lit := [(1312, false), (1333, false), (1342, true)]
theorem step706 (p : Nat → Bool) (h : Constraints p) : clause p c706 = true := by
  simpa only [c706,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause706
def c707 : List Lit := [(1313, false), (1330, false), (1340, true)]
theorem step707 (p : Nat → Bool) (h : Constraints p) : clause p c707 = true := by
  simpa only [c707,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause707
def c708 : List Lit := [(1313, false), (1331, false), (1341, true)]
theorem step708 (p : Nat → Bool) (h : Constraints p) : clause p c708 = true := by
  simpa only [c708,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause708
def c709 : List Lit := [(1313, false), (1332, false), (1342, true)]
theorem step709 (p : Nat → Bool) (h : Constraints p) : clause p c709 = true := by
  simpa only [c709,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause709
def c710 : List Lit := [(1314, false), (1330, false), (1341, true)]
theorem step710 (p : Nat → Bool) (h : Constraints p) : clause p c710 = true := by
  simpa only [c710,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause710
def c711 : List Lit := [(1314, false), (1331, false), (1342, true)]
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true := by
  simpa only [c711,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause711
def c712 : List Lit := [(1288, false), (1340, false), (1354, true)]
theorem step712 (p : Nat → Bool) (h : Constraints p) : clause p c712 = true := by
  simpa only [c712,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause712
def c713 : List Lit := [(1288, false), (1341, false), (1355, true)]
theorem step713 (p : Nat → Bool) (h : Constraints p) : clause p c713 = true := by
  simpa only [c713,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause713
def c714 : List Lit := [(1289, false), (1337, false), (1352, true)]
theorem step714 (p : Nat → Bool) (h : Constraints p) : clause p c714 = true := by
  simpa only [c714,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause714
def c715 : List Lit := [(1289, false), (1338, false), (1353, true)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true := by
  simpa only [c715,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause715
def c716 : List Lit := [(1289, false), (1339, false), (1354, true)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true := by
  simpa only [c716,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause716
def c717 : List Lit := [(1289, false), (1340, false), (1355, true)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true := by
  simpa only [c717,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause717
def c718 : List Lit := [(1289, false), (1341, false), (1356, true)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true := by
  simpa only [c718,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause718
def c719 : List Lit := [(1289, false), (1342, false), (1357, true)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true := by
  simpa only [c719,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause719
def c720 : List Lit := [(1290, false), (1337, false), (1353, true)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true := by
  simpa only [c720,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause720
def c721 : List Lit := [(1290, false), (1338, false), (1354, true)]
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true := by
  simpa only [c721,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause721
def c722 : List Lit := [(1290, false), (1339, false), (1355, true)]
theorem step722 (p : Nat → Bool) (h : Constraints p) : clause p c722 = true := by
  simpa only [c722,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause722
def c723 : List Lit := [(1290, false), (1340, false), (1356, true)]
theorem step723 (p : Nat → Bool) (h : Constraints p) : clause p c723 = true := by
  simpa only [c723,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause723
def c724 : List Lit := [(1290, false), (1341, false), (1357, true)]
theorem step724 (p : Nat → Bool) (h : Constraints p) : clause p c724 = true := by
  simpa only [c724,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause724
def c725 : List Lit := [(1291, false), (1353, true)]
theorem step725 (p : Nat → Bool) (h : Constraints p) : clause p c725 = true := by
  simpa only [c725,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause725
def c726 : List Lit := [(1291, false), (1337, false), (1354, true)]
theorem step726 (p : Nat → Bool) (h : Constraints p) : clause p c726 = true := by
  simpa only [c726,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause726
def c727 : List Lit := [(1291, false), (1338, false), (1355, true)]
theorem step727 (p : Nat → Bool) (h : Constraints p) : clause p c727 = true := by
  simpa only [c727,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause727
def c728 : List Lit := [(1291, false), (1339, false), (1356, true)]
theorem step728 (p : Nat → Bool) (h : Constraints p) : clause p c728 = true := by
  simpa only [c728,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause728
def c729 : List Lit := [(1291, false), (1340, false), (1357, true)]
theorem step729 (p : Nat → Bool) (h : Constraints p) : clause p c729 = true := by
  simpa only [c729,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause729
def c730 : List Lit := [(1291, false), (1341, false), (1358, true)]
theorem step730 (p : Nat → Bool) (h : Constraints p) : clause p c730 = true := by
  simpa only [c730,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause730
def c731 : List Lit := [(1291, false), (1342, false), (1359, true)]
theorem step731 (p : Nat → Bool) (h : Constraints p) : clause p c731 = true := by
  simpa only [c731,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause731
def c732 : List Lit := [(1292, false), (1337, false), (1355, true)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true := by
  simpa only [c732,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause732
def c733 : List Lit := [(1292, false), (1338, false), (1356, true)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true := by
  simpa only [c733,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause733
def c734 : List Lit := [(1292, false), (1339, false), (1357, true)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true := by
  simpa only [c734,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause734
def c735 : List Lit := [(1292, false), (1340, false), (1358, true)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true := by
  simpa only [c735,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause735
def c736 : List Lit := [(55, true), (1363, true)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true := by
  simpa only [c736,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block22.clause736
def c737 : List Lit := [(53, true), (1363, true)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true := by
  simpa only [c737,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause737
def c738 : List Lit := [(53, true), (55, true), (1364, true)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true := by
  simpa only [c738,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause738
def c739 : List Lit := [(1363, false), (1365, true)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true := by
  simpa only [c739,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause739
def c740 : List Lit := [(1364, false), (1366, true)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true := by
  simpa only [c740,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause740
def c741 : List Lit := [(52, true), (1365, true)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true := by
  simpa only [c741,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause741
def c742 : List Lit := [(52, true), (1363, false), (1366, true)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true := by
  simpa only [c742,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause742
def c743 : List Lit := [(52, true), (1364, false), (1367, true)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true := by
  simpa only [c743,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause743
def c744 : List Lit := [(62, true), (1368, true)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true := by
  simpa only [c744,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause744
def c745 : List Lit := [(61, true), (1368, true)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true := by
  simpa only [c745,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause745
def c746 : List Lit := [(61, true), (62, true), (1369, true)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true := by
  simpa only [c746,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause746
def c747 : List Lit := [(1368, false), (1370, true)]
theorem step747 (p : Nat → Bool) (h : Constraints p) : clause p c747 = true := by
  simpa only [c747,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause747
def c748 : List Lit := [(1369, false), (1371, true)]
theorem step748 (p : Nat → Bool) (h : Constraints p) : clause p c748 = true := by
  simpa only [c748,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause748
def c749 : List Lit := [(57, true), (1370, true)]
theorem step749 (p : Nat → Bool) (h : Constraints p) : clause p c749 = true := by
  simpa only [c749,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause749
def c750 : List Lit := [(57, true), (1368, false), (1371, true)]
theorem step750 (p : Nat → Bool) (h : Constraints p) : clause p c750 = true := by
  simpa only [c750,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause750
def c751 : List Lit := [(57, true), (1369, false), (1372, true)]
theorem step751 (p : Nat → Bool) (h : Constraints p) : clause p c751 = true := by
  simpa only [c751,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause751
def c752 : List Lit := [(1370, false), (1373, true)]
theorem step752 (p : Nat → Bool) (h : Constraints p) : clause p c752 = true := by
  simpa only [c752,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause752
def c753 : List Lit := [(1365, false), (1370, false), (1374, true)]
theorem step753 (p : Nat → Bool) (h : Constraints p) : clause p c753 = true := by
  simpa only [c753,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause753
def c754 : List Lit := [(1365, false), (1371, false), (1375, true)]
theorem step754 (p : Nat → Bool) (h : Constraints p) : clause p c754 = true := by
  simpa only [c754,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause754
def c755 : List Lit := [(1365, false), (1372, false), (1376, true)]
theorem step755 (p : Nat → Bool) (h : Constraints p) : clause p c755 = true := by
  simpa only [c755,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause755
def c756 : List Lit := [(1366, false), (1370, false), (1375, true)]
theorem step756 (p : Nat → Bool) (h : Constraints p) : clause p c756 = true := by
  simpa only [c756,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause756
def c757 : List Lit := [(1366, false), (1371, false), (1376, true)]
theorem step757 (p : Nat → Bool) (h : Constraints p) : clause p c757 = true := by
  simpa only [c757,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause757
def c758 : List Lit := [(1366, false), (1372, false), (1377, true)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true := by
  simpa only [c758,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause758
def c759 : List Lit := [(1367, false), (1370, false), (1376, true)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true := by
  simpa only [c759,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause759
def c760 : List Lit := [(1367, false), (1371, false), (1377, true)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true := by
  simpa only [c760,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause760
def c761 : List Lit := [(1367, false), (1372, false), (1378, true)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true := by
  simpa only [c761,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause761
def c762 : List Lit := [(68, true), (1379, true)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true := by
  simpa only [c762,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause762
def c763 : List Lit := [(65, true), (1379, true)]
theorem step763 (p : Nat → Bool) (h : Constraints p) : clause p c763 = true := by
  simpa only [c763,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause763
def c764 : List Lit := [(1379, false), (1381, true)]
theorem step764 (p : Nat → Bool) (h : Constraints p) : clause p c764 = true := by
  simpa only [c764,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause764
def c765 : List Lit := [(63, true), (1381, true)]
theorem step765 (p : Nat → Bool) (h : Constraints p) : clause p c765 = true := by
  simpa only [c765,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause765
def c766 : List Lit := [(63, true), (1379, false), (1382, true)]
theorem step766 (p : Nat → Bool) (h : Constraints p) : clause p c766 = true := by
  simpa only [c766,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause766
def c767 : List Lit := [(73, true), (1384, true)]
theorem step767 (p : Nat → Bool) (h : Constraints p) : clause p c767 = true := by
  simpa only [c767,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause767
def c768 : List Lit := [(76, true), (1386, true)]
theorem step768 (p : Nat → Bool) (h : Constraints p) : clause p c768 = true := by
  simpa only [c768,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block23.clause768
def c769 : List Lit := [(1386, false), (1388, true)]
theorem step769 (p : Nat → Bool) (h : Constraints p) : clause p c769 = true := by
  simpa only [c769,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause769
def c770 : List Lit := [(1384, false), (1388, true)]
theorem step770 (p : Nat → Bool) (h : Constraints p) : clause p c770 = true := by
  simpa only [c770,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause770
def c771 : List Lit := [(1384, false), (1386, false), (1389, true)]
theorem step771 (p : Nat → Bool) (h : Constraints p) : clause p c771 = true := by
  simpa only [c771,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause771
def c772 : List Lit := [(1388, false), (1392, true)]
theorem step772 (p : Nat → Bool) (h : Constraints p) : clause p c772 = true := by
  simpa only [c772,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause772
def c773 : List Lit := [(1381, false), (1392, true)]
theorem step773 (p : Nat → Bool) (h : Constraints p) : clause p c773 = true := by
  simpa only [c773,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause773
def c774 : List Lit := [(1381, false), (1388, false), (1393, true)]
theorem step774 (p : Nat → Bool) (h : Constraints p) : clause p c774 = true := by
  simpa only [c774,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause774
def c775 : List Lit := [(1381, false), (1389, false), (1394, true)]
theorem step775 (p : Nat → Bool) (h : Constraints p) : clause p c775 = true := by
  simpa only [c775,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause775
def c776 : List Lit := [(1382, false), (1393, true)]
theorem step776 (p : Nat → Bool) (h : Constraints p) : clause p c776 = true := by
  simpa only [c776,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause776
def c777 : List Lit := [(1382, false), (1388, false), (1394, true)]
theorem step777 (p : Nat → Bool) (h : Constraints p) : clause p c777 = true := by
  simpa only [c777,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause777
def c778 : List Lit := [(1373, false), (1399, true)]
theorem step778 (p : Nat → Bool) (h : Constraints p) : clause p c778 = true := by
  simpa only [c778,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause778
def c779 : List Lit := [(1373, false), (1392, false), (1400, true)]
theorem step779 (p : Nat → Bool) (h : Constraints p) : clause p c779 = true := by
  simpa only [c779,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause779
def c780 : List Lit := [(1373, false), (1393, false), (1401, true)]
theorem step780 (p : Nat → Bool) (h : Constraints p) : clause p c780 = true := by
  simpa only [c780,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause780
def c781 : List Lit := [(1374, false), (1400, true)]
theorem step781 (p : Nat → Bool) (h : Constraints p) : clause p c781 = true := by
  simpa only [c781,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause781
def c782 : List Lit := [(1374, false), (1392, false), (1401, true)]
theorem step782 (p : Nat → Bool) (h : Constraints p) : clause p c782 = true := by
  simpa only [c782,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause782
def c783 : List Lit := [(1374, false), (1393, false), (1402, true)]
theorem step783 (p : Nat → Bool) (h : Constraints p) : clause p c783 = true := by
  simpa only [c783,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause783
def c784 : List Lit := [(1374, false), (1394, false), (1403, true)]
theorem step784 (p : Nat → Bool) (h : Constraints p) : clause p c784 = true := by
  simpa only [c784,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause784
def c785 : List Lit := [(1375, false), (1401, true)]
theorem step785 (p : Nat → Bool) (h : Constraints p) : clause p c785 = true := by
  simpa only [c785,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause785
def c786 : List Lit := [(1375, false), (1392, false), (1402, true)]
theorem step786 (p : Nat → Bool) (h : Constraints p) : clause p c786 = true := by
  simpa only [c786,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause786
def c787 : List Lit := [(1375, false), (1393, false), (1403, true)]
theorem step787 (p : Nat → Bool) (h : Constraints p) : clause p c787 = true := by
  simpa only [c787,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause787
def c788 : List Lit := [(1375, false), (1394, false), (1404, true)]
theorem step788 (p : Nat → Bool) (h : Constraints p) : clause p c788 = true := by
  simpa only [c788,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause788
def c789 : List Lit := [(1376, false), (1402, true)]
theorem step789 (p : Nat → Bool) (h : Constraints p) : clause p c789 = true := by
  simpa only [c789,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause789
def c790 : List Lit := [(1376, false), (1392, false), (1403, true)]
theorem step790 (p : Nat → Bool) (h : Constraints p) : clause p c790 = true := by
  simpa only [c790,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause790
def c791 : List Lit := [(1376, false), (1393, false), (1404, true)]
theorem step791 (p : Nat → Bool) (h : Constraints p) : clause p c791 = true := by
  simpa only [c791,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause791
def c792 : List Lit := [(1376, false), (1394, false), (1405, true)]
theorem step792 (p : Nat → Bool) (h : Constraints p) : clause p c792 = true := by
  simpa only [c792,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause792
def c793 : List Lit := [(1377, false), (1403, true)]
theorem step793 (p : Nat → Bool) (h : Constraints p) : clause p c793 = true := by
  simpa only [c793,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause793
def c794 : List Lit := [(1377, false), (1392, false), (1404, true)]
theorem step794 (p : Nat → Bool) (h : Constraints p) : clause p c794 = true := by
  simpa only [c794,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause794
def c795 : List Lit := [(1377, false), (1393, false), (1405, true)]
theorem step795 (p : Nat → Bool) (h : Constraints p) : clause p c795 = true := by
  simpa only [c795,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause795
def c796 : List Lit := [(1378, false), (1404, true)]
theorem step796 (p : Nat → Bool) (h : Constraints p) : clause p c796 = true := by
  simpa only [c796,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause796
def c797 : List Lit := [(1378, false), (1392, false), (1405, true)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true := by
  simpa only [c797,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause797
def c798 : List Lit := [(1378, false), (1393, false), (1406, true)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true := by
  simpa only [c798,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause798
def c799 : List Lit := [(83, true), (1412, true)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true := by
  simpa only [c799,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause799
def c800 : List Lit := [(81, true), (1412, true)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true := by
  simpa only [c800,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block24.clause800
def c801 : List Lit := [(1412, false), (1414, true)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true := by
  simpa only [c801,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause801
def c802 : List Lit := [(78, true), (1414, true)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true := by
  simpa only [c802,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause802
def c803 : List Lit := [(78, true), (1412, false), (1415, true)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true := by
  simpa only [c803,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause803
def c804 : List Lit := [(87, true), (1417, true)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true := by
  simpa only [c804,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause804
def c805 : List Lit := [(85, true), (1417, true)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true := by
  simpa only [c805,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause805
def c806 : List Lit := [(85, true), (87, true), (1418, true)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true := by
  simpa only [c806,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause806
def c807 : List Lit := [(91, true), (1419, true)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true := by
  simpa only [c807,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause807
def c808 : List Lit := [(89, true), (1419, true)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true := by
  simpa only [c808,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause808
def c809 : List Lit := [(89, true), (91, true), (1420, true)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true := by
  simpa only [c809,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause809
def c810 : List Lit := [(1419, false), (1421, true)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true := by
  simpa only [c810,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause810
def c811 : List Lit := [(1420, false), (1422, true)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true := by
  simpa only [c811,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause811
def c812 : List Lit := [(1417, false), (1421, true)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true := by
  simpa only [c812,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause812
def c813 : List Lit := [(1417, false), (1419, false), (1422, true)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true := by
  simpa only [c813,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause813
def c814 : List Lit := [(1417, false), (1420, false), (1423, true)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true := by
  simpa only [c814,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause814
def c815 : List Lit := [(1418, false), (1422, true)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true := by
  simpa only [c815,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause815
def c816 : List Lit := [(1418, false), (1419, false), (1423, true)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true := by
  simpa only [c816,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause816
def c817 : List Lit := [(1421, false), (1425, true)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true := by
  simpa only [c817,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause817
def c818 : List Lit := [(1422, false), (1426, true)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true := by
  simpa only [c818,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause818
def c819 : List Lit := [(1423, false), (1427, true)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true := by
  simpa only [c819,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause819
def c820 : List Lit := [(1414, false), (1425, true)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true := by
  simpa only [c820,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause820
def c821 : List Lit := [(1414, false), (1421, false), (1426, true)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true := by
  simpa only [c821,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause821
def c822 : List Lit := [(1414, false), (1422, false), (1427, true)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true := by
  simpa only [c822,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause822
def c823 : List Lit := [(1414, false), (1423, false), (1428, true)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true := by
  simpa only [c823,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause823
def c824 : List Lit := [(1415, false), (1426, true)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true := by
  simpa only [c824,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause824
def c825 : List Lit := [(1415, false), (1421, false), (1427, true)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true := by
  simpa only [c825,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause825
def c826 : List Lit := [(98, true), (1432, true)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true := by
  simpa only [c826,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause826
def c827 : List Lit := [(96, true), (1432, true)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true := by
  simpa only [c827,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause827
def c828 : List Lit := [(96, true), (98, true), (1433, true)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true := by
  simpa only [c828,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause828
def c829 : List Lit := [(1432, false), (1434, true)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true := by
  simpa only [c829,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause829
def c830 : List Lit := [(93, true), (1434, true)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true := by
  simpa only [c830,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause830
def c831 : List Lit := [(93, true), (1432, false), (1435, true)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true := by
  simpa only [c831,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause831
def c832 : List Lit := [(93, true), (1433, false), (1436, true)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true := by
  simpa only [c832,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block25.clause832
def c833 : List Lit := [(102, true), (1437, true)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true := by
  simpa only [c833,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause833
def c834 : List Lit := [(100, true), (1437, true)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true := by
  simpa only [c834,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause834
def c835 : List Lit := [(100, true), (102, true), (1438, true)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true := by
  simpa only [c835,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause835
def c836 : List Lit := [(105, true), (1439, true)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true := by
  simpa only [c836,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause836
def c837 : List Lit := [(103, true), (1439, true)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true := by
  simpa only [c837,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause837
def c838 : List Lit := [(1439, false), (1441, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true := by
  simpa only [c838,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause838
def c839 : List Lit := [(1437, false), (1441, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true := by
  simpa only [c839,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause839
def c840 : List Lit := [(1437, false), (1439, false), (1442, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true := by
  simpa only [c840,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause840
def c841 : List Lit := [(1438, false), (1439, false), (1443, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true := by
  simpa only [c841,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause841
def c842 : List Lit := [(1441, false), (1445, true)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true := by
  simpa only [c842,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause842
def c843 : List Lit := [(1442, false), (1446, true)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true := by
  simpa only [c843,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause843
def c844 : List Lit := [(1443, false), (1447, true)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true := by
  simpa only [c844,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause844
def c845 : List Lit := [(1434, false), (1445, true)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true := by
  simpa only [c845,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause845
def c846 : List Lit := [(1434, false), (1441, false), (1446, true)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true := by
  simpa only [c846,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause846
def c847 : List Lit := [(1434, false), (1442, false), (1447, true)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true := by
  simpa only [c847,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause847
def c848 : List Lit := [(1434, false), (1443, false), (1448, true)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true := by
  simpa only [c848,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause848
def c849 : List Lit := [(1435, false), (1446, true)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true := by
  simpa only [c849,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause849
def c850 : List Lit := [(1435, false), (1441, false), (1447, true)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true := by
  simpa only [c850,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause850
def c851 : List Lit := [(1435, false), (1442, false), (1448, true)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true := by
  simpa only [c851,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause851
def c852 : List Lit := [(1436, false), (1447, true)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true := by
  simpa only [c852,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause852
def c853 : List Lit := [(1445, false), (1452, true)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true := by
  simpa only [c853,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause853
def c854 : List Lit := [(1446, false), (1453, true)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true := by
  simpa only [c854,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause854
def c855 : List Lit := [(1447, false), (1454, true)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true := by
  simpa only [c855,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause855
def c856 : List Lit := [(1448, false), (1455, true)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true := by
  simpa only [c856,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause856
def c857 : List Lit := [(1425, false), (1452, true)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true := by
  simpa only [c857,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause857
def c858 : List Lit := [(1425, false), (1445, false), (1453, true)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true := by
  simpa only [c858,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause858
def c859 : List Lit := [(1425, false), (1446, false), (1454, true)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true := by
  simpa only [c859,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause859
def c860 : List Lit := [(1425, false), (1447, false), (1455, true)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true := by
  simpa only [c860,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause860
def c861 : List Lit := [(1426, false), (1453, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true := by
  simpa only [c861,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause861
def c862 : List Lit := [(1426, false), (1445, false), (1454, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true := by
  simpa only [c862,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause862
def c863 : List Lit := [(1426, false), (1446, false), (1455, true)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true := by
  simpa only [c863,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause863
def c864 : List Lit := [(1426, false), (1447, false), (1456, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true := by
  simpa only [c864,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block26.clause864
def c865 : List Lit := [(1427, false), (1454, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true := by
  simpa only [c865,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause865
def c866 : List Lit := [(1427, false), (1445, false), (1455, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true := by
  simpa only [c866,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause866
def c867 : List Lit := [(1427, false), (1446, false), (1456, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true := by
  simpa only [c867,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause867
def c868 : List Lit := [(1427, false), (1447, false), (1457, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true := by
  simpa only [c868,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause868
def c869 : List Lit := [(1428, false), (1455, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true := by
  simpa only [c869,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause869
def c870 : List Lit := [(1399, false), (1457, false), (1471, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true := by
  simpa only [c870,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause870
def c871 : List Lit := [(1400, false), (1453, false), (1468, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true := by
  simpa only [c871,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause871
def c872 : List Lit := [(1400, false), (1454, false), (1469, true)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true := by
  simpa only [c872,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause872
def c873 : List Lit := [(1400, false), (1455, false), (1470, true)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true := by
  simpa only [c873,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause873
def c874 : List Lit := [(1400, false), (1456, false), (1471, true)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true := by
  simpa only [c874,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause874
def c875 : List Lit := [(1400, false), (1457, false), (1472, true)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true := by
  simpa only [c875,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause875
def c876 : List Lit := [(1401, false), (1467, true)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true := by
  simpa only [c876,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause876
def c877 : List Lit := [(1401, false), (1452, false), (1468, true)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true := by
  simpa only [c877,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause877
def c878 : List Lit := [(1401, false), (1453, false), (1469, true)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true := by
  simpa only [c878,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause878
def c879 : List Lit := [(1401, false), (1454, false), (1470, true)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true := by
  simpa only [c879,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause879
def c880 : List Lit := [(1401, false), (1455, false), (1471, true)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true := by
  simpa only [c880,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause880
def c881 : List Lit := [(1401, false), (1456, false), (1472, true)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true := by
  simpa only [c881,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause881
def c882 : List Lit := [(1401, false), (1457, false), (1473, true)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true := by
  simpa only [c882,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause882
def c883 : List Lit := [(1402, false), (1452, false), (1469, true)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true := by
  simpa only [c883,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause883
def c884 : List Lit := [(1402, false), (1453, false), (1470, true)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true := by
  simpa only [c884,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause884
def c885 : List Lit := [(1402, false), (1454, false), (1471, true)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true := by
  simpa only [c885,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause885
def c886 : List Lit := [(1402, false), (1455, false), (1472, true)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true := by
  simpa only [c886,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause886
def c887 : List Lit := [(1402, false), (1456, false), (1473, true)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true := by
  simpa only [c887,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause887
def c888 : List Lit := [(1402, false), (1457, false), (1474, true)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true := by
  simpa only [c888,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause888
def c889 : List Lit := [(1403, false), (1469, true)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true := by
  simpa only [c889,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause889
def c890 : List Lit := [(1403, false), (1452, false), (1470, true)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true := by
  simpa only [c890,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause890
def c891 : List Lit := [(1403, false), (1453, false), (1471, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true := by
  simpa only [c891,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause891
def c892 : List Lit := [(1403, false), (1454, false), (1472, true)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true := by
  simpa only [c892,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause892
def c893 : List Lit := [(1403, false), (1455, false), (1473, true)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true := by
  simpa only [c893,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause893
def c894 : List Lit := [(1404, false), (1452, false), (1471, true)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true := by
  simpa only [c894,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause894
def c895 : List Lit := [(1404, false), (1453, false), (1472, true)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true := by
  simpa only [c895,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause895
def c896 : List Lit := [(1404, false), (1454, false), (1473, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true := by
  simpa only [c896,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block27.clause896
def c897 : List Lit := [(1404, false), (1455, false), (1474, true)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true := by
  simpa only [c897,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause897
def c898 : List Lit := [(1405, false), (1452, false), (1472, true)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true := by
  simpa only [c898,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause898
def c899 : List Lit := [(1405, false), (1453, false), (1473, true)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true := by
  simpa only [c899,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause899
def c900 : List Lit := [(1406, false), (1472, true)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true := by
  simpa only [c900,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause900
def c901 : List Lit := [(1406, false), (1452, false), (1473, true)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true := by
  simpa only [c901,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause901
def c902 : List Lit := [(1352, false), (1474, false), (1490, true)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true := by
  simpa only [c902,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause902
def c903 : List Lit := [(1353, false), (1473, false), (1490, true)]
theorem step903 (p : Nat → Bool) (h : Constraints p) : clause p c903 = true := by
  simpa only [c903,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause903
def c904 : List Lit := [(1354, false), (1472, false), (1490, true)]
theorem step904 (p : Nat → Bool) (h : Constraints p) : clause p c904 = true := by
  simpa only [c904,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause904
def c905 : List Lit := [(1355, false), (1471, false), (1490, true)]
theorem step905 (p : Nat → Bool) (h : Constraints p) : clause p c905 = true := by
  simpa only [c905,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause905
def c906 : List Lit := [(1356, false), (1470, false), (1490, true)]
theorem step906 (p : Nat → Bool) (h : Constraints p) : clause p c906 = true := by
  simpa only [c906,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause906
def c907 : List Lit := [(1357, false), (1469, false), (1490, true)]
theorem step907 (p : Nat → Bool) (h : Constraints p) : clause p c907 = true := by
  simpa only [c907,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause907
def c908 : List Lit := [(1358, false), (1468, false), (1490, true)]
theorem step908 (p : Nat → Bool) (h : Constraints p) : clause p c908 = true := by
  simpa only [c908,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause908
def c909 : List Lit := [(1359, false), (1467, false), (1490, true)]
theorem step909 (p : Nat → Bool) (h : Constraints p) : clause p c909 = true := by
  simpa only [c909,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause909
def c910 : List Lit := [(1490, false)]
theorem step910 (p : Nat → Bool) (h : Constraints p) : clause p c910 = true := by
  simpa only [c910,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause910
def c911 : List Lit := [(4, false), (5, false), (6, false), (7, false)]
theorem step911 (p : Nat → Bool) (h : Constraints p) : clause p c911 = true := by
  simpa only [c911,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause911
def c912 : List Lit := [(4, false), (5, false), (22, false), (23, false)]
theorem step912 (p : Nat → Bool) (h : Constraints p) : clause p c912 = true := by
  simpa only [c912,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause912
def c913 : List Lit := [(5, false), (7, false), (14, false), (16, false)]
theorem step913 (p : Nat → Bool) (h : Constraints p) : clause p c913 = true := by
  simpa only [c913,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause913
def c914 : List Lit := [(24, false), (25, false), (32, false), (33, false)]
theorem step914 (p : Nat → Bool) (h : Constraints p) : clause p c914 = true := by
  simpa only [c914,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause914
def c915 : List Lit := [(34, false), (37, false), (57, false), (58, false)]
theorem step915 (p : Nat → Bool) (h : Constraints p) : clause p c915 = true := by
  simpa only [c915,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause915
def c916 : List Lit := [(35, false), (36, false), (43, false), (45, false)]
theorem step916 (p : Nat → Bool) (h : Constraints p) : clause p c916 = true := by
  simpa only [c916,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause916
def c917 : List Lit := [(37, false), (39, false), (47, false), (49, false)]
theorem step917 (p : Nat → Bool) (h : Constraints p) : clause p c917 = true := by
  simpa only [c917,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause917
def c918 : List Lit := [(82, false), (83, false), (89, false), (90, false)]
theorem step918 (p : Nat → Bool) (h : Constraints p) : clause p c918 = true := by
  simpa only [c918,clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block28.clause918
end B112E091
