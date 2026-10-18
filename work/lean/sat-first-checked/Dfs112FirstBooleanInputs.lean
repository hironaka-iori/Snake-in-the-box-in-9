import Std
import Std.Sat.CNF

namespace Dfs112FirstBoolean
open Std.Sat
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unnecessarySimpa false

-- Exact clauses grouped into records to keep projection checking bounded.
structure Block0 (p : Nat → Bool) : Prop where
  clause1 : p 1 = false ∨ p 123 = true ∨ p 6 = true
  clause2 : p 1 = false ∨ p 123 = true ∨ p 2 = true
  clause3 : p 2 = false ∨ p 124 = true ∨ p 7 = true ∨ p 17 = true
  clause4 : p 2 = false ∨ p 124 = true ∨ p 1 = true ∨ p 17 = true
  clause5 : p 2 = false ∨ p 124 = true ∨ p 1 = true ∨ p 7 = true
  clause6 : p 3 = false ∨ p 4 = false ∨ p 8 = false ∨ p 10 = false
  clause7 : p 3 = false ∨ p 4 = false ∨ p 8 = false ∨ p 18 = false
  clause8 : p 3 = false ∨ p 4 = false ∨ p 10 = false ∨ p 18 = false
  clause9 : p 3 = false ∨ p 8 = false ∨ p 10 = false ∨ p 18 = false
  clause10 : p 3 = false ∨ p 125 = true ∨ p 8 = true ∨ p 10 = true ∨ p 18 = true
  clause11 : p 3 = false ∨ p 125 = true ∨ p 4 = true ∨ p 8 = true ∨ p 10 = true
  clause12 : p 4 = false ∨ p 3 = false ∨ p 11 = false ∨ p 57 = false
  clause13 : p 4 = false ∨ p 126 = true ∨ p 11 = true ∨ p 57 = true
  clause14 : p 4 = false ∨ p 126 = true ∨ p 3 = true ∨ p 57 = true
  clause15 : p 5 = false ∨ p 6 = false ∨ p 8 = false ∨ p 13 = false
  clause16 : p 5 = false ∨ p 6 = false ∨ p 8 = false ∨ p 24 = false
  clause17 : p 5 = false ∨ p 6 = false ∨ p 8 = false ∨ p 60 = false
  clause18 : p 5 = false ∨ p 6 = false ∨ p 13 = false ∨ p 24 = false
  clause19 : p 5 = false ∨ p 6 = false ∨ p 13 = false ∨ p 60 = false
  clause20 : p 5 = false ∨ p 6 = false ∨ p 24 = false ∨ p 60 = false
  clause21 : p 5 = false ∨ p 8 = false ∨ p 13 = false ∨ p 24 = false
  clause22 : p 5 = false ∨ p 8 = false ∨ p 13 = false ∨ p 60 = false
  clause23 : p 5 = false ∨ p 8 = false ∨ p 24 = false ∨ p 60 = false
  clause24 : p 5 = false ∨ p 13 = false ∨ p 24 = false ∨ p 60 = false
  clause25 : p 5 = false ∨ p 127 = true ∨ p 6 = true ∨ p 8 = true ∨ p 13 = true ∨ p 24 = true
  clause26 : p 6 = false ∨ p 1 = false ∨ p 5 = false ∨ p 9 = false
  clause27 : p 6 = false ∨ p 128 = true ∨ p 5 = true ∨ p 7 = true ∨ p 9 = true
  clause28 : p 6 = false ∨ p 128 = true ∨ p 1 = true ∨ p 7 = true ∨ p 9 = true
  clause29 : p 6 = false ∨ p 128 = true ∨ p 1 = true ∨ p 5 = true ∨ p 9 = true
  clause30 : p 6 = false ∨ p 128 = true ∨ p 1 = true ∨ p 5 = true ∨ p 7 = true
  clause31 : p 7 = false ∨ p 2 = false ∨ p 6 = false ∨ p 15 = false
  clause32 : p 7 = false ∨ p 2 = false ∨ p 6 = false ∨ p 26 = false

structure Block1 (p : Nat → Bool) : Prop where
  clause33 : p 7 = false ∨ p 2 = false ∨ p 6 = false ∨ p 61 = false
  clause34 : p 7 = false ∨ p 2 = false ∨ p 15 = false ∨ p 26 = false
  clause35 : p 7 = false ∨ p 2 = false ∨ p 15 = false ∨ p 61 = false
  clause36 : p 7 = false ∨ p 2 = false ∨ p 26 = false ∨ p 61 = false
  clause37 : p 7 = false ∨ p 6 = false ∨ p 15 = false ∨ p 26 = false
  clause38 : p 7 = false ∨ p 6 = false ∨ p 15 = false ∨ p 61 = false
  clause39 : p 7 = false ∨ p 6 = false ∨ p 26 = false ∨ p 61 = false
  clause40 : p 7 = false ∨ p 15 = false ∨ p 26 = false ∨ p 61 = false
  clause41 : p 7 = false ∨ p 129 = true ∨ p 2 = true ∨ p 6 = true ∨ p 15 = true ∨ p 26 = true
  clause42 : p 8 = false ∨ p 130 = true ∨ p 5 = true ∨ p 9 = true
  clause43 : p 8 = false ∨ p 130 = true ∨ p 3 = true ∨ p 9 = true
  clause44 : p 8 = false ∨ p 130 = true ∨ p 3 = true ∨ p 5 = true
  clause45 : p 9 = false ∨ p 131 = true ∨ p 8 = true
  clause46 : p 9 = false ∨ p 131 = true ∨ p 6 = true
  clause47 : p 10 = false ∨ p 3 = false ∨ p 11 = false ∨ p 32 = false
  clause48 : p 10 = false ∨ p 132 = true ∨ p 3 = true ∨ p 32 = true
  clause49 : p 11 = false ∨ p 4 = false ∨ p 10 = false ∨ p 12 = false
  clause50 : p 133 = false ∨ p 4 = false ∨ p 12 = false
  clause51 : p 11 = false ∨ p 133 = true ∨ p 10 = true ∨ p 12 = true
  clause52 : p 11 = false ∨ p 133 = true ∨ p 4 = true ∨ p 10 = true
  clause53 : p 12 = false ∨ p 134 = true ∨ p 16 = true
  clause54 : p 12 = false ∨ p 134 = true ∨ p 11 = true
  clause55 : p 13 = false ∨ p 135 = true ∨ p 14 = true
  clause56 : p 13 = false ∨ p 135 = true ∨ p 5 = true
  clause57 : p 14 = false ∨ p 136 = true ∨ p 15 = true
  clause58 : p 14 = false ∨ p 136 = true ∨ p 13 = true
  clause59 : p 15 = false ∨ p 7 = false ∨ p 14 = false ∨ p 16 = false
  clause60 : p 15 = false ∨ p 137 = true ∨ p 14 = true ∨ p 16 = true
  clause61 : p 15 = false ∨ p 137 = true ∨ p 7 = true ∨ p 16 = true
  clause62 : p 15 = false ∨ p 137 = true ∨ p 7 = true ∨ p 14 = true
  clause63 : p 16 = false ∨ p 138 = true ∨ p 15 = true
  clause64 : p 16 = false ∨ p 138 = true ∨ p 12 = true

structure Block2 (p : Nat → Bool) : Prop where
  clause65 : p 17 = false ∨ p 2 = false ∨ p 19 = false ∨ p 39 = false
  clause66 : p 17 = false ∨ p 2 = false ∨ p 39 = false ∨ p 73 = false
  clause67 : p 17 = false ∨ p 139 = true ∨ p 19 = true ∨ p 39 = true ∨ p 73 = true
  clause68 : p 17 = false ∨ p 139 = true ∨ p 2 = true ∨ p 19 = true ∨ p 39 = true
  clause69 : p 18 = false ∨ p 3 = false ∨ p 40 = false ∨ p 74 = false
  clause70 : p 18 = false ∨ p 140 = true ∨ p 3 = true ∨ p 40 = true
  clause71 : p 19 = false ∨ p 141 = true ∨ p 75 = true
  clause72 : p 19 = false ∨ p 141 = true ∨ p 17 = true
  clause73 : p 20 = false ∨ p 21 = false ∨ p 24 = false ∨ p 80 = false
  clause74 : p 20 = false ∨ p 142 = true ∨ p 24 = true ∨ p 80 = true
  clause75 : p 21 = false ∨ p 20 = false ∨ p 25 = false ∨ p 29 = false
  clause76 : p 21 = false ∨ p 143 = true ∨ p 20 = true ∨ p 29 = true ∨ p 81 = true
  clause77 : p 21 = false ∨ p 143 = true ∨ p 20 = true ∨ p 25 = true ∨ p 81 = true
  clause78 : p 22 = false ∨ p 23 = false ∨ p 33 = false ∨ p 42 = false
  clause79 : p 22 = false ∨ p 23 = false ∨ p 33 = false ∨ p 85 = false
  clause80 : p 22 = false ∨ p 23 = false ∨ p 42 = false ∨ p 85 = false
  clause81 : p 22 = false ∨ p 33 = false ∨ p 42 = false ∨ p 85 = false
  clause82 : p 23 = false ∨ p 145 = true ∨ p 28 = true ∨ p 86 = true
  clause83 : p 23 = false ∨ p 145 = true ∨ p 22 = true ∨ p 86 = true
  clause84 : p 23 = false ∨ p 145 = true ∨ p 22 = true ∨ p 28 = true
  clause85 : p 24 = false ∨ p 5 = false ∨ p 20 = false ∨ p 87 = false
  clause86 : p 24 = false ∨ p 5 = false ∨ p 25 = false ∨ p 87 = false
  clause87 : p 24 = false ∨ p 146 = true ∨ p 20 = true ∨ p 25 = true ∨ p 87 = true
  clause88 : p 24 = false ∨ p 146 = true ∨ p 5 = true ∨ p 25 = true ∨ p 87 = true
  clause89 : p 24 = false ∨ p 146 = true ∨ p 5 = true ∨ p 20 = true ∨ p 87 = true
  clause90 : p 24 = false ∨ p 146 = true ∨ p 5 = true ∨ p 20 = true ∨ p 25 = true
  clause91 : p 25 = false ∨ p 21 = false ∨ p 24 = false ∨ p 26 = false
  clause92 : p 25 = false ∨ p 21 = false ∨ p 24 = false ∨ p 27 = false
  clause93 : p 25 = false ∨ p 21 = false ∨ p 26 = false ∨ p 27 = false
  clause94 : p 25 = false ∨ p 24 = false ∨ p 26 = false ∨ p 27 = false
  clause95 : p 26 = false ∨ p 7 = true ∨ p 25 = true ∨ p 28 = true ∨ p 44 = true ∨ p 89 = true
  clause96 : p 26 = false ∨ p 7 = false ∨ p 25 = false ∨ p 44 = false

structure Block3 (p : Nat → Bool) : Prop where
  clause97 : p 26 = false ∨ p 25 = false ∨ p 28 = false ∨ p 89 = false
  clause98 : p 26 = false ∨ p 148 = true ∨ p 7 = true ∨ p 25 = true ∨ p 44 = true ∨ p 89 = true
  clause99 : p 27 = false ∨ p 25 = false ∨ p 28 = false ∨ p 36 = false
  clause100 : p 27 = false ∨ p 149 = true ∨ p 25 = true ∨ p 36 = true
  clause101 : p 27 = false ∨ p 149 = true ∨ p 25 = true ∨ p 28 = true
  clause102 : p 28 = false ∨ p 23 = false ∨ p 26 = false ∨ p 27 = false
  clause103 : p 28 = false ∨ p 23 = false ∨ p 26 = false ∨ p 92 = false
  clause104 : p 28 = false ∨ p 23 = false ∨ p 27 = false ∨ p 92 = false
  clause105 : p 28 = false ∨ p 26 = false ∨ p 27 = false ∨ p 92 = false
  clause106 : p 29 = false ∨ p 21 = false ∨ p 31 = false ∨ p 93 = false
  clause107 : p 29 = false ∨ p 151 = true ∨ p 31 = true ∨ p 93 = true
  clause108 : p 29 = false ∨ p 151 = true ∨ p 21 = true ∨ p 93 = true
  clause109 : p 30 = false ∨ p 31 = false ∨ p 33 = false ∨ p 34 = false
  clause110 : p 30 = false ∨ p 152 = true ∨ p 33 = true ∨ p 34 = true
  clause111 : p 31 = false ∨ p 153 = true ∨ p 30 = true ∨ p 94 = true
  clause112 : p 31 = false ∨ p 153 = true ∨ p 29 = true ∨ p 94 = true
  clause113 : p 31 = false ∨ p 153 = true ∨ p 29 = true ∨ p 30 = true
  clause114 : p 32 = false ∨ p 10 = false ∨ p 33 = false ∨ p 35 = false
  clause115 : p 32 = false ∨ p 10 = false ∨ p 35 = false ∨ p 47 = false
  clause116 : p 32 = false ∨ p 10 = false ∨ p 35 = false ∨ p 95 = false
  clause117 : p 32 = false ∨ p 10 = false ∨ p 47 = false ∨ p 95 = false
  clause118 : p 32 = false ∨ p 33 = false ∨ p 35 = false ∨ p 47 = false
  clause119 : p 32 = false ∨ p 33 = false ∨ p 35 = false ∨ p 95 = false
  clause120 : p 32 = false ∨ p 33 = false ∨ p 47 = false ∨ p 95 = false
  clause121 : p 32 = false ∨ p 35 = false ∨ p 47 = false ∨ p 95 = false
  clause122 : p 33 = false ∨ p 22 = false ∨ p 30 = false ∨ p 32 = false
  clause123 : p 33 = false ∨ p 22 = false ∨ p 32 = false ∨ p 37 = false
  clause124 : p 33 = false ∨ p 155 = true ∨ p 22 = true ∨ p 30 = true ∨ p 37 = true
  clause125 : p 34 = false ∨ p 156 = true ∨ p 37 = true ∨ p 52 = true ∨ p 100 = true
  clause126 : p 34 = false ∨ p 156 = true ∨ p 30 = true ∨ p 37 = true ∨ p 100 = true
  clause127 : p 34 = false ∨ p 156 = true ∨ p 30 = true ∨ p 37 = true ∨ p 52 = true
  clause128 : p 35 = false ∨ p 157 = true ∨ p 32 = true ∨ p 37 = true

structure Block4 (p : Nat → Bool) : Prop where
  clause129 : p 35 = false ∨ p 157 = true ∨ p 32 = true ∨ p 36 = true
  clause130 : p 36 = false ∨ p 158 = true ∨ p 35 = true
  clause131 : p 37 = false ∨ p 33 = false ∨ p 34 = false ∨ p 35 = false
  clause132 : p 38 = false ∨ p 39 = false ∨ p 42 = false ∨ p 43 = false
  clause133 : p 38 = false ∨ p 39 = false ∨ p 42 = false ∨ p 105 = false
  clause134 : p 38 = false ∨ p 39 = false ∨ p 43 = false ∨ p 105 = false
  clause135 : p 38 = false ∨ p 42 = false ∨ p 43 = false ∨ p 105 = false
  clause136 : p 39 = false ∨ p 17 = false ∨ p 38 = false ∨ p 106 = false
  clause137 : p 39 = false ∨ p 161 = true ∨ p 38 = true ∨ p 44 = true ∨ p 106 = true
  clause138 : p 39 = false ∨ p 161 = true ∨ p 17 = true ∨ p 44 = true ∨ p 106 = true
  clause139 : p 39 = false ∨ p 161 = true ∨ p 17 = true ∨ p 38 = true ∨ p 106 = true
  clause140 : p 40 = false ∨ p 18 = false ∨ p 41 = false ∨ p 45 = false
  clause141 : p 40 = false ∨ p 18 = false ∨ p 41 = false ∨ p 47 = false
  clause142 : p 40 = false ∨ p 18 = false ∨ p 42 = false ∨ p 47 = false
  clause143 : p 40 = false ∨ p 18 = false ∨ p 45 = false ∨ p 47 = false
  clause144 : p 40 = false ∨ p 41 = false ∨ p 42 = false ∨ p 47 = false
  clause145 : p 40 = false ∨ p 41 = false ∨ p 45 = false ∨ p 47 = false
  clause146 : p 41 = false ∨ p 40 = false ∨ p 48 = false ∨ p 107 = false
  clause147 : p 41 = false ∨ p 163 = true ∨ p 40 = true ∨ p 107 = true
  clause148 : p 41 = false ∨ p 163 = true ∨ p 40 = true ∨ p 48 = true
  clause149 : p 43 = false ∨ p 165 = true ∨ p 44 = true ∨ p 46 = true ∨ p 52 = true
  clause150 : p 43 = false ∨ p 165 = true ∨ p 38 = true ∨ p 44 = true ∨ p 52 = true
  clause151 : p 44 = false ∨ p 26 = false ∨ p 43 = false ∨ p 110 = false
  clause152 : p 44 = false ∨ p 39 = false ∨ p 43 = false ∨ p 53 = false
  clause153 : p 44 = false ∨ p 39 = false ∨ p 43 = false ∨ p 110 = false
  clause154 : p 44 = false ∨ p 39 = false ∨ p 53 = false ∨ p 110 = false
  clause155 : p 44 = false ∨ p 43 = false ∨ p 53 = false ∨ p 110 = false
  clause156 : p 45 = false ∨ p 167 = true ∨ p 46 = true
  clause157 : p 45 = false ∨ p 167 = true ∨ p 40 = true
  clause158 : p 46 = false ∨ p 168 = true ∨ p 42 = true ∨ p 45 = true
  clause159 : p 46 = false ∨ p 168 = true ∨ p 42 = true ∨ p 43 = true
  clause160 : p 47 = false ∨ p 32 = false ∨ p 40 = false ∨ p 48 = false

structure Block5 (p : Nat → Bool) : Prop where
  clause161 : p 47 = false ∨ p 169 = true ∨ p 40 = true ∨ p 48 = true
  clause162 : p 47 = false ∨ p 169 = true ∨ p 32 = true ∨ p 40 = true
  clause163 : p 48 = false ∨ p 41 = false ∨ p 47 = false ∨ p 49 = false
  clause164 : p 48 = false ∨ p 170 = true ∨ p 41 = true ∨ p 47 = true
  clause165 : p 49 = false ∨ p 171 = true ∨ p 54 = true
  clause166 : p 49 = false ∨ p 171 = true ∨ p 48 = true
  clause167 : p 50 = false ∨ p 172 = true ∨ p 52 = true ∨ p 118 = true
  clause168 : p 50 = false ∨ p 172 = true ∨ p 51 = true ∨ p 118 = true
  clause169 : p 50 = false ∨ p 172 = true ∨ p 51 = true ∨ p 52 = true
  clause170 : p 173 = false ∨ p 50 = false ∨ p 53 = false
  clause171 : p 51 = false ∨ p 173 = true ∨ p 53 = true
  clause172 : p 52 = false ∨ p 34 = false ∨ p 43 = false ∨ p 50 = false
  clause173 : p 52 = false ∨ p 34 = false ∨ p 43 = false ∨ p 53 = false
  clause174 : p 52 = false ∨ p 34 = false ∨ p 50 = false ∨ p 53 = false
  clause175 : p 52 = false ∨ p 43 = false ∨ p 50 = false ∨ p 53 = false
  clause176 : p 52 = false ∨ p 174 = true ∨ p 34 = true ∨ p 43 = true ∨ p 53 = true
  clause177 : p 53 = false ∨ p 44 = false ∨ p 51 = false ∨ p 54 = false
  clause178 : p 53 = false ∨ p 44 = false ∨ p 52 = false ∨ p 54 = false
  clause179 : p 53 = false ∨ p 51 = false ∨ p 52 = false ∨ p 54 = false
  clause180 : p 54 = false ∨ p 49 = false ∨ p 53 = false ∨ p 122 = false
  clause181 : p 54 = false ∨ p 176 = true ∨ p 53 = true ∨ p 122 = true
  clause182 : p 55 = false ∨ p 56 = false ∨ p 60 = false ∨ p 64 = false
  clause183 : p 55 = false ∨ p 56 = false ∨ p 60 = false ∨ p 72 = false
  clause184 : p 55 = false ∨ p 56 = false ∨ p 60 = false ∨ p 80 = false
  clause185 : p 55 = false ∨ p 56 = false ∨ p 64 = false ∨ p 72 = false
  clause186 : p 55 = false ∨ p 56 = false ∨ p 64 = false ∨ p 80 = false
  clause187 : p 55 = false ∨ p 56 = false ∨ p 72 = false ∨ p 80 = false
  clause188 : p 55 = false ∨ p 60 = false ∨ p 64 = false ∨ p 72 = false
  clause189 : p 55 = false ∨ p 60 = false ∨ p 64 = false ∨ p 80 = false
  clause190 : p 55 = false ∨ p 60 = false ∨ p 72 = false ∨ p 80 = false
  clause191 : p 55 = false ∨ p 64 = false ∨ p 72 = false ∨ p 80 = false
  clause192 : p 177 = false ∨ p 56 = false ∨ p 60 = false

structure Block6 (p : Nat → Bool) : Prop where
  clause193 : p 177 = false ∨ p 60 = false ∨ p 64 = false
  clause194 : p 55 = false ∨ p 177 = true ∨ p 60 = true ∨ p 64 = true ∨ p 72 = true ∨ p 80 = true
  clause195 : p 55 = false ∨ p 177 = true ∨ p 56 = true ∨ p 64 = true ∨ p 72 = true ∨ p 80 = true
  clause196 : p 55 = false ∨ p 177 = true ∨ p 56 = true ∨ p 60 = true ∨ p 72 = true ∨ p 80 = true
  clause197 : p 56 = false ∨ p 55 = false ∨ p 57 = false ∨ p 65 = false
  clause198 : p 56 = false ∨ p 55 = false ∨ p 57 = false ∨ p 81 = false
  clause199 : p 56 = false ∨ p 55 = false ∨ p 65 = false ∨ p 81 = false
  clause200 : p 56 = false ∨ p 178 = true ∨ p 57 = true ∨ p 65 = true ∨ p 81 = true
  clause201 : p 56 = false ∨ p 178 = true ∨ p 55 = true ∨ p 65 = true ∨ p 81 = true
  clause202 : p 56 = false ∨ p 178 = true ∨ p 55 = true ∨ p 57 = true ∨ p 81 = true
  clause203 : p 179 = false ∨ p 57 = true
  clause204 : p 57 = false ∨ p 4 = false ∨ p 56 = false ∨ p 59 = false
  clause205 : p 57 = false ∨ p 4 = false ∨ p 56 = false ∨ p 62 = false
  clause206 : p 57 = false ∨ p 4 = false ∨ p 56 = false ∨ p 84 = false
  clause207 : p 57 = false ∨ p 4 = false ∨ p 59 = false ∨ p 62 = false
  clause208 : p 57 = false ∨ p 4 = false ∨ p 59 = false ∨ p 84 = false
  clause209 : p 57 = false ∨ p 4 = false ∨ p 62 = false ∨ p 84 = false
  clause210 : p 57 = false ∨ p 56 = false ∨ p 59 = false ∨ p 62 = false
  clause211 : p 57 = false ∨ p 56 = false ∨ p 59 = false ∨ p 84 = false
  clause212 : p 57 = false ∨ p 56 = false ∨ p 62 = false ∨ p 84 = false
  clause213 : p 57 = false ∨ p 59 = false ∨ p 62 = false ∨ p 84 = false
  clause214 : p 58 = false ∨ p 59 = false ∨ p 68 = false ∨ p 85 = false
  clause215 : p 58 = false ∨ p 180 = true ∨ p 59 = true ∨ p 85 = true
  clause216 : p 59 = false ∨ p 57 = false ∨ p 58 = false ∨ p 63 = false
  clause217 : p 59 = false ∨ p 57 = false ∨ p 58 = false ∨ p 75 = false
  clause218 : p 59 = false ∨ p 57 = false ∨ p 63 = false ∨ p 75 = false
  clause219 : p 59 = false ∨ p 57 = false ∨ p 75 = false ∨ p 86 = false
  clause220 : p 59 = false ∨ p 58 = false ∨ p 63 = false ∨ p 75 = false
  clause221 : p 59 = false ∨ p 63 = false ∨ p 75 = false ∨ p 86 = false
  clause222 : p 59 = false ∨ p 181 = true ∨ p 57 = true ∨ p 58 = true ∨ p 63 = true ∨ p 86 = true
  clause223 : p 60 = false ∨ p 5 = false ∨ p 55 = false ∨ p 87 = false
  clause224 : p 60 = false ∨ p 182 = true ∨ p 55 = true ∨ p 87 = true

structure Block7 (p : Nat → Bool) : Prop where
  clause225 : p 60 = false ∨ p 182 = true ∨ p 5 = true ∨ p 87 = true
  clause226 : p 60 = false ∨ p 182 = true ∨ p 5 = true ∨ p 55 = true
  clause227 : p 61 = false ∨ p 7 = false ∨ p 63 = false ∨ p 89 = false
  clause228 : p 61 = false ∨ p 183 = true ∨ p 63 = true ∨ p 89 = true
  clause229 : p 61 = false ∨ p 183 = true ∨ p 7 = true ∨ p 89 = true
  clause230 : p 61 = false ∨ p 183 = true ∨ p 7 = true ∨ p 63 = true
  clause231 : p 62 = false ∨ p 57 = false ∨ p 63 = false ∨ p 70 = false
  clause232 : p 62 = false ∨ p 184 = true ∨ p 63 = true ∨ p 70 = true
  clause233 : p 62 = false ∨ p 184 = true ∨ p 57 = true ∨ p 70 = true
  clause234 : p 62 = false ∨ p 184 = true ∨ p 57 = true ∨ p 63 = true
  clause235 : p 63 = false ∨ p 59 = false ∨ p 61 = false ∨ p 62 = false
  clause236 : p 63 = false ∨ p 59 = false ∨ p 61 = false ∨ p 92 = false
  clause237 : p 63 = false ∨ p 59 = false ∨ p 62 = false ∨ p 92 = false
  clause238 : p 63 = false ∨ p 61 = false ∨ p 62 = false ∨ p 92 = false
  clause239 : p 185 = false ∨ p 61 = false ∨ p 62 = false
  clause240 : p 63 = false ∨ p 185 = true ∨ p 59 = true ∨ p 62 = true ∨ p 92 = true
  clause241 : p 63 = false ∨ p 185 = true ∨ p 59 = true ∨ p 61 = true ∨ p 92 = true
  clause242 : p 64 = false ∨ p 186 = true ∨ p 65 = true ∨ p 66 = true
  clause243 : p 64 = false ∨ p 186 = true ∨ p 55 = true ∨ p 66 = true
  clause244 : p 64 = false ∨ p 186 = true ∨ p 55 = true ∨ p 65 = true
  clause245 : p 65 = false ∨ p 56 = false ∨ p 64 = false ∨ p 67 = false
  clause246 : p 65 = false ∨ p 56 = false ∨ p 64 = false ∨ p 93 = false
  clause247 : p 65 = false ∨ p 56 = false ∨ p 67 = false ∨ p 93 = false
  clause248 : p 65 = false ∨ p 64 = false ∨ p 67 = false ∨ p 93 = false
  clause249 : p 187 = false ∨ p 64 = false ∨ p 67 = false
  clause250 : p 65 = false ∨ p 187 = true ∨ p 56 = true ∨ p 64 = true ∨ p 93 = true
  clause251 : p 66 = false ∨ p 64 = false ∨ p 67 = false ∨ p 68 = false
  clause252 : p 188 = false ∨ p 64 = false ∨ p 67 = false
  clause253 : p 66 = false ∨ p 188 = true ∨ p 64 = true ∨ p 67 = true
  clause254 : p 67 = false ∨ p 65 = false ∨ p 66 = false ∨ p 94 = false
  clause255 : p 67 = false ∨ p 189 = true ∨ p 66 = true ∨ p 94 = true
  clause256 : p 67 = false ∨ p 189 = true ∨ p 65 = true ∨ p 94 = true

structure Block8 (p : Nat → Bool) : Prop where
  clause257 : p 67 = false ∨ p 189 = true ∨ p 65 = true ∨ p 66 = true
  clause258 : p 68 = false ∨ p 58 = false ∨ p 66 = false ∨ p 71 = false
  clause259 : p 68 = false ∨ p 190 = true ∨ p 66 = true ∨ p 71 = true
  clause260 : p 68 = false ∨ p 190 = true ∨ p 58 = true ∨ p 71 = true
  clause261 : p 68 = false ∨ p 190 = true ∨ p 58 = true ∨ p 66 = true
  clause262 : p 69 = false ∨ p 191 = true ∨ p 71 = true
  clause263 : p 69 = false ∨ p 191 = true ∨ p 70 = true
  clause264 : p 192 = false ∨ p 62 = false ∨ p 69 = false
  clause265 : p 70 = false ∨ p 192 = true ∨ p 69 = true
  clause266 : p 70 = false ∨ p 192 = true ∨ p 62 = true
  clause267 : p 193 = false ∨ p 68 = false ∨ p 69 = false
  clause268 : p 71 = false ∨ p 193 = true ∨ p 69 = true
  clause269 : p 71 = false ∨ p 193 = true ∨ p 68 = true
  clause270 : p 72 = false ∨ p 55 = false ∨ p 74 = false ∨ p 103 = false
  clause271 : p 72 = false ∨ p 194 = true ∨ p 55 = true ∨ p 103 = true
  clause272 : p 73 = false ∨ p 17 = false ∨ p 75 = false ∨ p 106 = false
  clause273 : p 73 = false ∨ p 195 = true ∨ p 75 = true ∨ p 106 = true
  clause274 : p 73 = false ∨ p 195 = true ∨ p 17 = true ∨ p 106 = true
  clause275 : p 73 = false ∨ p 195 = true ∨ p 17 = true ∨ p 75 = true
  clause276 : p 74 = false ∨ p 18 = false ∨ p 72 = false ∨ p 76 = false
  clause277 : p 74 = false ∨ p 18 = false ∨ p 76 = false ∨ p 77 = false
  clause278 : p 74 = false ∨ p 72 = false ∨ p 76 = false ∨ p 77 = false
  clause279 : p 196 = false ∨ p 76 = false ∨ p 77 = false
  clause280 : p 74 = false ∨ p 196 = true ∨ p 18 = true ∨ p 72 = true ∨ p 77 = true
  clause281 : p 75 = false ∨ p 19 = false ∨ p 59 = false ∨ p 79 = false
  clause282 : p 75 = false ∨ p 19 = false ∨ p 73 = false ∨ p 79 = false
  clause283 : p 75 = false ∨ p 59 = false ∨ p 73 = false ∨ p 79 = false
  clause284 : p 197 = false ∨ p 19 = false ∨ p 79 = false
  clause285 : p 75 = false ∨ p 197 = true ∨ p 59 = true ∨ p 73 = true ∨ p 79 = true
  clause286 : p 75 = false ∨ p 197 = true ∨ p 19 = true ∨ p 59 = true ∨ p 79 = true
  clause287 : p 75 = false ∨ p 197 = true ∨ p 19 = true ∨ p 59 = true ∨ p 73 = true
  clause288 : p 76 = false ∨ p 74 = true

structure Block9 (p : Nat → Bool) : Prop where
  clause289 : p 76 = true
  clause290 : p 77 = false ∨ p 199 = true ∨ p 78 = true
  clause291 : p 200 = false ∨ p 78 = true
  clause292 : p 78 = false ∨ p 77 = true ∨ p 79 = true
  clause293 : p 200 = false ∨ p 77 = false ∨ p 79 = false
  clause294 : p 78 = false ∨ p 200 = true ∨ p 79 = true
  clause295 : p 78 = false ∨ p 200 = true ∨ p 77 = true
  clause296 : p 79 = false ∨ p 201 = true ∨ p 78 = true
  clause297 : p 79 = false ∨ p 201 = true ∨ p 75 = true
  clause298 : p 80 = false ∨ p 20 = false ∨ p 55 = false ∨ p 81 = false
  clause299 : p 80 = false ∨ p 20 = false ∨ p 55 = false ∨ p 87 = false
  clause300 : p 80 = false ∨ p 55 = false ∨ p 81 = false ∨ p 87 = false
  clause301 : p 80 = false ∨ p 55 = false ∨ p 82 = false ∨ p 83 = false
  clause302 : p 80 = false ∨ p 55 = false ∨ p 83 = false ∨ p 87 = false
  clause303 : p 80 = false ∨ p 55 = false ∨ p 83 = false ∨ p 103 = false
  clause304 : p 80 = false ∨ p 55 = false ∨ p 87 = false ∨ p 103 = false
  clause305 : p 80 = false ∨ p 81 = false ∨ p 83 = false ∨ p 87 = false
  clause306 : p 80 = false ∨ p 81 = false ∨ p 87 = false ∨ p 103 = false
  clause307 : p 80 = false ∨ p 83 = false ∨ p 87 = false ∨ p 103 = false
  clause308 : p 80 = false ∨ p 202 = true ∨ p 55 = true ∨ p 81 = true ∨ p 82 = true ∨ p 83 = true ∨ p 87 = true ∨ p 103 = true
  clause309 : p 81 = false ∨ p 21 = false ∨ p 56 = false ∨ p 80 = false
  clause310 : p 81 = false ∨ p 21 = false ∨ p 56 = false ∨ p 84 = false
  clause311 : p 81 = false ∨ p 21 = false ∨ p 56 = false ∨ p 93 = false
  clause312 : p 81 = false ∨ p 21 = false ∨ p 56 = false ∨ p 104 = false
  clause313 : p 81 = false ∨ p 21 = false ∨ p 80 = false ∨ p 84 = false
  clause314 : p 81 = false ∨ p 21 = false ∨ p 80 = false ∨ p 93 = false
  clause315 : p 81 = false ∨ p 21 = false ∨ p 80 = false ∨ p 104 = false
  clause316 : p 81 = false ∨ p 21 = false ∨ p 84 = false ∨ p 93 = false
  clause317 : p 81 = false ∨ p 21 = false ∨ p 84 = false ∨ p 104 = false
  clause318 : p 81 = false ∨ p 21 = false ∨ p 93 = false ∨ p 104 = false
  clause319 : p 81 = false ∨ p 56 = false ∨ p 80 = false ∨ p 84 = false
  clause320 : p 81 = false ∨ p 56 = false ∨ p 80 = false ∨ p 93 = false

structure Block10 (p : Nat → Bool) : Prop where
  clause321 : p 81 = false ∨ p 56 = false ∨ p 80 = false ∨ p 104 = false
  clause322 : p 81 = false ∨ p 56 = false ∨ p 84 = false ∨ p 93 = false
  clause323 : p 81 = false ∨ p 56 = false ∨ p 84 = false ∨ p 104 = false
  clause324 : p 81 = false ∨ p 56 = false ∨ p 93 = false ∨ p 104 = false
  clause325 : p 81 = false ∨ p 80 = false ∨ p 84 = false ∨ p 93 = false
  clause326 : p 81 = false ∨ p 80 = false ∨ p 84 = false ∨ p 104 = false
  clause327 : p 81 = false ∨ p 80 = false ∨ p 93 = false ∨ p 104 = false
  clause328 : p 81 = false ∨ p 84 = false ∨ p 93 = false ∨ p 104 = false
  clause329 : p 82 = false ∨ p 80 = false ∨ p 85 = false ∨ p 88 = false
  clause330 : p 82 = false ∨ p 80 = false ∨ p 85 = false ∨ p 105 = false
  clause331 : p 82 = false ∨ p 80 = false ∨ p 88 = false ∨ p 105 = false
  clause332 : p 82 = false ∨ p 85 = false ∨ p 88 = false ∨ p 105 = false
  clause333 : p 82 = false ∨ p 204 = true ∨ p 80 = true ∨ p 85 = true ∨ p 105 = true
  clause334 : p 83 = false ∨ p 80 = false ∨ p 84 = false ∨ p 85 = false
  clause335 : p 83 = false ∨ p 80 = false ∨ p 84 = false ∨ p 90 = false
  clause336 : p 83 = false ∨ p 80 = false ∨ p 84 = false ∨ p 95 = false
  clause337 : p 83 = false ∨ p 80 = false ∨ p 85 = false ∨ p 90 = false
  clause338 : p 83 = false ∨ p 80 = false ∨ p 85 = false ∨ p 95 = false
  clause339 : p 83 = false ∨ p 80 = false ∨ p 90 = false ∨ p 95 = false
  clause340 : p 83 = false ∨ p 84 = false ∨ p 85 = false ∨ p 90 = false
  clause341 : p 83 = false ∨ p 84 = false ∨ p 85 = false ∨ p 95 = false
  clause342 : p 83 = false ∨ p 84 = false ∨ p 90 = false ∨ p 95 = false
  clause343 : p 83 = false ∨ p 85 = false ∨ p 90 = false ∨ p 95 = false
  clause344 : p 83 = false ∨ p 205 = true ∨ p 80 = true ∨ p 84 = true ∨ p 85 = true ∨ p 95 = true
  clause345 : p 84 = false ∨ p 57 = false ∨ p 83 = false ∨ p 86 = false
  clause346 : p 84 = false ∨ p 81 = false ∨ p 83 = false ∨ p 86 = false
  clause347 : p 84 = false ∨ p 81 = false ∨ p 83 = false ∨ p 96 = false
  clause348 : p 84 = false ∨ p 83 = false ∨ p 96 = false ∨ p 107 = false
  clause349 : p 84 = false ∨ p 206 = true ∨ p 81 = true ∨ p 83 = true ∨ p 86 = true ∨ p 96 = true ∨ p 107 = true
  clause350 : p 84 = false ∨ p 206 = true ∨ p 57 = true ∨ p 81 = true ∨ p 86 = true ∨ p 96 = true ∨ p 107 = true
  clause351 : p 84 = false ∨ p 206 = true ∨ p 57 = true ∨ p 81 = true ∨ p 83 = true ∨ p 86 = true ∨ p 107 = true
  clause352 : p 84 = false ∨ p 206 = true ∨ p 57 = true ∨ p 81 = true ∨ p 83 = true ∨ p 86 = true ∨ p 96 = true

structure Block11 (p : Nat → Bool) : Prop where
  clause353 : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 82 = false
  clause354 : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 83 = false
  clause355 : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 86 = false
  clause356 : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 91 = false
  clause357 : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 108 = false
  clause358 : p 85 = false ∨ p 22 = false ∨ p 91 = false ∨ p 108 = false
  clause359 : p 85 = false ∨ p 58 = false ∨ p 83 = false ∨ p 108 = false
  clause360 : p 85 = false ∨ p 58 = false ∨ p 86 = false ∨ p 108 = false
  clause361 : p 85 = false ∨ p 58 = false ∨ p 91 = false ∨ p 108 = false
  clause362 : p 85 = false ∨ p 82 = false ∨ p 83 = false ∨ p 108 = false
  clause363 : p 85 = false ∨ p 83 = false ∨ p 86 = false ∨ p 91 = false
  clause364 : p 85 = false ∨ p 83 = false ∨ p 86 = false ∨ p 108 = false
  clause365 : p 85 = false ∨ p 207 = true ∨ p 58 = true ∨ p 82 = true ∨ p 83 = true ∨ p 86 = true ∨ p 91 = true ∨ p 108 = true
  clause366 : p 85 = false ∨ p 207 = true ∨ p 22 = true ∨ p 58 = true ∨ p 82 = true ∨ p 83 = true ∨ p 86 = true ∨ p 91 = true
  clause367 : p 86 = false ∨ p 23 = false ∨ p 59 = false ∨ p 92 = false
  clause368 : p 86 = false ∨ p 23 = false ∨ p 59 = false ∨ p 97 = false
  clause369 : p 86 = false ∨ p 23 = false ∨ p 84 = false ∨ p 85 = false
  clause370 : p 86 = false ∨ p 23 = false ∨ p 84 = false ∨ p 92 = false
  clause371 : p 86 = false ∨ p 23 = false ∨ p 84 = false ∨ p 97 = false
  clause372 : p 86 = false ∨ p 23 = false ∨ p 85 = false ∨ p 97 = false
  clause373 : p 86 = false ∨ p 23 = false ∨ p 92 = false ∨ p 97 = false
  clause374 : p 86 = false ∨ p 59 = false ∨ p 84 = false ∨ p 85 = false
  clause375 : p 86 = false ∨ p 59 = false ∨ p 84 = false ∨ p 97 = false
  clause376 : p 86 = false ∨ p 59 = false ∨ p 85 = false ∨ p 97 = false
  clause377 : p 86 = false ∨ p 59 = false ∨ p 92 = false ∨ p 97 = false
  clause378 : p 86 = false ∨ p 84 = false ∨ p 85 = false ∨ p 92 = false
  clause379 : p 86 = false ∨ p 84 = false ∨ p 85 = false ∨ p 97 = false
  clause380 : p 86 = false ∨ p 84 = false ∨ p 92 = false ∨ p 97 = false
  clause381 : p 86 = false ∨ p 85 = false ∨ p 92 = false ∨ p 97 = false
  clause382 : p 209 = false ∨ p 87 = true
  clause383 : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 80 = false
  clause384 : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 88 = false

structure Block12 (p : Nat → Bool) : Prop where
  clause385 : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 90 = false
  clause386 : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 98 = false
  clause387 : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 109 = false
  clause388 : p 87 = false ∨ p 24 = false ∨ p 80 = false ∨ p 88 = false
  clause389 : p 87 = false ∨ p 24 = false ∨ p 80 = false ∨ p 90 = false
  clause390 : p 87 = false ∨ p 24 = false ∨ p 80 = false ∨ p 98 = false
  clause391 : p 87 = false ∨ p 24 = false ∨ p 80 = false ∨ p 109 = false
  clause392 : p 87 = false ∨ p 24 = false ∨ p 88 = false ∨ p 90 = false
  clause393 : p 87 = false ∨ p 24 = false ∨ p 88 = false ∨ p 98 = false
  clause394 : p 87 = false ∨ p 24 = false ∨ p 88 = false ∨ p 109 = false
  clause395 : p 87 = false ∨ p 24 = false ∨ p 90 = false ∨ p 98 = false
  clause396 : p 87 = false ∨ p 24 = false ∨ p 90 = false ∨ p 109 = false
  clause397 : p 87 = false ∨ p 24 = false ∨ p 98 = false ∨ p 109 = false
  clause398 : p 87 = false ∨ p 60 = false ∨ p 80 = false ∨ p 88 = false
  clause399 : p 87 = false ∨ p 60 = false ∨ p 80 = false ∨ p 90 = false
  clause400 : p 87 = false ∨ p 60 = false ∨ p 80 = false ∨ p 98 = false
  clause401 : p 87 = false ∨ p 60 = false ∨ p 80 = false ∨ p 109 = false
  clause402 : p 87 = false ∨ p 60 = false ∨ p 88 = false ∨ p 90 = false
  clause403 : p 87 = false ∨ p 60 = false ∨ p 88 = false ∨ p 98 = false
  clause404 : p 87 = false ∨ p 60 = false ∨ p 88 = false ∨ p 109 = false
  clause405 : p 87 = false ∨ p 60 = false ∨ p 90 = false ∨ p 98 = false
  clause406 : p 87 = false ∨ p 60 = false ∨ p 90 = false ∨ p 109 = false
  clause407 : p 87 = false ∨ p 60 = false ∨ p 98 = false ∨ p 109 = false
  clause408 : p 87 = false ∨ p 80 = false ∨ p 88 = false ∨ p 90 = false
  clause409 : p 87 = false ∨ p 80 = false ∨ p 88 = false ∨ p 98 = false
  clause410 : p 87 = false ∨ p 80 = false ∨ p 88 = false ∨ p 109 = false
  clause411 : p 87 = false ∨ p 80 = false ∨ p 90 = false ∨ p 98 = false
  clause412 : p 87 = false ∨ p 80 = false ∨ p 90 = false ∨ p 109 = false
  clause413 : p 87 = false ∨ p 80 = false ∨ p 98 = false ∨ p 109 = false
  clause414 : p 87 = false ∨ p 88 = false ∨ p 90 = false ∨ p 98 = false
  clause415 : p 87 = false ∨ p 88 = false ∨ p 90 = false ∨ p 109 = false
  clause416 : p 87 = false ∨ p 88 = false ∨ p 98 = false ∨ p 109 = false

structure Block13 (p : Nat → Bool) : Prop where
  clause417 : p 87 = false ∨ p 90 = false ∨ p 98 = false ∨ p 109 = false
  clause418 : p 88 = false ∨ p 87 = false ∨ p 89 = false ∨ p 100 = false
  clause419 : p 88 = false ∨ p 89 = false ∨ p 91 = false ∨ p 100 = false
  clause420 : p 88 = false ∨ p 210 = true ∨ p 87 = true ∨ p 89 = true ∨ p 91 = true ∨ p 100 = true
  clause421 : p 88 = false ∨ p 210 = true ∨ p 82 = true ∨ p 89 = true ∨ p 91 = true ∨ p 100 = true
  clause422 : p 88 = false ∨ p 210 = true ∨ p 82 = true ∨ p 87 = true ∨ p 91 = true ∨ p 100 = true
  clause423 : p 88 = false ∨ p 210 = true ∨ p 82 = true ∨ p 87 = true ∨ p 89 = true ∨ p 100 = true
  clause424 : p 88 = false ∨ p 210 = true ∨ p 82 = true ∨ p 87 = true ∨ p 89 = true ∨ p 91 = true
  clause425 : p 89 = false ∨ p 26 = false ∨ p 61 = false ∨ p 88 = false
  clause426 : p 89 = false ∨ p 26 = false ∨ p 61 = false ∨ p 92 = false
  clause427 : p 89 = false ∨ p 26 = false ∨ p 61 = false ∨ p 101 = false
  clause428 : p 89 = false ∨ p 26 = false ∨ p 61 = false ∨ p 110 = false
  clause429 : p 89 = false ∨ p 26 = false ∨ p 88 = false ∨ p 92 = false
  clause430 : p 89 = false ∨ p 26 = false ∨ p 88 = false ∨ p 101 = false
  clause431 : p 89 = false ∨ p 26 = false ∨ p 92 = false ∨ p 101 = false
  clause432 : p 89 = false ∨ p 26 = false ∨ p 92 = false ∨ p 110 = false
  clause433 : p 89 = false ∨ p 26 = false ∨ p 101 = false ∨ p 110 = false
  clause434 : p 89 = false ∨ p 61 = false ∨ p 88 = false ∨ p 92 = false
  clause435 : p 89 = false ∨ p 61 = false ∨ p 88 = false ∨ p 101 = false
  clause436 : p 89 = false ∨ p 61 = false ∨ p 88 = false ∨ p 110 = false
  clause437 : p 89 = false ∨ p 61 = false ∨ p 92 = false ∨ p 101 = false
  clause438 : p 89 = false ∨ p 61 = false ∨ p 92 = false ∨ p 110 = false
  clause439 : p 89 = false ∨ p 61 = false ∨ p 101 = false ∨ p 110 = false
  clause440 : p 89 = false ∨ p 88 = false ∨ p 92 = false ∨ p 101 = false
  clause441 : p 89 = false ∨ p 88 = false ∨ p 92 = false ∨ p 110 = false
  clause442 : p 89 = false ∨ p 88 = false ∨ p 101 = false ∨ p 110 = false
  clause443 : p 89 = false ∨ p 92 = false ∨ p 101 = false ∨ p 110 = false
  clause444 : p 90 = false ∨ p 212 = true ∨ p 87 = true ∨ p 91 = true
  clause445 : p 90 = false ∨ p 212 = true ∨ p 83 = true ∨ p 91 = true
  clause446 : p 90 = false ∨ p 212 = true ∨ p 83 = true ∨ p 87 = true
  clause447 : p 91 = false ∨ p 85 = false ∨ p 88 = false ∨ p 90 = false
  clause448 : p 91 = false ∨ p 85 = false ∨ p 88 = false ∨ p 92 = false

structure Block14 (p : Nat → Bool) : Prop where
  clause449 : p 91 = false ∨ p 85 = false ∨ p 90 = false ∨ p 92 = false
  clause450 : p 91 = false ∨ p 88 = false ∨ p 90 = false ∨ p 92 = false
  clause451 : p 91 = false ∨ p 213 = true ∨ p 85 = true ∨ p 90 = true ∨ p 92 = true
  clause452 : p 91 = false ∨ p 213 = true ∨ p 85 = true ∨ p 88 = true ∨ p 92 = true
  clause453 : p 92 = false ∨ p 63 = false ∨ p 86 = false ∨ p 112 = false
  clause454 : p 92 = false ∨ p 63 = false ∨ p 102 = false ∨ p 112 = false
  clause455 : p 92 = false ∨ p 86 = false ∨ p 89 = false ∨ p 91 = false
  clause456 : p 92 = false ∨ p 91 = false ∨ p 102 = false ∨ p 112 = false
  clause457 : p 93 = false ∨ p 29 = false ∨ p 65 = false ∨ p 99 = false
  clause458 : p 93 = false ∨ p 29 = false ∨ p 65 = false ∨ p 114 = false
  clause459 : p 93 = false ∨ p 29 = false ∨ p 81 = false ∨ p 99 = false
  clause460 : p 93 = false ∨ p 29 = false ∨ p 94 = false ∨ p 99 = false
  clause461 : p 93 = false ∨ p 65 = false ∨ p 94 = false ∨ p 96 = false
  clause462 : p 93 = false ∨ p 65 = false ∨ p 94 = false ∨ p 114 = false
  clause463 : p 93 = false ∨ p 65 = false ∨ p 99 = false ∨ p 114 = false
  clause464 : p 93 = false ∨ p 81 = false ∨ p 94 = false ∨ p 114 = false
  clause465 : p 93 = false ∨ p 94 = false ∨ p 96 = false ∨ p 114 = false
  clause466 : p 93 = false ∨ p 94 = false ∨ p 99 = false ∨ p 114 = false
  clause467 : p 94 = false ∨ p 31 = false ∨ p 67 = false ∨ p 93 = false
  clause468 : p 94 = false ∨ p 31 = false ∨ p 67 = false ∨ p 97 = false
  clause469 : p 94 = false ∨ p 31 = false ∨ p 67 = false ∨ p 101 = false
  clause470 : p 94 = false ∨ p 31 = false ∨ p 67 = false ∨ p 116 = false
  clause471 : p 94 = false ∨ p 31 = false ∨ p 93 = false ∨ p 97 = false
  clause472 : p 94 = false ∨ p 31 = false ∨ p 93 = false ∨ p 101 = false
  clause473 : p 94 = false ∨ p 31 = false ∨ p 93 = false ∨ p 116 = false
  clause474 : p 94 = false ∨ p 31 = false ∨ p 97 = false ∨ p 101 = false
  clause475 : p 94 = false ∨ p 31 = false ∨ p 97 = false ∨ p 116 = false
  clause476 : p 94 = false ∨ p 31 = false ∨ p 101 = false ∨ p 116 = false
  clause477 : p 94 = false ∨ p 67 = false ∨ p 93 = false ∨ p 97 = false
  clause478 : p 94 = false ∨ p 67 = false ∨ p 93 = false ∨ p 101 = false
  clause479 : p 94 = false ∨ p 67 = false ∨ p 93 = false ∨ p 116 = false
  clause480 : p 94 = false ∨ p 67 = false ∨ p 97 = false ∨ p 101 = false

structure Block15 (p : Nat → Bool) : Prop where
  clause481 : p 94 = false ∨ p 67 = false ∨ p 97 = false ∨ p 116 = false
  clause482 : p 94 = false ∨ p 67 = false ∨ p 101 = false ∨ p 116 = false
  clause483 : p 94 = false ∨ p 93 = false ∨ p 97 = false ∨ p 101 = false
  clause484 : p 94 = false ∨ p 93 = false ∨ p 97 = false ∨ p 116 = false
  clause485 : p 94 = false ∨ p 93 = false ∨ p 101 = false ∨ p 116 = false
  clause486 : p 94 = false ∨ p 97 = false ∨ p 101 = false ∨ p 116 = false
  clause487 : p 95 = false ∨ p 217 = true ∨ p 83 = true ∨ p 96 = true
  clause488 : p 95 = false ∨ p 217 = true ∨ p 32 = true ∨ p 96 = true
  clause489 : p 95 = false ∨ p 217 = true ∨ p 32 = true ∨ p 83 = true
  clause490 : p 96 = false ∨ p 84 = false ∨ p 93 = false ∨ p 95 = false
  clause491 : p 96 = false ∨ p 84 = false ∨ p 93 = false ∨ p 97 = false
  clause492 : p 96 = false ∨ p 84 = false ∨ p 95 = false ∨ p 97 = false
  clause493 : p 96 = false ∨ p 93 = false ∨ p 95 = false ∨ p 97 = false
  clause494 : p 96 = false ∨ p 218 = true ∨ p 84 = true ∨ p 93 = true ∨ p 95 = true
  clause495 : p 97 = false ∨ p 219 = true ∨ p 94 = true ∨ p 96 = true ∨ p 102 = true
  clause496 : p 97 = false ∨ p 219 = true ∨ p 86 = true ∨ p 96 = true ∨ p 102 = true
  clause497 : p 97 = false ∨ p 219 = true ∨ p 86 = true ∨ p 94 = true ∨ p 102 = true
  clause498 : p 97 = false ∨ p 219 = true ∨ p 86 = true ∨ p 94 = true ∨ p 96 = true
  clause499 : p 98 = false ∨ p 87 = false ∨ p 99 = false ∨ p 118 = false
  clause500 : p 98 = false ∨ p 87 = false ∨ p 100 = false ∨ p 118 = false
  clause501 : p 98 = false ∨ p 220 = true ∨ p 99 = true ∨ p 100 = true ∨ p 118 = true
  clause502 : p 98 = false ∨ p 220 = true ∨ p 87 = true ∨ p 100 = true ∨ p 118 = true
  clause503 : p 98 = false ∨ p 220 = true ∨ p 87 = true ∨ p 99 = true ∨ p 118 = true
  clause504 : p 98 = false ∨ p 220 = true ∨ p 87 = true ∨ p 99 = true ∨ p 100 = true
  clause505 : p 99 = false ∨ p 93 = false ∨ p 98 = false ∨ p 101 = false
  clause506 : p 99 = false ∨ p 221 = true ∨ p 93 = true ∨ p 101 = true
  clause507 : p 100 = false ∨ p 34 = false ∨ p 88 = false ∨ p 98 = false
  clause508 : p 100 = false ∨ p 34 = false ∨ p 88 = false ∨ p 101 = false
  clause509 : p 100 = false ∨ p 34 = false ∨ p 98 = false ∨ p 101 = false
  clause510 : p 100 = false ∨ p 88 = false ∨ p 98 = false ∨ p 101 = false
  clause511 : p 100 = false ∨ p 222 = true ∨ p 88 = true ∨ p 98 = true ∨ p 101 = true
  clause512 : p 101 = false ∨ p 89 = false ∨ p 94 = false ∨ p 99 = false

structure Block16 (p : Nat → Bool) : Prop where
  clause513 : p 101 = false ∨ p 89 = false ∨ p 94 = false ∨ p 100 = false
  clause514 : p 101 = false ∨ p 89 = false ∨ p 94 = false ∨ p 102 = false
  clause515 : p 101 = false ∨ p 89 = false ∨ p 99 = false ∨ p 102 = false
  clause516 : p 101 = false ∨ p 89 = false ∨ p 100 = false ∨ p 102 = false
  clause517 : p 101 = false ∨ p 94 = false ∨ p 99 = false ∨ p 100 = false
  clause518 : p 101 = false ∨ p 223 = true ∨ p 94 = true ∨ p 99 = true ∨ p 100 = true ∨ p 102 = true
  clause519 : p 101 = false ∨ p 223 = true ∨ p 89 = true ∨ p 99 = true ∨ p 100 = true ∨ p 102 = true
  clause520 : p 101 = false ∨ p 223 = true ∨ p 89 = true ∨ p 94 = true ∨ p 100 = true ∨ p 102 = true
  clause521 : p 101 = false ∨ p 223 = true ∨ p 89 = true ∨ p 94 = true ∨ p 99 = true ∨ p 102 = true
  clause522 : p 101 = false ∨ p 223 = true ∨ p 89 = true ∨ p 94 = true ∨ p 99 = true ∨ p 100 = true
  clause523 : p 102 = false ∨ p 92 = false ∨ p 97 = false ∨ p 101 = false
  clause524 : p 102 = false ∨ p 92 = false ∨ p 97 = false ∨ p 122 = false
  clause525 : p 102 = false ∨ p 92 = false ∨ p 101 = false ∨ p 122 = false
  clause526 : p 102 = false ∨ p 97 = false ∨ p 101 = false ∨ p 122 = false
  clause527 : p 102 = false ∨ p 224 = true ∨ p 92 = true ∨ p 101 = true ∨ p 122 = true
  clause528 : p 103 = false ∨ p 72 = false ∨ p 80 = false ∨ p 104 = false
  clause529 : p 103 = false ∨ p 72 = false ∨ p 80 = false ∨ p 105 = false
  clause530 : p 103 = false ∨ p 72 = false ∨ p 80 = false ∨ p 109 = false
  clause531 : p 103 = false ∨ p 72 = false ∨ p 80 = false ∨ p 113 = false
  clause532 : p 103 = false ∨ p 72 = false ∨ p 104 = false ∨ p 105 = false
  clause533 : p 103 = false ∨ p 72 = false ∨ p 104 = false ∨ p 109 = false
  clause534 : p 103 = false ∨ p 72 = false ∨ p 104 = false ∨ p 113 = false
  clause535 : p 103 = false ∨ p 72 = false ∨ p 105 = false ∨ p 109 = false
  clause536 : p 103 = false ∨ p 72 = false ∨ p 105 = false ∨ p 113 = false
  clause537 : p 103 = false ∨ p 72 = false ∨ p 109 = false ∨ p 113 = false
  clause538 : p 103 = false ∨ p 80 = false ∨ p 104 = false ∨ p 105 = false
  clause539 : p 103 = false ∨ p 80 = false ∨ p 104 = false ∨ p 109 = false
  clause540 : p 103 = false ∨ p 80 = false ∨ p 104 = false ∨ p 113 = false
  clause541 : p 103 = false ∨ p 80 = false ∨ p 105 = false ∨ p 109 = false
  clause542 : p 103 = false ∨ p 80 = false ∨ p 105 = false ∨ p 113 = false
  clause543 : p 103 = false ∨ p 80 = false ∨ p 109 = false ∨ p 113 = false
  clause544 : p 103 = false ∨ p 104 = false ∨ p 105 = false ∨ p 109 = false

structure Block17 (p : Nat → Bool) : Prop where
  clause545 : p 103 = false ∨ p 104 = false ∨ p 105 = false ∨ p 113 = false
  clause546 : p 103 = false ∨ p 104 = false ∨ p 109 = false ∨ p 113 = false
  clause547 : p 103 = false ∨ p 105 = false ∨ p 109 = false ∨ p 113 = false
  clause548 : p 104 = false ∨ p 81 = false ∨ p 106 = false ∨ p 107 = false
  clause549 : p 104 = false ∨ p 81 = false ∨ p 107 = false ∨ p 114 = false
  clause550 : p 104 = false ∨ p 103 = false ∨ p 106 = false ∨ p 107 = false
  clause551 : p 104 = false ∨ p 103 = false ∨ p 107 = false ∨ p 114 = false
  clause552 : p 104 = false ∨ p 106 = false ∨ p 107 = false ∨ p 114 = false
  clause553 : p 104 = false ∨ p 226 = true ∨ p 103 = true ∨ p 106 = true ∨ p 107 = true ∨ p 114 = true
  clause554 : p 104 = false ∨ p 226 = true ∨ p 81 = true ∨ p 106 = true ∨ p 107 = true ∨ p 114 = true
  clause555 : p 104 = false ∨ p 226 = true ∨ p 81 = true ∨ p 103 = true ∨ p 107 = true ∨ p 114 = true
  clause556 : p 104 = false ∨ p 226 = true ∨ p 81 = true ∨ p 103 = true ∨ p 106 = true ∨ p 114 = true
  clause557 : p 104 = false ∨ p 226 = true ∨ p 81 = true ∨ p 103 = true ∨ p 106 = true ∨ p 107 = true
  clause558 : p 105 = false ∨ p 82 = false ∨ p 106 = false ∨ p 108 = false
  clause559 : p 105 = false ∨ p 103 = false ∨ p 106 = false ∨ p 108 = false
  clause560 : p 105 = false ∨ p 103 = false ∨ p 106 = false ∨ p 115 = false
  clause561 : p 105 = false ∨ p 227 = true ∨ p 82 = true ∨ p 103 = true ∨ p 106 = true ∨ p 108 = true ∨ p 115 = true
  clause562 : p 105 = false ∨ p 227 = true ∨ p 38 = true ∨ p 82 = true ∨ p 103 = true ∨ p 106 = true ∨ p 108 = true
  clause563 : p 106 = false ∨ p 39 = false ∨ p 73 = false ∨ p 104 = false
  clause564 : p 106 = false ∨ p 39 = false ∨ p 73 = false ∨ p 105 = false
  clause565 : p 106 = false ∨ p 39 = false ∨ p 73 = false ∨ p 110 = false
  clause566 : p 106 = false ∨ p 39 = false ∨ p 73 = false ∨ p 116 = false
  clause567 : p 106 = false ∨ p 39 = false ∨ p 104 = false ∨ p 105 = false
  clause568 : p 106 = false ∨ p 39 = false ∨ p 104 = false ∨ p 110 = false
  clause569 : p 106 = false ∨ p 39 = false ∨ p 104 = false ∨ p 116 = false
  clause570 : p 106 = false ∨ p 39 = false ∨ p 105 = false ∨ p 110 = false
  clause571 : p 106 = false ∨ p 39 = false ∨ p 105 = false ∨ p 116 = false
  clause572 : p 106 = false ∨ p 39 = false ∨ p 110 = false ∨ p 116 = false
  clause573 : p 106 = false ∨ p 73 = false ∨ p 104 = false ∨ p 105 = false
  clause574 : p 106 = false ∨ p 73 = false ∨ p 104 = false ∨ p 110 = false
  clause575 : p 106 = false ∨ p 73 = false ∨ p 104 = false ∨ p 116 = false
  clause576 : p 106 = false ∨ p 73 = false ∨ p 105 = false ∨ p 110 = false

structure Block18 (p : Nat → Bool) : Prop where
  clause577 : p 106 = false ∨ p 73 = false ∨ p 105 = false ∨ p 116 = false
  clause578 : p 106 = false ∨ p 73 = false ∨ p 110 = false ∨ p 116 = false
  clause579 : p 106 = false ∨ p 104 = false ∨ p 105 = false ∨ p 110 = false
  clause580 : p 106 = false ∨ p 104 = false ∨ p 105 = false ∨ p 116 = false
  clause581 : p 106 = false ∨ p 104 = false ∨ p 110 = false ∨ p 116 = false
  clause582 : p 106 = false ∨ p 105 = false ∨ p 110 = false ∨ p 116 = false
  clause583 : p 106 = false ∨ p 228 = true ∨ p 39 = true ∨ p 73 = true ∨ p 104 = true ∨ p 105 = true ∨ p 110 = true
  clause584 : p 107 = false ∨ p 41 = false ∨ p 84 = false ∨ p 104 = false
  clause585 : p 107 = false ∨ p 41 = false ∨ p 84 = false ∨ p 111 = false
  clause586 : p 107 = false ∨ p 41 = false ∨ p 104 = false ∨ p 111 = false
  clause587 : p 107 = false ∨ p 84 = false ∨ p 104 = false ∨ p 111 = false
  clause588 : p 108 = false ∨ p 42 = false ∨ p 85 = false ∨ p 105 = false
  clause589 : p 108 = false ∨ p 42 = false ∨ p 85 = false ∨ p 117 = false
  clause590 : p 108 = false ∨ p 42 = false ∨ p 105 = false ∨ p 117 = false
  clause591 : p 108 = false ∨ p 85 = false ∨ p 105 = false ∨ p 117 = false
  clause592 : p 109 = false ∨ p 87 = false ∨ p 103 = false ∨ p 118 = false
  clause593 : p 109 = false ∨ p 231 = true ∨ p 103 = true ∨ p 118 = true
  clause594 : p 109 = false ∨ p 231 = true ∨ p 87 = true ∨ p 118 = true
  clause595 : p 109 = false ∨ p 231 = true ∨ p 87 = true ∨ p 103 = true
  clause596 : p 110 = false ∨ p 44 = false ∨ p 89 = false ∨ p 112 = false
  clause597 : p 110 = false ∨ p 44 = false ∨ p 106 = false ∨ p 112 = false
  clause598 : p 110 = false ∨ p 232 = true ∨ p 89 = true ∨ p 106 = true ∨ p 112 = true
  clause599 : p 110 = false ∨ p 232 = true ∨ p 44 = true ∨ p 106 = true ∨ p 112 = true
  clause600 : p 110 = false ∨ p 232 = true ∨ p 44 = true ∨ p 89 = true ∨ p 112 = true
  clause601 : p 110 = false ∨ p 232 = true ∨ p 44 = true ∨ p 89 = true ∨ p 106 = true
  clause602 : p 111 = false ∨ p 107 = false ∨ p 112 = false ∨ p 120 = false
  clause603 : p 111 = false ∨ p 233 = true ∨ p 112 = true ∨ p 120 = true
  clause604 : p 111 = false ∨ p 233 = true ∨ p 107 = true ∨ p 120 = true
  clause605 : p 111 = false ∨ p 233 = true ∨ p 107 = true ∨ p 112 = true
  clause606 : p 112 = false ∨ p 92 = false ∨ p 110 = false ∨ p 111 = false
  clause607 : p 112 = false ∨ p 92 = false ∨ p 110 = false ∨ p 122 = false
  clause608 : p 112 = false ∨ p 92 = false ∨ p 111 = false ∨ p 122 = false

structure Block19 (p : Nat → Bool) : Prop where
  clause609 : p 112 = false ∨ p 110 = false ∨ p 111 = false ∨ p 122 = false
  clause610 : p 112 = false ∨ p 234 = true ∨ p 92 = true ∨ p 110 = true ∨ p 122 = true
  clause611 : p 113 = false ∨ p 114 = false ∨ p 115 = false ∨ p 118 = false
  clause612 : p 113 = false ∨ p 235 = true ∨ p 114 = true ∨ p 115 = true ∨ p 118 = true
  clause613 : p 113 = false ∨ p 235 = true ∨ p 103 = true ∨ p 115 = true ∨ p 118 = true
  clause614 : p 113 = false ∨ p 235 = true ∨ p 103 = true ∨ p 114 = true ∨ p 118 = true
  clause615 : p 113 = false ∨ p 235 = true ∨ p 103 = true ∨ p 114 = true ∨ p 115 = true
  clause616 : p 114 = false ∨ p 93 = false ∨ p 104 = false ∨ p 113 = false
  clause617 : p 114 = false ∨ p 93 = false ∨ p 104 = false ∨ p 116 = false
  clause618 : p 114 = false ∨ p 93 = false ∨ p 113 = false ∨ p 116 = false
  clause619 : p 114 = false ∨ p 104 = false ∨ p 113 = false ∨ p 116 = false
  clause620 : p 114 = false ∨ p 236 = true ∨ p 93 = true ∨ p 104 = true ∨ p 116 = true
  clause621 : p 114 = false ∨ p 236 = true ∨ p 93 = true ∨ p 104 = true ∨ p 113 = true
  clause622 : p 115 = false ∨ p 105 = false ∨ p 113 = false ∨ p 116 = false
  clause623 : p 115 = false ∨ p 105 = false ∨ p 113 = false ∨ p 117 = false
  clause624 : p 115 = false ∨ p 105 = false ∨ p 116 = false ∨ p 117 = false
  clause625 : p 115 = false ∨ p 113 = false ∨ p 116 = false ∨ p 117 = false
  clause626 : p 116 = false ∨ p 94 = false ∨ p 106 = false ∨ p 114 = false
  clause627 : p 116 = false ∨ p 94 = false ∨ p 106 = false ∨ p 115 = false
  clause628 : p 116 = false ∨ p 238 = true ∨ p 106 = true ∨ p 114 = true ∨ p 115 = true
  clause629 : p 116 = false ∨ p 238 = true ∨ p 94 = true ∨ p 114 = true ∨ p 115 = true
  clause630 : p 116 = false ∨ p 238 = true ∨ p 94 = true ∨ p 106 = true ∨ p 115 = true
  clause631 : p 116 = false ∨ p 238 = true ∨ p 94 = true ∨ p 106 = true ∨ p 114 = true
  clause632 : p 117 = false ∨ p 108 = false ∨ p 115 = false ∨ p 121 = false
  clause633 : p 117 = false ∨ p 239 = true ∨ p 115 = true ∨ p 121 = true
  clause634 : p 117 = false ∨ p 239 = true ∨ p 108 = true ∨ p 121 = true
  clause635 : p 117 = false ∨ p 239 = true ∨ p 108 = true ∨ p 115 = true
  clause636 : p 118 = false ∨ p 50 = false ∨ p 98 = false ∨ p 109 = false
  clause637 : p 118 = false ∨ p 50 = false ∨ p 98 = false ∨ p 113 = false
  clause638 : p 118 = false ∨ p 50 = false ∨ p 98 = false ∨ p 119 = false
  clause639 : p 118 = false ∨ p 50 = false ∨ p 109 = false ∨ p 113 = false
  clause640 : p 118 = false ∨ p 50 = false ∨ p 109 = false ∨ p 119 = false

structure Block20 (p : Nat → Bool) : Prop where
  clause641 : p 118 = false ∨ p 50 = false ∨ p 113 = false ∨ p 119 = false
  clause642 : p 118 = false ∨ p 98 = false ∨ p 109 = false ∨ p 113 = false
  clause643 : p 118 = false ∨ p 98 = false ∨ p 109 = false ∨ p 119 = false
  clause644 : p 118 = false ∨ p 98 = false ∨ p 113 = false ∨ p 119 = false
  clause645 : p 118 = false ∨ p 109 = false ∨ p 113 = false ∨ p 119 = false
  clause646 : p 240 = false ∨ p 50 = false ∨ p 113 = false
  clause647 : p 119 = false ∨ p 118 = false ∨ p 120 = false ∨ p 121 = false
  clause648 : p 119 = false ∨ p 241 = true ∨ p 120 = true ∨ p 121 = true
  clause649 : p 119 = false ∨ p 241 = true ∨ p 118 = true ∨ p 121 = true
  clause650 : p 119 = false ∨ p 241 = true ∨ p 118 = true ∨ p 120 = true
  clause651 : p 120 = false ∨ p 111 = false ∨ p 119 = false ∨ p 122 = false
  clause652 : p 242 = false ∨ p 111 = false ∨ p 122 = false
  clause653 : p 120 = false ∨ p 242 = true ∨ p 119 = true ∨ p 122 = true
  clause654 : p 121 = false ∨ p 117 = false ∨ p 119 = false ∨ p 122 = false
  clause655 : p 121 = false ∨ p 243 = true ∨ p 119 = true ∨ p 122 = true
  clause656 : p 122 = false ∨ p 54 = false ∨ p 112 = false ∨ p 121 = false
  clause657 : p 122 = false ∨ p 54 = false ∨ p 120 = false ∨ p 121 = false
  clause658 : p 122 = false ∨ p 102 = false ∨ p 112 = false ∨ p 121 = false
  clause659 : p 122 = false ∨ p 102 = false ∨ p 120 = false ∨ p 121 = false
  clause660 : p 122 = false ∨ p 112 = false ∨ p 120 = false ∨ p 121 = false
  clause661 : p 124 = false
  clause662 : p 126 = false
  clause663 : p 128 = false
  clause664 : p 130 = false
  clause665 : p 132 = false
  clause666 : p 134 = false
  clause667 : p 135 = false
  clause668 : p 137 = false
  clause669 : p 140 = false
  clause670 : p 141 = false
  clause671 : p 143 = false
  clause672 : p 145 = false

structure Block21 (p : Nat → Bool) : Prop where
  clause673 : p 146 = false
  clause674 : p 148 = false
  clause675 : p 149 = false
  clause676 : p 153 = false
  clause677 : p 155 = false
  clause678 : p 156 = false
  clause679 : p 157 = false
  clause680 : p 161 = false
  clause681 : p 163 = false
  clause682 : p 164 = false
  clause683 : p 165 = false
  clause684 : p 167 = false
  clause685 : p 169 = false
  clause686 : p 171 = false
  clause687 : p 172 = false
  clause688 : p 175 = false
  clause689 : p 178 = false
  clause690 : p 181 = false
  clause691 : p 182 = false
  clause692 : p 183 = false
  clause693 : p 184 = false
  clause694 : p 186 = false
  clause695 : p 189 = false
  clause696 : p 190 = false
  clause697 : p 191 = false
  clause698 : p 194 = false
  clause699 : p 195 = false
  clause700 : p 199 = false
  clause701 : p 201 = false
  clause702 : p 202 = false
  clause703 : p 206 = false
  clause704 : p 207 = false

structure Block22 (p : Nat → Bool) : Prop where
  clause705 : p 210 = false
  clause706 : p 212 = false
  clause707 : p 214 = false
  clause708 : p 215 = false
  clause709 : p 217 = false
  clause710 : p 219 = false
  clause711 : p 220 = false
  clause712 : p 223 = false
  clause713 : p 226 = false
  clause714 : p 227 = false
  clause715 : p 231 = false
  clause716 : p 232 = false
  clause717 : p 233 = false
  clause718 : p 235 = false
  clause719 : p 238 = false
  clause720 : p 239 = false
  clause721 : p 241 = false
  clause722 : p 244 = false
  clause723 : p 125 = false ∨ p 245 = true
  clause724 : p 245 = false ∨ p 247 = true
  clause725 : p 123 = false ∨ p 247 = true
  clause726 : p 123 = false ∨ p 245 = false ∨ p 248 = true
  clause727 : p 127 = false ∨ p 249 = true
  clause728 : p 129 = false ∨ p 251 = true
  clause729 : p 251 = false ∨ p 253 = true
  clause730 : p 249 = false ∨ p 253 = true
  clause731 : p 253 = false ∨ p 255 = true
  clause732 : p 247 = false ∨ p 255 = true
  clause733 : p 248 = false ∨ p 256 = true
  clause734 : p 131 = false ∨ p 257 = true
  clause735 : p 133 = false ∨ p 259 = true
  clause736 : p 259 = false ∨ p 261 = true

structure Block23 (p : Nat → Bool) : Prop where
  clause737 : p 257 = false ∨ p 261 = true
  clause738 : p 136 = false ∨ p 265 = true
  clause739 : p 265 = false ∨ p 267 = true
  clause740 : p 267 = false ∨ p 269 = true
  clause741 : p 261 = false ∨ p 269 = true
  clause742 : p 261 = false ∨ p 267 = false ∨ p 270 = true
  clause743 : p 269 = false ∨ p 271 = true
  clause744 : p 270 = false ∨ p 272 = true
  clause745 : p 255 = false ∨ p 271 = true
  clause746 : p 255 = false ∨ p 269 = false ∨ p 272 = true
  clause747 : p 256 = false ∨ p 272 = true
  clause748 : p 139 = false ∨ p 273 = true
  clause749 : p 273 = false ∨ p 275 = true
  clause750 : p 138 = false ∨ p 275 = true
  clause751 : p 142 = false ∨ p 277 = true
  clause752 : p 144 = false ∨ p 279 = true
  clause753 : p 279 = false ∨ p 281 = true
  clause754 : p 277 = false ∨ p 281 = true
  clause755 : p 281 = false ∨ p 283 = true
  clause756 : p 275 = false ∨ p 283 = true
  clause757 : p 147 = false ∨ p 287 = true
  clause758 : p 287 = false ∨ p 289 = true
  clause759 : p 150 = false ∨ p 291 = true
  clause760 : p 152 = false ∨ p 293 = true
  clause761 : p 151 = false ∨ p 293 = true
  clause762 : p 293 = false ∨ p 295 = true
  clause763 : p 291 = false ∨ p 295 = true
  clause764 : p 295 = false ∨ p 297 = true
  clause765 : p 289 = false ∨ p 297 = true
  clause766 : p 297 = false ∨ p 299 = true
  clause767 : p 283 = false ∨ p 299 = true
  clause768 : p 299 = false ∨ p 301 = true

structure Block24 (p : Nat → Bool) : Prop where
  clause769 : p 271 = false ∨ p 301 = true
  clause770 : p 271 = false ∨ p 299 = false ∨ p 302 = true
  clause771 : p 272 = false ∨ p 302 = true
  clause772 : p 154 = false ∨ p 303 = true
  clause773 : p 303 = false ∨ p 305 = true
  clause774 : p 159 = false ∨ p 309 = true
  clause775 : p 158 = false ∨ p 309 = true
  clause776 : p 309 = false ∨ p 311 = true
  clause777 : p 311 = false ∨ p 313 = true
  clause778 : p 305 = false ∨ p 313 = true
  clause779 : p 160 = false ∨ p 315 = true
  clause780 : p 162 = false ∨ p 317 = true
  clause781 : p 317 = false ∨ p 319 = true
  clause782 : p 315 = false ∨ p 319 = true
  clause783 : p 166 = false ∨ p 323 = true
  clause784 : p 323 = false ∨ p 325 = true
  clause785 : p 325 = false ∨ p 327 = true
  clause786 : p 319 = false ∨ p 327 = true
  clause787 : p 327 = false ∨ p 329 = true
  clause788 : p 313 = false ∨ p 329 = true
  clause789 : p 170 = false ∨ p 331 = true
  clause790 : p 331 = false ∨ p 333 = true
  clause791 : p 168 = false ∨ p 333 = true
  clause792 : p 174 = false ∨ p 337 = true
  clause793 : p 173 = false ∨ p 337 = true
  clause794 : p 173 = false ∨ p 174 = false ∨ p 338 = true
  clause795 : p 337 = false ∨ p 339 = true
  clause796 : p 338 = false ∨ p 340 = true
  clause797 : p 339 = false ∨ p 341 = true
  clause798 : p 340 = false ∨ p 342 = true
  clause799 : p 333 = false ∨ p 341 = true
  clause800 : p 176 = false ∨ p 343 = true

structure Block25 (p : Nat → Bool) : Prop where
  clause801 : p 177 = false ∨ p 345 = true
  clause802 : p 345 = false ∨ p 347 = true
  clause803 : p 343 = false ∨ p 347 = true
  clause804 : p 180 = false ∨ p 349 = true
  clause805 : p 349 = false ∨ p 353 = true
  clause806 : p 353 = false ∨ p 355 = true
  clause807 : p 347 = false ∨ p 355 = true
  clause808 : p 347 = false ∨ p 353 = false ∨ p 356 = true
  clause809 : p 355 = false ∨ p 357 = true
  clause810 : p 356 = false ∨ p 358 = true
  clause811 : p 341 = false ∨ p 357 = true
  clause812 : p 341 = false ∨ p 355 = false ∨ p 358 = true
  clause813 : p 342 = false ∨ p 358 = true
  clause814 : p 357 = false ∨ p 359 = true
  clause815 : p 358 = false ∨ p 360 = true
  clause816 : p 329 = false ∨ p 359 = true
  clause817 : p 359 = false ∨ p 361 = true
  clause818 : p 360 = false ∨ p 362 = true
  clause819 : p 301 = false ∨ p 361 = true
  clause820 : p 301 = false ∨ p 359 = false ∨ p 362 = true
  clause821 : p 302 = false ∨ p 362 = true
  clause822 : p 185 = false ∨ p 363 = true
  clause823 : p 363 = false ∨ p 365 = true
  clause824 : p 187 = false ∨ p 367 = true
  clause825 : p 188 = false ∨ p 369 = true
  clause826 : p 369 = false ∨ p 371 = true
  clause827 : p 367 = false ∨ p 371 = true
  clause828 : p 371 = false ∨ p 373 = true
  clause829 : p 365 = false ∨ p 373 = true
  clause830 : p 193 = false ∨ p 377 = true
  clause831 : p 192 = false ∨ p 377 = true
  clause832 : p 192 = false ∨ p 193 = false ∨ p 378 = true

structure Block26 (p : Nat → Bool) : Prop where
  clause833 : p 377 = false ∨ p 379 = true
  clause834 : p 378 = false ∨ p 380 = true
  clause835 : p 197 = false ∨ p 383 = true
  clause836 : p 196 = false ∨ p 383 = true
  clause837 : p 383 = false ∨ p 385 = true
  clause838 : p 385 = false ∨ p 387 = true
  clause839 : p 379 = false ∨ p 387 = true
  clause840 : p 379 = false ∨ p 385 = false ∨ p 388 = true
  clause841 : p 380 = false ∨ p 388 = true
  clause842 : p 387 = false ∨ p 389 = true
  clause843 : p 388 = false ∨ p 390 = true
  clause844 : p 373 = false ∨ p 389 = true
  clause845 : p 373 = false ∨ p 387 = false ∨ p 390 = true
  clause846 : p 200 = false ∨ p 391 = true
  clause847 : p 391 = false ∨ p 393 = true
  clause848 : p 203 = false ∨ p 395 = true
  clause849 : p 205 = false ∨ p 397 = true
  clause850 : p 204 = false ∨ p 397 = true
  clause851 : p 397 = false ∨ p 399 = true
  clause852 : p 395 = false ∨ p 399 = true
  clause853 : p 399 = false ∨ p 401 = true
  clause854 : p 393 = false ∨ p 401 = true
  clause855 : p 393 = false ∨ p 399 = false ∨ p 402 = true
  clause856 : p 208 = false ∨ p 405 = true
  clause857 : p 405 = false ∨ p 407 = true
  clause858 : p 211 = false ∨ p 409 = true
  clause859 : p 213 = false ∨ p 411 = true
  clause860 : p 411 = false ∨ p 413 = true
  clause861 : p 409 = false ∨ p 413 = true
  clause862 : p 413 = false ∨ p 415 = true
  clause863 : p 407 = false ∨ p 415 = true
  clause864 : p 415 = false ∨ p 417 = true

structure Block27 (p : Nat → Bool) : Prop where
  clause865 : p 401 = false ∨ p 417 = true
  clause866 : p 401 = false ∨ p 415 = false ∨ p 418 = true
  clause867 : p 402 = false ∨ p 418 = true
  clause868 : p 417 = false ∨ p 419 = true
  clause869 : p 418 = false ∨ p 420 = true
  clause870 : p 389 = false ∨ p 419 = true
  clause871 : p 389 = false ∨ p 417 = false ∨ p 420 = true
  clause872 : p 390 = false ∨ p 420 = true
  clause873 : p 216 = false ∨ p 421 = true
  clause874 : p 421 = false ∨ p 423 = true
  clause875 : p 218 = false ∨ p 425 = true
  clause876 : p 425 = false ∨ p 429 = true
  clause877 : p 429 = false ∨ p 431 = true
  clause878 : p 423 = false ∨ p 431 = true
  clause879 : p 222 = false ∨ p 433 = true
  clause880 : p 221 = false ∨ p 433 = true
  clause881 : p 224 = false ∨ p 435 = true
  clause882 : p 435 = false ∨ p 437 = true
  clause883 : p 433 = false ∨ p 437 = true
  clause884 : p 225 = false ∨ p 439 = true
  clause885 : p 228 = false ∨ p 441 = true
  clause886 : p 441 = false ∨ p 443 = true
  clause887 : p 439 = false ∨ p 443 = true
  clause888 : p 443 = false ∨ p 445 = true
  clause889 : p 437 = false ∨ p 445 = true
  clause890 : p 445 = false ∨ p 447 = true
  clause891 : p 431 = false ∨ p 447 = true
  clause892 : p 230 = false ∨ p 449 = true
  clause893 : p 229 = false ∨ p 449 = true
  clause894 : p 449 = false ∨ p 453 = true
  clause895 : p 234 = false ∨ p 455 = true
  clause896 : p 236 = false ∨ p 457 = true

structure Block28 (p : Nat → Bool) : Prop where
  clause897 : p 457 = false ∨ p 459 = true
  clause898 : p 455 = false ∨ p 459 = true
  clause899 : p 459 = false ∨ p 461 = true
  clause900 : p 453 = false ∨ p 461 = true
  clause901 : p 237 = false ∨ p 463 = true
  clause902 : p 463 = false ∨ p 467 = true
  clause903 : p 242 = false ∨ p 469 = true
  clause904 : p 243 = false ∨ p 471 = true
  clause905 : p 471 = false ∨ p 473 = true
  clause906 : p 469 = false ∨ p 473 = true
  clause907 : p 469 = false ∨ p 471 = false ∨ p 474 = true
  clause908 : p 473 = false ∨ p 475 = true
  clause909 : p 474 = false ∨ p 476 = true
  clause910 : p 467 = false ∨ p 475 = true
  clause911 : p 475 = false ∨ p 477 = true
  clause912 : p 476 = false ∨ p 478 = true
  clause913 : p 461 = false ∨ p 477 = true
  clause914 : p 477 = false ∨ p 479 = true
  clause915 : p 478 = false ∨ p 480 = true
  clause916 : p 447 = false ∨ p 479 = true
  clause917 : p 447 = false ∨ p 477 = false ∨ p 480 = true
  clause918 : p 479 = false ∨ p 481 = true
  clause919 : p 480 = false ∨ p 482 = true
  clause920 : p 419 = false ∨ p 481 = true
  clause921 : p 419 = false ∨ p 479 = false ∨ p 482 = true
  clause922 : p 420 = false ∨ p 482 = true
  clause923 : p 482 = false ∨ p 484 = true
  clause924 : p 361 = false ∨ p 481 = false ∨ p 484 = true
  clause925 : p 362 = false ∨ p 484 = true
  clause926 : p 484 = false
  clause927 : p 123 = true ∨ p 124 = true ∨ p 125 = true ∨ p 126 = true ∨ p 127 = true ∨ p 128 = true ∨ p 129 = true ∨ p 130 = true ∨ p 131 = true ∨ p 132 = true ∨ p 133 = true ∨ p 134 = true ∨ p 135 = true ∨ p 136 = true ∨ p 137 = true ∨ p 138 = true ∨ p 139 = true ∨ p 140 = true ∨ p 141 = true ∨ p 142 = true ∨ p 143 = true ∨ p 144 = true ∨ p 145 = true ∨ p 146 = true ∨ p 147 = true ∨ p 148 = true ∨ p 149 = true ∨ p 150 = true ∨ p 151 = true ∨ p 152 = true ∨ p 153 = true ∨ p 154 = true ∨ p 155 = true ∨ p 156 = true ∨ p 157 = true ∨ p 158 = true ∨ p 159 = true ∨ p 160 = true ∨ p 161 = true ∨ p 162 = true ∨ p 163 = true ∨ p 164 = true ∨ p 165 = true ∨ p 166 = true ∨ p 167 = true ∨ p 168 = true ∨ p 169 = true ∨ p 170 = true ∨ p 171 = true ∨ p 172 = true ∨ p 173 = true ∨ p 174 = true ∨ p 175 = true ∨ p 176 = true ∨ p 177 = true ∨ p 178 = true ∨ p 179 = true ∨ p 180 = true ∨ p 181 = true ∨ p 182 = true ∨ p 183 = true ∨ p 184 = true ∨ p 185 = true ∨ p 186 = true ∨ p 187 = true ∨ p 188 = true ∨ p 189 = true ∨ p 190 = true ∨ p 191 = true ∨ p 192 = true ∨ p 193 = true ∨ p 194 = true ∨ p 195 = true ∨ p 196 = true ∨ p 197 = true ∨ p 199 = true ∨ p 200 = true ∨ p 201 = true ∨ p 202 = true ∨ p 203 = true ∨ p 204 = true ∨ p 205 = true ∨ p 206 = true ∨ p 207 = true ∨ p 208 = true ∨ p 209 = true ∨ p 210 = true ∨ p 211 = true ∨ p 212 = true ∨ p 213 = true ∨ p 214 = true ∨ p 215 = true ∨ p 216 = true ∨ p 217 = true ∨ p 218 = true ∨ p 219 = true ∨ p 220 = true ∨ p 221 = true ∨ p 222 = true ∨ p 223 = true ∨ p 224 = true ∨ p 225 = true ∨ p 226 = true ∨ p 227 = true ∨ p 228 = true ∨ p 229 = true ∨ p 230 = true ∨ p 231 = true ∨ p 232 = true ∨ p 233 = true ∨ p 234 = true ∨ p 235 = true ∨ p 236 = true ∨ p 237 = true ∨ p 238 = true ∨ p 239 = true ∨ p 240 = true ∨ p 241 = true ∨ p 242 = true ∨ p 243 = true ∨ p 244 = true
  clause928 : p 6 = true ∨ p 1461 = true

structure Block29 (p : Nat → Bool) : Prop where
  clause929 : p 4 = true ∨ p 1461 = true
  clause930 : p 4 = true ∨ p 6 = true ∨ p 1462 = true
  clause931 : p 1461 = false ∨ p 1463 = true
  clause932 : p 1462 = false ∨ p 1464 = true
  clause933 : p 2 = true ∨ p 1463 = true
  clause934 : p 2 = true ∨ p 1461 = false ∨ p 1464 = true
  clause935 : p 2 = true ∨ p 1462 = false ∨ p 1465 = true
  clause936 : p 10 = true ∨ p 1466 = true
  clause937 : p 8 = true ∨ p 1466 = true
  clause938 : p 8 = true ∨ p 10 = true ∨ p 1467 = true
  clause939 : p 13 = true ∨ p 1468 = true
  clause940 : p 12 = true ∨ p 1468 = true
  clause941 : p 12 = true ∨ p 13 = true ∨ p 1469 = true
  clause942 : p 1468 = false ∨ p 1470 = true
  clause943 : p 1469 = false ∨ p 1471 = true
  clause944 : p 1466 = false ∨ p 1470 = true
  clause945 : p 1466 = false ∨ p 1468 = false ∨ p 1471 = true
  clause946 : p 1466 = false ∨ p 1469 = false ∨ p 1472 = true
  clause947 : p 1467 = false ∨ p 1471 = true
  clause948 : p 1467 = false ∨ p 1468 = false ∨ p 1472 = true
  clause949 : p 1467 = false ∨ p 1469 = false ∨ p 1473 = true
  clause950 : p 1470 = false ∨ p 1474 = true
  clause951 : p 1471 = false ∨ p 1475 = true
  clause952 : p 1472 = false ∨ p 1476 = true
  clause953 : p 1473 = false ∨ p 1477 = true
  clause954 : p 1463 = false ∨ p 1474 = true
  clause955 : p 1463 = false ∨ p 1470 = false ∨ p 1475 = true
  clause956 : p 1463 = false ∨ p 1471 = false ∨ p 1476 = true
  clause957 : p 1463 = false ∨ p 1472 = false ∨ p 1477 = true
  clause958 : p 1463 = false ∨ p 1473 = false ∨ p 1478 = true
  clause959 : p 1464 = false ∨ p 1475 = true
  clause960 : p 1464 = false ∨ p 1470 = false ∨ p 1476 = true

structure Block30 (p : Nat → Bool) : Prop where
  clause961 : p 1464 = false ∨ p 1471 = false ∨ p 1477 = true
  clause962 : p 1464 = false ∨ p 1472 = false ∨ p 1478 = true
  clause963 : p 1464 = false ∨ p 1473 = false ∨ p 1479 = true
  clause964 : p 1465 = false ∨ p 1476 = true
  clause965 : p 1465 = false ∨ p 1470 = false ∨ p 1477 = true
  clause966 : p 1465 = false ∨ p 1471 = false ∨ p 1478 = true
  clause967 : p 18 = true ∨ p 1481 = true
  clause968 : p 15 = true ∨ p 1481 = true
  clause969 : p 15 = true ∨ p 18 = true ∨ p 1482 = true
  clause970 : p 21 = true ∨ p 1483 = true
  clause971 : p 19 = true ∨ p 1483 = true
  clause972 : p 19 = true ∨ p 21 = true ∨ p 1484 = true
  clause973 : p 1483 = false ∨ p 1485 = true
  clause974 : p 1484 = false ∨ p 1486 = true
  clause975 : p 1481 = false ∨ p 1485 = true
  clause976 : p 1481 = false ∨ p 1483 = false ∨ p 1486 = true
  clause977 : p 1481 = false ∨ p 1484 = false ∨ p 1487 = true
  clause978 : p 1482 = false ∨ p 1486 = true
  clause979 : p 1482 = false ∨ p 1483 = false ∨ p 1487 = true
  clause980 : p 1482 = false ∨ p 1484 = false ∨ p 1488 = true
  clause981 : p 24 = true ∨ p 1489 = true
  clause982 : p 23 = true ∨ p 1489 = true
  clause983 : p 23 = true ∨ p 24 = true ∨ p 1490 = true
  clause984 : p 27 = true ∨ p 1491 = true
  clause985 : p 26 = true ∨ p 1491 = true
  clause986 : p 26 = true ∨ p 27 = true ∨ p 1492 = true
  clause987 : p 1491 = false ∨ p 1493 = true
  clause988 : p 1492 = false ∨ p 1494 = true
  clause989 : p 1489 = false ∨ p 1493 = true
  clause990 : p 1489 = false ∨ p 1491 = false ∨ p 1494 = true
  clause991 : p 1489 = false ∨ p 1492 = false ∨ p 1495 = true
  clause992 : p 1490 = false ∨ p 1494 = true

structure Block31 (p : Nat → Bool) : Prop where
  clause993 : p 1490 = false ∨ p 1491 = false ∨ p 1495 = true
  clause994 : p 1493 = false ∨ p 1497 = true
  clause995 : p 1494 = false ∨ p 1498 = true
  clause996 : p 1495 = false ∨ p 1499 = true
  clause997 : p 1485 = false ∨ p 1497 = true
  clause998 : p 1485 = false ∨ p 1493 = false ∨ p 1498 = true
  clause999 : p 1485 = false ∨ p 1494 = false ∨ p 1499 = true
  clause1000 : p 1485 = false ∨ p 1495 = false ∨ p 1500 = true
  clause1001 : p 1486 = false ∨ p 1493 = false ∨ p 1499 = true
  clause1002 : p 1486 = false ∨ p 1494 = false ∨ p 1500 = true
  clause1003 : p 1486 = false ∨ p 1495 = false ∨ p 1501 = true
  clause1004 : p 1487 = false ∨ p 1499 = true
  clause1005 : p 1487 = false ∨ p 1493 = false ∨ p 1500 = true
  clause1006 : p 1487 = false ∨ p 1494 = false ∨ p 1501 = true
  clause1007 : p 1487 = false ∨ p 1495 = false ∨ p 1502 = true
  clause1008 : p 1488 = false ∨ p 1493 = false ∨ p 1501 = true
  clause1009 : p 1474 = false ∨ p 1499 = false ∨ p 1508 = true
  clause1010 : p 1474 = false ∨ p 1500 = false ∨ p 1509 = true
  clause1011 : p 1475 = false ∨ p 1497 = false ∨ p 1507 = true
  clause1012 : p 1475 = false ∨ p 1498 = false ∨ p 1508 = true
  clause1013 : p 1475 = false ∨ p 1499 = false ∨ p 1509 = true
  clause1014 : p 1475 = false ∨ p 1500 = false ∨ p 1510 = true
  clause1015 : p 1475 = false ∨ p 1501 = false ∨ p 1511 = true
  clause1016 : p 1476 = false ∨ p 1497 = false ∨ p 1508 = true
  clause1017 : p 1476 = false ∨ p 1498 = false ∨ p 1509 = true
  clause1018 : p 1476 = false ∨ p 1499 = false ∨ p 1510 = true
  clause1019 : p 1476 = false ∨ p 1500 = false ∨ p 1511 = true
  clause1020 : p 1476 = false ∨ p 1501 = false ∨ p 1512 = true
  clause1021 : p 1476 = false ∨ p 1502 = false ∨ p 1513 = true
  clause1022 : p 1477 = false ∨ p 1508 = true
  clause1023 : p 1477 = false ∨ p 1497 = false ∨ p 1509 = true
  clause1024 : p 1477 = false ∨ p 1498 = false ∨ p 1510 = true

structure Block32 (p : Nat → Bool) : Prop where
  clause1025 : p 1477 = false ∨ p 1499 = false ∨ p 1511 = true
  clause1026 : p 1477 = false ∨ p 1500 = false ∨ p 1512 = true
  clause1027 : p 1477 = false ∨ p 1501 = false ∨ p 1513 = true
  clause1028 : p 1478 = false ∨ p 1497 = false ∨ p 1510 = true
  clause1029 : p 1478 = false ∨ p 1498 = false ∨ p 1511 = true
  clause1030 : p 1478 = false ∨ p 1499 = false ∨ p 1512 = true
  clause1031 : p 1478 = false ∨ p 1500 = false ∨ p 1513 = true
  clause1032 : p 1479 = false ∨ p 1497 = false ∨ p 1511 = true
  clause1033 : p 33 = true ∨ p 1520 = true
  clause1034 : p 31 = true ∨ p 1520 = true
  clause1035 : p 31 = true ∨ p 33 = true ∨ p 1521 = true
  clause1036 : p 35 = true ∨ p 1522 = true
  clause1037 : p 34 = true ∨ p 1522 = true
  clause1038 : p 34 = true ∨ p 35 = true ∨ p 1523 = true
  clause1039 : p 1522 = false ∨ p 1524 = true
  clause1040 : p 1523 = false ∨ p 1525 = true
  clause1041 : p 1520 = false ∨ p 1524 = true
  clause1042 : p 1520 = false ∨ p 1522 = false ∨ p 1525 = true
  clause1043 : p 1521 = false ∨ p 1525 = true
  clause1044 : p 41 = true ∨ p 1528 = true
  clause1045 : p 39 = true ∨ p 1528 = true
  clause1046 : p 39 = true ∨ p 41 = true ∨ p 1529 = true
  clause1047 : p 43 = true ∨ p 1530 = true
  clause1048 : p 42 = true ∨ p 1530 = true
  clause1049 : p 42 = true ∨ p 43 = true ∨ p 1531 = true
  clause1050 : p 1530 = false ∨ p 1532 = true
  clause1051 : p 1531 = false ∨ p 1533 = true
  clause1052 : p 1528 = false ∨ p 1532 = true
  clause1053 : p 1528 = false ∨ p 1530 = false ∨ p 1533 = true
  clause1054 : p 1528 = false ∨ p 1531 = false ∨ p 1534 = true
  clause1055 : p 1529 = false ∨ p 1533 = true
  clause1056 : p 1529 = false ∨ p 1530 = false ∨ p 1534 = true

structure Block33 (p : Nat → Bool) : Prop where
  clause1057 : p 1529 = false ∨ p 1531 = false ∨ p 1535 = true
  clause1058 : p 1532 = false ∨ p 1536 = true
  clause1059 : p 1533 = false ∨ p 1537 = true
  clause1060 : p 1534 = false ∨ p 1538 = true
  clause1061 : p 1524 = false ∨ p 1536 = true
  clause1062 : p 1524 = false ∨ p 1532 = false ∨ p 1537 = true
  clause1063 : p 1524 = false ∨ p 1533 = false ∨ p 1538 = true
  clause1064 : p 1524 = false ∨ p 1534 = false ∨ p 1539 = true
  clause1065 : p 1524 = false ∨ p 1535 = false ∨ p 1540 = true
  clause1066 : p 1525 = false ∨ p 1537 = true
  clause1067 : p 1525 = false ∨ p 1532 = false ∨ p 1538 = true
  clause1068 : p 1525 = false ∨ p 1533 = false ∨ p 1539 = true
  clause1069 : p 1525 = false ∨ p 1534 = false ∨ p 1540 = true
  clause1070 : p 47 = true ∨ p 1544 = true
  clause1071 : p 45 = true ∨ p 1544 = true
  clause1072 : p 45 = true ∨ p 47 = true ∨ p 1545 = true
  clause1073 : p 50 = true ∨ p 1546 = true
  clause1074 : p 49 = true ∨ p 1546 = true
  clause1075 : p 49 = true ∨ p 50 = true ∨ p 1547 = true
  clause1076 : p 1546 = false ∨ p 1548 = true
  clause1077 : p 1547 = false ∨ p 1549 = true
  clause1078 : p 1544 = false ∨ p 1548 = true
  clause1079 : p 1544 = false ∨ p 1546 = false ∨ p 1549 = true
  clause1080 : p 1544 = false ∨ p 1547 = false ∨ p 1550 = true
  clause1081 : p 1545 = false ∨ p 1549 = true
  clause1082 : p 1545 = false ∨ p 1546 = false ∨ p 1550 = true
  clause1083 : p 1545 = false ∨ p 1547 = false ∨ p 1551 = true
  clause1084 : p 56 = true ∨ p 1552 = true
  clause1085 : p 53 = true ∨ p 1552 = true
  clause1086 : p 53 = true ∨ p 56 = true ∨ p 1553 = true
  clause1087 : p 60 = true ∨ p 1554 = true
  clause1088 : p 59 = true ∨ p 1554 = true

structure Block34 (p : Nat → Bool) : Prop where
  clause1089 : p 59 = true ∨ p 60 = true ∨ p 1555 = true
  clause1090 : p 1554 = false ∨ p 1556 = true
  clause1091 : p 1555 = false ∨ p 1557 = true
  clause1092 : p 1552 = false ∨ p 1556 = true
  clause1093 : p 1552 = false ∨ p 1554 = false ∨ p 1557 = true
  clause1094 : p 1552 = false ∨ p 1555 = false ∨ p 1558 = true
  clause1095 : p 1553 = false ∨ p 1557 = true
  clause1096 : p 1553 = false ∨ p 1554 = false ∨ p 1558 = true
  clause1097 : p 1553 = false ∨ p 1555 = false ∨ p 1559 = true
  clause1098 : p 1556 = false ∨ p 1560 = true
  clause1099 : p 1557 = false ∨ p 1561 = true
  clause1100 : p 1558 = false ∨ p 1562 = true
  clause1101 : p 1559 = false ∨ p 1563 = true
  clause1102 : p 1548 = false ∨ p 1560 = true
  clause1103 : p 1548 = false ∨ p 1556 = false ∨ p 1561 = true
  clause1104 : p 1548 = false ∨ p 1557 = false ∨ p 1562 = true
  clause1105 : p 1548 = false ∨ p 1558 = false ∨ p 1563 = true
  clause1106 : p 1548 = false ∨ p 1559 = false ∨ p 1564 = true
  clause1107 : p 1549 = false ∨ p 1561 = true
  clause1108 : p 1549 = false ∨ p 1556 = false ∨ p 1562 = true
  clause1109 : p 1549 = false ∨ p 1557 = false ∨ p 1563 = true
  clause1110 : p 1549 = false ∨ p 1558 = false ∨ p 1564 = true
  clause1111 : p 1549 = false ∨ p 1559 = false ∨ p 1565 = true
  clause1112 : p 1550 = false ∨ p 1562 = true
  clause1113 : p 1550 = false ∨ p 1556 = false ∨ p 1563 = true
  clause1114 : p 1550 = false ∨ p 1557 = false ∨ p 1564 = true
  clause1115 : p 1550 = false ∨ p 1558 = false ∨ p 1565 = true
  clause1116 : p 1550 = false ∨ p 1559 = false ∨ p 1566 = true
  clause1117 : p 1551 = false ∨ p 1556 = false ∨ p 1564 = true
  clause1118 : p 1563 = false ∨ p 1571 = true
  clause1119 : p 1564 = false ∨ p 1572 = true
  clause1120 : p 1566 = false ∨ p 1574 = true

structure Block35 (p : Nat → Bool) : Prop where
  clause1121 : p 1536 = false ∨ p 1561 = false ∨ p 1570 = true
  clause1122 : p 1536 = false ∨ p 1562 = false ∨ p 1571 = true
  clause1123 : p 1536 = false ∨ p 1563 = false ∨ p 1572 = true
  clause1124 : p 1536 = false ∨ p 1564 = false ∨ p 1573 = true
  clause1125 : p 1536 = false ∨ p 1565 = false ∨ p 1574 = true
  clause1126 : p 1537 = false ∨ p 1560 = false ∨ p 1570 = true
  clause1127 : p 1537 = false ∨ p 1561 = false ∨ p 1571 = true
  clause1128 : p 1537 = false ∨ p 1562 = false ∨ p 1572 = true
  clause1129 : p 1537 = false ∨ p 1563 = false ∨ p 1573 = true
  clause1130 : p 1537 = false ∨ p 1564 = false ∨ p 1574 = true
  clause1131 : p 1537 = false ∨ p 1565 = false ∨ p 1575 = true
  clause1132 : p 1538 = false ∨ p 1570 = true
  clause1133 : p 1538 = false ∨ p 1560 = false ∨ p 1571 = true
  clause1134 : p 1538 = false ∨ p 1561 = false ∨ p 1572 = true
  clause1135 : p 1538 = false ∨ p 1562 = false ∨ p 1573 = true
  clause1136 : p 1538 = false ∨ p 1563 = false ∨ p 1574 = true
  clause1137 : p 1538 = false ∨ p 1564 = false ∨ p 1575 = true
  clause1138 : p 1539 = false ∨ p 1571 = true
  clause1139 : p 1539 = false ∨ p 1560 = false ∨ p 1572 = true
  clause1140 : p 1539 = false ∨ p 1561 = false ∨ p 1573 = true
  clause1141 : p 1539 = false ∨ p 1562 = false ∨ p 1574 = true
  clause1142 : p 1539 = false ∨ p 1563 = false ∨ p 1575 = true
  clause1143 : p 1539 = false ∨ p 1564 = false ∨ p 1576 = true
  clause1144 : p 1539 = false ∨ p 1565 = false ∨ p 1577 = true
  clause1145 : p 1540 = false ∨ p 1572 = true
  clause1146 : p 1540 = false ∨ p 1560 = false ∨ p 1573 = true
  clause1147 : p 1540 = false ∨ p 1561 = false ∨ p 1574 = true
  clause1148 : p 1540 = false ∨ p 1562 = false ∨ p 1575 = true
  clause1149 : p 1540 = false ∨ p 1563 = false ∨ p 1576 = true
  clause1150 : p 1507 = false ∨ p 1571 = false ∨ p 1590 = true
  clause1151 : p 1507 = false ∨ p 1572 = false ∨ p 1591 = true
  clause1152 : p 1507 = false ∨ p 1573 = false ∨ p 1592 = true

structure Block36 (p : Nat → Bool) : Prop where
  clause1153 : p 1507 = false ∨ p 1574 = false ∨ p 1593 = true
  clause1154 : p 1507 = false ∨ p 1575 = false ∨ p 1594 = true
  clause1155 : p 1507 = false ∨ p 1576 = false ∨ p 1595 = true
  clause1156 : p 1508 = false ∨ p 1570 = false ∨ p 1590 = true
  clause1157 : p 1508 = false ∨ p 1571 = false ∨ p 1591 = true
  clause1158 : p 1508 = false ∨ p 1572 = false ∨ p 1592 = true
  clause1159 : p 1508 = false ∨ p 1573 = false ∨ p 1593 = true
  clause1160 : p 1508 = false ∨ p 1574 = false ∨ p 1594 = true
  clause1161 : p 1508 = false ∨ p 1575 = false ∨ p 1595 = true
  clause1162 : p 1508 = false ∨ p 1576 = false ∨ p 1596 = true
  clause1163 : p 1508 = false ∨ p 1577 = false ∨ p 1597 = true
  clause1164 : p 1509 = false ∨ p 1570 = false ∨ p 1591 = true
  clause1165 : p 1509 = false ∨ p 1571 = false ∨ p 1592 = true
  clause1166 : p 1509 = false ∨ p 1572 = false ∨ p 1593 = true
  clause1167 : p 1509 = false ∨ p 1573 = false ∨ p 1594 = true
  clause1168 : p 1509 = false ∨ p 1574 = false ∨ p 1595 = true
  clause1169 : p 1509 = false ∨ p 1575 = false ∨ p 1596 = true
  clause1170 : p 1509 = false ∨ p 1576 = false ∨ p 1597 = true
  clause1171 : p 1510 = false ∨ p 1570 = false ∨ p 1592 = true
  clause1172 : p 1510 = false ∨ p 1571 = false ∨ p 1593 = true
  clause1173 : p 1510 = false ∨ p 1572 = false ∨ p 1594 = true
  clause1174 : p 1510 = false ∨ p 1573 = false ∨ p 1595 = true
  clause1175 : p 1510 = false ∨ p 1574 = false ∨ p 1596 = true
  clause1176 : p 1511 = false ∨ p 1570 = false ∨ p 1593 = true
  clause1177 : p 1511 = false ∨ p 1571 = false ∨ p 1594 = true
  clause1178 : p 1511 = false ∨ p 1572 = false ∨ p 1595 = true
  clause1179 : p 1511 = false ∨ p 1573 = false ∨ p 1596 = true
  clause1180 : p 1511 = false ∨ p 1574 = false ∨ p 1597 = true
  clause1181 : p 1512 = false ∨ p 1570 = false ∨ p 1594 = true
  clause1182 : p 1512 = false ∨ p 1571 = false ∨ p 1595 = true
  clause1183 : p 1512 = false ∨ p 1572 = false ∨ p 1596 = true
  clause1184 : p 1512 = false ∨ p 1573 = false ∨ p 1597 = true

structure Block37 (p : Nat → Bool) : Prop where
  clause1185 : p 1513 = false ∨ p 1571 = false ∨ p 1596 = true
  clause1186 : p 1513 = false ∨ p 1572 = false ∨ p 1597 = true
  clause1187 : p 62 = true ∨ p 1607 = true
  clause1188 : p 61 = true ∨ p 1607 = true
  clause1189 : p 61 = true ∨ p 62 = true ∨ p 1608 = true
  clause1190 : p 67 = true ∨ p 1609 = true
  clause1191 : p 64 = true ∨ p 1609 = true
  clause1192 : p 64 = true ∨ p 67 = true ∨ p 1610 = true
  clause1193 : p 1609 = false ∨ p 1611 = true
  clause1194 : p 1610 = false ∨ p 1612 = true
  clause1195 : p 1607 = false ∨ p 1611 = true
  clause1196 : p 1607 = false ∨ p 1609 = false ∨ p 1612 = true
  clause1197 : p 1607 = false ∨ p 1610 = false ∨ p 1613 = true
  clause1198 : p 1608 = false ∨ p 1612 = true
  clause1199 : p 1608 = false ∨ p 1609 = false ∨ p 1613 = true
  clause1200 : p 1608 = false ∨ p 1610 = false ∨ p 1614 = true
  clause1201 : p 69 = true ∨ p 1615 = true
  clause1202 : p 68 = true ∨ p 1615 = true
  clause1203 : p 68 = true ∨ p 69 = true ∨ p 1616 = true
  clause1204 : p 73 = true ∨ p 1617 = true
  clause1205 : p 72 = true ∨ p 1617 = true
  clause1206 : p 72 = true ∨ p 73 = true ∨ p 1618 = true
  clause1207 : p 1617 = false ∨ p 1619 = true
  clause1208 : p 1618 = false ∨ p 1620 = true
  clause1209 : p 1615 = false ∨ p 1619 = true
  clause1210 : p 1615 = false ∨ p 1617 = false ∨ p 1620 = true
  clause1211 : p 1615 = false ∨ p 1618 = false ∨ p 1621 = true
  clause1212 : p 1616 = false ∨ p 1617 = false ∨ p 1621 = true
  clause1213 : p 1616 = false ∨ p 1618 = false ∨ p 1622 = true
  clause1214 : p 1619 = false ∨ p 1623 = true
  clause1215 : p 1620 = false ∨ p 1624 = true
  clause1216 : p 1621 = false ∨ p 1625 = true

structure Block38 (p : Nat → Bool) : Prop where
  clause1217 : p 1622 = false ∨ p 1626 = true
  clause1218 : p 1611 = false ∨ p 1623 = true
  clause1219 : p 1611 = false ∨ p 1619 = false ∨ p 1624 = true
  clause1220 : p 1611 = false ∨ p 1620 = false ∨ p 1625 = true
  clause1221 : p 1611 = false ∨ p 1621 = false ∨ p 1626 = true
  clause1222 : p 1611 = false ∨ p 1622 = false ∨ p 1627 = true
  clause1223 : p 1612 = false ∨ p 1624 = true
  clause1224 : p 1612 = false ∨ p 1619 = false ∨ p 1625 = true
  clause1225 : p 1612 = false ∨ p 1620 = false ∨ p 1626 = true
  clause1226 : p 1612 = false ∨ p 1621 = false ∨ p 1627 = true
  clause1227 : p 1612 = false ∨ p 1622 = false ∨ p 1628 = true
  clause1228 : p 1613 = false ∨ p 1625 = true
  clause1229 : p 1613 = false ∨ p 1619 = false ∨ p 1626 = true
  clause1230 : p 1613 = false ∨ p 1620 = false ∨ p 1627 = true
  clause1231 : p 1613 = false ∨ p 1621 = false ∨ p 1628 = true
  clause1232 : p 1614 = false ∨ p 1619 = false ∨ p 1627 = true
  clause1233 : p 1614 = false ∨ p 1620 = false ∨ p 1628 = true
  clause1234 : p 77 = true ∨ p 1631 = true
  clause1235 : p 80 = true ∨ p 1633 = true
  clause1236 : p 79 = true ∨ p 1633 = true
  clause1237 : p 79 = true ∨ p 80 = true ∨ p 1634 = true
  clause1238 : p 1633 = false ∨ p 1635 = true
  clause1239 : p 1634 = false ∨ p 1636 = true
  clause1240 : p 1631 = false ∨ p 1635 = true
  clause1241 : p 1631 = false ∨ p 1633 = false ∨ p 1636 = true
  clause1242 : p 1631 = false ∨ p 1634 = false ∨ p 1637 = true
  clause1243 : p 85 = true ∨ p 1639 = true
  clause1244 : p 84 = true ∨ p 1639 = true
  clause1245 : p 84 = true ∨ p 85 = true ∨ p 1640 = true
  clause1246 : p 90 = true ∨ p 1641 = true
  clause1247 : p 88 = true ∨ p 1641 = true
  clause1248 : p 88 = true ∨ p 90 = true ∨ p 1642 = true

structure Block39 (p : Nat → Bool) : Prop where
  clause1249 : p 1641 = false ∨ p 1643 = true
  clause1250 : p 1642 = false ∨ p 1644 = true
  clause1251 : p 1639 = false ∨ p 1643 = true
  clause1252 : p 1639 = false ∨ p 1641 = false ∨ p 1644 = true
  clause1253 : p 1639 = false ∨ p 1642 = false ∨ p 1645 = true
  clause1254 : p 1640 = false ∨ p 1644 = true
  clause1255 : p 1640 = false ∨ p 1641 = false ∨ p 1645 = true
  clause1256 : p 1640 = false ∨ p 1642 = false ∨ p 1646 = true
  clause1257 : p 1643 = false ∨ p 1647 = true
  clause1258 : p 1644 = false ∨ p 1648 = true
  clause1259 : p 1645 = false ∨ p 1649 = true
  clause1260 : p 1646 = false ∨ p 1650 = true
  clause1261 : p 1635 = false ∨ p 1643 = false ∨ p 1648 = true
  clause1262 : p 1635 = false ∨ p 1644 = false ∨ p 1649 = true
  clause1263 : p 1635 = false ∨ p 1645 = false ∨ p 1650 = true
  clause1264 : p 1635 = false ∨ p 1646 = false ∨ p 1651 = true
  clause1265 : p 1636 = false ∨ p 1648 = true
  clause1266 : p 1636 = false ∨ p 1643 = false ∨ p 1649 = true
  clause1267 : p 1636 = false ∨ p 1644 = false ∨ p 1650 = true
  clause1268 : p 1636 = false ∨ p 1645 = false ∨ p 1651 = true
  clause1269 : p 1636 = false ∨ p 1646 = false ∨ p 1652 = true
  clause1270 : p 1637 = false ∨ p 1649 = true
  clause1271 : p 1637 = false ∨ p 1643 = false ∨ p 1650 = true
  clause1272 : p 1637 = false ∨ p 1644 = false ∨ p 1651 = true
  clause1273 : p 1637 = false ∨ p 1645 = false ∨ p 1652 = true
  clause1274 : p 1637 = false ∨ p 1646 = false ∨ p 1653 = true
  clause1275 : p 1648 = false ∨ p 1656 = true
  clause1276 : p 1649 = false ∨ p 1657 = true
  clause1277 : p 1650 = false ∨ p 1658 = true
  clause1278 : p 1651 = false ∨ p 1659 = true
  clause1279 : p 1652 = false ∨ p 1660 = true
  clause1280 : p 1623 = false ∨ p 1647 = false ∨ p 1656 = true

structure Block40 (p : Nat → Bool) : Prop where
  clause1281 : p 1623 = false ∨ p 1648 = false ∨ p 1657 = true
  clause1282 : p 1623 = false ∨ p 1649 = false ∨ p 1658 = true
  clause1283 : p 1623 = false ∨ p 1650 = false ∨ p 1659 = true
  clause1284 : p 1623 = false ∨ p 1651 = false ∨ p 1660 = true
  clause1285 : p 1623 = false ∨ p 1652 = false ∨ p 1661 = true
  clause1286 : p 1624 = false ∨ p 1647 = false ∨ p 1657 = true
  clause1287 : p 1624 = false ∨ p 1648 = false ∨ p 1658 = true
  clause1288 : p 1624 = false ∨ p 1649 = false ∨ p 1659 = true
  clause1289 : p 1624 = false ∨ p 1650 = false ∨ p 1660 = true
  clause1290 : p 1624 = false ∨ p 1651 = false ∨ p 1661 = true
  clause1291 : p 1624 = false ∨ p 1652 = false ∨ p 1662 = true
  clause1292 : p 1624 = false ∨ p 1653 = false ∨ p 1663 = true
  clause1293 : p 1625 = false ∨ p 1647 = false ∨ p 1658 = true
  clause1294 : p 1625 = false ∨ p 1648 = false ∨ p 1659 = true
  clause1295 : p 1625 = false ∨ p 1649 = false ∨ p 1660 = true
  clause1296 : p 1625 = false ∨ p 1650 = false ∨ p 1661 = true
  clause1297 : p 1625 = false ∨ p 1651 = false ∨ p 1662 = true
  clause1298 : p 1625 = false ∨ p 1652 = false ∨ p 1663 = true
  clause1299 : p 1625 = false ∨ p 1653 = false ∨ p 1664 = true
  clause1300 : p 1626 = false ∨ p 1647 = false ∨ p 1659 = true
  clause1301 : p 1626 = false ∨ p 1648 = false ∨ p 1660 = true
  clause1302 : p 1626 = false ∨ p 1649 = false ∨ p 1661 = true
  clause1303 : p 1626 = false ∨ p 1650 = false ∨ p 1662 = true
  clause1304 : p 1626 = false ∨ p 1651 = false ∨ p 1663 = true
  clause1305 : p 1626 = false ∨ p 1652 = false ∨ p 1664 = true
  clause1306 : p 1627 = false ∨ p 1647 = false ∨ p 1660 = true
  clause1307 : p 1627 = false ∨ p 1648 = false ∨ p 1661 = true
  clause1308 : p 1627 = false ∨ p 1649 = false ∨ p 1662 = true
  clause1309 : p 1627 = false ∨ p 1650 = false ∨ p 1663 = true
  clause1310 : p 1627 = false ∨ p 1651 = false ∨ p 1664 = true
  clause1311 : p 1628 = false ∨ p 1648 = false ∨ p 1662 = true
  clause1312 : p 1628 = false ∨ p 1649 = false ∨ p 1663 = true

structure Block41 (p : Nat → Bool) : Prop where
  clause1313 : p 93 = true ∨ p 1671 = true
  clause1314 : p 92 = true ∨ p 1671 = true
  clause1315 : p 92 = true ∨ p 93 = true ∨ p 1672 = true
  clause1316 : p 97 = true ∨ p 1673 = true
  clause1317 : p 95 = true ∨ p 1673 = true
  clause1318 : p 95 = true ∨ p 97 = true ∨ p 1674 = true
  clause1319 : p 1673 = false ∨ p 1675 = true
  clause1320 : p 1674 = false ∨ p 1676 = true
  clause1321 : p 1671 = false ∨ p 1675 = true
  clause1322 : p 1671 = false ∨ p 1673 = false ∨ p 1676 = true
  clause1323 : p 1671 = false ∨ p 1674 = false ∨ p 1677 = true
  clause1324 : p 1672 = false ∨ p 1676 = true
  clause1325 : p 1672 = false ∨ p 1673 = false ∨ p 1677 = true
  clause1326 : p 1672 = false ∨ p 1674 = false ∨ p 1678 = true
  clause1327 : p 101 = true ∨ p 1679 = true
  clause1328 : p 98 = true ∨ p 1679 = true
  clause1329 : p 98 = true ∨ p 101 = true ∨ p 1680 = true
  clause1330 : p 105 = true ∨ p 1681 = true
  clause1331 : p 104 = true ∨ p 1681 = true
  clause1332 : p 104 = true ∨ p 105 = true ∨ p 1682 = true
  clause1333 : p 1681 = false ∨ p 1683 = true
  clause1334 : p 1682 = false ∨ p 1684 = true
  clause1335 : p 1679 = false ∨ p 1683 = true
  clause1336 : p 1679 = false ∨ p 1681 = false ∨ p 1684 = true
  clause1337 : p 1679 = false ∨ p 1682 = false ∨ p 1685 = true
  clause1338 : p 1680 = false ∨ p 1684 = true
  clause1339 : p 1680 = false ∨ p 1681 = false ∨ p 1685 = true
  clause1340 : p 1680 = false ∨ p 1682 = false ∨ p 1686 = true
  clause1341 : p 1683 = false ∨ p 1687 = true
  clause1342 : p 1684 = false ∨ p 1688 = true
  clause1343 : p 1685 = false ∨ p 1689 = true
  clause1344 : p 1686 = false ∨ p 1690 = true

structure Block42 (p : Nat → Bool) : Prop where
  clause1345 : p 1675 = false ∨ p 1687 = true
  clause1346 : p 1675 = false ∨ p 1683 = false ∨ p 1688 = true
  clause1347 : p 1675 = false ∨ p 1684 = false ∨ p 1689 = true
  clause1348 : p 1675 = false ∨ p 1685 = false ∨ p 1690 = true
  clause1349 : p 1675 = false ∨ p 1686 = false ∨ p 1691 = true
  clause1350 : p 1676 = false ∨ p 1688 = true
  clause1351 : p 1676 = false ∨ p 1683 = false ∨ p 1689 = true
  clause1352 : p 1676 = false ∨ p 1684 = false ∨ p 1690 = true
  clause1353 : p 1676 = false ∨ p 1685 = false ∨ p 1691 = true
  clause1354 : p 1676 = false ∨ p 1686 = false ∨ p 1692 = true
  clause1355 : p 1677 = false ∨ p 1689 = true
  clause1356 : p 1677 = false ∨ p 1683 = false ∨ p 1690 = true
  clause1357 : p 1677 = false ∨ p 1684 = false ∨ p 1691 = true
  clause1358 : p 1677 = false ∨ p 1685 = false ∨ p 1692 = true
  clause1359 : p 1677 = false ∨ p 1686 = false ∨ p 1693 = true
  clause1360 : p 1678 = false ∨ p 1690 = true
  clause1361 : p 1678 = false ∨ p 1683 = false ∨ p 1691 = true
  clause1362 : p 1678 = false ∨ p 1684 = false ∨ p 1692 = true
  clause1363 : p 1678 = false ∨ p 1685 = false ∨ p 1693 = true
  clause1364 : p 110 = true ∨ p 1695 = true
  clause1365 : p 109 = true ∨ p 1695 = true
  clause1366 : p 109 = true ∨ p 110 = true ∨ p 1696 = true
  clause1367 : p 113 = true ∨ p 1697 = true
  clause1368 : p 111 = true ∨ p 1697 = true
  clause1369 : p 111 = true ∨ p 113 = true ∨ p 1698 = true
  clause1370 : p 1697 = false ∨ p 1699 = true
  clause1371 : p 1698 = false ∨ p 1700 = true
  clause1372 : p 1695 = false ∨ p 1699 = true
  clause1373 : p 1695 = false ∨ p 1697 = false ∨ p 1700 = true
  clause1374 : p 1695 = false ∨ p 1698 = false ∨ p 1701 = true
  clause1375 : p 1696 = false ∨ p 1700 = true
  clause1376 : p 1696 = false ∨ p 1697 = false ∨ p 1701 = true

structure Block43 (p : Nat → Bool) : Prop where
  clause1377 : p 1696 = false ∨ p 1698 = false ∨ p 1702 = true
  clause1378 : p 117 = true ∨ p 1703 = true
  clause1379 : p 116 = true ∨ p 1703 = true
  clause1380 : p 116 = true ∨ p 117 = true ∨ p 1704 = true
  clause1381 : p 122 = true ∨ p 1705 = true
  clause1382 : p 119 = true ∨ p 1705 = true
  clause1383 : p 119 = true ∨ p 122 = true ∨ p 1706 = true
  clause1384 : p 1705 = false ∨ p 1707 = true
  clause1385 : p 1706 = false ∨ p 1708 = true
  clause1386 : p 1703 = false ∨ p 1707 = true
  clause1387 : p 1703 = false ∨ p 1705 = false ∨ p 1708 = true
  clause1388 : p 1703 = false ∨ p 1706 = false ∨ p 1709 = true
  clause1389 : p 1704 = false ∨ p 1708 = true
  clause1390 : p 1704 = false ∨ p 1705 = false ∨ p 1709 = true
  clause1391 : p 1704 = false ∨ p 1706 = false ∨ p 1710 = true
  clause1392 : p 1707 = false ∨ p 1711 = true
  clause1393 : p 1708 = false ∨ p 1712 = true
  clause1394 : p 1709 = false ∨ p 1713 = true
  clause1395 : p 1710 = false ∨ p 1714 = true
  clause1396 : p 1699 = false ∨ p 1711 = true
  clause1397 : p 1699 = false ∨ p 1707 = false ∨ p 1712 = true
  clause1398 : p 1699 = false ∨ p 1708 = false ∨ p 1713 = true
  clause1399 : p 1699 = false ∨ p 1709 = false ∨ p 1714 = true
  clause1400 : p 1699 = false ∨ p 1710 = false ∨ p 1715 = true
  clause1401 : p 1700 = false ∨ p 1712 = true
  clause1402 : p 1700 = false ∨ p 1707 = false ∨ p 1713 = true
  clause1403 : p 1700 = false ∨ p 1708 = false ∨ p 1714 = true
  clause1404 : p 1700 = false ∨ p 1709 = false ∨ p 1715 = true
  clause1405 : p 1700 = false ∨ p 1710 = false ∨ p 1716 = true
  clause1406 : p 1701 = false ∨ p 1713 = true
  clause1407 : p 1701 = false ∨ p 1707 = false ∨ p 1714 = true
  clause1408 : p 1701 = false ∨ p 1708 = false ∨ p 1715 = true

structure Block44 (p : Nat → Bool) : Prop where
  clause1409 : p 1701 = false ∨ p 1709 = false ∨ p 1716 = true
  clause1410 : p 1702 = false ∨ p 1714 = true
  clause1411 : p 1702 = false ∨ p 1707 = false ∨ p 1715 = true
  clause1412 : p 1687 = false ∨ p 1712 = false ∨ p 1721 = true
  clause1413 : p 1687 = false ∨ p 1713 = false ∨ p 1722 = true
  clause1414 : p 1687 = false ∨ p 1714 = false ∨ p 1723 = true
  clause1415 : p 1687 = false ∨ p 1715 = false ∨ p 1724 = true
  clause1416 : p 1687 = false ∨ p 1716 = false ∨ p 1725 = true
  clause1417 : p 1688 = false ∨ p 1711 = false ∨ p 1721 = true
  clause1418 : p 1688 = false ∨ p 1712 = false ∨ p 1722 = true
  clause1419 : p 1688 = false ∨ p 1713 = false ∨ p 1723 = true
  clause1420 : p 1688 = false ∨ p 1714 = false ∨ p 1724 = true
  clause1421 : p 1688 = false ∨ p 1715 = false ∨ p 1725 = true
  clause1422 : p 1688 = false ∨ p 1716 = false ∨ p 1726 = true
  clause1423 : p 1689 = false ∨ p 1711 = false ∨ p 1722 = true
  clause1424 : p 1689 = false ∨ p 1712 = false ∨ p 1723 = true
  clause1425 : p 1689 = false ∨ p 1713 = false ∨ p 1724 = true
  clause1426 : p 1689 = false ∨ p 1714 = false ∨ p 1725 = true
  clause1427 : p 1689 = false ∨ p 1715 = false ∨ p 1726 = true
  clause1428 : p 1690 = false ∨ p 1711 = false ∨ p 1723 = true
  clause1429 : p 1690 = false ∨ p 1712 = false ∨ p 1724 = true
  clause1430 : p 1690 = false ∨ p 1713 = false ∨ p 1725 = true
  clause1431 : p 1690 = false ∨ p 1714 = false ∨ p 1726 = true
  clause1432 : p 1690 = false ∨ p 1715 = false ∨ p 1727 = true
  clause1433 : p 1690 = false ∨ p 1716 = false ∨ p 1728 = true
  clause1434 : p 1691 = false ∨ p 1711 = false ∨ p 1724 = true
  clause1435 : p 1691 = false ∨ p 1712 = false ∨ p 1725 = true
  clause1436 : p 1691 = false ∨ p 1713 = false ∨ p 1726 = true
  clause1437 : p 1691 = false ∨ p 1714 = false ∨ p 1727 = true
  clause1438 : p 1691 = false ∨ p 1715 = false ∨ p 1728 = true
  clause1439 : p 1692 = false ∨ p 1724 = true
  clause1440 : p 1692 = false ∨ p 1711 = false ∨ p 1725 = true

structure Block45 (p : Nat → Bool) : Prop where
  clause1441 : p 1692 = false ∨ p 1712 = false ∨ p 1726 = true
  clause1442 : p 1692 = false ∨ p 1713 = false ∨ p 1727 = true
  clause1443 : p 1692 = false ∨ p 1714 = false ∨ p 1728 = true
  clause1444 : p 1693 = false ∨ p 1711 = false ∨ p 1726 = true
  clause1445 : p 1693 = false ∨ p 1712 = false ∨ p 1727 = true
  clause1446 : p 1693 = false ∨ p 1713 = false ∨ p 1728 = true
  clause1447 : p 1656 = false ∨ p 1725 = false ∨ p 1743 = true
  clause1448 : p 1656 = false ∨ p 1726 = false ∨ p 1744 = true
  clause1449 : p 1656 = false ∨ p 1727 = false ∨ p 1745 = true
  clause1450 : p 1657 = false ∨ p 1724 = false ∨ p 1743 = true
  clause1451 : p 1657 = false ∨ p 1725 = false ∨ p 1744 = true
  clause1452 : p 1657 = false ∨ p 1726 = false ∨ p 1745 = true
  clause1453 : p 1657 = false ∨ p 1727 = false ∨ p 1746 = true
  clause1454 : p 1657 = false ∨ p 1728 = false ∨ p 1747 = true
  clause1455 : p 1658 = false ∨ p 1723 = false ∨ p 1743 = true
  clause1456 : p 1658 = false ∨ p 1724 = false ∨ p 1744 = true
  clause1457 : p 1658 = false ∨ p 1725 = false ∨ p 1745 = true
  clause1458 : p 1658 = false ∨ p 1726 = false ∨ p 1746 = true
  clause1459 : p 1658 = false ∨ p 1727 = false ∨ p 1747 = true
  clause1460 : p 1658 = false ∨ p 1728 = false ∨ p 1748 = true
  clause1461 : p 1659 = false ∨ p 1722 = false ∨ p 1743 = true
  clause1462 : p 1659 = false ∨ p 1723 = false ∨ p 1744 = true
  clause1463 : p 1659 = false ∨ p 1724 = false ∨ p 1745 = true
  clause1464 : p 1659 = false ∨ p 1725 = false ∨ p 1746 = true
  clause1465 : p 1659 = false ∨ p 1726 = false ∨ p 1747 = true
  clause1466 : p 1659 = false ∨ p 1727 = false ∨ p 1748 = true
  clause1467 : p 1659 = false ∨ p 1728 = false ∨ p 1749 = true
  clause1468 : p 1660 = false ∨ p 1722 = false ∨ p 1744 = true
  clause1469 : p 1660 = false ∨ p 1723 = false ∨ p 1745 = true
  clause1470 : p 1660 = false ∨ p 1724 = false ∨ p 1746 = true
  clause1471 : p 1660 = false ∨ p 1725 = false ∨ p 1747 = true
  clause1472 : p 1660 = false ∨ p 1726 = false ∨ p 1748 = true

structure Block46 (p : Nat → Bool) : Prop where
  clause1473 : p 1660 = false ∨ p 1727 = false ∨ p 1749 = true
  clause1474 : p 1660 = false ∨ p 1728 = false ∨ p 1750 = true
  clause1475 : p 1661 = false ∨ p 1721 = false ∨ p 1744 = true
  clause1476 : p 1661 = false ∨ p 1722 = false ∨ p 1745 = true
  clause1477 : p 1661 = false ∨ p 1723 = false ∨ p 1746 = true
  clause1478 : p 1661 = false ∨ p 1724 = false ∨ p 1747 = true
  clause1479 : p 1661 = false ∨ p 1725 = false ∨ p 1748 = true
  clause1480 : p 1661 = false ∨ p 1726 = false ∨ p 1749 = true
  clause1481 : p 1662 = false ∨ p 1721 = false ∨ p 1745 = true
  clause1482 : p 1662 = false ∨ p 1722 = false ∨ p 1746 = true
  clause1483 : p 1662 = false ∨ p 1723 = false ∨ p 1747 = true
  clause1484 : p 1662 = false ∨ p 1724 = false ∨ p 1748 = true
  clause1485 : p 1662 = false ∨ p 1725 = false ∨ p 1749 = true
  clause1486 : p 1662 = false ∨ p 1726 = false ∨ p 1750 = true
  clause1487 : p 1663 = false ∨ p 1721 = false ∨ p 1746 = true
  clause1488 : p 1663 = false ∨ p 1722 = false ∨ p 1747 = true
  clause1489 : p 1663 = false ∨ p 1723 = false ∨ p 1748 = true
  clause1490 : p 1663 = false ∨ p 1724 = false ∨ p 1749 = true
  clause1491 : p 1663 = false ∨ p 1725 = false ∨ p 1750 = true
  clause1492 : p 1664 = false ∨ p 1721 = false ∨ p 1747 = true
  clause1493 : p 1664 = false ∨ p 1722 = false ∨ p 1748 = true
  clause1494 : p 1664 = false ∨ p 1723 = false ∨ p 1749 = true
  clause1495 : p 1664 = false ∨ p 1724 = false ∨ p 1750 = true
  clause1496 : p 1590 = false ∨ p 1750 = false ∨ p 1780 = true
  clause1497 : p 1591 = false ∨ p 1749 = false ∨ p 1780 = true
  clause1498 : p 1592 = false ∨ p 1748 = false ∨ p 1780 = true
  clause1499 : p 1593 = false ∨ p 1747 = false ∨ p 1780 = true
  clause1500 : p 1594 = false ∨ p 1746 = false ∨ p 1780 = true
  clause1501 : p 1595 = false ∨ p 1745 = false ∨ p 1780 = true
  clause1502 : p 1596 = false ∨ p 1744 = false ∨ p 1780 = true
  clause1503 : p 1597 = false ∨ p 1743 = false ∨ p 1780 = true
  clause1504 : p 1780 = false

structure Block47 (p : Nat → Bool) : Prop where
  clause1505 : p 3 = false ∨ p 4 = false ∨ p 10 = false ∨ p 11 = false
  clause1506 : p 5 = false ∨ p 6 = false ∨ p 8 = false ∨ p 9 = false
  clause1507 : p 5 = false ∨ p 24 = false ∨ p 60 = false ∨ p 87 = false
  clause1508 : p 7 = false ∨ p 26 = false ∨ p 61 = false ∨ p 89 = false
  clause1509 : p 17 = false ∨ p 19 = false ∨ p 73 = false ∨ p 75 = false
  clause1510 : p 17 = false ∨ p 39 = false ∨ p 73 = false ∨ p 106 = false
  clause1511 : p 20 = false ∨ p 24 = false ∨ p 80 = false ∨ p 87 = false
  clause1512 : p 22 = false ∨ p 23 = false ∨ p 85 = false ∨ p 86 = false
  clause1513 : p 22 = false ∨ p 42 = false ∨ p 85 = false ∨ p 108 = false
  clause1514 : p 26 = false ∨ p 44 = false ∨ p 89 = false ∨ p 110 = false
  clause1515 : p 29 = false ∨ p 31 = false ∨ p 93 = false ∨ p 94 = false
  clause1516 : p 32 = false ∨ p 33 = false ∨ p 35 = false ∨ p 37 = false
  clause1517 : p 38 = false ∨ p 42 = false ∨ p 43 = false ∨ p 46 = false
  clause1518 : p 39 = false ∨ p 44 = false ∨ p 106 = false ∨ p 110 = false
  clause1519 : p 40 = false ∨ p 42 = false ∨ p 45 = false ∨ p 46 = false
  clause1520 : p 50 = false ∨ p 51 = false ∨ p 52 = false ∨ p 53 = false
  clause1521 : p 55 = false ∨ p 56 = false ∨ p 64 = false ∨ p 65 = false
  clause1522 : p 55 = false ∨ p 56 = false ∨ p 80 = false ∨ p 81 = false
  clause1523 : p 55 = false ∨ p 60 = false ∨ p 80 = false ∨ p 87 = false
  clause1524 : p 61 = false ∨ p 63 = false ∨ p 89 = false ∨ p 92 = false
  clause1525 : p 64 = false ∨ p 65 = false ∨ p 66 = false ∨ p 67 = false
  clause1526 : p 65 = false ∨ p 67 = false ∨ p 93 = false ∨ p 94 = false
  clause1527 : p 80 = false ∨ p 83 = false ∨ p 87 = false ∨ p 90 = false
  clause1528 : p 80 = false ∨ p 87 = false ∨ p 103 = false ∨ p 109 = false
  clause1529 : p 81 = false ∨ p 93 = false ∨ p 104 = false ∨ p 114 = false
  clause1530 : p 82 = false ∨ p 85 = false ∨ p 88 = false ∨ p 91 = false
  clause1531 : p 83 = false ∨ p 85 = false ∨ p 90 = false ∨ p 91 = false
  clause1532 : p 84 = false ∨ p 86 = false ∨ p 96 = false ∨ p 97 = false
  clause1533 : p 86 = false ∨ p 92 = false ∨ p 97 = false ∨ p 102 = false
  clause1534 : p 87 = false ∨ p 88 = false ∨ p 90 = false ∨ p 91 = false
  clause1535 : p 87 = false ∨ p 88 = false ∨ p 98 = false ∨ p 100 = false
  clause1536 : p 87 = false ∨ p 98 = false ∨ p 109 = false ∨ p 118 = false

structure Block48 (p : Nat → Bool) : Prop where
  clause1537 : p 89 = false ∨ p 92 = false ∨ p 110 = false ∨ p 112 = false
  clause1538 : p 93 = false ∨ p 94 = false ∨ p 96 = false ∨ p 97 = false
  clause1539 : p 93 = false ∨ p 94 = false ∨ p 114 = false ∨ p 116 = false
  clause1540 : p 94 = false ∨ p 97 = false ∨ p 101 = false ∨ p 102 = false
  clause1541 : p 98 = false ∨ p 99 = false ∨ p 100 = false ∨ p 101 = false
  clause1542 : p 103 = false ∨ p 109 = false ∨ p 113 = false ∨ p 118 = false
  clause1543 : p 104 = false ∨ p 106 = false ∨ p 114 = false ∨ p 116 = false
  clause1544 : p 105 = false ∨ p 108 = false ∨ p 115 = false ∨ p 117 = false
  clause1545 : p 111 = false ∨ p 112 = false ∨ p 120 = false ∨ p 122 = false
  clause1546 : p 113 = false ∨ p 114 = false ∨ p 115 = false ∨ p 116 = false
  clause1547 : p 119 = false ∨ p 120 = false ∨ p 121 = false ∨ p 122 = false

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

theorem bool_contra {b : Bool} (ht : b = true) (hf : b = false) : False :=
  Bool.noConfusion (ht.symm.trans hf)

theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

theorem bool_true_of_not_false {b : Bool} (h : ¬ b = false) : b = true := by
  cases b <;> simp_all

theorem step1 (p : Nat → Bool) (h : Constraints p) : p 1 = false ∨ p 123 = true ∨ p 6 = true := h.block0.clause1

theorem step2 (p : Nat → Bool) (h : Constraints p) : p 1 = false ∨ p 123 = true ∨ p 2 = true := h.block0.clause2

theorem step3 (p : Nat → Bool) (h : Constraints p) : p 2 = false ∨ p 124 = true ∨ p 7 = true ∨ p 17 = true := h.block0.clause3

theorem step4 (p : Nat → Bool) (h : Constraints p) : p 2 = false ∨ p 124 = true ∨ p 1 = true ∨ p 17 = true := h.block0.clause4

theorem step5 (p : Nat → Bool) (h : Constraints p) : p 2 = false ∨ p 124 = true ∨ p 1 = true ∨ p 7 = true := h.block0.clause5

theorem step6 (p : Nat → Bool) (h : Constraints p) : p 3 = false ∨ p 4 = false ∨ p 8 = false ∨ p 10 = false := h.block0.clause6

theorem step7 (p : Nat → Bool) (h : Constraints p) : p 3 = false ∨ p 4 = false ∨ p 8 = false ∨ p 18 = false := h.block0.clause7

theorem step8 (p : Nat → Bool) (h : Constraints p) : p 3 = false ∨ p 4 = false ∨ p 10 = false ∨ p 18 = false := h.block0.clause8

theorem step9 (p : Nat → Bool) (h : Constraints p) : p 3 = false ∨ p 8 = false ∨ p 10 = false ∨ p 18 = false := h.block0.clause9

theorem step10 (p : Nat → Bool) (h : Constraints p) : p 3 = false ∨ p 125 = true ∨ p 8 = true ∨ p 10 = true ∨ p 18 = true := h.block0.clause10

theorem step11 (p : Nat → Bool) (h : Constraints p) : p 3 = false ∨ p 125 = true ∨ p 4 = true ∨ p 8 = true ∨ p 10 = true := h.block0.clause11

theorem step12 (p : Nat → Bool) (h : Constraints p) : p 4 = false ∨ p 3 = false ∨ p 11 = false ∨ p 57 = false := h.block0.clause12

theorem step13 (p : Nat → Bool) (h : Constraints p) : p 4 = false ∨ p 126 = true ∨ p 11 = true ∨ p 57 = true := h.block0.clause13

theorem step14 (p : Nat → Bool) (h : Constraints p) : p 4 = false ∨ p 126 = true ∨ p 3 = true ∨ p 57 = true := h.block0.clause14

theorem step15 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 6 = false ∨ p 8 = false ∨ p 13 = false := h.block0.clause15

theorem step16 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 6 = false ∨ p 8 = false ∨ p 24 = false := h.block0.clause16

theorem step17 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 6 = false ∨ p 8 = false ∨ p 60 = false := h.block0.clause17

theorem step18 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 6 = false ∨ p 13 = false ∨ p 24 = false := h.block0.clause18

theorem step19 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 6 = false ∨ p 13 = false ∨ p 60 = false := h.block0.clause19

theorem step20 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 6 = false ∨ p 24 = false ∨ p 60 = false := h.block0.clause20

theorem step21 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 8 = false ∨ p 13 = false ∨ p 24 = false := h.block0.clause21

theorem step22 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 8 = false ∨ p 13 = false ∨ p 60 = false := h.block0.clause22

theorem step23 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 8 = false ∨ p 24 = false ∨ p 60 = false := h.block0.clause23

theorem step24 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 13 = false ∨ p 24 = false ∨ p 60 = false := h.block0.clause24

theorem step25 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 127 = true ∨ p 6 = true ∨ p 8 = true ∨ p 13 = true ∨ p 24 = true := h.block0.clause25

theorem step26 (p : Nat → Bool) (h : Constraints p) : p 6 = false ∨ p 1 = false ∨ p 5 = false ∨ p 9 = false := h.block0.clause26

theorem step27 (p : Nat → Bool) (h : Constraints p) : p 6 = false ∨ p 128 = true ∨ p 5 = true ∨ p 7 = true ∨ p 9 = true := h.block0.clause27

theorem step28 (p : Nat → Bool) (h : Constraints p) : p 6 = false ∨ p 128 = true ∨ p 1 = true ∨ p 7 = true ∨ p 9 = true := h.block0.clause28

theorem step29 (p : Nat → Bool) (h : Constraints p) : p 6 = false ∨ p 128 = true ∨ p 1 = true ∨ p 5 = true ∨ p 9 = true := h.block0.clause29

theorem step30 (p : Nat → Bool) (h : Constraints p) : p 6 = false ∨ p 128 = true ∨ p 1 = true ∨ p 5 = true ∨ p 7 = true := h.block0.clause30

theorem step31 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 2 = false ∨ p 6 = false ∨ p 15 = false := h.block0.clause31

theorem step32 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 2 = false ∨ p 6 = false ∨ p 26 = false := h.block0.clause32

theorem step33 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 2 = false ∨ p 6 = false ∨ p 61 = false := h.block1.clause33

theorem step34 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 2 = false ∨ p 15 = false ∨ p 26 = false := h.block1.clause34

theorem step35 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 2 = false ∨ p 15 = false ∨ p 61 = false := h.block1.clause35

theorem step36 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 2 = false ∨ p 26 = false ∨ p 61 = false := h.block1.clause36

theorem step37 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 6 = false ∨ p 15 = false ∨ p 26 = false := h.block1.clause37

theorem step38 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 6 = false ∨ p 15 = false ∨ p 61 = false := h.block1.clause38

theorem step39 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 6 = false ∨ p 26 = false ∨ p 61 = false := h.block1.clause39

theorem step40 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 15 = false ∨ p 26 = false ∨ p 61 = false := h.block1.clause40

theorem step41 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 129 = true ∨ p 2 = true ∨ p 6 = true ∨ p 15 = true ∨ p 26 = true := h.block1.clause41

theorem step42 (p : Nat → Bool) (h : Constraints p) : p 8 = false ∨ p 130 = true ∨ p 5 = true ∨ p 9 = true := h.block1.clause42

theorem step43 (p : Nat → Bool) (h : Constraints p) : p 8 = false ∨ p 130 = true ∨ p 3 = true ∨ p 9 = true := h.block1.clause43

theorem step44 (p : Nat → Bool) (h : Constraints p) : p 8 = false ∨ p 130 = true ∨ p 3 = true ∨ p 5 = true := h.block1.clause44

theorem step45 (p : Nat → Bool) (h : Constraints p) : p 9 = false ∨ p 131 = true ∨ p 8 = true := h.block1.clause45

theorem step46 (p : Nat → Bool) (h : Constraints p) : p 9 = false ∨ p 131 = true ∨ p 6 = true := h.block1.clause46

theorem step47 (p : Nat → Bool) (h : Constraints p) : p 10 = false ∨ p 3 = false ∨ p 11 = false ∨ p 32 = false := h.block1.clause47

theorem step48 (p : Nat → Bool) (h : Constraints p) : p 10 = false ∨ p 132 = true ∨ p 3 = true ∨ p 32 = true := h.block1.clause48

theorem step49 (p : Nat → Bool) (h : Constraints p) : p 11 = false ∨ p 4 = false ∨ p 10 = false ∨ p 12 = false := h.block1.clause49

theorem step50 (p : Nat → Bool) (h : Constraints p) : p 133 = false ∨ p 4 = false ∨ p 12 = false := h.block1.clause50

theorem step51 (p : Nat → Bool) (h : Constraints p) : p 11 = false ∨ p 133 = true ∨ p 10 = true ∨ p 12 = true := h.block1.clause51

theorem step52 (p : Nat → Bool) (h : Constraints p) : p 11 = false ∨ p 133 = true ∨ p 4 = true ∨ p 10 = true := h.block1.clause52

theorem step53 (p : Nat → Bool) (h : Constraints p) : p 12 = false ∨ p 134 = true ∨ p 16 = true := h.block1.clause53

theorem step54 (p : Nat → Bool) (h : Constraints p) : p 12 = false ∨ p 134 = true ∨ p 11 = true := h.block1.clause54

theorem step55 (p : Nat → Bool) (h : Constraints p) : p 13 = false ∨ p 135 = true ∨ p 14 = true := h.block1.clause55

theorem step56 (p : Nat → Bool) (h : Constraints p) : p 13 = false ∨ p 135 = true ∨ p 5 = true := h.block1.clause56

theorem step57 (p : Nat → Bool) (h : Constraints p) : p 14 = false ∨ p 136 = true ∨ p 15 = true := h.block1.clause57

theorem step58 (p : Nat → Bool) (h : Constraints p) : p 14 = false ∨ p 136 = true ∨ p 13 = true := h.block1.clause58

theorem step59 (p : Nat → Bool) (h : Constraints p) : p 15 = false ∨ p 7 = false ∨ p 14 = false ∨ p 16 = false := h.block1.clause59

theorem step60 (p : Nat → Bool) (h : Constraints p) : p 15 = false ∨ p 137 = true ∨ p 14 = true ∨ p 16 = true := h.block1.clause60

theorem step61 (p : Nat → Bool) (h : Constraints p) : p 15 = false ∨ p 137 = true ∨ p 7 = true ∨ p 16 = true := h.block1.clause61

theorem step62 (p : Nat → Bool) (h : Constraints p) : p 15 = false ∨ p 137 = true ∨ p 7 = true ∨ p 14 = true := h.block1.clause62

theorem step63 (p : Nat → Bool) (h : Constraints p) : p 16 = false ∨ p 138 = true ∨ p 15 = true := h.block1.clause63

theorem step64 (p : Nat → Bool) (h : Constraints p) : p 16 = false ∨ p 138 = true ∨ p 12 = true := h.block1.clause64

theorem step65 (p : Nat → Bool) (h : Constraints p) : p 17 = false ∨ p 2 = false ∨ p 19 = false ∨ p 39 = false := h.block2.clause65

theorem step66 (p : Nat → Bool) (h : Constraints p) : p 17 = false ∨ p 2 = false ∨ p 39 = false ∨ p 73 = false := h.block2.clause66

theorem step67 (p : Nat → Bool) (h : Constraints p) : p 17 = false ∨ p 139 = true ∨ p 19 = true ∨ p 39 = true ∨ p 73 = true := h.block2.clause67

theorem step68 (p : Nat → Bool) (h : Constraints p) : p 17 = false ∨ p 139 = true ∨ p 2 = true ∨ p 19 = true ∨ p 39 = true := h.block2.clause68

theorem step69 (p : Nat → Bool) (h : Constraints p) : p 18 = false ∨ p 3 = false ∨ p 40 = false ∨ p 74 = false := h.block2.clause69

theorem step70 (p : Nat → Bool) (h : Constraints p) : p 18 = false ∨ p 140 = true ∨ p 3 = true ∨ p 40 = true := h.block2.clause70

theorem step71 (p : Nat → Bool) (h : Constraints p) : p 19 = false ∨ p 141 = true ∨ p 75 = true := h.block2.clause71

theorem step72 (p : Nat → Bool) (h : Constraints p) : p 19 = false ∨ p 141 = true ∨ p 17 = true := h.block2.clause72

theorem step73 (p : Nat → Bool) (h : Constraints p) : p 20 = false ∨ p 21 = false ∨ p 24 = false ∨ p 80 = false := h.block2.clause73

theorem step74 (p : Nat → Bool) (h : Constraints p) : p 20 = false ∨ p 142 = true ∨ p 24 = true ∨ p 80 = true := h.block2.clause74

theorem step75 (p : Nat → Bool) (h : Constraints p) : p 21 = false ∨ p 20 = false ∨ p 25 = false ∨ p 29 = false := h.block2.clause75

theorem step76 (p : Nat → Bool) (h : Constraints p) : p 21 = false ∨ p 143 = true ∨ p 20 = true ∨ p 29 = true ∨ p 81 = true := h.block2.clause76

theorem step77 (p : Nat → Bool) (h : Constraints p) : p 21 = false ∨ p 143 = true ∨ p 20 = true ∨ p 25 = true ∨ p 81 = true := h.block2.clause77

theorem step78 (p : Nat → Bool) (h : Constraints p) : p 22 = false ∨ p 23 = false ∨ p 33 = false ∨ p 42 = false := h.block2.clause78

theorem step79 (p : Nat → Bool) (h : Constraints p) : p 22 = false ∨ p 23 = false ∨ p 33 = false ∨ p 85 = false := h.block2.clause79

theorem step80 (p : Nat → Bool) (h : Constraints p) : p 22 = false ∨ p 23 = false ∨ p 42 = false ∨ p 85 = false := h.block2.clause80

theorem step81 (p : Nat → Bool) (h : Constraints p) : p 22 = false ∨ p 33 = false ∨ p 42 = false ∨ p 85 = false := h.block2.clause81

theorem step82 (p : Nat → Bool) (h : Constraints p) : p 23 = false ∨ p 145 = true ∨ p 28 = true ∨ p 86 = true := h.block2.clause82

theorem step83 (p : Nat → Bool) (h : Constraints p) : p 23 = false ∨ p 145 = true ∨ p 22 = true ∨ p 86 = true := h.block2.clause83

theorem step84 (p : Nat → Bool) (h : Constraints p) : p 23 = false ∨ p 145 = true ∨ p 22 = true ∨ p 28 = true := h.block2.clause84

theorem step85 (p : Nat → Bool) (h : Constraints p) : p 24 = false ∨ p 5 = false ∨ p 20 = false ∨ p 87 = false := h.block2.clause85

theorem step86 (p : Nat → Bool) (h : Constraints p) : p 24 = false ∨ p 5 = false ∨ p 25 = false ∨ p 87 = false := h.block2.clause86

theorem step87 (p : Nat → Bool) (h : Constraints p) : p 24 = false ∨ p 146 = true ∨ p 20 = true ∨ p 25 = true ∨ p 87 = true := h.block2.clause87

theorem step88 (p : Nat → Bool) (h : Constraints p) : p 24 = false ∨ p 146 = true ∨ p 5 = true ∨ p 25 = true ∨ p 87 = true := h.block2.clause88

theorem step89 (p : Nat → Bool) (h : Constraints p) : p 24 = false ∨ p 146 = true ∨ p 5 = true ∨ p 20 = true ∨ p 87 = true := h.block2.clause89

theorem step90 (p : Nat → Bool) (h : Constraints p) : p 24 = false ∨ p 146 = true ∨ p 5 = true ∨ p 20 = true ∨ p 25 = true := h.block2.clause90

theorem step91 (p : Nat → Bool) (h : Constraints p) : p 25 = false ∨ p 21 = false ∨ p 24 = false ∨ p 26 = false := h.block2.clause91

theorem step92 (p : Nat → Bool) (h : Constraints p) : p 25 = false ∨ p 21 = false ∨ p 24 = false ∨ p 27 = false := h.block2.clause92

theorem step93 (p : Nat → Bool) (h : Constraints p) : p 25 = false ∨ p 21 = false ∨ p 26 = false ∨ p 27 = false := h.block2.clause93

theorem step94 (p : Nat → Bool) (h : Constraints p) : p 25 = false ∨ p 24 = false ∨ p 26 = false ∨ p 27 = false := h.block2.clause94

theorem step95 (p : Nat → Bool) (h : Constraints p) : p 26 = false ∨ p 7 = true ∨ p 25 = true ∨ p 28 = true ∨ p 44 = true ∨ p 89 = true := h.block2.clause95

theorem step96 (p : Nat → Bool) (h : Constraints p) : p 26 = false ∨ p 7 = false ∨ p 25 = false ∨ p 44 = false := h.block2.clause96

theorem step97 (p : Nat → Bool) (h : Constraints p) : p 26 = false ∨ p 25 = false ∨ p 28 = false ∨ p 89 = false := h.block3.clause97

theorem step98 (p : Nat → Bool) (h : Constraints p) : p 26 = false ∨ p 148 = true ∨ p 7 = true ∨ p 25 = true ∨ p 44 = true ∨ p 89 = true := h.block3.clause98

theorem step99 (p : Nat → Bool) (h : Constraints p) : p 27 = false ∨ p 25 = false ∨ p 28 = false ∨ p 36 = false := h.block3.clause99

theorem step100 (p : Nat → Bool) (h : Constraints p) : p 27 = false ∨ p 149 = true ∨ p 25 = true ∨ p 36 = true := h.block3.clause100

theorem step101 (p : Nat → Bool) (h : Constraints p) : p 27 = false ∨ p 149 = true ∨ p 25 = true ∨ p 28 = true := h.block3.clause101

theorem step102 (p : Nat → Bool) (h : Constraints p) : p 28 = false ∨ p 23 = false ∨ p 26 = false ∨ p 27 = false := h.block3.clause102

theorem step103 (p : Nat → Bool) (h : Constraints p) : p 28 = false ∨ p 23 = false ∨ p 26 = false ∨ p 92 = false := h.block3.clause103

theorem step104 (p : Nat → Bool) (h : Constraints p) : p 28 = false ∨ p 23 = false ∨ p 27 = false ∨ p 92 = false := h.block3.clause104

theorem step105 (p : Nat → Bool) (h : Constraints p) : p 28 = false ∨ p 26 = false ∨ p 27 = false ∨ p 92 = false := h.block3.clause105

theorem step106 (p : Nat → Bool) (h : Constraints p) : p 29 = false ∨ p 21 = false ∨ p 31 = false ∨ p 93 = false := h.block3.clause106

theorem step107 (p : Nat → Bool) (h : Constraints p) : p 29 = false ∨ p 151 = true ∨ p 31 = true ∨ p 93 = true := h.block3.clause107

theorem step108 (p : Nat → Bool) (h : Constraints p) : p 29 = false ∨ p 151 = true ∨ p 21 = true ∨ p 93 = true := h.block3.clause108

theorem step109 (p : Nat → Bool) (h : Constraints p) : p 30 = false ∨ p 31 = false ∨ p 33 = false ∨ p 34 = false := h.block3.clause109

theorem step110 (p : Nat → Bool) (h : Constraints p) : p 30 = false ∨ p 152 = true ∨ p 33 = true ∨ p 34 = true := h.block3.clause110

theorem step111 (p : Nat → Bool) (h : Constraints p) : p 31 = false ∨ p 153 = true ∨ p 30 = true ∨ p 94 = true := h.block3.clause111

theorem step112 (p : Nat → Bool) (h : Constraints p) : p 31 = false ∨ p 153 = true ∨ p 29 = true ∨ p 94 = true := h.block3.clause112

theorem step113 (p : Nat → Bool) (h : Constraints p) : p 31 = false ∨ p 153 = true ∨ p 29 = true ∨ p 30 = true := h.block3.clause113

theorem step114 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 10 = false ∨ p 33 = false ∨ p 35 = false := h.block3.clause114

theorem step115 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 10 = false ∨ p 35 = false ∨ p 47 = false := h.block3.clause115

theorem step116 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 10 = false ∨ p 35 = false ∨ p 95 = false := h.block3.clause116

theorem step117 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 10 = false ∨ p 47 = false ∨ p 95 = false := h.block3.clause117

theorem step118 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 33 = false ∨ p 35 = false ∨ p 47 = false := h.block3.clause118

theorem step119 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 33 = false ∨ p 35 = false ∨ p 95 = false := h.block3.clause119

theorem step120 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 33 = false ∨ p 47 = false ∨ p 95 = false := h.block3.clause120

theorem step121 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 35 = false ∨ p 47 = false ∨ p 95 = false := h.block3.clause121

theorem step122 (p : Nat → Bool) (h : Constraints p) : p 33 = false ∨ p 22 = false ∨ p 30 = false ∨ p 32 = false := h.block3.clause122

theorem step123 (p : Nat → Bool) (h : Constraints p) : p 33 = false ∨ p 22 = false ∨ p 32 = false ∨ p 37 = false := h.block3.clause123

theorem step124 (p : Nat → Bool) (h : Constraints p) : p 33 = false ∨ p 155 = true ∨ p 22 = true ∨ p 30 = true ∨ p 37 = true := h.block3.clause124

theorem step125 (p : Nat → Bool) (h : Constraints p) : p 34 = false ∨ p 156 = true ∨ p 37 = true ∨ p 52 = true ∨ p 100 = true := h.block3.clause125

theorem step126 (p : Nat → Bool) (h : Constraints p) : p 34 = false ∨ p 156 = true ∨ p 30 = true ∨ p 37 = true ∨ p 100 = true := h.block3.clause126

theorem step127 (p : Nat → Bool) (h : Constraints p) : p 34 = false ∨ p 156 = true ∨ p 30 = true ∨ p 37 = true ∨ p 52 = true := h.block3.clause127

theorem step128 (p : Nat → Bool) (h : Constraints p) : p 35 = false ∨ p 157 = true ∨ p 32 = true ∨ p 37 = true := h.block3.clause128

theorem step129 (p : Nat → Bool) (h : Constraints p) : p 35 = false ∨ p 157 = true ∨ p 32 = true ∨ p 36 = true := h.block4.clause129

theorem step130 (p : Nat → Bool) (h : Constraints p) : p 36 = false ∨ p 158 = true ∨ p 35 = true := h.block4.clause130

theorem step131 (p : Nat → Bool) (h : Constraints p) : p 37 = false ∨ p 33 = false ∨ p 34 = false ∨ p 35 = false := h.block4.clause131

theorem step132 (p : Nat → Bool) (h : Constraints p) : p 38 = false ∨ p 39 = false ∨ p 42 = false ∨ p 43 = false := h.block4.clause132

theorem step133 (p : Nat → Bool) (h : Constraints p) : p 38 = false ∨ p 39 = false ∨ p 42 = false ∨ p 105 = false := h.block4.clause133

theorem step134 (p : Nat → Bool) (h : Constraints p) : p 38 = false ∨ p 39 = false ∨ p 43 = false ∨ p 105 = false := h.block4.clause134

theorem step135 (p : Nat → Bool) (h : Constraints p) : p 38 = false ∨ p 42 = false ∨ p 43 = false ∨ p 105 = false := h.block4.clause135

theorem step136 (p : Nat → Bool) (h : Constraints p) : p 39 = false ∨ p 17 = false ∨ p 38 = false ∨ p 106 = false := h.block4.clause136

theorem step137 (p : Nat → Bool) (h : Constraints p) : p 39 = false ∨ p 161 = true ∨ p 38 = true ∨ p 44 = true ∨ p 106 = true := h.block4.clause137

theorem step138 (p : Nat → Bool) (h : Constraints p) : p 39 = false ∨ p 161 = true ∨ p 17 = true ∨ p 44 = true ∨ p 106 = true := h.block4.clause138

theorem step139 (p : Nat → Bool) (h : Constraints p) : p 39 = false ∨ p 161 = true ∨ p 17 = true ∨ p 38 = true ∨ p 106 = true := h.block4.clause139

theorem step140 (p : Nat → Bool) (h : Constraints p) : p 40 = false ∨ p 18 = false ∨ p 41 = false ∨ p 45 = false := h.block4.clause140

theorem step141 (p : Nat → Bool) (h : Constraints p) : p 40 = false ∨ p 18 = false ∨ p 41 = false ∨ p 47 = false := h.block4.clause141

theorem step142 (p : Nat → Bool) (h : Constraints p) : p 40 = false ∨ p 18 = false ∨ p 42 = false ∨ p 47 = false := h.block4.clause142

theorem step143 (p : Nat → Bool) (h : Constraints p) : p 40 = false ∨ p 18 = false ∨ p 45 = false ∨ p 47 = false := h.block4.clause143

theorem step144 (p : Nat → Bool) (h : Constraints p) : p 40 = false ∨ p 41 = false ∨ p 42 = false ∨ p 47 = false := h.block4.clause144

theorem step145 (p : Nat → Bool) (h : Constraints p) : p 40 = false ∨ p 41 = false ∨ p 45 = false ∨ p 47 = false := h.block4.clause145

theorem step146 (p : Nat → Bool) (h : Constraints p) : p 41 = false ∨ p 40 = false ∨ p 48 = false ∨ p 107 = false := h.block4.clause146

theorem step147 (p : Nat → Bool) (h : Constraints p) : p 41 = false ∨ p 163 = true ∨ p 40 = true ∨ p 107 = true := h.block4.clause147

theorem step148 (p : Nat → Bool) (h : Constraints p) : p 41 = false ∨ p 163 = true ∨ p 40 = true ∨ p 48 = true := h.block4.clause148

theorem step149 (p : Nat → Bool) (h : Constraints p) : p 43 = false ∨ p 165 = true ∨ p 44 = true ∨ p 46 = true ∨ p 52 = true := h.block4.clause149

theorem step150 (p : Nat → Bool) (h : Constraints p) : p 43 = false ∨ p 165 = true ∨ p 38 = true ∨ p 44 = true ∨ p 52 = true := h.block4.clause150

theorem step151 (p : Nat → Bool) (h : Constraints p) : p 44 = false ∨ p 26 = false ∨ p 43 = false ∨ p 110 = false := h.block4.clause151

theorem step152 (p : Nat → Bool) (h : Constraints p) : p 44 = false ∨ p 39 = false ∨ p 43 = false ∨ p 53 = false := h.block4.clause152

theorem step153 (p : Nat → Bool) (h : Constraints p) : p 44 = false ∨ p 39 = false ∨ p 43 = false ∨ p 110 = false := h.block4.clause153

theorem step154 (p : Nat → Bool) (h : Constraints p) : p 44 = false ∨ p 39 = false ∨ p 53 = false ∨ p 110 = false := h.block4.clause154

theorem step155 (p : Nat → Bool) (h : Constraints p) : p 44 = false ∨ p 43 = false ∨ p 53 = false ∨ p 110 = false := h.block4.clause155

theorem step156 (p : Nat → Bool) (h : Constraints p) : p 45 = false ∨ p 167 = true ∨ p 46 = true := h.block4.clause156

theorem step157 (p : Nat → Bool) (h : Constraints p) : p 45 = false ∨ p 167 = true ∨ p 40 = true := h.block4.clause157

theorem step158 (p : Nat → Bool) (h : Constraints p) : p 46 = false ∨ p 168 = true ∨ p 42 = true ∨ p 45 = true := h.block4.clause158

theorem step159 (p : Nat → Bool) (h : Constraints p) : p 46 = false ∨ p 168 = true ∨ p 42 = true ∨ p 43 = true := h.block4.clause159

theorem step160 (p : Nat → Bool) (h : Constraints p) : p 47 = false ∨ p 32 = false ∨ p 40 = false ∨ p 48 = false := h.block4.clause160

theorem step161 (p : Nat → Bool) (h : Constraints p) : p 47 = false ∨ p 169 = true ∨ p 40 = true ∨ p 48 = true := h.block5.clause161

theorem step162 (p : Nat → Bool) (h : Constraints p) : p 47 = false ∨ p 169 = true ∨ p 32 = true ∨ p 40 = true := h.block5.clause162

theorem step163 (p : Nat → Bool) (h : Constraints p) : p 48 = false ∨ p 41 = false ∨ p 47 = false ∨ p 49 = false := h.block5.clause163

theorem step164 (p : Nat → Bool) (h : Constraints p) : p 48 = false ∨ p 170 = true ∨ p 41 = true ∨ p 47 = true := h.block5.clause164

theorem step165 (p : Nat → Bool) (h : Constraints p) : p 49 = false ∨ p 171 = true ∨ p 54 = true := h.block5.clause165

theorem step166 (p : Nat → Bool) (h : Constraints p) : p 49 = false ∨ p 171 = true ∨ p 48 = true := h.block5.clause166

theorem step167 (p : Nat → Bool) (h : Constraints p) : p 50 = false ∨ p 172 = true ∨ p 52 = true ∨ p 118 = true := h.block5.clause167

theorem step168 (p : Nat → Bool) (h : Constraints p) : p 50 = false ∨ p 172 = true ∨ p 51 = true ∨ p 118 = true := h.block5.clause168

theorem step169 (p : Nat → Bool) (h : Constraints p) : p 50 = false ∨ p 172 = true ∨ p 51 = true ∨ p 52 = true := h.block5.clause169

theorem step170 (p : Nat → Bool) (h : Constraints p) : p 173 = false ∨ p 50 = false ∨ p 53 = false := h.block5.clause170

theorem step171 (p : Nat → Bool) (h : Constraints p) : p 51 = false ∨ p 173 = true ∨ p 53 = true := h.block5.clause171

theorem step172 (p : Nat → Bool) (h : Constraints p) : p 52 = false ∨ p 34 = false ∨ p 43 = false ∨ p 50 = false := h.block5.clause172

theorem step173 (p : Nat → Bool) (h : Constraints p) : p 52 = false ∨ p 34 = false ∨ p 43 = false ∨ p 53 = false := h.block5.clause173

theorem step174 (p : Nat → Bool) (h : Constraints p) : p 52 = false ∨ p 34 = false ∨ p 50 = false ∨ p 53 = false := h.block5.clause174

theorem step175 (p : Nat → Bool) (h : Constraints p) : p 52 = false ∨ p 43 = false ∨ p 50 = false ∨ p 53 = false := h.block5.clause175

theorem step176 (p : Nat → Bool) (h : Constraints p) : p 52 = false ∨ p 174 = true ∨ p 34 = true ∨ p 43 = true ∨ p 53 = true := h.block5.clause176

theorem step177 (p : Nat → Bool) (h : Constraints p) : p 53 = false ∨ p 44 = false ∨ p 51 = false ∨ p 54 = false := h.block5.clause177

theorem step178 (p : Nat → Bool) (h : Constraints p) : p 53 = false ∨ p 44 = false ∨ p 52 = false ∨ p 54 = false := h.block5.clause178

theorem step179 (p : Nat → Bool) (h : Constraints p) : p 53 = false ∨ p 51 = false ∨ p 52 = false ∨ p 54 = false := h.block5.clause179

theorem step180 (p : Nat → Bool) (h : Constraints p) : p 54 = false ∨ p 49 = false ∨ p 53 = false ∨ p 122 = false := h.block5.clause180

theorem step181 (p : Nat → Bool) (h : Constraints p) : p 54 = false ∨ p 176 = true ∨ p 53 = true ∨ p 122 = true := h.block5.clause181

theorem step182 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 56 = false ∨ p 60 = false ∨ p 64 = false := h.block5.clause182

theorem step183 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 56 = false ∨ p 60 = false ∨ p 72 = false := h.block5.clause183

theorem step184 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 56 = false ∨ p 60 = false ∨ p 80 = false := h.block5.clause184

theorem step185 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 56 = false ∨ p 64 = false ∨ p 72 = false := h.block5.clause185

theorem step186 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 56 = false ∨ p 64 = false ∨ p 80 = false := h.block5.clause186

theorem step187 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 56 = false ∨ p 72 = false ∨ p 80 = false := h.block5.clause187

theorem step188 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 60 = false ∨ p 64 = false ∨ p 72 = false := h.block5.clause188

theorem step189 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 60 = false ∨ p 64 = false ∨ p 80 = false := h.block5.clause189

theorem step190 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 60 = false ∨ p 72 = false ∨ p 80 = false := h.block5.clause190

theorem step191 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 64 = false ∨ p 72 = false ∨ p 80 = false := h.block5.clause191

theorem step192 (p : Nat → Bool) (h : Constraints p) : p 177 = false ∨ p 56 = false ∨ p 60 = false := h.block5.clause192

theorem step193 (p : Nat → Bool) (h : Constraints p) : p 177 = false ∨ p 60 = false ∨ p 64 = false := h.block6.clause193

theorem step194 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 177 = true ∨ p 60 = true ∨ p 64 = true ∨ p 72 = true ∨ p 80 = true := h.block6.clause194

theorem step195 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 177 = true ∨ p 56 = true ∨ p 64 = true ∨ p 72 = true ∨ p 80 = true := h.block6.clause195

theorem step196 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 177 = true ∨ p 56 = true ∨ p 60 = true ∨ p 72 = true ∨ p 80 = true := h.block6.clause196

theorem step197 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 55 = false ∨ p 57 = false ∨ p 65 = false := h.block6.clause197

theorem step198 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 55 = false ∨ p 57 = false ∨ p 81 = false := h.block6.clause198

theorem step199 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 55 = false ∨ p 65 = false ∨ p 81 = false := h.block6.clause199

theorem step200 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 178 = true ∨ p 57 = true ∨ p 65 = true ∨ p 81 = true := h.block6.clause200

theorem step201 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 178 = true ∨ p 55 = true ∨ p 65 = true ∨ p 81 = true := h.block6.clause201

theorem step202 (p : Nat → Bool) (h : Constraints p) : p 56 = false ∨ p 178 = true ∨ p 55 = true ∨ p 57 = true ∨ p 81 = true := h.block6.clause202

theorem step203 (p : Nat → Bool) (h : Constraints p) : p 179 = false ∨ p 57 = true := h.block6.clause203

theorem step204 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 4 = false ∨ p 56 = false ∨ p 59 = false := h.block6.clause204

theorem step205 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 4 = false ∨ p 56 = false ∨ p 62 = false := h.block6.clause205

theorem step206 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 4 = false ∨ p 56 = false ∨ p 84 = false := h.block6.clause206

theorem step207 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 4 = false ∨ p 59 = false ∨ p 62 = false := h.block6.clause207

theorem step208 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 4 = false ∨ p 59 = false ∨ p 84 = false := h.block6.clause208

theorem step209 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 4 = false ∨ p 62 = false ∨ p 84 = false := h.block6.clause209

theorem step210 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 56 = false ∨ p 59 = false ∨ p 62 = false := h.block6.clause210

theorem step211 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 56 = false ∨ p 59 = false ∨ p 84 = false := h.block6.clause211

theorem step212 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 56 = false ∨ p 62 = false ∨ p 84 = false := h.block6.clause212

theorem step213 (p : Nat → Bool) (h : Constraints p) : p 57 = false ∨ p 59 = false ∨ p 62 = false ∨ p 84 = false := h.block6.clause213

theorem step214 (p : Nat → Bool) (h : Constraints p) : p 58 = false ∨ p 59 = false ∨ p 68 = false ∨ p 85 = false := h.block6.clause214

theorem step215 (p : Nat → Bool) (h : Constraints p) : p 58 = false ∨ p 180 = true ∨ p 59 = true ∨ p 85 = true := h.block6.clause215

theorem step216 (p : Nat → Bool) (h : Constraints p) : p 59 = false ∨ p 57 = false ∨ p 58 = false ∨ p 63 = false := h.block6.clause216

theorem step217 (p : Nat → Bool) (h : Constraints p) : p 59 = false ∨ p 57 = false ∨ p 58 = false ∨ p 75 = false := h.block6.clause217

theorem step218 (p : Nat → Bool) (h : Constraints p) : p 59 = false ∨ p 57 = false ∨ p 63 = false ∨ p 75 = false := h.block6.clause218

theorem step219 (p : Nat → Bool) (h : Constraints p) : p 59 = false ∨ p 57 = false ∨ p 75 = false ∨ p 86 = false := h.block6.clause219

theorem step220 (p : Nat → Bool) (h : Constraints p) : p 59 = false ∨ p 58 = false ∨ p 63 = false ∨ p 75 = false := h.block6.clause220

theorem step221 (p : Nat → Bool) (h : Constraints p) : p 59 = false ∨ p 63 = false ∨ p 75 = false ∨ p 86 = false := h.block6.clause221

theorem step222 (p : Nat → Bool) (h : Constraints p) : p 59 = false ∨ p 181 = true ∨ p 57 = true ∨ p 58 = true ∨ p 63 = true ∨ p 86 = true := h.block6.clause222

theorem step223 (p : Nat → Bool) (h : Constraints p) : p 60 = false ∨ p 5 = false ∨ p 55 = false ∨ p 87 = false := h.block6.clause223

theorem step224 (p : Nat → Bool) (h : Constraints p) : p 60 = false ∨ p 182 = true ∨ p 55 = true ∨ p 87 = true := h.block6.clause224

theorem step225 (p : Nat → Bool) (h : Constraints p) : p 60 = false ∨ p 182 = true ∨ p 5 = true ∨ p 87 = true := h.block7.clause225

theorem step226 (p : Nat → Bool) (h : Constraints p) : p 60 = false ∨ p 182 = true ∨ p 5 = true ∨ p 55 = true := h.block7.clause226

theorem step227 (p : Nat → Bool) (h : Constraints p) : p 61 = false ∨ p 7 = false ∨ p 63 = false ∨ p 89 = false := h.block7.clause227

theorem step228 (p : Nat → Bool) (h : Constraints p) : p 61 = false ∨ p 183 = true ∨ p 63 = true ∨ p 89 = true := h.block7.clause228

theorem step229 (p : Nat → Bool) (h : Constraints p) : p 61 = false ∨ p 183 = true ∨ p 7 = true ∨ p 89 = true := h.block7.clause229

theorem step230 (p : Nat → Bool) (h : Constraints p) : p 61 = false ∨ p 183 = true ∨ p 7 = true ∨ p 63 = true := h.block7.clause230

theorem step231 (p : Nat → Bool) (h : Constraints p) : p 62 = false ∨ p 57 = false ∨ p 63 = false ∨ p 70 = false := h.block7.clause231

theorem step232 (p : Nat → Bool) (h : Constraints p) : p 62 = false ∨ p 184 = true ∨ p 63 = true ∨ p 70 = true := h.block7.clause232

theorem step233 (p : Nat → Bool) (h : Constraints p) : p 62 = false ∨ p 184 = true ∨ p 57 = true ∨ p 70 = true := h.block7.clause233

theorem step234 (p : Nat → Bool) (h : Constraints p) : p 62 = false ∨ p 184 = true ∨ p 57 = true ∨ p 63 = true := h.block7.clause234

theorem step235 (p : Nat → Bool) (h : Constraints p) : p 63 = false ∨ p 59 = false ∨ p 61 = false ∨ p 62 = false := h.block7.clause235

theorem step236 (p : Nat → Bool) (h : Constraints p) : p 63 = false ∨ p 59 = false ∨ p 61 = false ∨ p 92 = false := h.block7.clause236

theorem step237 (p : Nat → Bool) (h : Constraints p) : p 63 = false ∨ p 59 = false ∨ p 62 = false ∨ p 92 = false := h.block7.clause237

theorem step238 (p : Nat → Bool) (h : Constraints p) : p 63 = false ∨ p 61 = false ∨ p 62 = false ∨ p 92 = false := h.block7.clause238

theorem step239 (p : Nat → Bool) (h : Constraints p) : p 185 = false ∨ p 61 = false ∨ p 62 = false := h.block7.clause239

theorem step240 (p : Nat → Bool) (h : Constraints p) : p 63 = false ∨ p 185 = true ∨ p 59 = true ∨ p 62 = true ∨ p 92 = true := h.block7.clause240

theorem step241 (p : Nat → Bool) (h : Constraints p) : p 63 = false ∨ p 185 = true ∨ p 59 = true ∨ p 61 = true ∨ p 92 = true := h.block7.clause241

theorem step242 (p : Nat → Bool) (h : Constraints p) : p 64 = false ∨ p 186 = true ∨ p 65 = true ∨ p 66 = true := h.block7.clause242

theorem step243 (p : Nat → Bool) (h : Constraints p) : p 64 = false ∨ p 186 = true ∨ p 55 = true ∨ p 66 = true := h.block7.clause243

theorem step244 (p : Nat → Bool) (h : Constraints p) : p 64 = false ∨ p 186 = true ∨ p 55 = true ∨ p 65 = true := h.block7.clause244

theorem step245 (p : Nat → Bool) (h : Constraints p) : p 65 = false ∨ p 56 = false ∨ p 64 = false ∨ p 67 = false := h.block7.clause245

theorem step246 (p : Nat → Bool) (h : Constraints p) : p 65 = false ∨ p 56 = false ∨ p 64 = false ∨ p 93 = false := h.block7.clause246

theorem step247 (p : Nat → Bool) (h : Constraints p) : p 65 = false ∨ p 56 = false ∨ p 67 = false ∨ p 93 = false := h.block7.clause247

theorem step248 (p : Nat → Bool) (h : Constraints p) : p 65 = false ∨ p 64 = false ∨ p 67 = false ∨ p 93 = false := h.block7.clause248

theorem step249 (p : Nat → Bool) (h : Constraints p) : p 187 = false ∨ p 64 = false ∨ p 67 = false := h.block7.clause249

theorem step250 (p : Nat → Bool) (h : Constraints p) : p 65 = false ∨ p 187 = true ∨ p 56 = true ∨ p 64 = true ∨ p 93 = true := h.block7.clause250

theorem step251 (p : Nat → Bool) (h : Constraints p) : p 66 = false ∨ p 64 = false ∨ p 67 = false ∨ p 68 = false := h.block7.clause251

theorem step252 (p : Nat → Bool) (h : Constraints p) : p 188 = false ∨ p 64 = false ∨ p 67 = false := h.block7.clause252

theorem step253 (p : Nat → Bool) (h : Constraints p) : p 66 = false ∨ p 188 = true ∨ p 64 = true ∨ p 67 = true := h.block7.clause253

theorem step254 (p : Nat → Bool) (h : Constraints p) : p 67 = false ∨ p 65 = false ∨ p 66 = false ∨ p 94 = false := h.block7.clause254

theorem step255 (p : Nat → Bool) (h : Constraints p) : p 67 = false ∨ p 189 = true ∨ p 66 = true ∨ p 94 = true := h.block7.clause255

theorem step256 (p : Nat → Bool) (h : Constraints p) : p 67 = false ∨ p 189 = true ∨ p 65 = true ∨ p 94 = true := h.block7.clause256

theorem step257 (p : Nat → Bool) (h : Constraints p) : p 67 = false ∨ p 189 = true ∨ p 65 = true ∨ p 66 = true := h.block8.clause257

theorem step258 (p : Nat → Bool) (h : Constraints p) : p 68 = false ∨ p 58 = false ∨ p 66 = false ∨ p 71 = false := h.block8.clause258

theorem step259 (p : Nat → Bool) (h : Constraints p) : p 68 = false ∨ p 190 = true ∨ p 66 = true ∨ p 71 = true := h.block8.clause259

theorem step260 (p : Nat → Bool) (h : Constraints p) : p 68 = false ∨ p 190 = true ∨ p 58 = true ∨ p 71 = true := h.block8.clause260

theorem step261 (p : Nat → Bool) (h : Constraints p) : p 68 = false ∨ p 190 = true ∨ p 58 = true ∨ p 66 = true := h.block8.clause261

theorem step262 (p : Nat → Bool) (h : Constraints p) : p 69 = false ∨ p 191 = true ∨ p 71 = true := h.block8.clause262

theorem step263 (p : Nat → Bool) (h : Constraints p) : p 69 = false ∨ p 191 = true ∨ p 70 = true := h.block8.clause263

theorem step264 (p : Nat → Bool) (h : Constraints p) : p 192 = false ∨ p 62 = false ∨ p 69 = false := h.block8.clause264

theorem step265 (p : Nat → Bool) (h : Constraints p) : p 70 = false ∨ p 192 = true ∨ p 69 = true := h.block8.clause265

theorem step266 (p : Nat → Bool) (h : Constraints p) : p 70 = false ∨ p 192 = true ∨ p 62 = true := h.block8.clause266

theorem step267 (p : Nat → Bool) (h : Constraints p) : p 193 = false ∨ p 68 = false ∨ p 69 = false := h.block8.clause267

theorem step268 (p : Nat → Bool) (h : Constraints p) : p 71 = false ∨ p 193 = true ∨ p 69 = true := h.block8.clause268

theorem step269 (p : Nat → Bool) (h : Constraints p) : p 71 = false ∨ p 193 = true ∨ p 68 = true := h.block8.clause269

theorem step270 (p : Nat → Bool) (h : Constraints p) : p 72 = false ∨ p 55 = false ∨ p 74 = false ∨ p 103 = false := h.block8.clause270

theorem step271 (p : Nat → Bool) (h : Constraints p) : p 72 = false ∨ p 194 = true ∨ p 55 = true ∨ p 103 = true := h.block8.clause271

theorem step272 (p : Nat → Bool) (h : Constraints p) : p 73 = false ∨ p 17 = false ∨ p 75 = false ∨ p 106 = false := h.block8.clause272

theorem step273 (p : Nat → Bool) (h : Constraints p) : p 73 = false ∨ p 195 = true ∨ p 75 = true ∨ p 106 = true := h.block8.clause273

theorem step274 (p : Nat → Bool) (h : Constraints p) : p 73 = false ∨ p 195 = true ∨ p 17 = true ∨ p 106 = true := h.block8.clause274

theorem step275 (p : Nat → Bool) (h : Constraints p) : p 73 = false ∨ p 195 = true ∨ p 17 = true ∨ p 75 = true := h.block8.clause275

theorem step276 (p : Nat → Bool) (h : Constraints p) : p 74 = false ∨ p 18 = false ∨ p 72 = false ∨ p 76 = false := h.block8.clause276

theorem step277 (p : Nat → Bool) (h : Constraints p) : p 74 = false ∨ p 18 = false ∨ p 76 = false ∨ p 77 = false := h.block8.clause277

theorem step278 (p : Nat → Bool) (h : Constraints p) : p 74 = false ∨ p 72 = false ∨ p 76 = false ∨ p 77 = false := h.block8.clause278

theorem step279 (p : Nat → Bool) (h : Constraints p) : p 196 = false ∨ p 76 = false ∨ p 77 = false := h.block8.clause279

theorem step280 (p : Nat → Bool) (h : Constraints p) : p 74 = false ∨ p 196 = true ∨ p 18 = true ∨ p 72 = true ∨ p 77 = true := h.block8.clause280

theorem step281 (p : Nat → Bool) (h : Constraints p) : p 75 = false ∨ p 19 = false ∨ p 59 = false ∨ p 79 = false := h.block8.clause281

theorem step282 (p : Nat → Bool) (h : Constraints p) : p 75 = false ∨ p 19 = false ∨ p 73 = false ∨ p 79 = false := h.block8.clause282

theorem step283 (p : Nat → Bool) (h : Constraints p) : p 75 = false ∨ p 59 = false ∨ p 73 = false ∨ p 79 = false := h.block8.clause283

theorem step284 (p : Nat → Bool) (h : Constraints p) : p 197 = false ∨ p 19 = false ∨ p 79 = false := h.block8.clause284

theorem step285 (p : Nat → Bool) (h : Constraints p) : p 75 = false ∨ p 197 = true ∨ p 59 = true ∨ p 73 = true ∨ p 79 = true := h.block8.clause285

theorem step286 (p : Nat → Bool) (h : Constraints p) : p 75 = false ∨ p 197 = true ∨ p 19 = true ∨ p 59 = true ∨ p 79 = true := h.block8.clause286

theorem step287 (p : Nat → Bool) (h : Constraints p) : p 75 = false ∨ p 197 = true ∨ p 19 = true ∨ p 59 = true ∨ p 73 = true := h.block8.clause287

theorem step288 (p : Nat → Bool) (h : Constraints p) : p 76 = false ∨ p 74 = true := h.block8.clause288

theorem step289 (p : Nat → Bool) (h : Constraints p) : p 76 = true := h.block9.clause289

theorem step290 (p : Nat → Bool) (h : Constraints p) : p 77 = false ∨ p 199 = true ∨ p 78 = true := h.block9.clause290

theorem step291 (p : Nat → Bool) (h : Constraints p) : p 200 = false ∨ p 78 = true := h.block9.clause291

theorem step292 (p : Nat → Bool) (h : Constraints p) : p 78 = false ∨ p 77 = true ∨ p 79 = true := h.block9.clause292

theorem step293 (p : Nat → Bool) (h : Constraints p) : p 200 = false ∨ p 77 = false ∨ p 79 = false := h.block9.clause293

theorem step294 (p : Nat → Bool) (h : Constraints p) : p 78 = false ∨ p 200 = true ∨ p 79 = true := h.block9.clause294

theorem step295 (p : Nat → Bool) (h : Constraints p) : p 78 = false ∨ p 200 = true ∨ p 77 = true := h.block9.clause295

theorem step296 (p : Nat → Bool) (h : Constraints p) : p 79 = false ∨ p 201 = true ∨ p 78 = true := h.block9.clause296

theorem step297 (p : Nat → Bool) (h : Constraints p) : p 79 = false ∨ p 201 = true ∨ p 75 = true := h.block9.clause297

theorem step298 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 20 = false ∨ p 55 = false ∨ p 81 = false := h.block9.clause298

theorem step299 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 20 = false ∨ p 55 = false ∨ p 87 = false := h.block9.clause299

theorem step300 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 55 = false ∨ p 81 = false ∨ p 87 = false := h.block9.clause300

theorem step301 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 55 = false ∨ p 82 = false ∨ p 83 = false := h.block9.clause301

theorem step302 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 55 = false ∨ p 83 = false ∨ p 87 = false := h.block9.clause302

theorem step303 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 55 = false ∨ p 83 = false ∨ p 103 = false := h.block9.clause303

theorem step304 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 55 = false ∨ p 87 = false ∨ p 103 = false := h.block9.clause304

theorem step305 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 81 = false ∨ p 83 = false ∨ p 87 = false := h.block9.clause305

theorem step306 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 81 = false ∨ p 87 = false ∨ p 103 = false := h.block9.clause306

theorem step307 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 83 = false ∨ p 87 = false ∨ p 103 = false := h.block9.clause307

theorem step308 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 202 = true ∨ p 55 = true ∨ p 81 = true ∨ p 82 = true ∨ p 83 = true ∨ p 87 = true ∨ p 103 = true := h.block9.clause308

theorem step309 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 56 = false ∨ p 80 = false := h.block9.clause309

theorem step310 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 56 = false ∨ p 84 = false := h.block9.clause310

theorem step311 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 56 = false ∨ p 93 = false := h.block9.clause311

theorem step312 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 56 = false ∨ p 104 = false := h.block9.clause312

theorem step313 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 80 = false ∨ p 84 = false := h.block9.clause313

theorem step314 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 80 = false ∨ p 93 = false := h.block9.clause314

theorem step315 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 80 = false ∨ p 104 = false := h.block9.clause315

theorem step316 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 84 = false ∨ p 93 = false := h.block9.clause316

theorem step317 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 84 = false ∨ p 104 = false := h.block9.clause317

theorem step318 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 21 = false ∨ p 93 = false ∨ p 104 = false := h.block9.clause318

theorem step319 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 56 = false ∨ p 80 = false ∨ p 84 = false := h.block9.clause319

theorem step320 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 56 = false ∨ p 80 = false ∨ p 93 = false := h.block9.clause320

theorem step321 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 56 = false ∨ p 80 = false ∨ p 104 = false := h.block10.clause321

theorem step322 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 56 = false ∨ p 84 = false ∨ p 93 = false := h.block10.clause322

theorem step323 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 56 = false ∨ p 84 = false ∨ p 104 = false := h.block10.clause323

theorem step324 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 56 = false ∨ p 93 = false ∨ p 104 = false := h.block10.clause324

theorem step325 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 80 = false ∨ p 84 = false ∨ p 93 = false := h.block10.clause325

theorem step326 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 80 = false ∨ p 84 = false ∨ p 104 = false := h.block10.clause326

theorem step327 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 80 = false ∨ p 93 = false ∨ p 104 = false := h.block10.clause327

theorem step328 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 84 = false ∨ p 93 = false ∨ p 104 = false := h.block10.clause328

theorem step329 (p : Nat → Bool) (h : Constraints p) : p 82 = false ∨ p 80 = false ∨ p 85 = false ∨ p 88 = false := h.block10.clause329

theorem step330 (p : Nat → Bool) (h : Constraints p) : p 82 = false ∨ p 80 = false ∨ p 85 = false ∨ p 105 = false := h.block10.clause330

theorem step331 (p : Nat → Bool) (h : Constraints p) : p 82 = false ∨ p 80 = false ∨ p 88 = false ∨ p 105 = false := h.block10.clause331

theorem step332 (p : Nat → Bool) (h : Constraints p) : p 82 = false ∨ p 85 = false ∨ p 88 = false ∨ p 105 = false := h.block10.clause332

theorem step333 (p : Nat → Bool) (h : Constraints p) : p 82 = false ∨ p 204 = true ∨ p 80 = true ∨ p 85 = true ∨ p 105 = true := h.block10.clause333

theorem step334 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 80 = false ∨ p 84 = false ∨ p 85 = false := h.block10.clause334

theorem step335 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 80 = false ∨ p 84 = false ∨ p 90 = false := h.block10.clause335

theorem step336 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 80 = false ∨ p 84 = false ∨ p 95 = false := h.block10.clause336

theorem step337 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 80 = false ∨ p 85 = false ∨ p 90 = false := h.block10.clause337

theorem step338 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 80 = false ∨ p 85 = false ∨ p 95 = false := h.block10.clause338

theorem step339 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 80 = false ∨ p 90 = false ∨ p 95 = false := h.block10.clause339

theorem step340 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 84 = false ∨ p 85 = false ∨ p 90 = false := h.block10.clause340

theorem step341 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 84 = false ∨ p 85 = false ∨ p 95 = false := h.block10.clause341

theorem step342 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 84 = false ∨ p 90 = false ∨ p 95 = false := h.block10.clause342

theorem step343 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 85 = false ∨ p 90 = false ∨ p 95 = false := h.block10.clause343

theorem step344 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 205 = true ∨ p 80 = true ∨ p 84 = true ∨ p 85 = true ∨ p 95 = true := h.block10.clause344

theorem step345 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 57 = false ∨ p 83 = false ∨ p 86 = false := h.block10.clause345

theorem step346 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 81 = false ∨ p 83 = false ∨ p 86 = false := h.block10.clause346

theorem step347 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 81 = false ∨ p 83 = false ∨ p 96 = false := h.block10.clause347

theorem step348 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 83 = false ∨ p 96 = false ∨ p 107 = false := h.block10.clause348

theorem step349 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 206 = true ∨ p 81 = true ∨ p 83 = true ∨ p 86 = true ∨ p 96 = true ∨ p 107 = true := h.block10.clause349

theorem step350 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 206 = true ∨ p 57 = true ∨ p 81 = true ∨ p 86 = true ∨ p 96 = true ∨ p 107 = true := h.block10.clause350

theorem step351 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 206 = true ∨ p 57 = true ∨ p 81 = true ∨ p 83 = true ∨ p 86 = true ∨ p 107 = true := h.block10.clause351

theorem step352 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 206 = true ∨ p 57 = true ∨ p 81 = true ∨ p 83 = true ∨ p 86 = true ∨ p 96 = true := h.block10.clause352

theorem step353 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 82 = false := h.block11.clause353

theorem step354 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 83 = false := h.block11.clause354

theorem step355 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 86 = false := h.block11.clause355

theorem step356 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 91 = false := h.block11.clause356

theorem step357 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 22 = false ∨ p 58 = false ∨ p 108 = false := h.block11.clause357

theorem step358 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 22 = false ∨ p 91 = false ∨ p 108 = false := h.block11.clause358

theorem step359 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 58 = false ∨ p 83 = false ∨ p 108 = false := h.block11.clause359

theorem step360 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 58 = false ∨ p 86 = false ∨ p 108 = false := h.block11.clause360

theorem step361 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 58 = false ∨ p 91 = false ∨ p 108 = false := h.block11.clause361

theorem step362 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 82 = false ∨ p 83 = false ∨ p 108 = false := h.block11.clause362

theorem step363 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 83 = false ∨ p 86 = false ∨ p 91 = false := h.block11.clause363

theorem step364 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 83 = false ∨ p 86 = false ∨ p 108 = false := h.block11.clause364

theorem step365 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 207 = true ∨ p 58 = true ∨ p 82 = true ∨ p 83 = true ∨ p 86 = true ∨ p 91 = true ∨ p 108 = true := h.block11.clause365

theorem step366 (p : Nat → Bool) (h : Constraints p) : p 85 = false ∨ p 207 = true ∨ p 22 = true ∨ p 58 = true ∨ p 82 = true ∨ p 83 = true ∨ p 86 = true ∨ p 91 = true := h.block11.clause366

theorem step367 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 23 = false ∨ p 59 = false ∨ p 92 = false := h.block11.clause367

theorem step368 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 23 = false ∨ p 59 = false ∨ p 97 = false := h.block11.clause368

theorem step369 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 23 = false ∨ p 84 = false ∨ p 85 = false := h.block11.clause369

theorem step370 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 23 = false ∨ p 84 = false ∨ p 92 = false := h.block11.clause370

theorem step371 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 23 = false ∨ p 84 = false ∨ p 97 = false := h.block11.clause371

theorem step372 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 23 = false ∨ p 85 = false ∨ p 97 = false := h.block11.clause372

theorem step373 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 23 = false ∨ p 92 = false ∨ p 97 = false := h.block11.clause373

theorem step374 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 59 = false ∨ p 84 = false ∨ p 85 = false := h.block11.clause374

theorem step375 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 59 = false ∨ p 84 = false ∨ p 97 = false := h.block11.clause375

theorem step376 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 59 = false ∨ p 85 = false ∨ p 97 = false := h.block11.clause376

theorem step377 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 59 = false ∨ p 92 = false ∨ p 97 = false := h.block11.clause377

theorem step378 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 84 = false ∨ p 85 = false ∨ p 92 = false := h.block11.clause378

theorem step379 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 84 = false ∨ p 85 = false ∨ p 97 = false := h.block11.clause379

theorem step380 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 84 = false ∨ p 92 = false ∨ p 97 = false := h.block11.clause380

theorem step381 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 85 = false ∨ p 92 = false ∨ p 97 = false := h.block11.clause381

theorem step382 (p : Nat → Bool) (h : Constraints p) : p 209 = false ∨ p 87 = true := h.block11.clause382

theorem step383 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 80 = false := h.block11.clause383

theorem step384 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 88 = false := h.block11.clause384

theorem step385 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 90 = false := h.block12.clause385

theorem step386 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 98 = false := h.block12.clause386

theorem step387 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 60 = false ∨ p 109 = false := h.block12.clause387

theorem step388 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 80 = false ∨ p 88 = false := h.block12.clause388

theorem step389 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 80 = false ∨ p 90 = false := h.block12.clause389

theorem step390 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 80 = false ∨ p 98 = false := h.block12.clause390

theorem step391 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 80 = false ∨ p 109 = false := h.block12.clause391

theorem step392 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 88 = false ∨ p 90 = false := h.block12.clause392

theorem step393 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 88 = false ∨ p 98 = false := h.block12.clause393

theorem step394 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 88 = false ∨ p 109 = false := h.block12.clause394

theorem step395 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 90 = false ∨ p 98 = false := h.block12.clause395

theorem step396 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 90 = false ∨ p 109 = false := h.block12.clause396

theorem step397 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 24 = false ∨ p 98 = false ∨ p 109 = false := h.block12.clause397

theorem step398 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 80 = false ∨ p 88 = false := h.block12.clause398

theorem step399 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 80 = false ∨ p 90 = false := h.block12.clause399

theorem step400 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 80 = false ∨ p 98 = false := h.block12.clause400

theorem step401 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 80 = false ∨ p 109 = false := h.block12.clause401

theorem step402 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 88 = false ∨ p 90 = false := h.block12.clause402

theorem step403 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 88 = false ∨ p 98 = false := h.block12.clause403

theorem step404 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 88 = false ∨ p 109 = false := h.block12.clause404

theorem step405 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 90 = false ∨ p 98 = false := h.block12.clause405

theorem step406 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 90 = false ∨ p 109 = false := h.block12.clause406

theorem step407 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 60 = false ∨ p 98 = false ∨ p 109 = false := h.block12.clause407

theorem step408 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 80 = false ∨ p 88 = false ∨ p 90 = false := h.block12.clause408

theorem step409 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 80 = false ∨ p 88 = false ∨ p 98 = false := h.block12.clause409

theorem step410 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 80 = false ∨ p 88 = false ∨ p 109 = false := h.block12.clause410

theorem step411 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 80 = false ∨ p 90 = false ∨ p 98 = false := h.block12.clause411

theorem step412 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 80 = false ∨ p 90 = false ∨ p 109 = false := h.block12.clause412

theorem step413 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 80 = false ∨ p 98 = false ∨ p 109 = false := h.block12.clause413

theorem step414 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 88 = false ∨ p 90 = false ∨ p 98 = false := h.block12.clause414

theorem step415 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 88 = false ∨ p 90 = false ∨ p 109 = false := h.block12.clause415

theorem step416 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 88 = false ∨ p 98 = false ∨ p 109 = false := h.block12.clause416

theorem step417 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 90 = false ∨ p 98 = false ∨ p 109 = false := h.block13.clause417

theorem step418 (p : Nat → Bool) (h : Constraints p) : p 88 = false ∨ p 87 = false ∨ p 89 = false ∨ p 100 = false := h.block13.clause418

theorem step419 (p : Nat → Bool) (h : Constraints p) : p 88 = false ∨ p 89 = false ∨ p 91 = false ∨ p 100 = false := h.block13.clause419

theorem step420 (p : Nat → Bool) (h : Constraints p) : p 88 = false ∨ p 210 = true ∨ p 87 = true ∨ p 89 = true ∨ p 91 = true ∨ p 100 = true := h.block13.clause420

theorem step421 (p : Nat → Bool) (h : Constraints p) : p 88 = false ∨ p 210 = true ∨ p 82 = true ∨ p 89 = true ∨ p 91 = true ∨ p 100 = true := h.block13.clause421

theorem step422 (p : Nat → Bool) (h : Constraints p) : p 88 = false ∨ p 210 = true ∨ p 82 = true ∨ p 87 = true ∨ p 91 = true ∨ p 100 = true := h.block13.clause422

theorem step423 (p : Nat → Bool) (h : Constraints p) : p 88 = false ∨ p 210 = true ∨ p 82 = true ∨ p 87 = true ∨ p 89 = true ∨ p 100 = true := h.block13.clause423

theorem step424 (p : Nat → Bool) (h : Constraints p) : p 88 = false ∨ p 210 = true ∨ p 82 = true ∨ p 87 = true ∨ p 89 = true ∨ p 91 = true := h.block13.clause424

theorem step425 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 61 = false ∨ p 88 = false := h.block13.clause425

theorem step426 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 61 = false ∨ p 92 = false := h.block13.clause426

theorem step427 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 61 = false ∨ p 101 = false := h.block13.clause427

theorem step428 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 61 = false ∨ p 110 = false := h.block13.clause428

theorem step429 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 88 = false ∨ p 92 = false := h.block13.clause429

theorem step430 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 88 = false ∨ p 101 = false := h.block13.clause430

theorem step431 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 92 = false ∨ p 101 = false := h.block13.clause431

theorem step432 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 92 = false ∨ p 110 = false := h.block13.clause432

theorem step433 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 26 = false ∨ p 101 = false ∨ p 110 = false := h.block13.clause433

theorem step434 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 61 = false ∨ p 88 = false ∨ p 92 = false := h.block13.clause434

theorem step435 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 61 = false ∨ p 88 = false ∨ p 101 = false := h.block13.clause435

theorem step436 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 61 = false ∨ p 88 = false ∨ p 110 = false := h.block13.clause436

theorem step437 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 61 = false ∨ p 92 = false ∨ p 101 = false := h.block13.clause437

theorem step438 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 61 = false ∨ p 92 = false ∨ p 110 = false := h.block13.clause438

theorem step439 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 61 = false ∨ p 101 = false ∨ p 110 = false := h.block13.clause439

theorem step440 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 88 = false ∨ p 92 = false ∨ p 101 = false := h.block13.clause440

theorem step441 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 88 = false ∨ p 92 = false ∨ p 110 = false := h.block13.clause441

theorem step442 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 88 = false ∨ p 101 = false ∨ p 110 = false := h.block13.clause442

theorem step443 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 92 = false ∨ p 101 = false ∨ p 110 = false := h.block13.clause443

theorem step444 (p : Nat → Bool) (h : Constraints p) : p 90 = false ∨ p 212 = true ∨ p 87 = true ∨ p 91 = true := h.block13.clause444

theorem step445 (p : Nat → Bool) (h : Constraints p) : p 90 = false ∨ p 212 = true ∨ p 83 = true ∨ p 91 = true := h.block13.clause445

theorem step446 (p : Nat → Bool) (h : Constraints p) : p 90 = false ∨ p 212 = true ∨ p 83 = true ∨ p 87 = true := h.block13.clause446

theorem step447 (p : Nat → Bool) (h : Constraints p) : p 91 = false ∨ p 85 = false ∨ p 88 = false ∨ p 90 = false := h.block13.clause447

theorem step448 (p : Nat → Bool) (h : Constraints p) : p 91 = false ∨ p 85 = false ∨ p 88 = false ∨ p 92 = false := h.block13.clause448

theorem step449 (p : Nat → Bool) (h : Constraints p) : p 91 = false ∨ p 85 = false ∨ p 90 = false ∨ p 92 = false := h.block14.clause449

theorem step450 (p : Nat → Bool) (h : Constraints p) : p 91 = false ∨ p 88 = false ∨ p 90 = false ∨ p 92 = false := h.block14.clause450

theorem step451 (p : Nat → Bool) (h : Constraints p) : p 91 = false ∨ p 213 = true ∨ p 85 = true ∨ p 90 = true ∨ p 92 = true := h.block14.clause451

theorem step452 (p : Nat → Bool) (h : Constraints p) : p 91 = false ∨ p 213 = true ∨ p 85 = true ∨ p 88 = true ∨ p 92 = true := h.block14.clause452

theorem step453 (p : Nat → Bool) (h : Constraints p) : p 92 = false ∨ p 63 = false ∨ p 86 = false ∨ p 112 = false := h.block14.clause453

theorem step454 (p : Nat → Bool) (h : Constraints p) : p 92 = false ∨ p 63 = false ∨ p 102 = false ∨ p 112 = false := h.block14.clause454

theorem step455 (p : Nat → Bool) (h : Constraints p) : p 92 = false ∨ p 86 = false ∨ p 89 = false ∨ p 91 = false := h.block14.clause455

theorem step456 (p : Nat → Bool) (h : Constraints p) : p 92 = false ∨ p 91 = false ∨ p 102 = false ∨ p 112 = false := h.block14.clause456

theorem step457 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 29 = false ∨ p 65 = false ∨ p 99 = false := h.block14.clause457

theorem step458 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 29 = false ∨ p 65 = false ∨ p 114 = false := h.block14.clause458

theorem step459 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 29 = false ∨ p 81 = false ∨ p 99 = false := h.block14.clause459

theorem step460 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 29 = false ∨ p 94 = false ∨ p 99 = false := h.block14.clause460

theorem step461 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 65 = false ∨ p 94 = false ∨ p 96 = false := h.block14.clause461

theorem step462 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 65 = false ∨ p 94 = false ∨ p 114 = false := h.block14.clause462

theorem step463 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 65 = false ∨ p 99 = false ∨ p 114 = false := h.block14.clause463

theorem step464 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 81 = false ∨ p 94 = false ∨ p 114 = false := h.block14.clause464

theorem step465 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 94 = false ∨ p 96 = false ∨ p 114 = false := h.block14.clause465

theorem step466 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 94 = false ∨ p 99 = false ∨ p 114 = false := h.block14.clause466

theorem step467 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 67 = false ∨ p 93 = false := h.block14.clause467

theorem step468 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 67 = false ∨ p 97 = false := h.block14.clause468

theorem step469 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 67 = false ∨ p 101 = false := h.block14.clause469

theorem step470 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 67 = false ∨ p 116 = false := h.block14.clause470

theorem step471 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 93 = false ∨ p 97 = false := h.block14.clause471

theorem step472 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 93 = false ∨ p 101 = false := h.block14.clause472

theorem step473 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 93 = false ∨ p 116 = false := h.block14.clause473

theorem step474 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 97 = false ∨ p 101 = false := h.block14.clause474

theorem step475 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 97 = false ∨ p 116 = false := h.block14.clause475

theorem step476 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 31 = false ∨ p 101 = false ∨ p 116 = false := h.block14.clause476

theorem step477 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 67 = false ∨ p 93 = false ∨ p 97 = false := h.block14.clause477

theorem step478 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 67 = false ∨ p 93 = false ∨ p 101 = false := h.block14.clause478

theorem step479 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 67 = false ∨ p 93 = false ∨ p 116 = false := h.block14.clause479

theorem step480 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 67 = false ∨ p 97 = false ∨ p 101 = false := h.block14.clause480

theorem step481 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 67 = false ∨ p 97 = false ∨ p 116 = false := h.block15.clause481

theorem step482 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 67 = false ∨ p 101 = false ∨ p 116 = false := h.block15.clause482

theorem step483 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 93 = false ∨ p 97 = false ∨ p 101 = false := h.block15.clause483

theorem step484 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 93 = false ∨ p 97 = false ∨ p 116 = false := h.block15.clause484

theorem step485 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 93 = false ∨ p 101 = false ∨ p 116 = false := h.block15.clause485

theorem step486 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 97 = false ∨ p 101 = false ∨ p 116 = false := h.block15.clause486

theorem step487 (p : Nat → Bool) (h : Constraints p) : p 95 = false ∨ p 217 = true ∨ p 83 = true ∨ p 96 = true := h.block15.clause487

theorem step488 (p : Nat → Bool) (h : Constraints p) : p 95 = false ∨ p 217 = true ∨ p 32 = true ∨ p 96 = true := h.block15.clause488

theorem step489 (p : Nat → Bool) (h : Constraints p) : p 95 = false ∨ p 217 = true ∨ p 32 = true ∨ p 83 = true := h.block15.clause489

theorem step490 (p : Nat → Bool) (h : Constraints p) : p 96 = false ∨ p 84 = false ∨ p 93 = false ∨ p 95 = false := h.block15.clause490

theorem step491 (p : Nat → Bool) (h : Constraints p) : p 96 = false ∨ p 84 = false ∨ p 93 = false ∨ p 97 = false := h.block15.clause491

theorem step492 (p : Nat → Bool) (h : Constraints p) : p 96 = false ∨ p 84 = false ∨ p 95 = false ∨ p 97 = false := h.block15.clause492

theorem step493 (p : Nat → Bool) (h : Constraints p) : p 96 = false ∨ p 93 = false ∨ p 95 = false ∨ p 97 = false := h.block15.clause493

theorem step494 (p : Nat → Bool) (h : Constraints p) : p 96 = false ∨ p 218 = true ∨ p 84 = true ∨ p 93 = true ∨ p 95 = true := h.block15.clause494

theorem step495 (p : Nat → Bool) (h : Constraints p) : p 97 = false ∨ p 219 = true ∨ p 94 = true ∨ p 96 = true ∨ p 102 = true := h.block15.clause495

theorem step496 (p : Nat → Bool) (h : Constraints p) : p 97 = false ∨ p 219 = true ∨ p 86 = true ∨ p 96 = true ∨ p 102 = true := h.block15.clause496

theorem step497 (p : Nat → Bool) (h : Constraints p) : p 97 = false ∨ p 219 = true ∨ p 86 = true ∨ p 94 = true ∨ p 102 = true := h.block15.clause497

theorem step498 (p : Nat → Bool) (h : Constraints p) : p 97 = false ∨ p 219 = true ∨ p 86 = true ∨ p 94 = true ∨ p 96 = true := h.block15.clause498

theorem step499 (p : Nat → Bool) (h : Constraints p) : p 98 = false ∨ p 87 = false ∨ p 99 = false ∨ p 118 = false := h.block15.clause499

theorem step500 (p : Nat → Bool) (h : Constraints p) : p 98 = false ∨ p 87 = false ∨ p 100 = false ∨ p 118 = false := h.block15.clause500

theorem step501 (p : Nat → Bool) (h : Constraints p) : p 98 = false ∨ p 220 = true ∨ p 99 = true ∨ p 100 = true ∨ p 118 = true := h.block15.clause501

theorem step502 (p : Nat → Bool) (h : Constraints p) : p 98 = false ∨ p 220 = true ∨ p 87 = true ∨ p 100 = true ∨ p 118 = true := h.block15.clause502

theorem step503 (p : Nat → Bool) (h : Constraints p) : p 98 = false ∨ p 220 = true ∨ p 87 = true ∨ p 99 = true ∨ p 118 = true := h.block15.clause503

theorem step504 (p : Nat → Bool) (h : Constraints p) : p 98 = false ∨ p 220 = true ∨ p 87 = true ∨ p 99 = true ∨ p 100 = true := h.block15.clause504

theorem step505 (p : Nat → Bool) (h : Constraints p) : p 99 = false ∨ p 93 = false ∨ p 98 = false ∨ p 101 = false := h.block15.clause505

theorem step506 (p : Nat → Bool) (h : Constraints p) : p 99 = false ∨ p 221 = true ∨ p 93 = true ∨ p 101 = true := h.block15.clause506

theorem step507 (p : Nat → Bool) (h : Constraints p) : p 100 = false ∨ p 34 = false ∨ p 88 = false ∨ p 98 = false := h.block15.clause507

theorem step508 (p : Nat → Bool) (h : Constraints p) : p 100 = false ∨ p 34 = false ∨ p 88 = false ∨ p 101 = false := h.block15.clause508

theorem step509 (p : Nat → Bool) (h : Constraints p) : p 100 = false ∨ p 34 = false ∨ p 98 = false ∨ p 101 = false := h.block15.clause509

theorem step510 (p : Nat → Bool) (h : Constraints p) : p 100 = false ∨ p 88 = false ∨ p 98 = false ∨ p 101 = false := h.block15.clause510

theorem step511 (p : Nat → Bool) (h : Constraints p) : p 100 = false ∨ p 222 = true ∨ p 88 = true ∨ p 98 = true ∨ p 101 = true := h.block15.clause511

theorem step512 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 89 = false ∨ p 94 = false ∨ p 99 = false := h.block15.clause512

theorem step513 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 89 = false ∨ p 94 = false ∨ p 100 = false := h.block16.clause513

theorem step514 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 89 = false ∨ p 94 = false ∨ p 102 = false := h.block16.clause514

theorem step515 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 89 = false ∨ p 99 = false ∨ p 102 = false := h.block16.clause515

theorem step516 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 89 = false ∨ p 100 = false ∨ p 102 = false := h.block16.clause516

theorem step517 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 94 = false ∨ p 99 = false ∨ p 100 = false := h.block16.clause517

theorem step518 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 223 = true ∨ p 94 = true ∨ p 99 = true ∨ p 100 = true ∨ p 102 = true := h.block16.clause518

theorem step519 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 223 = true ∨ p 89 = true ∨ p 99 = true ∨ p 100 = true ∨ p 102 = true := h.block16.clause519

theorem step520 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 223 = true ∨ p 89 = true ∨ p 94 = true ∨ p 100 = true ∨ p 102 = true := h.block16.clause520

theorem step521 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 223 = true ∨ p 89 = true ∨ p 94 = true ∨ p 99 = true ∨ p 102 = true := h.block16.clause521

theorem step522 (p : Nat → Bool) (h : Constraints p) : p 101 = false ∨ p 223 = true ∨ p 89 = true ∨ p 94 = true ∨ p 99 = true ∨ p 100 = true := h.block16.clause522

theorem step523 (p : Nat → Bool) (h : Constraints p) : p 102 = false ∨ p 92 = false ∨ p 97 = false ∨ p 101 = false := h.block16.clause523

theorem step524 (p : Nat → Bool) (h : Constraints p) : p 102 = false ∨ p 92 = false ∨ p 97 = false ∨ p 122 = false := h.block16.clause524

theorem step525 (p : Nat → Bool) (h : Constraints p) : p 102 = false ∨ p 92 = false ∨ p 101 = false ∨ p 122 = false := h.block16.clause525

theorem step526 (p : Nat → Bool) (h : Constraints p) : p 102 = false ∨ p 97 = false ∨ p 101 = false ∨ p 122 = false := h.block16.clause526

theorem step527 (p : Nat → Bool) (h : Constraints p) : p 102 = false ∨ p 224 = true ∨ p 92 = true ∨ p 101 = true ∨ p 122 = true := h.block16.clause527

theorem step528 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 80 = false ∨ p 104 = false := h.block16.clause528

theorem step529 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 80 = false ∨ p 105 = false := h.block16.clause529

theorem step530 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 80 = false ∨ p 109 = false := h.block16.clause530

theorem step531 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 80 = false ∨ p 113 = false := h.block16.clause531

theorem step532 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 104 = false ∨ p 105 = false := h.block16.clause532

theorem step533 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 104 = false ∨ p 109 = false := h.block16.clause533

theorem step534 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 104 = false ∨ p 113 = false := h.block16.clause534

theorem step535 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 105 = false ∨ p 109 = false := h.block16.clause535

theorem step536 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 105 = false ∨ p 113 = false := h.block16.clause536

theorem step537 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 72 = false ∨ p 109 = false ∨ p 113 = false := h.block16.clause537

theorem step538 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 80 = false ∨ p 104 = false ∨ p 105 = false := h.block16.clause538

theorem step539 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 80 = false ∨ p 104 = false ∨ p 109 = false := h.block16.clause539

theorem step540 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 80 = false ∨ p 104 = false ∨ p 113 = false := h.block16.clause540

theorem step541 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 80 = false ∨ p 105 = false ∨ p 109 = false := h.block16.clause541

theorem step542 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 80 = false ∨ p 105 = false ∨ p 113 = false := h.block16.clause542

theorem step543 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 80 = false ∨ p 109 = false ∨ p 113 = false := h.block16.clause543

theorem step544 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 104 = false ∨ p 105 = false ∨ p 109 = false := h.block16.clause544

theorem step545 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 104 = false ∨ p 105 = false ∨ p 113 = false := h.block17.clause545

theorem step546 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 104 = false ∨ p 109 = false ∨ p 113 = false := h.block17.clause546

theorem step547 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 105 = false ∨ p 109 = false ∨ p 113 = false := h.block17.clause547

theorem step548 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 81 = false ∨ p 106 = false ∨ p 107 = false := h.block17.clause548

theorem step549 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 81 = false ∨ p 107 = false ∨ p 114 = false := h.block17.clause549

theorem step550 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 103 = false ∨ p 106 = false ∨ p 107 = false := h.block17.clause550

theorem step551 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 103 = false ∨ p 107 = false ∨ p 114 = false := h.block17.clause551

theorem step552 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 106 = false ∨ p 107 = false ∨ p 114 = false := h.block17.clause552

theorem step553 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 226 = true ∨ p 103 = true ∨ p 106 = true ∨ p 107 = true ∨ p 114 = true := h.block17.clause553

theorem step554 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 226 = true ∨ p 81 = true ∨ p 106 = true ∨ p 107 = true ∨ p 114 = true := h.block17.clause554

theorem step555 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 226 = true ∨ p 81 = true ∨ p 103 = true ∨ p 107 = true ∨ p 114 = true := h.block17.clause555

theorem step556 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 226 = true ∨ p 81 = true ∨ p 103 = true ∨ p 106 = true ∨ p 114 = true := h.block17.clause556

theorem step557 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 226 = true ∨ p 81 = true ∨ p 103 = true ∨ p 106 = true ∨ p 107 = true := h.block17.clause557

theorem step558 (p : Nat → Bool) (h : Constraints p) : p 105 = false ∨ p 82 = false ∨ p 106 = false ∨ p 108 = false := h.block17.clause558

theorem step559 (p : Nat → Bool) (h : Constraints p) : p 105 = false ∨ p 103 = false ∨ p 106 = false ∨ p 108 = false := h.block17.clause559

theorem step560 (p : Nat → Bool) (h : Constraints p) : p 105 = false ∨ p 103 = false ∨ p 106 = false ∨ p 115 = false := h.block17.clause560

theorem step561 (p : Nat → Bool) (h : Constraints p) : p 105 = false ∨ p 227 = true ∨ p 82 = true ∨ p 103 = true ∨ p 106 = true ∨ p 108 = true ∨ p 115 = true := h.block17.clause561

theorem step562 (p : Nat → Bool) (h : Constraints p) : p 105 = false ∨ p 227 = true ∨ p 38 = true ∨ p 82 = true ∨ p 103 = true ∨ p 106 = true ∨ p 108 = true := h.block17.clause562

theorem step563 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 73 = false ∨ p 104 = false := h.block17.clause563

theorem step564 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 73 = false ∨ p 105 = false := h.block17.clause564

theorem step565 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 73 = false ∨ p 110 = false := h.block17.clause565

theorem step566 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 73 = false ∨ p 116 = false := h.block17.clause566

theorem step567 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 104 = false ∨ p 105 = false := h.block17.clause567

theorem step568 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 104 = false ∨ p 110 = false := h.block17.clause568

theorem step569 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 104 = false ∨ p 116 = false := h.block17.clause569

theorem step570 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 105 = false ∨ p 110 = false := h.block17.clause570

theorem step571 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 105 = false ∨ p 116 = false := h.block17.clause571

theorem step572 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 39 = false ∨ p 110 = false ∨ p 116 = false := h.block17.clause572

theorem step573 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 73 = false ∨ p 104 = false ∨ p 105 = false := h.block17.clause573

theorem step574 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 73 = false ∨ p 104 = false ∨ p 110 = false := h.block17.clause574

theorem step575 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 73 = false ∨ p 104 = false ∨ p 116 = false := h.block17.clause575

theorem step576 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 73 = false ∨ p 105 = false ∨ p 110 = false := h.block17.clause576

theorem step577 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 73 = false ∨ p 105 = false ∨ p 116 = false := h.block18.clause577

theorem step578 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 73 = false ∨ p 110 = false ∨ p 116 = false := h.block18.clause578

theorem step579 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 104 = false ∨ p 105 = false ∨ p 110 = false := h.block18.clause579

theorem step580 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 104 = false ∨ p 105 = false ∨ p 116 = false := h.block18.clause580

theorem step581 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 104 = false ∨ p 110 = false ∨ p 116 = false := h.block18.clause581

theorem step582 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 105 = false ∨ p 110 = false ∨ p 116 = false := h.block18.clause582

theorem step583 (p : Nat → Bool) (h : Constraints p) : p 106 = false ∨ p 228 = true ∨ p 39 = true ∨ p 73 = true ∨ p 104 = true ∨ p 105 = true ∨ p 110 = true := h.block18.clause583

theorem step584 (p : Nat → Bool) (h : Constraints p) : p 107 = false ∨ p 41 = false ∨ p 84 = false ∨ p 104 = false := h.block18.clause584

theorem step585 (p : Nat → Bool) (h : Constraints p) : p 107 = false ∨ p 41 = false ∨ p 84 = false ∨ p 111 = false := h.block18.clause585

theorem step586 (p : Nat → Bool) (h : Constraints p) : p 107 = false ∨ p 41 = false ∨ p 104 = false ∨ p 111 = false := h.block18.clause586

theorem step587 (p : Nat → Bool) (h : Constraints p) : p 107 = false ∨ p 84 = false ∨ p 104 = false ∨ p 111 = false := h.block18.clause587

theorem step588 (p : Nat → Bool) (h : Constraints p) : p 108 = false ∨ p 42 = false ∨ p 85 = false ∨ p 105 = false := h.block18.clause588

theorem step589 (p : Nat → Bool) (h : Constraints p) : p 108 = false ∨ p 42 = false ∨ p 85 = false ∨ p 117 = false := h.block18.clause589

theorem step590 (p : Nat → Bool) (h : Constraints p) : p 108 = false ∨ p 42 = false ∨ p 105 = false ∨ p 117 = false := h.block18.clause590

theorem step591 (p : Nat → Bool) (h : Constraints p) : p 108 = false ∨ p 85 = false ∨ p 105 = false ∨ p 117 = false := h.block18.clause591

theorem step592 (p : Nat → Bool) (h : Constraints p) : p 109 = false ∨ p 87 = false ∨ p 103 = false ∨ p 118 = false := h.block18.clause592

theorem step593 (p : Nat → Bool) (h : Constraints p) : p 109 = false ∨ p 231 = true ∨ p 103 = true ∨ p 118 = true := h.block18.clause593

theorem step594 (p : Nat → Bool) (h : Constraints p) : p 109 = false ∨ p 231 = true ∨ p 87 = true ∨ p 118 = true := h.block18.clause594

theorem step595 (p : Nat → Bool) (h : Constraints p) : p 109 = false ∨ p 231 = true ∨ p 87 = true ∨ p 103 = true := h.block18.clause595

theorem step596 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 44 = false ∨ p 89 = false ∨ p 112 = false := h.block18.clause596

theorem step597 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 44 = false ∨ p 106 = false ∨ p 112 = false := h.block18.clause597

theorem step598 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 232 = true ∨ p 89 = true ∨ p 106 = true ∨ p 112 = true := h.block18.clause598

theorem step599 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 232 = true ∨ p 44 = true ∨ p 106 = true ∨ p 112 = true := h.block18.clause599

theorem step600 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 232 = true ∨ p 44 = true ∨ p 89 = true ∨ p 112 = true := h.block18.clause600

theorem step601 (p : Nat → Bool) (h : Constraints p) : p 110 = false ∨ p 232 = true ∨ p 44 = true ∨ p 89 = true ∨ p 106 = true := h.block18.clause601

theorem step602 (p : Nat → Bool) (h : Constraints p) : p 111 = false ∨ p 107 = false ∨ p 112 = false ∨ p 120 = false := h.block18.clause602

theorem step603 (p : Nat → Bool) (h : Constraints p) : p 111 = false ∨ p 233 = true ∨ p 112 = true ∨ p 120 = true := h.block18.clause603

theorem step604 (p : Nat → Bool) (h : Constraints p) : p 111 = false ∨ p 233 = true ∨ p 107 = true ∨ p 120 = true := h.block18.clause604

theorem step605 (p : Nat → Bool) (h : Constraints p) : p 111 = false ∨ p 233 = true ∨ p 107 = true ∨ p 112 = true := h.block18.clause605

theorem step606 (p : Nat → Bool) (h : Constraints p) : p 112 = false ∨ p 92 = false ∨ p 110 = false ∨ p 111 = false := h.block18.clause606

theorem step607 (p : Nat → Bool) (h : Constraints p) : p 112 = false ∨ p 92 = false ∨ p 110 = false ∨ p 122 = false := h.block18.clause607

theorem step608 (p : Nat → Bool) (h : Constraints p) : p 112 = false ∨ p 92 = false ∨ p 111 = false ∨ p 122 = false := h.block18.clause608

theorem step609 (p : Nat → Bool) (h : Constraints p) : p 112 = false ∨ p 110 = false ∨ p 111 = false ∨ p 122 = false := h.block19.clause609

theorem step610 (p : Nat → Bool) (h : Constraints p) : p 112 = false ∨ p 234 = true ∨ p 92 = true ∨ p 110 = true ∨ p 122 = true := h.block19.clause610

theorem step611 (p : Nat → Bool) (h : Constraints p) : p 113 = false ∨ p 114 = false ∨ p 115 = false ∨ p 118 = false := h.block19.clause611

theorem step612 (p : Nat → Bool) (h : Constraints p) : p 113 = false ∨ p 235 = true ∨ p 114 = true ∨ p 115 = true ∨ p 118 = true := h.block19.clause612

theorem step613 (p : Nat → Bool) (h : Constraints p) : p 113 = false ∨ p 235 = true ∨ p 103 = true ∨ p 115 = true ∨ p 118 = true := h.block19.clause613

theorem step614 (p : Nat → Bool) (h : Constraints p) : p 113 = false ∨ p 235 = true ∨ p 103 = true ∨ p 114 = true ∨ p 118 = true := h.block19.clause614

theorem step615 (p : Nat → Bool) (h : Constraints p) : p 113 = false ∨ p 235 = true ∨ p 103 = true ∨ p 114 = true ∨ p 115 = true := h.block19.clause615

theorem step616 (p : Nat → Bool) (h : Constraints p) : p 114 = false ∨ p 93 = false ∨ p 104 = false ∨ p 113 = false := h.block19.clause616

theorem step617 (p : Nat → Bool) (h : Constraints p) : p 114 = false ∨ p 93 = false ∨ p 104 = false ∨ p 116 = false := h.block19.clause617

theorem step618 (p : Nat → Bool) (h : Constraints p) : p 114 = false ∨ p 93 = false ∨ p 113 = false ∨ p 116 = false := h.block19.clause618

theorem step619 (p : Nat → Bool) (h : Constraints p) : p 114 = false ∨ p 104 = false ∨ p 113 = false ∨ p 116 = false := h.block19.clause619

theorem step620 (p : Nat → Bool) (h : Constraints p) : p 114 = false ∨ p 236 = true ∨ p 93 = true ∨ p 104 = true ∨ p 116 = true := h.block19.clause620

theorem step621 (p : Nat → Bool) (h : Constraints p) : p 114 = false ∨ p 236 = true ∨ p 93 = true ∨ p 104 = true ∨ p 113 = true := h.block19.clause621

theorem step622 (p : Nat → Bool) (h : Constraints p) : p 115 = false ∨ p 105 = false ∨ p 113 = false ∨ p 116 = false := h.block19.clause622

theorem step623 (p : Nat → Bool) (h : Constraints p) : p 115 = false ∨ p 105 = false ∨ p 113 = false ∨ p 117 = false := h.block19.clause623

theorem step624 (p : Nat → Bool) (h : Constraints p) : p 115 = false ∨ p 105 = false ∨ p 116 = false ∨ p 117 = false := h.block19.clause624

theorem step625 (p : Nat → Bool) (h : Constraints p) : p 115 = false ∨ p 113 = false ∨ p 116 = false ∨ p 117 = false := h.block19.clause625

theorem step626 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 94 = false ∨ p 106 = false ∨ p 114 = false := h.block19.clause626

theorem step627 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 94 = false ∨ p 106 = false ∨ p 115 = false := h.block19.clause627

theorem step628 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 238 = true ∨ p 106 = true ∨ p 114 = true ∨ p 115 = true := h.block19.clause628

theorem step629 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 238 = true ∨ p 94 = true ∨ p 114 = true ∨ p 115 = true := h.block19.clause629

theorem step630 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 238 = true ∨ p 94 = true ∨ p 106 = true ∨ p 115 = true := h.block19.clause630

theorem step631 (p : Nat → Bool) (h : Constraints p) : p 116 = false ∨ p 238 = true ∨ p 94 = true ∨ p 106 = true ∨ p 114 = true := h.block19.clause631

theorem step632 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 108 = false ∨ p 115 = false ∨ p 121 = false := h.block19.clause632

theorem step633 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 239 = true ∨ p 115 = true ∨ p 121 = true := h.block19.clause633

theorem step634 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 239 = true ∨ p 108 = true ∨ p 121 = true := h.block19.clause634

theorem step635 (p : Nat → Bool) (h : Constraints p) : p 117 = false ∨ p 239 = true ∨ p 108 = true ∨ p 115 = true := h.block19.clause635

theorem step636 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 50 = false ∨ p 98 = false ∨ p 109 = false := h.block19.clause636

theorem step637 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 50 = false ∨ p 98 = false ∨ p 113 = false := h.block19.clause637

theorem step638 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 50 = false ∨ p 98 = false ∨ p 119 = false := h.block19.clause638

theorem step639 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 50 = false ∨ p 109 = false ∨ p 113 = false := h.block19.clause639

theorem step640 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 50 = false ∨ p 109 = false ∨ p 119 = false := h.block19.clause640

theorem step641 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 50 = false ∨ p 113 = false ∨ p 119 = false := h.block20.clause641

theorem step642 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 98 = false ∨ p 109 = false ∨ p 113 = false := h.block20.clause642

theorem step643 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 98 = false ∨ p 109 = false ∨ p 119 = false := h.block20.clause643

theorem step644 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 98 = false ∨ p 113 = false ∨ p 119 = false := h.block20.clause644

theorem step645 (p : Nat → Bool) (h : Constraints p) : p 118 = false ∨ p 109 = false ∨ p 113 = false ∨ p 119 = false := h.block20.clause645

theorem step646 (p : Nat → Bool) (h : Constraints p) : p 240 = false ∨ p 50 = false ∨ p 113 = false := h.block20.clause646

theorem step647 (p : Nat → Bool) (h : Constraints p) : p 119 = false ∨ p 118 = false ∨ p 120 = false ∨ p 121 = false := h.block20.clause647

theorem step648 (p : Nat → Bool) (h : Constraints p) : p 119 = false ∨ p 241 = true ∨ p 120 = true ∨ p 121 = true := h.block20.clause648

theorem step649 (p : Nat → Bool) (h : Constraints p) : p 119 = false ∨ p 241 = true ∨ p 118 = true ∨ p 121 = true := h.block20.clause649

theorem step650 (p : Nat → Bool) (h : Constraints p) : p 119 = false ∨ p 241 = true ∨ p 118 = true ∨ p 120 = true := h.block20.clause650

theorem step651 (p : Nat → Bool) (h : Constraints p) : p 120 = false ∨ p 111 = false ∨ p 119 = false ∨ p 122 = false := h.block20.clause651

theorem step652 (p : Nat → Bool) (h : Constraints p) : p 242 = false ∨ p 111 = false ∨ p 122 = false := h.block20.clause652

theorem step653 (p : Nat → Bool) (h : Constraints p) : p 120 = false ∨ p 242 = true ∨ p 119 = true ∨ p 122 = true := h.block20.clause653

theorem step654 (p : Nat → Bool) (h : Constraints p) : p 121 = false ∨ p 117 = false ∨ p 119 = false ∨ p 122 = false := h.block20.clause654

theorem step655 (p : Nat → Bool) (h : Constraints p) : p 121 = false ∨ p 243 = true ∨ p 119 = true ∨ p 122 = true := h.block20.clause655

theorem step656 (p : Nat → Bool) (h : Constraints p) : p 122 = false ∨ p 54 = false ∨ p 112 = false ∨ p 121 = false := h.block20.clause656

theorem step657 (p : Nat → Bool) (h : Constraints p) : p 122 = false ∨ p 54 = false ∨ p 120 = false ∨ p 121 = false := h.block20.clause657

theorem step658 (p : Nat → Bool) (h : Constraints p) : p 122 = false ∨ p 102 = false ∨ p 112 = false ∨ p 121 = false := h.block20.clause658

theorem step659 (p : Nat → Bool) (h : Constraints p) : p 122 = false ∨ p 102 = false ∨ p 120 = false ∨ p 121 = false := h.block20.clause659

theorem step660 (p : Nat → Bool) (h : Constraints p) : p 122 = false ∨ p 112 = false ∨ p 120 = false ∨ p 121 = false := h.block20.clause660

theorem step661 (p : Nat → Bool) (h : Constraints p) : p 124 = false := h.block20.clause661

theorem step662 (p : Nat → Bool) (h : Constraints p) : p 126 = false := h.block20.clause662

theorem step663 (p : Nat → Bool) (h : Constraints p) : p 128 = false := h.block20.clause663

theorem step664 (p : Nat → Bool) (h : Constraints p) : p 130 = false := h.block20.clause664

theorem step665 (p : Nat → Bool) (h : Constraints p) : p 132 = false := h.block20.clause665

theorem step666 (p : Nat → Bool) (h : Constraints p) : p 134 = false := h.block20.clause666

theorem step667 (p : Nat → Bool) (h : Constraints p) : p 135 = false := h.block20.clause667

theorem step668 (p : Nat → Bool) (h : Constraints p) : p 137 = false := h.block20.clause668

theorem step669 (p : Nat → Bool) (h : Constraints p) : p 140 = false := h.block20.clause669

theorem step670 (p : Nat → Bool) (h : Constraints p) : p 141 = false := h.block20.clause670

theorem step671 (p : Nat → Bool) (h : Constraints p) : p 143 = false := h.block20.clause671

theorem step672 (p : Nat → Bool) (h : Constraints p) : p 145 = false := h.block20.clause672

theorem step673 (p : Nat → Bool) (h : Constraints p) : p 146 = false := h.block21.clause673

theorem step674 (p : Nat → Bool) (h : Constraints p) : p 148 = false := h.block21.clause674

theorem step675 (p : Nat → Bool) (h : Constraints p) : p 149 = false := h.block21.clause675

theorem step676 (p : Nat → Bool) (h : Constraints p) : p 153 = false := h.block21.clause676

theorem step677 (p : Nat → Bool) (h : Constraints p) : p 155 = false := h.block21.clause677

theorem step678 (p : Nat → Bool) (h : Constraints p) : p 156 = false := h.block21.clause678

theorem step679 (p : Nat → Bool) (h : Constraints p) : p 157 = false := h.block21.clause679

theorem step680 (p : Nat → Bool) (h : Constraints p) : p 161 = false := h.block21.clause680

theorem step681 (p : Nat → Bool) (h : Constraints p) : p 163 = false := h.block21.clause681

theorem step682 (p : Nat → Bool) (h : Constraints p) : p 164 = false := h.block21.clause682

theorem step683 (p : Nat → Bool) (h : Constraints p) : p 165 = false := h.block21.clause683

theorem step684 (p : Nat → Bool) (h : Constraints p) : p 167 = false := h.block21.clause684

theorem step685 (p : Nat → Bool) (h : Constraints p) : p 169 = false := h.block21.clause685

theorem step686 (p : Nat → Bool) (h : Constraints p) : p 171 = false := h.block21.clause686

theorem step687 (p : Nat → Bool) (h : Constraints p) : p 172 = false := h.block21.clause687

theorem step688 (p : Nat → Bool) (h : Constraints p) : p 175 = false := h.block21.clause688

theorem step689 (p : Nat → Bool) (h : Constraints p) : p 178 = false := h.block21.clause689

theorem step690 (p : Nat → Bool) (h : Constraints p) : p 181 = false := h.block21.clause690

theorem step691 (p : Nat → Bool) (h : Constraints p) : p 182 = false := h.block21.clause691

theorem step692 (p : Nat → Bool) (h : Constraints p) : p 183 = false := h.block21.clause692

theorem step693 (p : Nat → Bool) (h : Constraints p) : p 184 = false := h.block21.clause693

theorem step694 (p : Nat → Bool) (h : Constraints p) : p 186 = false := h.block21.clause694

theorem step695 (p : Nat → Bool) (h : Constraints p) : p 189 = false := h.block21.clause695

theorem step696 (p : Nat → Bool) (h : Constraints p) : p 190 = false := h.block21.clause696

theorem step697 (p : Nat → Bool) (h : Constraints p) : p 191 = false := h.block21.clause697

theorem step698 (p : Nat → Bool) (h : Constraints p) : p 194 = false := h.block21.clause698

theorem step699 (p : Nat → Bool) (h : Constraints p) : p 195 = false := h.block21.clause699

theorem step700 (p : Nat → Bool) (h : Constraints p) : p 199 = false := h.block21.clause700

theorem step701 (p : Nat → Bool) (h : Constraints p) : p 201 = false := h.block21.clause701

theorem step702 (p : Nat → Bool) (h : Constraints p) : p 202 = false := h.block21.clause702

theorem step703 (p : Nat → Bool) (h : Constraints p) : p 206 = false := h.block21.clause703

theorem step704 (p : Nat → Bool) (h : Constraints p) : p 207 = false := h.block21.clause704

theorem step705 (p : Nat → Bool) (h : Constraints p) : p 210 = false := h.block22.clause705

theorem step706 (p : Nat → Bool) (h : Constraints p) : p 212 = false := h.block22.clause706

theorem step707 (p : Nat → Bool) (h : Constraints p) : p 214 = false := h.block22.clause707

theorem step708 (p : Nat → Bool) (h : Constraints p) : p 215 = false := h.block22.clause708

theorem step709 (p : Nat → Bool) (h : Constraints p) : p 217 = false := h.block22.clause709

theorem step710 (p : Nat → Bool) (h : Constraints p) : p 219 = false := h.block22.clause710

theorem step711 (p : Nat → Bool) (h : Constraints p) : p 220 = false := h.block22.clause711

theorem step712 (p : Nat → Bool) (h : Constraints p) : p 223 = false := h.block22.clause712

theorem step713 (p : Nat → Bool) (h : Constraints p) : p 226 = false := h.block22.clause713

theorem step714 (p : Nat → Bool) (h : Constraints p) : p 227 = false := h.block22.clause714

theorem step715 (p : Nat → Bool) (h : Constraints p) : p 231 = false := h.block22.clause715

theorem step716 (p : Nat → Bool) (h : Constraints p) : p 232 = false := h.block22.clause716

theorem step717 (p : Nat → Bool) (h : Constraints p) : p 233 = false := h.block22.clause717

theorem step718 (p : Nat → Bool) (h : Constraints p) : p 235 = false := h.block22.clause718

theorem step719 (p : Nat → Bool) (h : Constraints p) : p 238 = false := h.block22.clause719

theorem step720 (p : Nat → Bool) (h : Constraints p) : p 239 = false := h.block22.clause720

theorem step721 (p : Nat → Bool) (h : Constraints p) : p 241 = false := h.block22.clause721

theorem step722 (p : Nat → Bool) (h : Constraints p) : p 244 = false := h.block22.clause722

theorem step723 (p : Nat → Bool) (h : Constraints p) : p 125 = false ∨ p 245 = true := h.block22.clause723

theorem step724 (p : Nat → Bool) (h : Constraints p) : p 245 = false ∨ p 247 = true := h.block22.clause724

theorem step725 (p : Nat → Bool) (h : Constraints p) : p 123 = false ∨ p 247 = true := h.block22.clause725

theorem step726 (p : Nat → Bool) (h : Constraints p) : p 123 = false ∨ p 245 = false ∨ p 248 = true := h.block22.clause726

theorem step727 (p : Nat → Bool) (h : Constraints p) : p 127 = false ∨ p 249 = true := h.block22.clause727

theorem step728 (p : Nat → Bool) (h : Constraints p) : p 129 = false ∨ p 251 = true := h.block22.clause728

theorem step729 (p : Nat → Bool) (h : Constraints p) : p 251 = false ∨ p 253 = true := h.block22.clause729

theorem step730 (p : Nat → Bool) (h : Constraints p) : p 249 = false ∨ p 253 = true := h.block22.clause730

theorem step731 (p : Nat → Bool) (h : Constraints p) : p 253 = false ∨ p 255 = true := h.block22.clause731

theorem step732 (p : Nat → Bool) (h : Constraints p) : p 247 = false ∨ p 255 = true := h.block22.clause732

theorem step733 (p : Nat → Bool) (h : Constraints p) : p 248 = false ∨ p 256 = true := h.block22.clause733

theorem step734 (p : Nat → Bool) (h : Constraints p) : p 131 = false ∨ p 257 = true := h.block22.clause734

theorem step735 (p : Nat → Bool) (h : Constraints p) : p 133 = false ∨ p 259 = true := h.block22.clause735

theorem step736 (p : Nat → Bool) (h : Constraints p) : p 259 = false ∨ p 261 = true := h.block22.clause736

theorem step737 (p : Nat → Bool) (h : Constraints p) : p 257 = false ∨ p 261 = true := h.block23.clause737

theorem step738 (p : Nat → Bool) (h : Constraints p) : p 136 = false ∨ p 265 = true := h.block23.clause738

theorem step739 (p : Nat → Bool) (h : Constraints p) : p 265 = false ∨ p 267 = true := h.block23.clause739

theorem step740 (p : Nat → Bool) (h : Constraints p) : p 267 = false ∨ p 269 = true := h.block23.clause740

theorem step741 (p : Nat → Bool) (h : Constraints p) : p 261 = false ∨ p 269 = true := h.block23.clause741

theorem step742 (p : Nat → Bool) (h : Constraints p) : p 261 = false ∨ p 267 = false ∨ p 270 = true := h.block23.clause742

theorem step743 (p : Nat → Bool) (h : Constraints p) : p 269 = false ∨ p 271 = true := h.block23.clause743

theorem step744 (p : Nat → Bool) (h : Constraints p) : p 270 = false ∨ p 272 = true := h.block23.clause744

theorem step745 (p : Nat → Bool) (h : Constraints p) : p 255 = false ∨ p 271 = true := h.block23.clause745

theorem step746 (p : Nat → Bool) (h : Constraints p) : p 255 = false ∨ p 269 = false ∨ p 272 = true := h.block23.clause746

theorem step747 (p : Nat → Bool) (h : Constraints p) : p 256 = false ∨ p 272 = true := h.block23.clause747

theorem step748 (p : Nat → Bool) (h : Constraints p) : p 139 = false ∨ p 273 = true := h.block23.clause748

theorem step749 (p : Nat → Bool) (h : Constraints p) : p 273 = false ∨ p 275 = true := h.block23.clause749

theorem step750 (p : Nat → Bool) (h : Constraints p) : p 138 = false ∨ p 275 = true := h.block23.clause750

theorem step751 (p : Nat → Bool) (h : Constraints p) : p 142 = false ∨ p 277 = true := h.block23.clause751

theorem step752 (p : Nat → Bool) (h : Constraints p) : p 144 = false ∨ p 279 = true := h.block23.clause752

theorem step753 (p : Nat → Bool) (h : Constraints p) : p 279 = false ∨ p 281 = true := h.block23.clause753

theorem step754 (p : Nat → Bool) (h : Constraints p) : p 277 = false ∨ p 281 = true := h.block23.clause754

theorem step755 (p : Nat → Bool) (h : Constraints p) : p 281 = false ∨ p 283 = true := h.block23.clause755

theorem step756 (p : Nat → Bool) (h : Constraints p) : p 275 = false ∨ p 283 = true := h.block23.clause756

theorem step757 (p : Nat → Bool) (h : Constraints p) : p 147 = false ∨ p 287 = true := h.block23.clause757

theorem step758 (p : Nat → Bool) (h : Constraints p) : p 287 = false ∨ p 289 = true := h.block23.clause758

theorem step759 (p : Nat → Bool) (h : Constraints p) : p 150 = false ∨ p 291 = true := h.block23.clause759

theorem step760 (p : Nat → Bool) (h : Constraints p) : p 152 = false ∨ p 293 = true := h.block23.clause760

theorem step761 (p : Nat → Bool) (h : Constraints p) : p 151 = false ∨ p 293 = true := h.block23.clause761

theorem step762 (p : Nat → Bool) (h : Constraints p) : p 293 = false ∨ p 295 = true := h.block23.clause762

theorem step763 (p : Nat → Bool) (h : Constraints p) : p 291 = false ∨ p 295 = true := h.block23.clause763

theorem step764 (p : Nat → Bool) (h : Constraints p) : p 295 = false ∨ p 297 = true := h.block23.clause764

theorem step765 (p : Nat → Bool) (h : Constraints p) : p 289 = false ∨ p 297 = true := h.block23.clause765

theorem step766 (p : Nat → Bool) (h : Constraints p) : p 297 = false ∨ p 299 = true := h.block23.clause766

theorem step767 (p : Nat → Bool) (h : Constraints p) : p 283 = false ∨ p 299 = true := h.block23.clause767

theorem step768 (p : Nat → Bool) (h : Constraints p) : p 299 = false ∨ p 301 = true := h.block23.clause768

theorem step769 (p : Nat → Bool) (h : Constraints p) : p 271 = false ∨ p 301 = true := h.block24.clause769

theorem step770 (p : Nat → Bool) (h : Constraints p) : p 271 = false ∨ p 299 = false ∨ p 302 = true := h.block24.clause770

theorem step771 (p : Nat → Bool) (h : Constraints p) : p 272 = false ∨ p 302 = true := h.block24.clause771

theorem step772 (p : Nat → Bool) (h : Constraints p) : p 154 = false ∨ p 303 = true := h.block24.clause772

theorem step773 (p : Nat → Bool) (h : Constraints p) : p 303 = false ∨ p 305 = true := h.block24.clause773

theorem step774 (p : Nat → Bool) (h : Constraints p) : p 159 = false ∨ p 309 = true := h.block24.clause774

theorem step775 (p : Nat → Bool) (h : Constraints p) : p 158 = false ∨ p 309 = true := h.block24.clause775

theorem step776 (p : Nat → Bool) (h : Constraints p) : p 309 = false ∨ p 311 = true := h.block24.clause776

theorem step777 (p : Nat → Bool) (h : Constraints p) : p 311 = false ∨ p 313 = true := h.block24.clause777

theorem step778 (p : Nat → Bool) (h : Constraints p) : p 305 = false ∨ p 313 = true := h.block24.clause778

theorem step779 (p : Nat → Bool) (h : Constraints p) : p 160 = false ∨ p 315 = true := h.block24.clause779

theorem step780 (p : Nat → Bool) (h : Constraints p) : p 162 = false ∨ p 317 = true := h.block24.clause780

theorem step781 (p : Nat → Bool) (h : Constraints p) : p 317 = false ∨ p 319 = true := h.block24.clause781

theorem step782 (p : Nat → Bool) (h : Constraints p) : p 315 = false ∨ p 319 = true := h.block24.clause782

theorem step783 (p : Nat → Bool) (h : Constraints p) : p 166 = false ∨ p 323 = true := h.block24.clause783

theorem step784 (p : Nat → Bool) (h : Constraints p) : p 323 = false ∨ p 325 = true := h.block24.clause784

theorem step785 (p : Nat → Bool) (h : Constraints p) : p 325 = false ∨ p 327 = true := h.block24.clause785

theorem step786 (p : Nat → Bool) (h : Constraints p) : p 319 = false ∨ p 327 = true := h.block24.clause786

theorem step787 (p : Nat → Bool) (h : Constraints p) : p 327 = false ∨ p 329 = true := h.block24.clause787

theorem step788 (p : Nat → Bool) (h : Constraints p) : p 313 = false ∨ p 329 = true := h.block24.clause788

theorem step789 (p : Nat → Bool) (h : Constraints p) : p 170 = false ∨ p 331 = true := h.block24.clause789

theorem step790 (p : Nat → Bool) (h : Constraints p) : p 331 = false ∨ p 333 = true := h.block24.clause790

theorem step791 (p : Nat → Bool) (h : Constraints p) : p 168 = false ∨ p 333 = true := h.block24.clause791

theorem step792 (p : Nat → Bool) (h : Constraints p) : p 174 = false ∨ p 337 = true := h.block24.clause792

theorem step793 (p : Nat → Bool) (h : Constraints p) : p 173 = false ∨ p 337 = true := h.block24.clause793

theorem step794 (p : Nat → Bool) (h : Constraints p) : p 173 = false ∨ p 174 = false ∨ p 338 = true := h.block24.clause794

theorem step795 (p : Nat → Bool) (h : Constraints p) : p 337 = false ∨ p 339 = true := h.block24.clause795

theorem step796 (p : Nat → Bool) (h : Constraints p) : p 338 = false ∨ p 340 = true := h.block24.clause796

theorem step797 (p : Nat → Bool) (h : Constraints p) : p 339 = false ∨ p 341 = true := h.block24.clause797

theorem step798 (p : Nat → Bool) (h : Constraints p) : p 340 = false ∨ p 342 = true := h.block24.clause798

theorem step799 (p : Nat → Bool) (h : Constraints p) : p 333 = false ∨ p 341 = true := h.block24.clause799

theorem step800 (p : Nat → Bool) (h : Constraints p) : p 176 = false ∨ p 343 = true := h.block24.clause800

theorem step801 (p : Nat → Bool) (h : Constraints p) : p 177 = false ∨ p 345 = true := h.block25.clause801

theorem step802 (p : Nat → Bool) (h : Constraints p) : p 345 = false ∨ p 347 = true := h.block25.clause802

theorem step803 (p : Nat → Bool) (h : Constraints p) : p 343 = false ∨ p 347 = true := h.block25.clause803

theorem step804 (p : Nat → Bool) (h : Constraints p) : p 180 = false ∨ p 349 = true := h.block25.clause804

theorem step805 (p : Nat → Bool) (h : Constraints p) : p 349 = false ∨ p 353 = true := h.block25.clause805

theorem step806 (p : Nat → Bool) (h : Constraints p) : p 353 = false ∨ p 355 = true := h.block25.clause806

theorem step807 (p : Nat → Bool) (h : Constraints p) : p 347 = false ∨ p 355 = true := h.block25.clause807

theorem step808 (p : Nat → Bool) (h : Constraints p) : p 347 = false ∨ p 353 = false ∨ p 356 = true := h.block25.clause808

theorem step809 (p : Nat → Bool) (h : Constraints p) : p 355 = false ∨ p 357 = true := h.block25.clause809

theorem step810 (p : Nat → Bool) (h : Constraints p) : p 356 = false ∨ p 358 = true := h.block25.clause810

theorem step811 (p : Nat → Bool) (h : Constraints p) : p 341 = false ∨ p 357 = true := h.block25.clause811

theorem step812 (p : Nat → Bool) (h : Constraints p) : p 341 = false ∨ p 355 = false ∨ p 358 = true := h.block25.clause812

theorem step813 (p : Nat → Bool) (h : Constraints p) : p 342 = false ∨ p 358 = true := h.block25.clause813

theorem step814 (p : Nat → Bool) (h : Constraints p) : p 357 = false ∨ p 359 = true := h.block25.clause814

theorem step815 (p : Nat → Bool) (h : Constraints p) : p 358 = false ∨ p 360 = true := h.block25.clause815

theorem step816 (p : Nat → Bool) (h : Constraints p) : p 329 = false ∨ p 359 = true := h.block25.clause816

theorem step817 (p : Nat → Bool) (h : Constraints p) : p 359 = false ∨ p 361 = true := h.block25.clause817

theorem step818 (p : Nat → Bool) (h : Constraints p) : p 360 = false ∨ p 362 = true := h.block25.clause818

theorem step819 (p : Nat → Bool) (h : Constraints p) : p 301 = false ∨ p 361 = true := h.block25.clause819

theorem step820 (p : Nat → Bool) (h : Constraints p) : p 301 = false ∨ p 359 = false ∨ p 362 = true := h.block25.clause820

theorem step821 (p : Nat → Bool) (h : Constraints p) : p 302 = false ∨ p 362 = true := h.block25.clause821

theorem step822 (p : Nat → Bool) (h : Constraints p) : p 185 = false ∨ p 363 = true := h.block25.clause822

theorem step823 (p : Nat → Bool) (h : Constraints p) : p 363 = false ∨ p 365 = true := h.block25.clause823

theorem step824 (p : Nat → Bool) (h : Constraints p) : p 187 = false ∨ p 367 = true := h.block25.clause824

theorem step825 (p : Nat → Bool) (h : Constraints p) : p 188 = false ∨ p 369 = true := h.block25.clause825

theorem step826 (p : Nat → Bool) (h : Constraints p) : p 369 = false ∨ p 371 = true := h.block25.clause826

theorem step827 (p : Nat → Bool) (h : Constraints p) : p 367 = false ∨ p 371 = true := h.block25.clause827

theorem step828 (p : Nat → Bool) (h : Constraints p) : p 371 = false ∨ p 373 = true := h.block25.clause828

theorem step829 (p : Nat → Bool) (h : Constraints p) : p 365 = false ∨ p 373 = true := h.block25.clause829

theorem step830 (p : Nat → Bool) (h : Constraints p) : p 193 = false ∨ p 377 = true := h.block25.clause830

theorem step831 (p : Nat → Bool) (h : Constraints p) : p 192 = false ∨ p 377 = true := h.block25.clause831

theorem step832 (p : Nat → Bool) (h : Constraints p) : p 192 = false ∨ p 193 = false ∨ p 378 = true := h.block25.clause832

theorem step833 (p : Nat → Bool) (h : Constraints p) : p 377 = false ∨ p 379 = true := h.block26.clause833

theorem step834 (p : Nat → Bool) (h : Constraints p) : p 378 = false ∨ p 380 = true := h.block26.clause834

theorem step835 (p : Nat → Bool) (h : Constraints p) : p 197 = false ∨ p 383 = true := h.block26.clause835

theorem step836 (p : Nat → Bool) (h : Constraints p) : p 196 = false ∨ p 383 = true := h.block26.clause836

theorem step837 (p : Nat → Bool) (h : Constraints p) : p 383 = false ∨ p 385 = true := h.block26.clause837

theorem step838 (p : Nat → Bool) (h : Constraints p) : p 385 = false ∨ p 387 = true := h.block26.clause838

theorem step839 (p : Nat → Bool) (h : Constraints p) : p 379 = false ∨ p 387 = true := h.block26.clause839

theorem step840 (p : Nat → Bool) (h : Constraints p) : p 379 = false ∨ p 385 = false ∨ p 388 = true := h.block26.clause840

theorem step841 (p : Nat → Bool) (h : Constraints p) : p 380 = false ∨ p 388 = true := h.block26.clause841

theorem step842 (p : Nat → Bool) (h : Constraints p) : p 387 = false ∨ p 389 = true := h.block26.clause842

theorem step843 (p : Nat → Bool) (h : Constraints p) : p 388 = false ∨ p 390 = true := h.block26.clause843

theorem step844 (p : Nat → Bool) (h : Constraints p) : p 373 = false ∨ p 389 = true := h.block26.clause844

theorem step845 (p : Nat → Bool) (h : Constraints p) : p 373 = false ∨ p 387 = false ∨ p 390 = true := h.block26.clause845

theorem step846 (p : Nat → Bool) (h : Constraints p) : p 200 = false ∨ p 391 = true := h.block26.clause846

theorem step847 (p : Nat → Bool) (h : Constraints p) : p 391 = false ∨ p 393 = true := h.block26.clause847

theorem step848 (p : Nat → Bool) (h : Constraints p) : p 203 = false ∨ p 395 = true := h.block26.clause848

theorem step849 (p : Nat → Bool) (h : Constraints p) : p 205 = false ∨ p 397 = true := h.block26.clause849

theorem step850 (p : Nat → Bool) (h : Constraints p) : p 204 = false ∨ p 397 = true := h.block26.clause850

theorem step851 (p : Nat → Bool) (h : Constraints p) : p 397 = false ∨ p 399 = true := h.block26.clause851

theorem step852 (p : Nat → Bool) (h : Constraints p) : p 395 = false ∨ p 399 = true := h.block26.clause852

theorem step853 (p : Nat → Bool) (h : Constraints p) : p 399 = false ∨ p 401 = true := h.block26.clause853

theorem step854 (p : Nat → Bool) (h : Constraints p) : p 393 = false ∨ p 401 = true := h.block26.clause854

theorem step855 (p : Nat → Bool) (h : Constraints p) : p 393 = false ∨ p 399 = false ∨ p 402 = true := h.block26.clause855

theorem step856 (p : Nat → Bool) (h : Constraints p) : p 208 = false ∨ p 405 = true := h.block26.clause856

theorem step857 (p : Nat → Bool) (h : Constraints p) : p 405 = false ∨ p 407 = true := h.block26.clause857

theorem step858 (p : Nat → Bool) (h : Constraints p) : p 211 = false ∨ p 409 = true := h.block26.clause858

theorem step859 (p : Nat → Bool) (h : Constraints p) : p 213 = false ∨ p 411 = true := h.block26.clause859

theorem step860 (p : Nat → Bool) (h : Constraints p) : p 411 = false ∨ p 413 = true := h.block26.clause860

theorem step861 (p : Nat → Bool) (h : Constraints p) : p 409 = false ∨ p 413 = true := h.block26.clause861

theorem step862 (p : Nat → Bool) (h : Constraints p) : p 413 = false ∨ p 415 = true := h.block26.clause862

theorem step863 (p : Nat → Bool) (h : Constraints p) : p 407 = false ∨ p 415 = true := h.block26.clause863

theorem step864 (p : Nat → Bool) (h : Constraints p) : p 415 = false ∨ p 417 = true := h.block26.clause864

theorem step865 (p : Nat → Bool) (h : Constraints p) : p 401 = false ∨ p 417 = true := h.block27.clause865

theorem step866 (p : Nat → Bool) (h : Constraints p) : p 401 = false ∨ p 415 = false ∨ p 418 = true := h.block27.clause866

theorem step867 (p : Nat → Bool) (h : Constraints p) : p 402 = false ∨ p 418 = true := h.block27.clause867

theorem step868 (p : Nat → Bool) (h : Constraints p) : p 417 = false ∨ p 419 = true := h.block27.clause868

theorem step869 (p : Nat → Bool) (h : Constraints p) : p 418 = false ∨ p 420 = true := h.block27.clause869

theorem step870 (p : Nat → Bool) (h : Constraints p) : p 389 = false ∨ p 419 = true := h.block27.clause870

theorem step871 (p : Nat → Bool) (h : Constraints p) : p 389 = false ∨ p 417 = false ∨ p 420 = true := h.block27.clause871

theorem step872 (p : Nat → Bool) (h : Constraints p) : p 390 = false ∨ p 420 = true := h.block27.clause872

theorem step873 (p : Nat → Bool) (h : Constraints p) : p 216 = false ∨ p 421 = true := h.block27.clause873

theorem step874 (p : Nat → Bool) (h : Constraints p) : p 421 = false ∨ p 423 = true := h.block27.clause874

theorem step875 (p : Nat → Bool) (h : Constraints p) : p 218 = false ∨ p 425 = true := h.block27.clause875

theorem step876 (p : Nat → Bool) (h : Constraints p) : p 425 = false ∨ p 429 = true := h.block27.clause876

theorem step877 (p : Nat → Bool) (h : Constraints p) : p 429 = false ∨ p 431 = true := h.block27.clause877

theorem step878 (p : Nat → Bool) (h : Constraints p) : p 423 = false ∨ p 431 = true := h.block27.clause878

theorem step879 (p : Nat → Bool) (h : Constraints p) : p 222 = false ∨ p 433 = true := h.block27.clause879

theorem step880 (p : Nat → Bool) (h : Constraints p) : p 221 = false ∨ p 433 = true := h.block27.clause880

theorem step881 (p : Nat → Bool) (h : Constraints p) : p 224 = false ∨ p 435 = true := h.block27.clause881

theorem step882 (p : Nat → Bool) (h : Constraints p) : p 435 = false ∨ p 437 = true := h.block27.clause882

theorem step883 (p : Nat → Bool) (h : Constraints p) : p 433 = false ∨ p 437 = true := h.block27.clause883

theorem step884 (p : Nat → Bool) (h : Constraints p) : p 225 = false ∨ p 439 = true := h.block27.clause884

theorem step885 (p : Nat → Bool) (h : Constraints p) : p 228 = false ∨ p 441 = true := h.block27.clause885

theorem step886 (p : Nat → Bool) (h : Constraints p) : p 441 = false ∨ p 443 = true := h.block27.clause886

theorem step887 (p : Nat → Bool) (h : Constraints p) : p 439 = false ∨ p 443 = true := h.block27.clause887

theorem step888 (p : Nat → Bool) (h : Constraints p) : p 443 = false ∨ p 445 = true := h.block27.clause888

theorem step889 (p : Nat → Bool) (h : Constraints p) : p 437 = false ∨ p 445 = true := h.block27.clause889

theorem step890 (p : Nat → Bool) (h : Constraints p) : p 445 = false ∨ p 447 = true := h.block27.clause890

theorem step891 (p : Nat → Bool) (h : Constraints p) : p 431 = false ∨ p 447 = true := h.block27.clause891

theorem step892 (p : Nat → Bool) (h : Constraints p) : p 230 = false ∨ p 449 = true := h.block27.clause892

theorem step893 (p : Nat → Bool) (h : Constraints p) : p 229 = false ∨ p 449 = true := h.block27.clause893

theorem step894 (p : Nat → Bool) (h : Constraints p) : p 449 = false ∨ p 453 = true := h.block27.clause894

theorem step895 (p : Nat → Bool) (h : Constraints p) : p 234 = false ∨ p 455 = true := h.block27.clause895

theorem step896 (p : Nat → Bool) (h : Constraints p) : p 236 = false ∨ p 457 = true := h.block27.clause896

theorem step897 (p : Nat → Bool) (h : Constraints p) : p 457 = false ∨ p 459 = true := h.block28.clause897

theorem step898 (p : Nat → Bool) (h : Constraints p) : p 455 = false ∨ p 459 = true := h.block28.clause898

theorem step899 (p : Nat → Bool) (h : Constraints p) : p 459 = false ∨ p 461 = true := h.block28.clause899

theorem step900 (p : Nat → Bool) (h : Constraints p) : p 453 = false ∨ p 461 = true := h.block28.clause900

theorem step901 (p : Nat → Bool) (h : Constraints p) : p 237 = false ∨ p 463 = true := h.block28.clause901

theorem step902 (p : Nat → Bool) (h : Constraints p) : p 463 = false ∨ p 467 = true := h.block28.clause902

theorem step903 (p : Nat → Bool) (h : Constraints p) : p 242 = false ∨ p 469 = true := h.block28.clause903

theorem step904 (p : Nat → Bool) (h : Constraints p) : p 243 = false ∨ p 471 = true := h.block28.clause904

theorem step905 (p : Nat → Bool) (h : Constraints p) : p 471 = false ∨ p 473 = true := h.block28.clause905

theorem step906 (p : Nat → Bool) (h : Constraints p) : p 469 = false ∨ p 473 = true := h.block28.clause906

theorem step907 (p : Nat → Bool) (h : Constraints p) : p 469 = false ∨ p 471 = false ∨ p 474 = true := h.block28.clause907

theorem step908 (p : Nat → Bool) (h : Constraints p) : p 473 = false ∨ p 475 = true := h.block28.clause908

theorem step909 (p : Nat → Bool) (h : Constraints p) : p 474 = false ∨ p 476 = true := h.block28.clause909

theorem step910 (p : Nat → Bool) (h : Constraints p) : p 467 = false ∨ p 475 = true := h.block28.clause910

theorem step911 (p : Nat → Bool) (h : Constraints p) : p 475 = false ∨ p 477 = true := h.block28.clause911

theorem step912 (p : Nat → Bool) (h : Constraints p) : p 476 = false ∨ p 478 = true := h.block28.clause912

theorem step913 (p : Nat → Bool) (h : Constraints p) : p 461 = false ∨ p 477 = true := h.block28.clause913

theorem step914 (p : Nat → Bool) (h : Constraints p) : p 477 = false ∨ p 479 = true := h.block28.clause914

theorem step915 (p : Nat → Bool) (h : Constraints p) : p 478 = false ∨ p 480 = true := h.block28.clause915

theorem step916 (p : Nat → Bool) (h : Constraints p) : p 447 = false ∨ p 479 = true := h.block28.clause916

theorem step917 (p : Nat → Bool) (h : Constraints p) : p 447 = false ∨ p 477 = false ∨ p 480 = true := h.block28.clause917

theorem step918 (p : Nat → Bool) (h : Constraints p) : p 479 = false ∨ p 481 = true := h.block28.clause918

theorem step919 (p : Nat → Bool) (h : Constraints p) : p 480 = false ∨ p 482 = true := h.block28.clause919

theorem step920 (p : Nat → Bool) (h : Constraints p) : p 419 = false ∨ p 481 = true := h.block28.clause920

theorem step921 (p : Nat → Bool) (h : Constraints p) : p 419 = false ∨ p 479 = false ∨ p 482 = true := h.block28.clause921

theorem step922 (p : Nat → Bool) (h : Constraints p) : p 420 = false ∨ p 482 = true := h.block28.clause922

theorem step923 (p : Nat → Bool) (h : Constraints p) : p 482 = false ∨ p 484 = true := h.block28.clause923

theorem step924 (p : Nat → Bool) (h : Constraints p) : p 361 = false ∨ p 481 = false ∨ p 484 = true := h.block28.clause924

theorem step925 (p : Nat → Bool) (h : Constraints p) : p 362 = false ∨ p 484 = true := h.block28.clause925

theorem step926 (p : Nat → Bool) (h : Constraints p) : p 484 = false := h.block28.clause926

theorem step927 (p : Nat → Bool) (h : Constraints p) : p 123 = true ∨ p 124 = true ∨ p 125 = true ∨ p 126 = true ∨ p 127 = true ∨ p 128 = true ∨ p 129 = true ∨ p 130 = true ∨ p 131 = true ∨ p 132 = true ∨ p 133 = true ∨ p 134 = true ∨ p 135 = true ∨ p 136 = true ∨ p 137 = true ∨ p 138 = true ∨ p 139 = true ∨ p 140 = true ∨ p 141 = true ∨ p 142 = true ∨ p 143 = true ∨ p 144 = true ∨ p 145 = true ∨ p 146 = true ∨ p 147 = true ∨ p 148 = true ∨ p 149 = true ∨ p 150 = true ∨ p 151 = true ∨ p 152 = true ∨ p 153 = true ∨ p 154 = true ∨ p 155 = true ∨ p 156 = true ∨ p 157 = true ∨ p 158 = true ∨ p 159 = true ∨ p 160 = true ∨ p 161 = true ∨ p 162 = true ∨ p 163 = true ∨ p 164 = true ∨ p 165 = true ∨ p 166 = true ∨ p 167 = true ∨ p 168 = true ∨ p 169 = true ∨ p 170 = true ∨ p 171 = true ∨ p 172 = true ∨ p 173 = true ∨ p 174 = true ∨ p 175 = true ∨ p 176 = true ∨ p 177 = true ∨ p 178 = true ∨ p 179 = true ∨ p 180 = true ∨ p 181 = true ∨ p 182 = true ∨ p 183 = true ∨ p 184 = true ∨ p 185 = true ∨ p 186 = true ∨ p 187 = true ∨ p 188 = true ∨ p 189 = true ∨ p 190 = true ∨ p 191 = true ∨ p 192 = true ∨ p 193 = true ∨ p 194 = true ∨ p 195 = true ∨ p 196 = true ∨ p 197 = true ∨ p 199 = true ∨ p 200 = true ∨ p 201 = true ∨ p 202 = true ∨ p 203 = true ∨ p 204 = true ∨ p 205 = true ∨ p 206 = true ∨ p 207 = true ∨ p 208 = true ∨ p 209 = true ∨ p 210 = true ∨ p 211 = true ∨ p 212 = true ∨ p 213 = true ∨ p 214 = true ∨ p 215 = true ∨ p 216 = true ∨ p 217 = true ∨ p 218 = true ∨ p 219 = true ∨ p 220 = true ∨ p 221 = true ∨ p 222 = true ∨ p 223 = true ∨ p 224 = true ∨ p 225 = true ∨ p 226 = true ∨ p 227 = true ∨ p 228 = true ∨ p 229 = true ∨ p 230 = true ∨ p 231 = true ∨ p 232 = true ∨ p 233 = true ∨ p 234 = true ∨ p 235 = true ∨ p 236 = true ∨ p 237 = true ∨ p 238 = true ∨ p 239 = true ∨ p 240 = true ∨ p 241 = true ∨ p 242 = true ∨ p 243 = true ∨ p 244 = true := h.block28.clause927

theorem step928 (p : Nat → Bool) (h : Constraints p) : p 6 = true ∨ p 1461 = true := h.block28.clause928

theorem step929 (p : Nat → Bool) (h : Constraints p) : p 4 = true ∨ p 1461 = true := h.block29.clause929

theorem step930 (p : Nat → Bool) (h : Constraints p) : p 4 = true ∨ p 6 = true ∨ p 1462 = true := h.block29.clause930

theorem step931 (p : Nat → Bool) (h : Constraints p) : p 1461 = false ∨ p 1463 = true := h.block29.clause931

theorem step932 (p : Nat → Bool) (h : Constraints p) : p 1462 = false ∨ p 1464 = true := h.block29.clause932

theorem step933 (p : Nat → Bool) (h : Constraints p) : p 2 = true ∨ p 1463 = true := h.block29.clause933

theorem step934 (p : Nat → Bool) (h : Constraints p) : p 2 = true ∨ p 1461 = false ∨ p 1464 = true := h.block29.clause934

theorem step935 (p : Nat → Bool) (h : Constraints p) : p 2 = true ∨ p 1462 = false ∨ p 1465 = true := h.block29.clause935

theorem step936 (p : Nat → Bool) (h : Constraints p) : p 10 = true ∨ p 1466 = true := h.block29.clause936

theorem step937 (p : Nat → Bool) (h : Constraints p) : p 8 = true ∨ p 1466 = true := h.block29.clause937

theorem step938 (p : Nat → Bool) (h : Constraints p) : p 8 = true ∨ p 10 = true ∨ p 1467 = true := h.block29.clause938

theorem step939 (p : Nat → Bool) (h : Constraints p) : p 13 = true ∨ p 1468 = true := h.block29.clause939

theorem step940 (p : Nat → Bool) (h : Constraints p) : p 12 = true ∨ p 1468 = true := h.block29.clause940

theorem step941 (p : Nat → Bool) (h : Constraints p) : p 12 = true ∨ p 13 = true ∨ p 1469 = true := h.block29.clause941

theorem step942 (p : Nat → Bool) (h : Constraints p) : p 1468 = false ∨ p 1470 = true := h.block29.clause942

theorem step943 (p : Nat → Bool) (h : Constraints p) : p 1469 = false ∨ p 1471 = true := h.block29.clause943

theorem step944 (p : Nat → Bool) (h : Constraints p) : p 1466 = false ∨ p 1470 = true := h.block29.clause944

theorem step945 (p : Nat → Bool) (h : Constraints p) : p 1466 = false ∨ p 1468 = false ∨ p 1471 = true := h.block29.clause945

theorem step946 (p : Nat → Bool) (h : Constraints p) : p 1466 = false ∨ p 1469 = false ∨ p 1472 = true := h.block29.clause946

theorem step947 (p : Nat → Bool) (h : Constraints p) : p 1467 = false ∨ p 1471 = true := h.block29.clause947

theorem step948 (p : Nat → Bool) (h : Constraints p) : p 1467 = false ∨ p 1468 = false ∨ p 1472 = true := h.block29.clause948

theorem step949 (p : Nat → Bool) (h : Constraints p) : p 1467 = false ∨ p 1469 = false ∨ p 1473 = true := h.block29.clause949

theorem step950 (p : Nat → Bool) (h : Constraints p) : p 1470 = false ∨ p 1474 = true := h.block29.clause950

theorem step951 (p : Nat → Bool) (h : Constraints p) : p 1471 = false ∨ p 1475 = true := h.block29.clause951

theorem step952 (p : Nat → Bool) (h : Constraints p) : p 1472 = false ∨ p 1476 = true := h.block29.clause952

theorem step953 (p : Nat → Bool) (h : Constraints p) : p 1473 = false ∨ p 1477 = true := h.block29.clause953

theorem step954 (p : Nat → Bool) (h : Constraints p) : p 1463 = false ∨ p 1474 = true := h.block29.clause954

theorem step955 (p : Nat → Bool) (h : Constraints p) : p 1463 = false ∨ p 1470 = false ∨ p 1475 = true := h.block29.clause955

theorem step956 (p : Nat → Bool) (h : Constraints p) : p 1463 = false ∨ p 1471 = false ∨ p 1476 = true := h.block29.clause956

theorem step957 (p : Nat → Bool) (h : Constraints p) : p 1463 = false ∨ p 1472 = false ∨ p 1477 = true := h.block29.clause957

theorem step958 (p : Nat → Bool) (h : Constraints p) : p 1463 = false ∨ p 1473 = false ∨ p 1478 = true := h.block29.clause958

theorem step959 (p : Nat → Bool) (h : Constraints p) : p 1464 = false ∨ p 1475 = true := h.block29.clause959

theorem step960 (p : Nat → Bool) (h : Constraints p) : p 1464 = false ∨ p 1470 = false ∨ p 1476 = true := h.block29.clause960

theorem step961 (p : Nat → Bool) (h : Constraints p) : p 1464 = false ∨ p 1471 = false ∨ p 1477 = true := h.block30.clause961

theorem step962 (p : Nat → Bool) (h : Constraints p) : p 1464 = false ∨ p 1472 = false ∨ p 1478 = true := h.block30.clause962

theorem step963 (p : Nat → Bool) (h : Constraints p) : p 1464 = false ∨ p 1473 = false ∨ p 1479 = true := h.block30.clause963

theorem step964 (p : Nat → Bool) (h : Constraints p) : p 1465 = false ∨ p 1476 = true := h.block30.clause964

theorem step965 (p : Nat → Bool) (h : Constraints p) : p 1465 = false ∨ p 1470 = false ∨ p 1477 = true := h.block30.clause965

theorem step966 (p : Nat → Bool) (h : Constraints p) : p 1465 = false ∨ p 1471 = false ∨ p 1478 = true := h.block30.clause966

theorem step967 (p : Nat → Bool) (h : Constraints p) : p 18 = true ∨ p 1481 = true := h.block30.clause967

theorem step968 (p : Nat → Bool) (h : Constraints p) : p 15 = true ∨ p 1481 = true := h.block30.clause968

theorem step969 (p : Nat → Bool) (h : Constraints p) : p 15 = true ∨ p 18 = true ∨ p 1482 = true := h.block30.clause969

theorem step970 (p : Nat → Bool) (h : Constraints p) : p 21 = true ∨ p 1483 = true := h.block30.clause970

theorem step971 (p : Nat → Bool) (h : Constraints p) : p 19 = true ∨ p 1483 = true := h.block30.clause971

theorem step972 (p : Nat → Bool) (h : Constraints p) : p 19 = true ∨ p 21 = true ∨ p 1484 = true := h.block30.clause972

theorem step973 (p : Nat → Bool) (h : Constraints p) : p 1483 = false ∨ p 1485 = true := h.block30.clause973

theorem step974 (p : Nat → Bool) (h : Constraints p) : p 1484 = false ∨ p 1486 = true := h.block30.clause974

theorem step975 (p : Nat → Bool) (h : Constraints p) : p 1481 = false ∨ p 1485 = true := h.block30.clause975

theorem step976 (p : Nat → Bool) (h : Constraints p) : p 1481 = false ∨ p 1483 = false ∨ p 1486 = true := h.block30.clause976

theorem step977 (p : Nat → Bool) (h : Constraints p) : p 1481 = false ∨ p 1484 = false ∨ p 1487 = true := h.block30.clause977

theorem step978 (p : Nat → Bool) (h : Constraints p) : p 1482 = false ∨ p 1486 = true := h.block30.clause978

theorem step979 (p : Nat → Bool) (h : Constraints p) : p 1482 = false ∨ p 1483 = false ∨ p 1487 = true := h.block30.clause979

theorem step980 (p : Nat → Bool) (h : Constraints p) : p 1482 = false ∨ p 1484 = false ∨ p 1488 = true := h.block30.clause980

theorem step981 (p : Nat → Bool) (h : Constraints p) : p 24 = true ∨ p 1489 = true := h.block30.clause981

theorem step982 (p : Nat → Bool) (h : Constraints p) : p 23 = true ∨ p 1489 = true := h.block30.clause982

theorem step983 (p : Nat → Bool) (h : Constraints p) : p 23 = true ∨ p 24 = true ∨ p 1490 = true := h.block30.clause983

theorem step984 (p : Nat → Bool) (h : Constraints p) : p 27 = true ∨ p 1491 = true := h.block30.clause984

theorem step985 (p : Nat → Bool) (h : Constraints p) : p 26 = true ∨ p 1491 = true := h.block30.clause985

theorem step986 (p : Nat → Bool) (h : Constraints p) : p 26 = true ∨ p 27 = true ∨ p 1492 = true := h.block30.clause986

theorem step987 (p : Nat → Bool) (h : Constraints p) : p 1491 = false ∨ p 1493 = true := h.block30.clause987

theorem step988 (p : Nat → Bool) (h : Constraints p) : p 1492 = false ∨ p 1494 = true := h.block30.clause988

theorem step989 (p : Nat → Bool) (h : Constraints p) : p 1489 = false ∨ p 1493 = true := h.block30.clause989

theorem step990 (p : Nat → Bool) (h : Constraints p) : p 1489 = false ∨ p 1491 = false ∨ p 1494 = true := h.block30.clause990

theorem step991 (p : Nat → Bool) (h : Constraints p) : p 1489 = false ∨ p 1492 = false ∨ p 1495 = true := h.block30.clause991

theorem step992 (p : Nat → Bool) (h : Constraints p) : p 1490 = false ∨ p 1494 = true := h.block30.clause992

theorem step993 (p : Nat → Bool) (h : Constraints p) : p 1490 = false ∨ p 1491 = false ∨ p 1495 = true := h.block31.clause993

theorem step994 (p : Nat → Bool) (h : Constraints p) : p 1493 = false ∨ p 1497 = true := h.block31.clause994

theorem step995 (p : Nat → Bool) (h : Constraints p) : p 1494 = false ∨ p 1498 = true := h.block31.clause995

theorem step996 (p : Nat → Bool) (h : Constraints p) : p 1495 = false ∨ p 1499 = true := h.block31.clause996

theorem step997 (p : Nat → Bool) (h : Constraints p) : p 1485 = false ∨ p 1497 = true := h.block31.clause997

theorem step998 (p : Nat → Bool) (h : Constraints p) : p 1485 = false ∨ p 1493 = false ∨ p 1498 = true := h.block31.clause998

theorem step999 (p : Nat → Bool) (h : Constraints p) : p 1485 = false ∨ p 1494 = false ∨ p 1499 = true := h.block31.clause999

theorem step1000 (p : Nat → Bool) (h : Constraints p) : p 1485 = false ∨ p 1495 = false ∨ p 1500 = true := h.block31.clause1000

theorem step1001 (p : Nat → Bool) (h : Constraints p) : p 1486 = false ∨ p 1493 = false ∨ p 1499 = true := h.block31.clause1001

theorem step1002 (p : Nat → Bool) (h : Constraints p) : p 1486 = false ∨ p 1494 = false ∨ p 1500 = true := h.block31.clause1002

theorem step1003 (p : Nat → Bool) (h : Constraints p) : p 1486 = false ∨ p 1495 = false ∨ p 1501 = true := h.block31.clause1003

theorem step1004 (p : Nat → Bool) (h : Constraints p) : p 1487 = false ∨ p 1499 = true := h.block31.clause1004

theorem step1005 (p : Nat → Bool) (h : Constraints p) : p 1487 = false ∨ p 1493 = false ∨ p 1500 = true := h.block31.clause1005

theorem step1006 (p : Nat → Bool) (h : Constraints p) : p 1487 = false ∨ p 1494 = false ∨ p 1501 = true := h.block31.clause1006

theorem step1007 (p : Nat → Bool) (h : Constraints p) : p 1487 = false ∨ p 1495 = false ∨ p 1502 = true := h.block31.clause1007

theorem step1008 (p : Nat → Bool) (h : Constraints p) : p 1488 = false ∨ p 1493 = false ∨ p 1501 = true := h.block31.clause1008

theorem step1009 (p : Nat → Bool) (h : Constraints p) : p 1474 = false ∨ p 1499 = false ∨ p 1508 = true := h.block31.clause1009

theorem step1010 (p : Nat → Bool) (h : Constraints p) : p 1474 = false ∨ p 1500 = false ∨ p 1509 = true := h.block31.clause1010

theorem step1011 (p : Nat → Bool) (h : Constraints p) : p 1475 = false ∨ p 1497 = false ∨ p 1507 = true := h.block31.clause1011

theorem step1012 (p : Nat → Bool) (h : Constraints p) : p 1475 = false ∨ p 1498 = false ∨ p 1508 = true := h.block31.clause1012

theorem step1013 (p : Nat → Bool) (h : Constraints p) : p 1475 = false ∨ p 1499 = false ∨ p 1509 = true := h.block31.clause1013

theorem step1014 (p : Nat → Bool) (h : Constraints p) : p 1475 = false ∨ p 1500 = false ∨ p 1510 = true := h.block31.clause1014

theorem step1015 (p : Nat → Bool) (h : Constraints p) : p 1475 = false ∨ p 1501 = false ∨ p 1511 = true := h.block31.clause1015

theorem step1016 (p : Nat → Bool) (h : Constraints p) : p 1476 = false ∨ p 1497 = false ∨ p 1508 = true := h.block31.clause1016

theorem step1017 (p : Nat → Bool) (h : Constraints p) : p 1476 = false ∨ p 1498 = false ∨ p 1509 = true := h.block31.clause1017

theorem step1018 (p : Nat → Bool) (h : Constraints p) : p 1476 = false ∨ p 1499 = false ∨ p 1510 = true := h.block31.clause1018

theorem step1019 (p : Nat → Bool) (h : Constraints p) : p 1476 = false ∨ p 1500 = false ∨ p 1511 = true := h.block31.clause1019

theorem step1020 (p : Nat → Bool) (h : Constraints p) : p 1476 = false ∨ p 1501 = false ∨ p 1512 = true := h.block31.clause1020

theorem step1021 (p : Nat → Bool) (h : Constraints p) : p 1476 = false ∨ p 1502 = false ∨ p 1513 = true := h.block31.clause1021

theorem step1022 (p : Nat → Bool) (h : Constraints p) : p 1477 = false ∨ p 1508 = true := h.block31.clause1022

theorem step1023 (p : Nat → Bool) (h : Constraints p) : p 1477 = false ∨ p 1497 = false ∨ p 1509 = true := h.block31.clause1023

theorem step1024 (p : Nat → Bool) (h : Constraints p) : p 1477 = false ∨ p 1498 = false ∨ p 1510 = true := h.block31.clause1024

theorem step1025 (p : Nat → Bool) (h : Constraints p) : p 1477 = false ∨ p 1499 = false ∨ p 1511 = true := h.block32.clause1025

theorem step1026 (p : Nat → Bool) (h : Constraints p) : p 1477 = false ∨ p 1500 = false ∨ p 1512 = true := h.block32.clause1026

theorem step1027 (p : Nat → Bool) (h : Constraints p) : p 1477 = false ∨ p 1501 = false ∨ p 1513 = true := h.block32.clause1027

theorem step1028 (p : Nat → Bool) (h : Constraints p) : p 1478 = false ∨ p 1497 = false ∨ p 1510 = true := h.block32.clause1028

theorem step1029 (p : Nat → Bool) (h : Constraints p) : p 1478 = false ∨ p 1498 = false ∨ p 1511 = true := h.block32.clause1029

theorem step1030 (p : Nat → Bool) (h : Constraints p) : p 1478 = false ∨ p 1499 = false ∨ p 1512 = true := h.block32.clause1030

theorem step1031 (p : Nat → Bool) (h : Constraints p) : p 1478 = false ∨ p 1500 = false ∨ p 1513 = true := h.block32.clause1031

theorem step1032 (p : Nat → Bool) (h : Constraints p) : p 1479 = false ∨ p 1497 = false ∨ p 1511 = true := h.block32.clause1032

theorem step1033 (p : Nat → Bool) (h : Constraints p) : p 33 = true ∨ p 1520 = true := h.block32.clause1033

theorem step1034 (p : Nat → Bool) (h : Constraints p) : p 31 = true ∨ p 1520 = true := h.block32.clause1034

theorem step1035 (p : Nat → Bool) (h : Constraints p) : p 31 = true ∨ p 33 = true ∨ p 1521 = true := h.block32.clause1035

theorem step1036 (p : Nat → Bool) (h : Constraints p) : p 35 = true ∨ p 1522 = true := h.block32.clause1036

theorem step1037 (p : Nat → Bool) (h : Constraints p) : p 34 = true ∨ p 1522 = true := h.block32.clause1037

theorem step1038 (p : Nat → Bool) (h : Constraints p) : p 34 = true ∨ p 35 = true ∨ p 1523 = true := h.block32.clause1038

theorem step1039 (p : Nat → Bool) (h : Constraints p) : p 1522 = false ∨ p 1524 = true := h.block32.clause1039

theorem step1040 (p : Nat → Bool) (h : Constraints p) : p 1523 = false ∨ p 1525 = true := h.block32.clause1040

theorem step1041 (p : Nat → Bool) (h : Constraints p) : p 1520 = false ∨ p 1524 = true := h.block32.clause1041

theorem step1042 (p : Nat → Bool) (h : Constraints p) : p 1520 = false ∨ p 1522 = false ∨ p 1525 = true := h.block32.clause1042

theorem step1043 (p : Nat → Bool) (h : Constraints p) : p 1521 = false ∨ p 1525 = true := h.block32.clause1043

theorem step1044 (p : Nat → Bool) (h : Constraints p) : p 41 = true ∨ p 1528 = true := h.block32.clause1044

theorem step1045 (p : Nat → Bool) (h : Constraints p) : p 39 = true ∨ p 1528 = true := h.block32.clause1045

theorem step1046 (p : Nat → Bool) (h : Constraints p) : p 39 = true ∨ p 41 = true ∨ p 1529 = true := h.block32.clause1046

theorem step1047 (p : Nat → Bool) (h : Constraints p) : p 43 = true ∨ p 1530 = true := h.block32.clause1047

theorem step1048 (p : Nat → Bool) (h : Constraints p) : p 42 = true ∨ p 1530 = true := h.block32.clause1048

theorem step1049 (p : Nat → Bool) (h : Constraints p) : p 42 = true ∨ p 43 = true ∨ p 1531 = true := h.block32.clause1049

theorem step1050 (p : Nat → Bool) (h : Constraints p) : p 1530 = false ∨ p 1532 = true := h.block32.clause1050

theorem step1051 (p : Nat → Bool) (h : Constraints p) : p 1531 = false ∨ p 1533 = true := h.block32.clause1051

theorem step1052 (p : Nat → Bool) (h : Constraints p) : p 1528 = false ∨ p 1532 = true := h.block32.clause1052

theorem step1053 (p : Nat → Bool) (h : Constraints p) : p 1528 = false ∨ p 1530 = false ∨ p 1533 = true := h.block32.clause1053

theorem step1054 (p : Nat → Bool) (h : Constraints p) : p 1528 = false ∨ p 1531 = false ∨ p 1534 = true := h.block32.clause1054

theorem step1055 (p : Nat → Bool) (h : Constraints p) : p 1529 = false ∨ p 1533 = true := h.block32.clause1055

theorem step1056 (p : Nat → Bool) (h : Constraints p) : p 1529 = false ∨ p 1530 = false ∨ p 1534 = true := h.block32.clause1056

theorem step1057 (p : Nat → Bool) (h : Constraints p) : p 1529 = false ∨ p 1531 = false ∨ p 1535 = true := h.block33.clause1057

theorem step1058 (p : Nat → Bool) (h : Constraints p) : p 1532 = false ∨ p 1536 = true := h.block33.clause1058

theorem step1059 (p : Nat → Bool) (h : Constraints p) : p 1533 = false ∨ p 1537 = true := h.block33.clause1059

theorem step1060 (p : Nat → Bool) (h : Constraints p) : p 1534 = false ∨ p 1538 = true := h.block33.clause1060

theorem step1061 (p : Nat → Bool) (h : Constraints p) : p 1524 = false ∨ p 1536 = true := h.block33.clause1061

theorem step1062 (p : Nat → Bool) (h : Constraints p) : p 1524 = false ∨ p 1532 = false ∨ p 1537 = true := h.block33.clause1062

theorem step1063 (p : Nat → Bool) (h : Constraints p) : p 1524 = false ∨ p 1533 = false ∨ p 1538 = true := h.block33.clause1063

theorem step1064 (p : Nat → Bool) (h : Constraints p) : p 1524 = false ∨ p 1534 = false ∨ p 1539 = true := h.block33.clause1064

theorem step1065 (p : Nat → Bool) (h : Constraints p) : p 1524 = false ∨ p 1535 = false ∨ p 1540 = true := h.block33.clause1065

theorem step1066 (p : Nat → Bool) (h : Constraints p) : p 1525 = false ∨ p 1537 = true := h.block33.clause1066

theorem step1067 (p : Nat → Bool) (h : Constraints p) : p 1525 = false ∨ p 1532 = false ∨ p 1538 = true := h.block33.clause1067

theorem step1068 (p : Nat → Bool) (h : Constraints p) : p 1525 = false ∨ p 1533 = false ∨ p 1539 = true := h.block33.clause1068

theorem step1069 (p : Nat → Bool) (h : Constraints p) : p 1525 = false ∨ p 1534 = false ∨ p 1540 = true := h.block33.clause1069

theorem step1070 (p : Nat → Bool) (h : Constraints p) : p 47 = true ∨ p 1544 = true := h.block33.clause1070

theorem step1071 (p : Nat → Bool) (h : Constraints p) : p 45 = true ∨ p 1544 = true := h.block33.clause1071

theorem step1072 (p : Nat → Bool) (h : Constraints p) : p 45 = true ∨ p 47 = true ∨ p 1545 = true := h.block33.clause1072

theorem step1073 (p : Nat → Bool) (h : Constraints p) : p 50 = true ∨ p 1546 = true := h.block33.clause1073

theorem step1074 (p : Nat → Bool) (h : Constraints p) : p 49 = true ∨ p 1546 = true := h.block33.clause1074

theorem step1075 (p : Nat → Bool) (h : Constraints p) : p 49 = true ∨ p 50 = true ∨ p 1547 = true := h.block33.clause1075

theorem step1076 (p : Nat → Bool) (h : Constraints p) : p 1546 = false ∨ p 1548 = true := h.block33.clause1076

theorem step1077 (p : Nat → Bool) (h : Constraints p) : p 1547 = false ∨ p 1549 = true := h.block33.clause1077

theorem step1078 (p : Nat → Bool) (h : Constraints p) : p 1544 = false ∨ p 1548 = true := h.block33.clause1078

theorem step1079 (p : Nat → Bool) (h : Constraints p) : p 1544 = false ∨ p 1546 = false ∨ p 1549 = true := h.block33.clause1079

theorem step1080 (p : Nat → Bool) (h : Constraints p) : p 1544 = false ∨ p 1547 = false ∨ p 1550 = true := h.block33.clause1080

theorem step1081 (p : Nat → Bool) (h : Constraints p) : p 1545 = false ∨ p 1549 = true := h.block33.clause1081

theorem step1082 (p : Nat → Bool) (h : Constraints p) : p 1545 = false ∨ p 1546 = false ∨ p 1550 = true := h.block33.clause1082

theorem step1083 (p : Nat → Bool) (h : Constraints p) : p 1545 = false ∨ p 1547 = false ∨ p 1551 = true := h.block33.clause1083

theorem step1084 (p : Nat → Bool) (h : Constraints p) : p 56 = true ∨ p 1552 = true := h.block33.clause1084

theorem step1085 (p : Nat → Bool) (h : Constraints p) : p 53 = true ∨ p 1552 = true := h.block33.clause1085

theorem step1086 (p : Nat → Bool) (h : Constraints p) : p 53 = true ∨ p 56 = true ∨ p 1553 = true := h.block33.clause1086

theorem step1087 (p : Nat → Bool) (h : Constraints p) : p 60 = true ∨ p 1554 = true := h.block33.clause1087

theorem step1088 (p : Nat → Bool) (h : Constraints p) : p 59 = true ∨ p 1554 = true := h.block33.clause1088

theorem step1089 (p : Nat → Bool) (h : Constraints p) : p 59 = true ∨ p 60 = true ∨ p 1555 = true := h.block34.clause1089

theorem step1090 (p : Nat → Bool) (h : Constraints p) : p 1554 = false ∨ p 1556 = true := h.block34.clause1090

theorem step1091 (p : Nat → Bool) (h : Constraints p) : p 1555 = false ∨ p 1557 = true := h.block34.clause1091

theorem step1092 (p : Nat → Bool) (h : Constraints p) : p 1552 = false ∨ p 1556 = true := h.block34.clause1092

theorem step1093 (p : Nat → Bool) (h : Constraints p) : p 1552 = false ∨ p 1554 = false ∨ p 1557 = true := h.block34.clause1093

theorem step1094 (p : Nat → Bool) (h : Constraints p) : p 1552 = false ∨ p 1555 = false ∨ p 1558 = true := h.block34.clause1094

theorem step1095 (p : Nat → Bool) (h : Constraints p) : p 1553 = false ∨ p 1557 = true := h.block34.clause1095

theorem step1096 (p : Nat → Bool) (h : Constraints p) : p 1553 = false ∨ p 1554 = false ∨ p 1558 = true := h.block34.clause1096

theorem step1097 (p : Nat → Bool) (h : Constraints p) : p 1553 = false ∨ p 1555 = false ∨ p 1559 = true := h.block34.clause1097

theorem step1098 (p : Nat → Bool) (h : Constraints p) : p 1556 = false ∨ p 1560 = true := h.block34.clause1098

theorem step1099 (p : Nat → Bool) (h : Constraints p) : p 1557 = false ∨ p 1561 = true := h.block34.clause1099

theorem step1100 (p : Nat → Bool) (h : Constraints p) : p 1558 = false ∨ p 1562 = true := h.block34.clause1100

theorem step1101 (p : Nat → Bool) (h : Constraints p) : p 1559 = false ∨ p 1563 = true := h.block34.clause1101

theorem step1102 (p : Nat → Bool) (h : Constraints p) : p 1548 = false ∨ p 1560 = true := h.block34.clause1102

theorem step1103 (p : Nat → Bool) (h : Constraints p) : p 1548 = false ∨ p 1556 = false ∨ p 1561 = true := h.block34.clause1103

theorem step1104 (p : Nat → Bool) (h : Constraints p) : p 1548 = false ∨ p 1557 = false ∨ p 1562 = true := h.block34.clause1104

theorem step1105 (p : Nat → Bool) (h : Constraints p) : p 1548 = false ∨ p 1558 = false ∨ p 1563 = true := h.block34.clause1105

theorem step1106 (p : Nat → Bool) (h : Constraints p) : p 1548 = false ∨ p 1559 = false ∨ p 1564 = true := h.block34.clause1106

theorem step1107 (p : Nat → Bool) (h : Constraints p) : p 1549 = false ∨ p 1561 = true := h.block34.clause1107

theorem step1108 (p : Nat → Bool) (h : Constraints p) : p 1549 = false ∨ p 1556 = false ∨ p 1562 = true := h.block34.clause1108

theorem step1109 (p : Nat → Bool) (h : Constraints p) : p 1549 = false ∨ p 1557 = false ∨ p 1563 = true := h.block34.clause1109

theorem step1110 (p : Nat → Bool) (h : Constraints p) : p 1549 = false ∨ p 1558 = false ∨ p 1564 = true := h.block34.clause1110

theorem step1111 (p : Nat → Bool) (h : Constraints p) : p 1549 = false ∨ p 1559 = false ∨ p 1565 = true := h.block34.clause1111

theorem step1112 (p : Nat → Bool) (h : Constraints p) : p 1550 = false ∨ p 1562 = true := h.block34.clause1112

theorem step1113 (p : Nat → Bool) (h : Constraints p) : p 1550 = false ∨ p 1556 = false ∨ p 1563 = true := h.block34.clause1113

theorem step1114 (p : Nat → Bool) (h : Constraints p) : p 1550 = false ∨ p 1557 = false ∨ p 1564 = true := h.block34.clause1114

theorem step1115 (p : Nat → Bool) (h : Constraints p) : p 1550 = false ∨ p 1558 = false ∨ p 1565 = true := h.block34.clause1115

theorem step1116 (p : Nat → Bool) (h : Constraints p) : p 1550 = false ∨ p 1559 = false ∨ p 1566 = true := h.block34.clause1116

theorem step1117 (p : Nat → Bool) (h : Constraints p) : p 1551 = false ∨ p 1556 = false ∨ p 1564 = true := h.block34.clause1117

theorem step1118 (p : Nat → Bool) (h : Constraints p) : p 1563 = false ∨ p 1571 = true := h.block34.clause1118

theorem step1119 (p : Nat → Bool) (h : Constraints p) : p 1564 = false ∨ p 1572 = true := h.block34.clause1119

theorem step1120 (p : Nat → Bool) (h : Constraints p) : p 1566 = false ∨ p 1574 = true := h.block34.clause1120

theorem step1121 (p : Nat → Bool) (h : Constraints p) : p 1536 = false ∨ p 1561 = false ∨ p 1570 = true := h.block35.clause1121

theorem step1122 (p : Nat → Bool) (h : Constraints p) : p 1536 = false ∨ p 1562 = false ∨ p 1571 = true := h.block35.clause1122

theorem step1123 (p : Nat → Bool) (h : Constraints p) : p 1536 = false ∨ p 1563 = false ∨ p 1572 = true := h.block35.clause1123

theorem step1124 (p : Nat → Bool) (h : Constraints p) : p 1536 = false ∨ p 1564 = false ∨ p 1573 = true := h.block35.clause1124

theorem step1125 (p : Nat → Bool) (h : Constraints p) : p 1536 = false ∨ p 1565 = false ∨ p 1574 = true := h.block35.clause1125

theorem step1126 (p : Nat → Bool) (h : Constraints p) : p 1537 = false ∨ p 1560 = false ∨ p 1570 = true := h.block35.clause1126

theorem step1127 (p : Nat → Bool) (h : Constraints p) : p 1537 = false ∨ p 1561 = false ∨ p 1571 = true := h.block35.clause1127

theorem step1128 (p : Nat → Bool) (h : Constraints p) : p 1537 = false ∨ p 1562 = false ∨ p 1572 = true := h.block35.clause1128

theorem step1129 (p : Nat → Bool) (h : Constraints p) : p 1537 = false ∨ p 1563 = false ∨ p 1573 = true := h.block35.clause1129

theorem step1130 (p : Nat → Bool) (h : Constraints p) : p 1537 = false ∨ p 1564 = false ∨ p 1574 = true := h.block35.clause1130

theorem step1131 (p : Nat → Bool) (h : Constraints p) : p 1537 = false ∨ p 1565 = false ∨ p 1575 = true := h.block35.clause1131

theorem step1132 (p : Nat → Bool) (h : Constraints p) : p 1538 = false ∨ p 1570 = true := h.block35.clause1132

theorem step1133 (p : Nat → Bool) (h : Constraints p) : p 1538 = false ∨ p 1560 = false ∨ p 1571 = true := h.block35.clause1133

theorem step1134 (p : Nat → Bool) (h : Constraints p) : p 1538 = false ∨ p 1561 = false ∨ p 1572 = true := h.block35.clause1134

theorem step1135 (p : Nat → Bool) (h : Constraints p) : p 1538 = false ∨ p 1562 = false ∨ p 1573 = true := h.block35.clause1135

theorem step1136 (p : Nat → Bool) (h : Constraints p) : p 1538 = false ∨ p 1563 = false ∨ p 1574 = true := h.block35.clause1136

theorem step1137 (p : Nat → Bool) (h : Constraints p) : p 1538 = false ∨ p 1564 = false ∨ p 1575 = true := h.block35.clause1137

theorem step1138 (p : Nat → Bool) (h : Constraints p) : p 1539 = false ∨ p 1571 = true := h.block35.clause1138

theorem step1139 (p : Nat → Bool) (h : Constraints p) : p 1539 = false ∨ p 1560 = false ∨ p 1572 = true := h.block35.clause1139

theorem step1140 (p : Nat → Bool) (h : Constraints p) : p 1539 = false ∨ p 1561 = false ∨ p 1573 = true := h.block35.clause1140

theorem step1141 (p : Nat → Bool) (h : Constraints p) : p 1539 = false ∨ p 1562 = false ∨ p 1574 = true := h.block35.clause1141

theorem step1142 (p : Nat → Bool) (h : Constraints p) : p 1539 = false ∨ p 1563 = false ∨ p 1575 = true := h.block35.clause1142

theorem step1143 (p : Nat → Bool) (h : Constraints p) : p 1539 = false ∨ p 1564 = false ∨ p 1576 = true := h.block35.clause1143

theorem step1144 (p : Nat → Bool) (h : Constraints p) : p 1539 = false ∨ p 1565 = false ∨ p 1577 = true := h.block35.clause1144

theorem step1145 (p : Nat → Bool) (h : Constraints p) : p 1540 = false ∨ p 1572 = true := h.block35.clause1145

theorem step1146 (p : Nat → Bool) (h : Constraints p) : p 1540 = false ∨ p 1560 = false ∨ p 1573 = true := h.block35.clause1146

theorem step1147 (p : Nat → Bool) (h : Constraints p) : p 1540 = false ∨ p 1561 = false ∨ p 1574 = true := h.block35.clause1147

theorem step1148 (p : Nat → Bool) (h : Constraints p) : p 1540 = false ∨ p 1562 = false ∨ p 1575 = true := h.block35.clause1148

theorem step1149 (p : Nat → Bool) (h : Constraints p) : p 1540 = false ∨ p 1563 = false ∨ p 1576 = true := h.block35.clause1149

theorem step1150 (p : Nat → Bool) (h : Constraints p) : p 1507 = false ∨ p 1571 = false ∨ p 1590 = true := h.block35.clause1150

theorem step1151 (p : Nat → Bool) (h : Constraints p) : p 1507 = false ∨ p 1572 = false ∨ p 1591 = true := h.block35.clause1151

theorem step1152 (p : Nat → Bool) (h : Constraints p) : p 1507 = false ∨ p 1573 = false ∨ p 1592 = true := h.block35.clause1152

theorem step1153 (p : Nat → Bool) (h : Constraints p) : p 1507 = false ∨ p 1574 = false ∨ p 1593 = true := h.block36.clause1153

theorem step1154 (p : Nat → Bool) (h : Constraints p) : p 1507 = false ∨ p 1575 = false ∨ p 1594 = true := h.block36.clause1154

theorem step1155 (p : Nat → Bool) (h : Constraints p) : p 1507 = false ∨ p 1576 = false ∨ p 1595 = true := h.block36.clause1155

theorem step1156 (p : Nat → Bool) (h : Constraints p) : p 1508 = false ∨ p 1570 = false ∨ p 1590 = true := h.block36.clause1156

theorem step1157 (p : Nat → Bool) (h : Constraints p) : p 1508 = false ∨ p 1571 = false ∨ p 1591 = true := h.block36.clause1157

theorem step1158 (p : Nat → Bool) (h : Constraints p) : p 1508 = false ∨ p 1572 = false ∨ p 1592 = true := h.block36.clause1158

theorem step1159 (p : Nat → Bool) (h : Constraints p) : p 1508 = false ∨ p 1573 = false ∨ p 1593 = true := h.block36.clause1159

theorem step1160 (p : Nat → Bool) (h : Constraints p) : p 1508 = false ∨ p 1574 = false ∨ p 1594 = true := h.block36.clause1160

theorem step1161 (p : Nat → Bool) (h : Constraints p) : p 1508 = false ∨ p 1575 = false ∨ p 1595 = true := h.block36.clause1161

theorem step1162 (p : Nat → Bool) (h : Constraints p) : p 1508 = false ∨ p 1576 = false ∨ p 1596 = true := h.block36.clause1162

theorem step1163 (p : Nat → Bool) (h : Constraints p) : p 1508 = false ∨ p 1577 = false ∨ p 1597 = true := h.block36.clause1163

theorem step1164 (p : Nat → Bool) (h : Constraints p) : p 1509 = false ∨ p 1570 = false ∨ p 1591 = true := h.block36.clause1164

theorem step1165 (p : Nat → Bool) (h : Constraints p) : p 1509 = false ∨ p 1571 = false ∨ p 1592 = true := h.block36.clause1165

theorem step1166 (p : Nat → Bool) (h : Constraints p) : p 1509 = false ∨ p 1572 = false ∨ p 1593 = true := h.block36.clause1166

theorem step1167 (p : Nat → Bool) (h : Constraints p) : p 1509 = false ∨ p 1573 = false ∨ p 1594 = true := h.block36.clause1167

theorem step1168 (p : Nat → Bool) (h : Constraints p) : p 1509 = false ∨ p 1574 = false ∨ p 1595 = true := h.block36.clause1168

theorem step1169 (p : Nat → Bool) (h : Constraints p) : p 1509 = false ∨ p 1575 = false ∨ p 1596 = true := h.block36.clause1169

theorem step1170 (p : Nat → Bool) (h : Constraints p) : p 1509 = false ∨ p 1576 = false ∨ p 1597 = true := h.block36.clause1170

theorem step1171 (p : Nat → Bool) (h : Constraints p) : p 1510 = false ∨ p 1570 = false ∨ p 1592 = true := h.block36.clause1171

theorem step1172 (p : Nat → Bool) (h : Constraints p) : p 1510 = false ∨ p 1571 = false ∨ p 1593 = true := h.block36.clause1172

theorem step1173 (p : Nat → Bool) (h : Constraints p) : p 1510 = false ∨ p 1572 = false ∨ p 1594 = true := h.block36.clause1173

theorem step1174 (p : Nat → Bool) (h : Constraints p) : p 1510 = false ∨ p 1573 = false ∨ p 1595 = true := h.block36.clause1174

theorem step1175 (p : Nat → Bool) (h : Constraints p) : p 1510 = false ∨ p 1574 = false ∨ p 1596 = true := h.block36.clause1175

theorem step1176 (p : Nat → Bool) (h : Constraints p) : p 1511 = false ∨ p 1570 = false ∨ p 1593 = true := h.block36.clause1176

theorem step1177 (p : Nat → Bool) (h : Constraints p) : p 1511 = false ∨ p 1571 = false ∨ p 1594 = true := h.block36.clause1177

theorem step1178 (p : Nat → Bool) (h : Constraints p) : p 1511 = false ∨ p 1572 = false ∨ p 1595 = true := h.block36.clause1178

theorem step1179 (p : Nat → Bool) (h : Constraints p) : p 1511 = false ∨ p 1573 = false ∨ p 1596 = true := h.block36.clause1179

theorem step1180 (p : Nat → Bool) (h : Constraints p) : p 1511 = false ∨ p 1574 = false ∨ p 1597 = true := h.block36.clause1180

theorem step1181 (p : Nat → Bool) (h : Constraints p) : p 1512 = false ∨ p 1570 = false ∨ p 1594 = true := h.block36.clause1181

theorem step1182 (p : Nat → Bool) (h : Constraints p) : p 1512 = false ∨ p 1571 = false ∨ p 1595 = true := h.block36.clause1182

theorem step1183 (p : Nat → Bool) (h : Constraints p) : p 1512 = false ∨ p 1572 = false ∨ p 1596 = true := h.block36.clause1183

theorem step1184 (p : Nat → Bool) (h : Constraints p) : p 1512 = false ∨ p 1573 = false ∨ p 1597 = true := h.block36.clause1184

theorem step1185 (p : Nat → Bool) (h : Constraints p) : p 1513 = false ∨ p 1571 = false ∨ p 1596 = true := h.block37.clause1185

theorem step1186 (p : Nat → Bool) (h : Constraints p) : p 1513 = false ∨ p 1572 = false ∨ p 1597 = true := h.block37.clause1186

theorem step1187 (p : Nat → Bool) (h : Constraints p) : p 62 = true ∨ p 1607 = true := h.block37.clause1187

theorem step1188 (p : Nat → Bool) (h : Constraints p) : p 61 = true ∨ p 1607 = true := h.block37.clause1188

theorem step1189 (p : Nat → Bool) (h : Constraints p) : p 61 = true ∨ p 62 = true ∨ p 1608 = true := h.block37.clause1189

theorem step1190 (p : Nat → Bool) (h : Constraints p) : p 67 = true ∨ p 1609 = true := h.block37.clause1190

theorem step1191 (p : Nat → Bool) (h : Constraints p) : p 64 = true ∨ p 1609 = true := h.block37.clause1191

theorem step1192 (p : Nat → Bool) (h : Constraints p) : p 64 = true ∨ p 67 = true ∨ p 1610 = true := h.block37.clause1192

theorem step1193 (p : Nat → Bool) (h : Constraints p) : p 1609 = false ∨ p 1611 = true := h.block37.clause1193

theorem step1194 (p : Nat → Bool) (h : Constraints p) : p 1610 = false ∨ p 1612 = true := h.block37.clause1194

theorem step1195 (p : Nat → Bool) (h : Constraints p) : p 1607 = false ∨ p 1611 = true := h.block37.clause1195

theorem step1196 (p : Nat → Bool) (h : Constraints p) : p 1607 = false ∨ p 1609 = false ∨ p 1612 = true := h.block37.clause1196

theorem step1197 (p : Nat → Bool) (h : Constraints p) : p 1607 = false ∨ p 1610 = false ∨ p 1613 = true := h.block37.clause1197

theorem step1198 (p : Nat → Bool) (h : Constraints p) : p 1608 = false ∨ p 1612 = true := h.block37.clause1198

theorem step1199 (p : Nat → Bool) (h : Constraints p) : p 1608 = false ∨ p 1609 = false ∨ p 1613 = true := h.block37.clause1199

theorem step1200 (p : Nat → Bool) (h : Constraints p) : p 1608 = false ∨ p 1610 = false ∨ p 1614 = true := h.block37.clause1200

theorem step1201 (p : Nat → Bool) (h : Constraints p) : p 69 = true ∨ p 1615 = true := h.block37.clause1201

theorem step1202 (p : Nat → Bool) (h : Constraints p) : p 68 = true ∨ p 1615 = true := h.block37.clause1202

theorem step1203 (p : Nat → Bool) (h : Constraints p) : p 68 = true ∨ p 69 = true ∨ p 1616 = true := h.block37.clause1203

theorem step1204 (p : Nat → Bool) (h : Constraints p) : p 73 = true ∨ p 1617 = true := h.block37.clause1204

theorem step1205 (p : Nat → Bool) (h : Constraints p) : p 72 = true ∨ p 1617 = true := h.block37.clause1205

theorem step1206 (p : Nat → Bool) (h : Constraints p) : p 72 = true ∨ p 73 = true ∨ p 1618 = true := h.block37.clause1206

theorem step1207 (p : Nat → Bool) (h : Constraints p) : p 1617 = false ∨ p 1619 = true := h.block37.clause1207

theorem step1208 (p : Nat → Bool) (h : Constraints p) : p 1618 = false ∨ p 1620 = true := h.block37.clause1208

theorem step1209 (p : Nat → Bool) (h : Constraints p) : p 1615 = false ∨ p 1619 = true := h.block37.clause1209

theorem step1210 (p : Nat → Bool) (h : Constraints p) : p 1615 = false ∨ p 1617 = false ∨ p 1620 = true := h.block37.clause1210

theorem step1211 (p : Nat → Bool) (h : Constraints p) : p 1615 = false ∨ p 1618 = false ∨ p 1621 = true := h.block37.clause1211

theorem step1212 (p : Nat → Bool) (h : Constraints p) : p 1616 = false ∨ p 1617 = false ∨ p 1621 = true := h.block37.clause1212

theorem step1213 (p : Nat → Bool) (h : Constraints p) : p 1616 = false ∨ p 1618 = false ∨ p 1622 = true := h.block37.clause1213

theorem step1214 (p : Nat → Bool) (h : Constraints p) : p 1619 = false ∨ p 1623 = true := h.block37.clause1214

theorem step1215 (p : Nat → Bool) (h : Constraints p) : p 1620 = false ∨ p 1624 = true := h.block37.clause1215

theorem step1216 (p : Nat → Bool) (h : Constraints p) : p 1621 = false ∨ p 1625 = true := h.block37.clause1216

theorem step1217 (p : Nat → Bool) (h : Constraints p) : p 1622 = false ∨ p 1626 = true := h.block38.clause1217

theorem step1218 (p : Nat → Bool) (h : Constraints p) : p 1611 = false ∨ p 1623 = true := h.block38.clause1218

theorem step1219 (p : Nat → Bool) (h : Constraints p) : p 1611 = false ∨ p 1619 = false ∨ p 1624 = true := h.block38.clause1219

theorem step1220 (p : Nat → Bool) (h : Constraints p) : p 1611 = false ∨ p 1620 = false ∨ p 1625 = true := h.block38.clause1220

theorem step1221 (p : Nat → Bool) (h : Constraints p) : p 1611 = false ∨ p 1621 = false ∨ p 1626 = true := h.block38.clause1221

theorem step1222 (p : Nat → Bool) (h : Constraints p) : p 1611 = false ∨ p 1622 = false ∨ p 1627 = true := h.block38.clause1222

theorem step1223 (p : Nat → Bool) (h : Constraints p) : p 1612 = false ∨ p 1624 = true := h.block38.clause1223

theorem step1224 (p : Nat → Bool) (h : Constraints p) : p 1612 = false ∨ p 1619 = false ∨ p 1625 = true := h.block38.clause1224

theorem step1225 (p : Nat → Bool) (h : Constraints p) : p 1612 = false ∨ p 1620 = false ∨ p 1626 = true := h.block38.clause1225

theorem step1226 (p : Nat → Bool) (h : Constraints p) : p 1612 = false ∨ p 1621 = false ∨ p 1627 = true := h.block38.clause1226

theorem step1227 (p : Nat → Bool) (h : Constraints p) : p 1612 = false ∨ p 1622 = false ∨ p 1628 = true := h.block38.clause1227

theorem step1228 (p : Nat → Bool) (h : Constraints p) : p 1613 = false ∨ p 1625 = true := h.block38.clause1228

theorem step1229 (p : Nat → Bool) (h : Constraints p) : p 1613 = false ∨ p 1619 = false ∨ p 1626 = true := h.block38.clause1229

theorem step1230 (p : Nat → Bool) (h : Constraints p) : p 1613 = false ∨ p 1620 = false ∨ p 1627 = true := h.block38.clause1230

theorem step1231 (p : Nat → Bool) (h : Constraints p) : p 1613 = false ∨ p 1621 = false ∨ p 1628 = true := h.block38.clause1231

theorem step1232 (p : Nat → Bool) (h : Constraints p) : p 1614 = false ∨ p 1619 = false ∨ p 1627 = true := h.block38.clause1232

theorem step1233 (p : Nat → Bool) (h : Constraints p) : p 1614 = false ∨ p 1620 = false ∨ p 1628 = true := h.block38.clause1233

theorem step1234 (p : Nat → Bool) (h : Constraints p) : p 77 = true ∨ p 1631 = true := h.block38.clause1234

theorem step1235 (p : Nat → Bool) (h : Constraints p) : p 80 = true ∨ p 1633 = true := h.block38.clause1235

theorem step1236 (p : Nat → Bool) (h : Constraints p) : p 79 = true ∨ p 1633 = true := h.block38.clause1236

theorem step1237 (p : Nat → Bool) (h : Constraints p) : p 79 = true ∨ p 80 = true ∨ p 1634 = true := h.block38.clause1237

theorem step1238 (p : Nat → Bool) (h : Constraints p) : p 1633 = false ∨ p 1635 = true := h.block38.clause1238

theorem step1239 (p : Nat → Bool) (h : Constraints p) : p 1634 = false ∨ p 1636 = true := h.block38.clause1239

theorem step1240 (p : Nat → Bool) (h : Constraints p) : p 1631 = false ∨ p 1635 = true := h.block38.clause1240

theorem step1241 (p : Nat → Bool) (h : Constraints p) : p 1631 = false ∨ p 1633 = false ∨ p 1636 = true := h.block38.clause1241

theorem step1242 (p : Nat → Bool) (h : Constraints p) : p 1631 = false ∨ p 1634 = false ∨ p 1637 = true := h.block38.clause1242

theorem step1243 (p : Nat → Bool) (h : Constraints p) : p 85 = true ∨ p 1639 = true := h.block38.clause1243

theorem step1244 (p : Nat → Bool) (h : Constraints p) : p 84 = true ∨ p 1639 = true := h.block38.clause1244

theorem step1245 (p : Nat → Bool) (h : Constraints p) : p 84 = true ∨ p 85 = true ∨ p 1640 = true := h.block38.clause1245

theorem step1246 (p : Nat → Bool) (h : Constraints p) : p 90 = true ∨ p 1641 = true := h.block38.clause1246

theorem step1247 (p : Nat → Bool) (h : Constraints p) : p 88 = true ∨ p 1641 = true := h.block38.clause1247

theorem step1248 (p : Nat → Bool) (h : Constraints p) : p 88 = true ∨ p 90 = true ∨ p 1642 = true := h.block38.clause1248

theorem step1249 (p : Nat → Bool) (h : Constraints p) : p 1641 = false ∨ p 1643 = true := h.block39.clause1249

theorem step1250 (p : Nat → Bool) (h : Constraints p) : p 1642 = false ∨ p 1644 = true := h.block39.clause1250

theorem step1251 (p : Nat → Bool) (h : Constraints p) : p 1639 = false ∨ p 1643 = true := h.block39.clause1251

theorem step1252 (p : Nat → Bool) (h : Constraints p) : p 1639 = false ∨ p 1641 = false ∨ p 1644 = true := h.block39.clause1252

theorem step1253 (p : Nat → Bool) (h : Constraints p) : p 1639 = false ∨ p 1642 = false ∨ p 1645 = true := h.block39.clause1253

theorem step1254 (p : Nat → Bool) (h : Constraints p) : p 1640 = false ∨ p 1644 = true := h.block39.clause1254

theorem step1255 (p : Nat → Bool) (h : Constraints p) : p 1640 = false ∨ p 1641 = false ∨ p 1645 = true := h.block39.clause1255

theorem step1256 (p : Nat → Bool) (h : Constraints p) : p 1640 = false ∨ p 1642 = false ∨ p 1646 = true := h.block39.clause1256

theorem step1257 (p : Nat → Bool) (h : Constraints p) : p 1643 = false ∨ p 1647 = true := h.block39.clause1257

theorem step1258 (p : Nat → Bool) (h : Constraints p) : p 1644 = false ∨ p 1648 = true := h.block39.clause1258

theorem step1259 (p : Nat → Bool) (h : Constraints p) : p 1645 = false ∨ p 1649 = true := h.block39.clause1259

theorem step1260 (p : Nat → Bool) (h : Constraints p) : p 1646 = false ∨ p 1650 = true := h.block39.clause1260

theorem step1261 (p : Nat → Bool) (h : Constraints p) : p 1635 = false ∨ p 1643 = false ∨ p 1648 = true := h.block39.clause1261

theorem step1262 (p : Nat → Bool) (h : Constraints p) : p 1635 = false ∨ p 1644 = false ∨ p 1649 = true := h.block39.clause1262

theorem step1263 (p : Nat → Bool) (h : Constraints p) : p 1635 = false ∨ p 1645 = false ∨ p 1650 = true := h.block39.clause1263

theorem step1264 (p : Nat → Bool) (h : Constraints p) : p 1635 = false ∨ p 1646 = false ∨ p 1651 = true := h.block39.clause1264

theorem step1265 (p : Nat → Bool) (h : Constraints p) : p 1636 = false ∨ p 1648 = true := h.block39.clause1265

theorem step1266 (p : Nat → Bool) (h : Constraints p) : p 1636 = false ∨ p 1643 = false ∨ p 1649 = true := h.block39.clause1266

theorem step1267 (p : Nat → Bool) (h : Constraints p) : p 1636 = false ∨ p 1644 = false ∨ p 1650 = true := h.block39.clause1267

theorem step1268 (p : Nat → Bool) (h : Constraints p) : p 1636 = false ∨ p 1645 = false ∨ p 1651 = true := h.block39.clause1268

theorem step1269 (p : Nat → Bool) (h : Constraints p) : p 1636 = false ∨ p 1646 = false ∨ p 1652 = true := h.block39.clause1269

theorem step1270 (p : Nat → Bool) (h : Constraints p) : p 1637 = false ∨ p 1649 = true := h.block39.clause1270

theorem step1271 (p : Nat → Bool) (h : Constraints p) : p 1637 = false ∨ p 1643 = false ∨ p 1650 = true := h.block39.clause1271

theorem step1272 (p : Nat → Bool) (h : Constraints p) : p 1637 = false ∨ p 1644 = false ∨ p 1651 = true := h.block39.clause1272

theorem step1273 (p : Nat → Bool) (h : Constraints p) : p 1637 = false ∨ p 1645 = false ∨ p 1652 = true := h.block39.clause1273

theorem step1274 (p : Nat → Bool) (h : Constraints p) : p 1637 = false ∨ p 1646 = false ∨ p 1653 = true := h.block39.clause1274

theorem step1275 (p : Nat → Bool) (h : Constraints p) : p 1648 = false ∨ p 1656 = true := h.block39.clause1275

theorem step1276 (p : Nat → Bool) (h : Constraints p) : p 1649 = false ∨ p 1657 = true := h.block39.clause1276

theorem step1277 (p : Nat → Bool) (h : Constraints p) : p 1650 = false ∨ p 1658 = true := h.block39.clause1277

theorem step1278 (p : Nat → Bool) (h : Constraints p) : p 1651 = false ∨ p 1659 = true := h.block39.clause1278

theorem step1279 (p : Nat → Bool) (h : Constraints p) : p 1652 = false ∨ p 1660 = true := h.block39.clause1279

theorem step1280 (p : Nat → Bool) (h : Constraints p) : p 1623 = false ∨ p 1647 = false ∨ p 1656 = true := h.block39.clause1280

theorem step1281 (p : Nat → Bool) (h : Constraints p) : p 1623 = false ∨ p 1648 = false ∨ p 1657 = true := h.block40.clause1281

theorem step1282 (p : Nat → Bool) (h : Constraints p) : p 1623 = false ∨ p 1649 = false ∨ p 1658 = true := h.block40.clause1282

theorem step1283 (p : Nat → Bool) (h : Constraints p) : p 1623 = false ∨ p 1650 = false ∨ p 1659 = true := h.block40.clause1283

theorem step1284 (p : Nat → Bool) (h : Constraints p) : p 1623 = false ∨ p 1651 = false ∨ p 1660 = true := h.block40.clause1284

theorem step1285 (p : Nat → Bool) (h : Constraints p) : p 1623 = false ∨ p 1652 = false ∨ p 1661 = true := h.block40.clause1285

theorem step1286 (p : Nat → Bool) (h : Constraints p) : p 1624 = false ∨ p 1647 = false ∨ p 1657 = true := h.block40.clause1286

theorem step1287 (p : Nat → Bool) (h : Constraints p) : p 1624 = false ∨ p 1648 = false ∨ p 1658 = true := h.block40.clause1287

theorem step1288 (p : Nat → Bool) (h : Constraints p) : p 1624 = false ∨ p 1649 = false ∨ p 1659 = true := h.block40.clause1288

theorem step1289 (p : Nat → Bool) (h : Constraints p) : p 1624 = false ∨ p 1650 = false ∨ p 1660 = true := h.block40.clause1289

theorem step1290 (p : Nat → Bool) (h : Constraints p) : p 1624 = false ∨ p 1651 = false ∨ p 1661 = true := h.block40.clause1290

theorem step1291 (p : Nat → Bool) (h : Constraints p) : p 1624 = false ∨ p 1652 = false ∨ p 1662 = true := h.block40.clause1291

theorem step1292 (p : Nat → Bool) (h : Constraints p) : p 1624 = false ∨ p 1653 = false ∨ p 1663 = true := h.block40.clause1292

theorem step1293 (p : Nat → Bool) (h : Constraints p) : p 1625 = false ∨ p 1647 = false ∨ p 1658 = true := h.block40.clause1293

theorem step1294 (p : Nat → Bool) (h : Constraints p) : p 1625 = false ∨ p 1648 = false ∨ p 1659 = true := h.block40.clause1294

theorem step1295 (p : Nat → Bool) (h : Constraints p) : p 1625 = false ∨ p 1649 = false ∨ p 1660 = true := h.block40.clause1295

theorem step1296 (p : Nat → Bool) (h : Constraints p) : p 1625 = false ∨ p 1650 = false ∨ p 1661 = true := h.block40.clause1296

theorem step1297 (p : Nat → Bool) (h : Constraints p) : p 1625 = false ∨ p 1651 = false ∨ p 1662 = true := h.block40.clause1297

theorem step1298 (p : Nat → Bool) (h : Constraints p) : p 1625 = false ∨ p 1652 = false ∨ p 1663 = true := h.block40.clause1298

theorem step1299 (p : Nat → Bool) (h : Constraints p) : p 1625 = false ∨ p 1653 = false ∨ p 1664 = true := h.block40.clause1299

theorem step1300 (p : Nat → Bool) (h : Constraints p) : p 1626 = false ∨ p 1647 = false ∨ p 1659 = true := h.block40.clause1300

theorem step1301 (p : Nat → Bool) (h : Constraints p) : p 1626 = false ∨ p 1648 = false ∨ p 1660 = true := h.block40.clause1301

theorem step1302 (p : Nat → Bool) (h : Constraints p) : p 1626 = false ∨ p 1649 = false ∨ p 1661 = true := h.block40.clause1302

theorem step1303 (p : Nat → Bool) (h : Constraints p) : p 1626 = false ∨ p 1650 = false ∨ p 1662 = true := h.block40.clause1303

theorem step1304 (p : Nat → Bool) (h : Constraints p) : p 1626 = false ∨ p 1651 = false ∨ p 1663 = true := h.block40.clause1304

theorem step1305 (p : Nat → Bool) (h : Constraints p) : p 1626 = false ∨ p 1652 = false ∨ p 1664 = true := h.block40.clause1305

theorem step1306 (p : Nat → Bool) (h : Constraints p) : p 1627 = false ∨ p 1647 = false ∨ p 1660 = true := h.block40.clause1306

theorem step1307 (p : Nat → Bool) (h : Constraints p) : p 1627 = false ∨ p 1648 = false ∨ p 1661 = true := h.block40.clause1307

theorem step1308 (p : Nat → Bool) (h : Constraints p) : p 1627 = false ∨ p 1649 = false ∨ p 1662 = true := h.block40.clause1308

theorem step1309 (p : Nat → Bool) (h : Constraints p) : p 1627 = false ∨ p 1650 = false ∨ p 1663 = true := h.block40.clause1309

theorem step1310 (p : Nat → Bool) (h : Constraints p) : p 1627 = false ∨ p 1651 = false ∨ p 1664 = true := h.block40.clause1310

theorem step1311 (p : Nat → Bool) (h : Constraints p) : p 1628 = false ∨ p 1648 = false ∨ p 1662 = true := h.block40.clause1311

theorem step1312 (p : Nat → Bool) (h : Constraints p) : p 1628 = false ∨ p 1649 = false ∨ p 1663 = true := h.block40.clause1312

theorem step1313 (p : Nat → Bool) (h : Constraints p) : p 93 = true ∨ p 1671 = true := h.block41.clause1313

theorem step1314 (p : Nat → Bool) (h : Constraints p) : p 92 = true ∨ p 1671 = true := h.block41.clause1314

theorem step1315 (p : Nat → Bool) (h : Constraints p) : p 92 = true ∨ p 93 = true ∨ p 1672 = true := h.block41.clause1315

theorem step1316 (p : Nat → Bool) (h : Constraints p) : p 97 = true ∨ p 1673 = true := h.block41.clause1316

theorem step1317 (p : Nat → Bool) (h : Constraints p) : p 95 = true ∨ p 1673 = true := h.block41.clause1317

theorem step1318 (p : Nat → Bool) (h : Constraints p) : p 95 = true ∨ p 97 = true ∨ p 1674 = true := h.block41.clause1318

theorem step1319 (p : Nat → Bool) (h : Constraints p) : p 1673 = false ∨ p 1675 = true := h.block41.clause1319

theorem step1320 (p : Nat → Bool) (h : Constraints p) : p 1674 = false ∨ p 1676 = true := h.block41.clause1320

theorem step1321 (p : Nat → Bool) (h : Constraints p) : p 1671 = false ∨ p 1675 = true := h.block41.clause1321

theorem step1322 (p : Nat → Bool) (h : Constraints p) : p 1671 = false ∨ p 1673 = false ∨ p 1676 = true := h.block41.clause1322

theorem step1323 (p : Nat → Bool) (h : Constraints p) : p 1671 = false ∨ p 1674 = false ∨ p 1677 = true := h.block41.clause1323

theorem step1324 (p : Nat → Bool) (h : Constraints p) : p 1672 = false ∨ p 1676 = true := h.block41.clause1324

theorem step1325 (p : Nat → Bool) (h : Constraints p) : p 1672 = false ∨ p 1673 = false ∨ p 1677 = true := h.block41.clause1325

theorem step1326 (p : Nat → Bool) (h : Constraints p) : p 1672 = false ∨ p 1674 = false ∨ p 1678 = true := h.block41.clause1326

theorem step1327 (p : Nat → Bool) (h : Constraints p) : p 101 = true ∨ p 1679 = true := h.block41.clause1327

theorem step1328 (p : Nat → Bool) (h : Constraints p) : p 98 = true ∨ p 1679 = true := h.block41.clause1328

theorem step1329 (p : Nat → Bool) (h : Constraints p) : p 98 = true ∨ p 101 = true ∨ p 1680 = true := h.block41.clause1329

theorem step1330 (p : Nat → Bool) (h : Constraints p) : p 105 = true ∨ p 1681 = true := h.block41.clause1330

theorem step1331 (p : Nat → Bool) (h : Constraints p) : p 104 = true ∨ p 1681 = true := h.block41.clause1331

theorem step1332 (p : Nat → Bool) (h : Constraints p) : p 104 = true ∨ p 105 = true ∨ p 1682 = true := h.block41.clause1332

theorem step1333 (p : Nat → Bool) (h : Constraints p) : p 1681 = false ∨ p 1683 = true := h.block41.clause1333

theorem step1334 (p : Nat → Bool) (h : Constraints p) : p 1682 = false ∨ p 1684 = true := h.block41.clause1334

theorem step1335 (p : Nat → Bool) (h : Constraints p) : p 1679 = false ∨ p 1683 = true := h.block41.clause1335

theorem step1336 (p : Nat → Bool) (h : Constraints p) : p 1679 = false ∨ p 1681 = false ∨ p 1684 = true := h.block41.clause1336

theorem step1337 (p : Nat → Bool) (h : Constraints p) : p 1679 = false ∨ p 1682 = false ∨ p 1685 = true := h.block41.clause1337

theorem step1338 (p : Nat → Bool) (h : Constraints p) : p 1680 = false ∨ p 1684 = true := h.block41.clause1338

theorem step1339 (p : Nat → Bool) (h : Constraints p) : p 1680 = false ∨ p 1681 = false ∨ p 1685 = true := h.block41.clause1339

theorem step1340 (p : Nat → Bool) (h : Constraints p) : p 1680 = false ∨ p 1682 = false ∨ p 1686 = true := h.block41.clause1340

theorem step1341 (p : Nat → Bool) (h : Constraints p) : p 1683 = false ∨ p 1687 = true := h.block41.clause1341

theorem step1342 (p : Nat → Bool) (h : Constraints p) : p 1684 = false ∨ p 1688 = true := h.block41.clause1342

theorem step1343 (p : Nat → Bool) (h : Constraints p) : p 1685 = false ∨ p 1689 = true := h.block41.clause1343

theorem step1344 (p : Nat → Bool) (h : Constraints p) : p 1686 = false ∨ p 1690 = true := h.block41.clause1344

theorem step1345 (p : Nat → Bool) (h : Constraints p) : p 1675 = false ∨ p 1687 = true := h.block42.clause1345

theorem step1346 (p : Nat → Bool) (h : Constraints p) : p 1675 = false ∨ p 1683 = false ∨ p 1688 = true := h.block42.clause1346

theorem step1347 (p : Nat → Bool) (h : Constraints p) : p 1675 = false ∨ p 1684 = false ∨ p 1689 = true := h.block42.clause1347

theorem step1348 (p : Nat → Bool) (h : Constraints p) : p 1675 = false ∨ p 1685 = false ∨ p 1690 = true := h.block42.clause1348

theorem step1349 (p : Nat → Bool) (h : Constraints p) : p 1675 = false ∨ p 1686 = false ∨ p 1691 = true := h.block42.clause1349

theorem step1350 (p : Nat → Bool) (h : Constraints p) : p 1676 = false ∨ p 1688 = true := h.block42.clause1350

theorem step1351 (p : Nat → Bool) (h : Constraints p) : p 1676 = false ∨ p 1683 = false ∨ p 1689 = true := h.block42.clause1351

theorem step1352 (p : Nat → Bool) (h : Constraints p) : p 1676 = false ∨ p 1684 = false ∨ p 1690 = true := h.block42.clause1352

theorem step1353 (p : Nat → Bool) (h : Constraints p) : p 1676 = false ∨ p 1685 = false ∨ p 1691 = true := h.block42.clause1353

theorem step1354 (p : Nat → Bool) (h : Constraints p) : p 1676 = false ∨ p 1686 = false ∨ p 1692 = true := h.block42.clause1354

theorem step1355 (p : Nat → Bool) (h : Constraints p) : p 1677 = false ∨ p 1689 = true := h.block42.clause1355

theorem step1356 (p : Nat → Bool) (h : Constraints p) : p 1677 = false ∨ p 1683 = false ∨ p 1690 = true := h.block42.clause1356

theorem step1357 (p : Nat → Bool) (h : Constraints p) : p 1677 = false ∨ p 1684 = false ∨ p 1691 = true := h.block42.clause1357

theorem step1358 (p : Nat → Bool) (h : Constraints p) : p 1677 = false ∨ p 1685 = false ∨ p 1692 = true := h.block42.clause1358

theorem step1359 (p : Nat → Bool) (h : Constraints p) : p 1677 = false ∨ p 1686 = false ∨ p 1693 = true := h.block42.clause1359

theorem step1360 (p : Nat → Bool) (h : Constraints p) : p 1678 = false ∨ p 1690 = true := h.block42.clause1360

theorem step1361 (p : Nat → Bool) (h : Constraints p) : p 1678 = false ∨ p 1683 = false ∨ p 1691 = true := h.block42.clause1361

theorem step1362 (p : Nat → Bool) (h : Constraints p) : p 1678 = false ∨ p 1684 = false ∨ p 1692 = true := h.block42.clause1362

theorem step1363 (p : Nat → Bool) (h : Constraints p) : p 1678 = false ∨ p 1685 = false ∨ p 1693 = true := h.block42.clause1363

theorem step1364 (p : Nat → Bool) (h : Constraints p) : p 110 = true ∨ p 1695 = true := h.block42.clause1364

theorem step1365 (p : Nat → Bool) (h : Constraints p) : p 109 = true ∨ p 1695 = true := h.block42.clause1365

theorem step1366 (p : Nat → Bool) (h : Constraints p) : p 109 = true ∨ p 110 = true ∨ p 1696 = true := h.block42.clause1366

theorem step1367 (p : Nat → Bool) (h : Constraints p) : p 113 = true ∨ p 1697 = true := h.block42.clause1367

theorem step1368 (p : Nat → Bool) (h : Constraints p) : p 111 = true ∨ p 1697 = true := h.block42.clause1368

theorem step1369 (p : Nat → Bool) (h : Constraints p) : p 111 = true ∨ p 113 = true ∨ p 1698 = true := h.block42.clause1369

theorem step1370 (p : Nat → Bool) (h : Constraints p) : p 1697 = false ∨ p 1699 = true := h.block42.clause1370

theorem step1371 (p : Nat → Bool) (h : Constraints p) : p 1698 = false ∨ p 1700 = true := h.block42.clause1371

theorem step1372 (p : Nat → Bool) (h : Constraints p) : p 1695 = false ∨ p 1699 = true := h.block42.clause1372

theorem step1373 (p : Nat → Bool) (h : Constraints p) : p 1695 = false ∨ p 1697 = false ∨ p 1700 = true := h.block42.clause1373

theorem step1374 (p : Nat → Bool) (h : Constraints p) : p 1695 = false ∨ p 1698 = false ∨ p 1701 = true := h.block42.clause1374

theorem step1375 (p : Nat → Bool) (h : Constraints p) : p 1696 = false ∨ p 1700 = true := h.block42.clause1375

theorem step1376 (p : Nat → Bool) (h : Constraints p) : p 1696 = false ∨ p 1697 = false ∨ p 1701 = true := h.block42.clause1376

theorem step1377 (p : Nat → Bool) (h : Constraints p) : p 1696 = false ∨ p 1698 = false ∨ p 1702 = true := h.block43.clause1377

theorem step1378 (p : Nat → Bool) (h : Constraints p) : p 117 = true ∨ p 1703 = true := h.block43.clause1378

theorem step1379 (p : Nat → Bool) (h : Constraints p) : p 116 = true ∨ p 1703 = true := h.block43.clause1379

theorem step1380 (p : Nat → Bool) (h : Constraints p) : p 116 = true ∨ p 117 = true ∨ p 1704 = true := h.block43.clause1380

theorem step1381 (p : Nat → Bool) (h : Constraints p) : p 122 = true ∨ p 1705 = true := h.block43.clause1381

theorem step1382 (p : Nat → Bool) (h : Constraints p) : p 119 = true ∨ p 1705 = true := h.block43.clause1382

theorem step1383 (p : Nat → Bool) (h : Constraints p) : p 119 = true ∨ p 122 = true ∨ p 1706 = true := h.block43.clause1383

theorem step1384 (p : Nat → Bool) (h : Constraints p) : p 1705 = false ∨ p 1707 = true := h.block43.clause1384

theorem step1385 (p : Nat → Bool) (h : Constraints p) : p 1706 = false ∨ p 1708 = true := h.block43.clause1385

theorem step1386 (p : Nat → Bool) (h : Constraints p) : p 1703 = false ∨ p 1707 = true := h.block43.clause1386

theorem step1387 (p : Nat → Bool) (h : Constraints p) : p 1703 = false ∨ p 1705 = false ∨ p 1708 = true := h.block43.clause1387

theorem step1388 (p : Nat → Bool) (h : Constraints p) : p 1703 = false ∨ p 1706 = false ∨ p 1709 = true := h.block43.clause1388

theorem step1389 (p : Nat → Bool) (h : Constraints p) : p 1704 = false ∨ p 1708 = true := h.block43.clause1389

theorem step1390 (p : Nat → Bool) (h : Constraints p) : p 1704 = false ∨ p 1705 = false ∨ p 1709 = true := h.block43.clause1390

theorem step1391 (p : Nat → Bool) (h : Constraints p) : p 1704 = false ∨ p 1706 = false ∨ p 1710 = true := h.block43.clause1391

theorem step1392 (p : Nat → Bool) (h : Constraints p) : p 1707 = false ∨ p 1711 = true := h.block43.clause1392

theorem step1393 (p : Nat → Bool) (h : Constraints p) : p 1708 = false ∨ p 1712 = true := h.block43.clause1393

theorem step1394 (p : Nat → Bool) (h : Constraints p) : p 1709 = false ∨ p 1713 = true := h.block43.clause1394

theorem step1395 (p : Nat → Bool) (h : Constraints p) : p 1710 = false ∨ p 1714 = true := h.block43.clause1395

theorem step1396 (p : Nat → Bool) (h : Constraints p) : p 1699 = false ∨ p 1711 = true := h.block43.clause1396

theorem step1397 (p : Nat → Bool) (h : Constraints p) : p 1699 = false ∨ p 1707 = false ∨ p 1712 = true := h.block43.clause1397

theorem step1398 (p : Nat → Bool) (h : Constraints p) : p 1699 = false ∨ p 1708 = false ∨ p 1713 = true := h.block43.clause1398

theorem step1399 (p : Nat → Bool) (h : Constraints p) : p 1699 = false ∨ p 1709 = false ∨ p 1714 = true := h.block43.clause1399

theorem step1400 (p : Nat → Bool) (h : Constraints p) : p 1699 = false ∨ p 1710 = false ∨ p 1715 = true := h.block43.clause1400

theorem step1401 (p : Nat → Bool) (h : Constraints p) : p 1700 = false ∨ p 1712 = true := h.block43.clause1401

theorem step1402 (p : Nat → Bool) (h : Constraints p) : p 1700 = false ∨ p 1707 = false ∨ p 1713 = true := h.block43.clause1402

theorem step1403 (p : Nat → Bool) (h : Constraints p) : p 1700 = false ∨ p 1708 = false ∨ p 1714 = true := h.block43.clause1403

theorem step1404 (p : Nat → Bool) (h : Constraints p) : p 1700 = false ∨ p 1709 = false ∨ p 1715 = true := h.block43.clause1404

theorem step1405 (p : Nat → Bool) (h : Constraints p) : p 1700 = false ∨ p 1710 = false ∨ p 1716 = true := h.block43.clause1405

theorem step1406 (p : Nat → Bool) (h : Constraints p) : p 1701 = false ∨ p 1713 = true := h.block43.clause1406

theorem step1407 (p : Nat → Bool) (h : Constraints p) : p 1701 = false ∨ p 1707 = false ∨ p 1714 = true := h.block43.clause1407

theorem step1408 (p : Nat → Bool) (h : Constraints p) : p 1701 = false ∨ p 1708 = false ∨ p 1715 = true := h.block43.clause1408

theorem step1409 (p : Nat → Bool) (h : Constraints p) : p 1701 = false ∨ p 1709 = false ∨ p 1716 = true := h.block44.clause1409

theorem step1410 (p : Nat → Bool) (h : Constraints p) : p 1702 = false ∨ p 1714 = true := h.block44.clause1410

theorem step1411 (p : Nat → Bool) (h : Constraints p) : p 1702 = false ∨ p 1707 = false ∨ p 1715 = true := h.block44.clause1411

theorem step1412 (p : Nat → Bool) (h : Constraints p) : p 1687 = false ∨ p 1712 = false ∨ p 1721 = true := h.block44.clause1412

theorem step1413 (p : Nat → Bool) (h : Constraints p) : p 1687 = false ∨ p 1713 = false ∨ p 1722 = true := h.block44.clause1413

theorem step1414 (p : Nat → Bool) (h : Constraints p) : p 1687 = false ∨ p 1714 = false ∨ p 1723 = true := h.block44.clause1414

theorem step1415 (p : Nat → Bool) (h : Constraints p) : p 1687 = false ∨ p 1715 = false ∨ p 1724 = true := h.block44.clause1415

theorem step1416 (p : Nat → Bool) (h : Constraints p) : p 1687 = false ∨ p 1716 = false ∨ p 1725 = true := h.block44.clause1416

theorem step1417 (p : Nat → Bool) (h : Constraints p) : p 1688 = false ∨ p 1711 = false ∨ p 1721 = true := h.block44.clause1417

theorem step1418 (p : Nat → Bool) (h : Constraints p) : p 1688 = false ∨ p 1712 = false ∨ p 1722 = true := h.block44.clause1418

theorem step1419 (p : Nat → Bool) (h : Constraints p) : p 1688 = false ∨ p 1713 = false ∨ p 1723 = true := h.block44.clause1419

theorem step1420 (p : Nat → Bool) (h : Constraints p) : p 1688 = false ∨ p 1714 = false ∨ p 1724 = true := h.block44.clause1420

theorem step1421 (p : Nat → Bool) (h : Constraints p) : p 1688 = false ∨ p 1715 = false ∨ p 1725 = true := h.block44.clause1421

theorem step1422 (p : Nat → Bool) (h : Constraints p) : p 1688 = false ∨ p 1716 = false ∨ p 1726 = true := h.block44.clause1422

theorem step1423 (p : Nat → Bool) (h : Constraints p) : p 1689 = false ∨ p 1711 = false ∨ p 1722 = true := h.block44.clause1423

theorem step1424 (p : Nat → Bool) (h : Constraints p) : p 1689 = false ∨ p 1712 = false ∨ p 1723 = true := h.block44.clause1424

theorem step1425 (p : Nat → Bool) (h : Constraints p) : p 1689 = false ∨ p 1713 = false ∨ p 1724 = true := h.block44.clause1425

theorem step1426 (p : Nat → Bool) (h : Constraints p) : p 1689 = false ∨ p 1714 = false ∨ p 1725 = true := h.block44.clause1426

theorem step1427 (p : Nat → Bool) (h : Constraints p) : p 1689 = false ∨ p 1715 = false ∨ p 1726 = true := h.block44.clause1427

theorem step1428 (p : Nat → Bool) (h : Constraints p) : p 1690 = false ∨ p 1711 = false ∨ p 1723 = true := h.block44.clause1428

theorem step1429 (p : Nat → Bool) (h : Constraints p) : p 1690 = false ∨ p 1712 = false ∨ p 1724 = true := h.block44.clause1429

theorem step1430 (p : Nat → Bool) (h : Constraints p) : p 1690 = false ∨ p 1713 = false ∨ p 1725 = true := h.block44.clause1430

theorem step1431 (p : Nat → Bool) (h : Constraints p) : p 1690 = false ∨ p 1714 = false ∨ p 1726 = true := h.block44.clause1431

theorem step1432 (p : Nat → Bool) (h : Constraints p) : p 1690 = false ∨ p 1715 = false ∨ p 1727 = true := h.block44.clause1432

theorem step1433 (p : Nat → Bool) (h : Constraints p) : p 1690 = false ∨ p 1716 = false ∨ p 1728 = true := h.block44.clause1433

theorem step1434 (p : Nat → Bool) (h : Constraints p) : p 1691 = false ∨ p 1711 = false ∨ p 1724 = true := h.block44.clause1434

theorem step1435 (p : Nat → Bool) (h : Constraints p) : p 1691 = false ∨ p 1712 = false ∨ p 1725 = true := h.block44.clause1435

theorem step1436 (p : Nat → Bool) (h : Constraints p) : p 1691 = false ∨ p 1713 = false ∨ p 1726 = true := h.block44.clause1436

theorem step1437 (p : Nat → Bool) (h : Constraints p) : p 1691 = false ∨ p 1714 = false ∨ p 1727 = true := h.block44.clause1437

theorem step1438 (p : Nat → Bool) (h : Constraints p) : p 1691 = false ∨ p 1715 = false ∨ p 1728 = true := h.block44.clause1438

theorem step1439 (p : Nat → Bool) (h : Constraints p) : p 1692 = false ∨ p 1724 = true := h.block44.clause1439

theorem step1440 (p : Nat → Bool) (h : Constraints p) : p 1692 = false ∨ p 1711 = false ∨ p 1725 = true := h.block44.clause1440

theorem step1441 (p : Nat → Bool) (h : Constraints p) : p 1692 = false ∨ p 1712 = false ∨ p 1726 = true := h.block45.clause1441

theorem step1442 (p : Nat → Bool) (h : Constraints p) : p 1692 = false ∨ p 1713 = false ∨ p 1727 = true := h.block45.clause1442

theorem step1443 (p : Nat → Bool) (h : Constraints p) : p 1692 = false ∨ p 1714 = false ∨ p 1728 = true := h.block45.clause1443

theorem step1444 (p : Nat → Bool) (h : Constraints p) : p 1693 = false ∨ p 1711 = false ∨ p 1726 = true := h.block45.clause1444

theorem step1445 (p : Nat → Bool) (h : Constraints p) : p 1693 = false ∨ p 1712 = false ∨ p 1727 = true := h.block45.clause1445

theorem step1446 (p : Nat → Bool) (h : Constraints p) : p 1693 = false ∨ p 1713 = false ∨ p 1728 = true := h.block45.clause1446

theorem step1447 (p : Nat → Bool) (h : Constraints p) : p 1656 = false ∨ p 1725 = false ∨ p 1743 = true := h.block45.clause1447

theorem step1448 (p : Nat → Bool) (h : Constraints p) : p 1656 = false ∨ p 1726 = false ∨ p 1744 = true := h.block45.clause1448

theorem step1449 (p : Nat → Bool) (h : Constraints p) : p 1656 = false ∨ p 1727 = false ∨ p 1745 = true := h.block45.clause1449

theorem step1450 (p : Nat → Bool) (h : Constraints p) : p 1657 = false ∨ p 1724 = false ∨ p 1743 = true := h.block45.clause1450

theorem step1451 (p : Nat → Bool) (h : Constraints p) : p 1657 = false ∨ p 1725 = false ∨ p 1744 = true := h.block45.clause1451

theorem step1452 (p : Nat → Bool) (h : Constraints p) : p 1657 = false ∨ p 1726 = false ∨ p 1745 = true := h.block45.clause1452

theorem step1453 (p : Nat → Bool) (h : Constraints p) : p 1657 = false ∨ p 1727 = false ∨ p 1746 = true := h.block45.clause1453

theorem step1454 (p : Nat → Bool) (h : Constraints p) : p 1657 = false ∨ p 1728 = false ∨ p 1747 = true := h.block45.clause1454

theorem step1455 (p : Nat → Bool) (h : Constraints p) : p 1658 = false ∨ p 1723 = false ∨ p 1743 = true := h.block45.clause1455

theorem step1456 (p : Nat → Bool) (h : Constraints p) : p 1658 = false ∨ p 1724 = false ∨ p 1744 = true := h.block45.clause1456

theorem step1457 (p : Nat → Bool) (h : Constraints p) : p 1658 = false ∨ p 1725 = false ∨ p 1745 = true := h.block45.clause1457

theorem step1458 (p : Nat → Bool) (h : Constraints p) : p 1658 = false ∨ p 1726 = false ∨ p 1746 = true := h.block45.clause1458

theorem step1459 (p : Nat → Bool) (h : Constraints p) : p 1658 = false ∨ p 1727 = false ∨ p 1747 = true := h.block45.clause1459

theorem step1460 (p : Nat → Bool) (h : Constraints p) : p 1658 = false ∨ p 1728 = false ∨ p 1748 = true := h.block45.clause1460

theorem step1461 (p : Nat → Bool) (h : Constraints p) : p 1659 = false ∨ p 1722 = false ∨ p 1743 = true := h.block45.clause1461

theorem step1462 (p : Nat → Bool) (h : Constraints p) : p 1659 = false ∨ p 1723 = false ∨ p 1744 = true := h.block45.clause1462

theorem step1463 (p : Nat → Bool) (h : Constraints p) : p 1659 = false ∨ p 1724 = false ∨ p 1745 = true := h.block45.clause1463

theorem step1464 (p : Nat → Bool) (h : Constraints p) : p 1659 = false ∨ p 1725 = false ∨ p 1746 = true := h.block45.clause1464

theorem step1465 (p : Nat → Bool) (h : Constraints p) : p 1659 = false ∨ p 1726 = false ∨ p 1747 = true := h.block45.clause1465

theorem step1466 (p : Nat → Bool) (h : Constraints p) : p 1659 = false ∨ p 1727 = false ∨ p 1748 = true := h.block45.clause1466

theorem step1467 (p : Nat → Bool) (h : Constraints p) : p 1659 = false ∨ p 1728 = false ∨ p 1749 = true := h.block45.clause1467

theorem step1468 (p : Nat → Bool) (h : Constraints p) : p 1660 = false ∨ p 1722 = false ∨ p 1744 = true := h.block45.clause1468

theorem step1469 (p : Nat → Bool) (h : Constraints p) : p 1660 = false ∨ p 1723 = false ∨ p 1745 = true := h.block45.clause1469

theorem step1470 (p : Nat → Bool) (h : Constraints p) : p 1660 = false ∨ p 1724 = false ∨ p 1746 = true := h.block45.clause1470

theorem step1471 (p : Nat → Bool) (h : Constraints p) : p 1660 = false ∨ p 1725 = false ∨ p 1747 = true := h.block45.clause1471

theorem step1472 (p : Nat → Bool) (h : Constraints p) : p 1660 = false ∨ p 1726 = false ∨ p 1748 = true := h.block45.clause1472

theorem step1473 (p : Nat → Bool) (h : Constraints p) : p 1660 = false ∨ p 1727 = false ∨ p 1749 = true := h.block46.clause1473

theorem step1474 (p : Nat → Bool) (h : Constraints p) : p 1660 = false ∨ p 1728 = false ∨ p 1750 = true := h.block46.clause1474

theorem step1475 (p : Nat → Bool) (h : Constraints p) : p 1661 = false ∨ p 1721 = false ∨ p 1744 = true := h.block46.clause1475

theorem step1476 (p : Nat → Bool) (h : Constraints p) : p 1661 = false ∨ p 1722 = false ∨ p 1745 = true := h.block46.clause1476

theorem step1477 (p : Nat → Bool) (h : Constraints p) : p 1661 = false ∨ p 1723 = false ∨ p 1746 = true := h.block46.clause1477

theorem step1478 (p : Nat → Bool) (h : Constraints p) : p 1661 = false ∨ p 1724 = false ∨ p 1747 = true := h.block46.clause1478

theorem step1479 (p : Nat → Bool) (h : Constraints p) : p 1661 = false ∨ p 1725 = false ∨ p 1748 = true := h.block46.clause1479

theorem step1480 (p : Nat → Bool) (h : Constraints p) : p 1661 = false ∨ p 1726 = false ∨ p 1749 = true := h.block46.clause1480

theorem step1481 (p : Nat → Bool) (h : Constraints p) : p 1662 = false ∨ p 1721 = false ∨ p 1745 = true := h.block46.clause1481

theorem step1482 (p : Nat → Bool) (h : Constraints p) : p 1662 = false ∨ p 1722 = false ∨ p 1746 = true := h.block46.clause1482

theorem step1483 (p : Nat → Bool) (h : Constraints p) : p 1662 = false ∨ p 1723 = false ∨ p 1747 = true := h.block46.clause1483

theorem step1484 (p : Nat → Bool) (h : Constraints p) : p 1662 = false ∨ p 1724 = false ∨ p 1748 = true := h.block46.clause1484

theorem step1485 (p : Nat → Bool) (h : Constraints p) : p 1662 = false ∨ p 1725 = false ∨ p 1749 = true := h.block46.clause1485

theorem step1486 (p : Nat → Bool) (h : Constraints p) : p 1662 = false ∨ p 1726 = false ∨ p 1750 = true := h.block46.clause1486

theorem step1487 (p : Nat → Bool) (h : Constraints p) : p 1663 = false ∨ p 1721 = false ∨ p 1746 = true := h.block46.clause1487

theorem step1488 (p : Nat → Bool) (h : Constraints p) : p 1663 = false ∨ p 1722 = false ∨ p 1747 = true := h.block46.clause1488

theorem step1489 (p : Nat → Bool) (h : Constraints p) : p 1663 = false ∨ p 1723 = false ∨ p 1748 = true := h.block46.clause1489

theorem step1490 (p : Nat → Bool) (h : Constraints p) : p 1663 = false ∨ p 1724 = false ∨ p 1749 = true := h.block46.clause1490

theorem step1491 (p : Nat → Bool) (h : Constraints p) : p 1663 = false ∨ p 1725 = false ∨ p 1750 = true := h.block46.clause1491

theorem step1492 (p : Nat → Bool) (h : Constraints p) : p 1664 = false ∨ p 1721 = false ∨ p 1747 = true := h.block46.clause1492

theorem step1493 (p : Nat → Bool) (h : Constraints p) : p 1664 = false ∨ p 1722 = false ∨ p 1748 = true := h.block46.clause1493

theorem step1494 (p : Nat → Bool) (h : Constraints p) : p 1664 = false ∨ p 1723 = false ∨ p 1749 = true := h.block46.clause1494

theorem step1495 (p : Nat → Bool) (h : Constraints p) : p 1664 = false ∨ p 1724 = false ∨ p 1750 = true := h.block46.clause1495

theorem step1496 (p : Nat → Bool) (h : Constraints p) : p 1590 = false ∨ p 1750 = false ∨ p 1780 = true := h.block46.clause1496

theorem step1497 (p : Nat → Bool) (h : Constraints p) : p 1591 = false ∨ p 1749 = false ∨ p 1780 = true := h.block46.clause1497

theorem step1498 (p : Nat → Bool) (h : Constraints p) : p 1592 = false ∨ p 1748 = false ∨ p 1780 = true := h.block46.clause1498

theorem step1499 (p : Nat → Bool) (h : Constraints p) : p 1593 = false ∨ p 1747 = false ∨ p 1780 = true := h.block46.clause1499

theorem step1500 (p : Nat → Bool) (h : Constraints p) : p 1594 = false ∨ p 1746 = false ∨ p 1780 = true := h.block46.clause1500

theorem step1501 (p : Nat → Bool) (h : Constraints p) : p 1595 = false ∨ p 1745 = false ∨ p 1780 = true := h.block46.clause1501

theorem step1502 (p : Nat → Bool) (h : Constraints p) : p 1596 = false ∨ p 1744 = false ∨ p 1780 = true := h.block46.clause1502

theorem step1503 (p : Nat → Bool) (h : Constraints p) : p 1597 = false ∨ p 1743 = false ∨ p 1780 = true := h.block46.clause1503

theorem step1504 (p : Nat → Bool) (h : Constraints p) : p 1780 = false := h.block46.clause1504

theorem step1505 (p : Nat → Bool) (h : Constraints p) : p 3 = false ∨ p 4 = false ∨ p 10 = false ∨ p 11 = false := h.block47.clause1505

theorem step1506 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 6 = false ∨ p 8 = false ∨ p 9 = false := h.block47.clause1506

theorem step1507 (p : Nat → Bool) (h : Constraints p) : p 5 = false ∨ p 24 = false ∨ p 60 = false ∨ p 87 = false := h.block47.clause1507

theorem step1508 (p : Nat → Bool) (h : Constraints p) : p 7 = false ∨ p 26 = false ∨ p 61 = false ∨ p 89 = false := h.block47.clause1508

theorem step1509 (p : Nat → Bool) (h : Constraints p) : p 17 = false ∨ p 19 = false ∨ p 73 = false ∨ p 75 = false := h.block47.clause1509

theorem step1510 (p : Nat → Bool) (h : Constraints p) : p 17 = false ∨ p 39 = false ∨ p 73 = false ∨ p 106 = false := h.block47.clause1510

theorem step1511 (p : Nat → Bool) (h : Constraints p) : p 20 = false ∨ p 24 = false ∨ p 80 = false ∨ p 87 = false := h.block47.clause1511

theorem step1512 (p : Nat → Bool) (h : Constraints p) : p 22 = false ∨ p 23 = false ∨ p 85 = false ∨ p 86 = false := h.block47.clause1512

theorem step1513 (p : Nat → Bool) (h : Constraints p) : p 22 = false ∨ p 42 = false ∨ p 85 = false ∨ p 108 = false := h.block47.clause1513

theorem step1514 (p : Nat → Bool) (h : Constraints p) : p 26 = false ∨ p 44 = false ∨ p 89 = false ∨ p 110 = false := h.block47.clause1514

theorem step1515 (p : Nat → Bool) (h : Constraints p) : p 29 = false ∨ p 31 = false ∨ p 93 = false ∨ p 94 = false := h.block47.clause1515

theorem step1516 (p : Nat → Bool) (h : Constraints p) : p 32 = false ∨ p 33 = false ∨ p 35 = false ∨ p 37 = false := h.block47.clause1516

theorem step1517 (p : Nat → Bool) (h : Constraints p) : p 38 = false ∨ p 42 = false ∨ p 43 = false ∨ p 46 = false := h.block47.clause1517

theorem step1518 (p : Nat → Bool) (h : Constraints p) : p 39 = false ∨ p 44 = false ∨ p 106 = false ∨ p 110 = false := h.block47.clause1518

theorem step1519 (p : Nat → Bool) (h : Constraints p) : p 40 = false ∨ p 42 = false ∨ p 45 = false ∨ p 46 = false := h.block47.clause1519

theorem step1520 (p : Nat → Bool) (h : Constraints p) : p 50 = false ∨ p 51 = false ∨ p 52 = false ∨ p 53 = false := h.block47.clause1520

theorem step1521 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 56 = false ∨ p 64 = false ∨ p 65 = false := h.block47.clause1521

theorem step1522 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 56 = false ∨ p 80 = false ∨ p 81 = false := h.block47.clause1522

theorem step1523 (p : Nat → Bool) (h : Constraints p) : p 55 = false ∨ p 60 = false ∨ p 80 = false ∨ p 87 = false := h.block47.clause1523

theorem step1524 (p : Nat → Bool) (h : Constraints p) : p 61 = false ∨ p 63 = false ∨ p 89 = false ∨ p 92 = false := h.block47.clause1524

theorem step1525 (p : Nat → Bool) (h : Constraints p) : p 64 = false ∨ p 65 = false ∨ p 66 = false ∨ p 67 = false := h.block47.clause1525

theorem step1526 (p : Nat → Bool) (h : Constraints p) : p 65 = false ∨ p 67 = false ∨ p 93 = false ∨ p 94 = false := h.block47.clause1526

theorem step1527 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 83 = false ∨ p 87 = false ∨ p 90 = false := h.block47.clause1527

theorem step1528 (p : Nat → Bool) (h : Constraints p) : p 80 = false ∨ p 87 = false ∨ p 103 = false ∨ p 109 = false := h.block47.clause1528

theorem step1529 (p : Nat → Bool) (h : Constraints p) : p 81 = false ∨ p 93 = false ∨ p 104 = false ∨ p 114 = false := h.block47.clause1529

theorem step1530 (p : Nat → Bool) (h : Constraints p) : p 82 = false ∨ p 85 = false ∨ p 88 = false ∨ p 91 = false := h.block47.clause1530

theorem step1531 (p : Nat → Bool) (h : Constraints p) : p 83 = false ∨ p 85 = false ∨ p 90 = false ∨ p 91 = false := h.block47.clause1531

theorem step1532 (p : Nat → Bool) (h : Constraints p) : p 84 = false ∨ p 86 = false ∨ p 96 = false ∨ p 97 = false := h.block47.clause1532

theorem step1533 (p : Nat → Bool) (h : Constraints p) : p 86 = false ∨ p 92 = false ∨ p 97 = false ∨ p 102 = false := h.block47.clause1533

theorem step1534 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 88 = false ∨ p 90 = false ∨ p 91 = false := h.block47.clause1534

theorem step1535 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 88 = false ∨ p 98 = false ∨ p 100 = false := h.block47.clause1535

theorem step1536 (p : Nat → Bool) (h : Constraints p) : p 87 = false ∨ p 98 = false ∨ p 109 = false ∨ p 118 = false := h.block47.clause1536

theorem step1537 (p : Nat → Bool) (h : Constraints p) : p 89 = false ∨ p 92 = false ∨ p 110 = false ∨ p 112 = false := h.block48.clause1537

theorem step1538 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 94 = false ∨ p 96 = false ∨ p 97 = false := h.block48.clause1538

theorem step1539 (p : Nat → Bool) (h : Constraints p) : p 93 = false ∨ p 94 = false ∨ p 114 = false ∨ p 116 = false := h.block48.clause1539

theorem step1540 (p : Nat → Bool) (h : Constraints p) : p 94 = false ∨ p 97 = false ∨ p 101 = false ∨ p 102 = false := h.block48.clause1540

theorem step1541 (p : Nat → Bool) (h : Constraints p) : p 98 = false ∨ p 99 = false ∨ p 100 = false ∨ p 101 = false := h.block48.clause1541

theorem step1542 (p : Nat → Bool) (h : Constraints p) : p 103 = false ∨ p 109 = false ∨ p 113 = false ∨ p 118 = false := h.block48.clause1542

theorem step1543 (p : Nat → Bool) (h : Constraints p) : p 104 = false ∨ p 106 = false ∨ p 114 = false ∨ p 116 = false := h.block48.clause1543

theorem step1544 (p : Nat → Bool) (h : Constraints p) : p 105 = false ∨ p 108 = false ∨ p 115 = false ∨ p 117 = false := h.block48.clause1544

theorem step1545 (p : Nat → Bool) (h : Constraints p) : p 111 = false ∨ p 112 = false ∨ p 120 = false ∨ p 122 = false := h.block48.clause1545

theorem step1546 (p : Nat → Bool) (h : Constraints p) : p 113 = false ∨ p 114 = false ∨ p 115 = false ∨ p 116 = false := h.block48.clause1546

theorem step1547 (p : Nat → Bool) (h : Constraints p) : p 119 = false ∨ p 120 = false ∨ p 121 = false ∨ p 122 = false := h.block48.clause1547

end Dfs112FirstBoolean
