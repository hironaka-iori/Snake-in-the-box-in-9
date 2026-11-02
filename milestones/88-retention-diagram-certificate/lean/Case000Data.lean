import GraphData
import BoxWitness

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Certificate88
open Snake9.Boxes88

def entries000 : List (Box × Witness) := [
([(1,6),(1,6),(1,3),(1,6),(1,3),(1,6)], Witness.short 10 3 false),
([(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)], Witness.short 8 3 false),
([(1,6),(1,6),(1,5),(1,3),(1,5),(1,3)], Witness.interval 2 2 true),
([(1,6),(1,2),(1,6),(1,6),(1,3),(1,6)], Witness.short 9 3 false),
([(1,6),(1,6),(1,3),(1,6),(1,6),(1,2)], Witness.short 9 3 true),
([(1,2),(1,6),(1,6),(1,2),(1,6),(1,6)], Witness.short 5 1 true),
([(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)], Witness.interval 3 0 true),
([(1,6),(1,6),(1,5),(1,5),(1,4),(1,2)], Witness.interval 0 2 true),
([(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)], Witness.short 8 3 true),
([(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)], Witness.interval 0 0 true),
([(1,6),(1,2),(1,4),(1,5),(1,5),(1,6)], Witness.interval 0 1 false),
([(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)], Witness.reference 2 0 false),
([(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)], Witness.reference 3 0 false),
([(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)], Witness.reference 3 4 false),
([(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)], Witness.interval 2 0 true),
([(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)], Witness.reference 3 2 false),
([(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)], Witness.reference 3 3 true),
([(1,6),(1,6),(1,5),(1,2),(1,5),(1,4)], Witness.interval 3 2 true),
([(1,3),(1,2),(1,5),(1,5),(1,6),(1,6)], Witness.interval 6 0 true),
([(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)], Witness.reference 3 4 true),
([(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)], Witness.reference 2 2 false),
([(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)], Witness.reference 2 3 true),
([(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)], Witness.reference 3 0 true),
([(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)], Witness.reference 0 0 false),
([(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)], Witness.reference 1 0 false),
([(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)], Witness.reference 1 0 true),
([(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)], Witness.reference 2 0 true),
([(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)], Witness.reference 3 1 true),
([(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)], Witness.reference 2 4 false),
([(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)], Witness.reference 1 4 true),
([(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)], Witness.reference 2 4 true),
([(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)], Witness.interval 5 0 true),
([(1,6),(1,5),(1,5),(1,2),(1,3),(1,6)], Witness.interval 6 1 false),
([(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)], Witness.reference 2 1 true),
([(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)], Witness.reference 3 3 false),
([(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)], Witness.reference 0 4 false),
([(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)], Witness.reference 1 4 false),
([(1,6),(1,6),(1,4),(1,5),(1,5),(1,2)], Witness.interval 1 2 true),
([(1,6),(1,6),(1,6),(4,4),(6,6),(1,1)], Witness.reference 12 3 true),
([(1,6),(2,2),(1,1),(1,6),(1,6),(1,6)], Witness.reference 1 1 true),
([(1,6),(5,5),(1,1),(5,5),(1,6),(1,6)], Witness.reference 34 1 false),
([(1,6),(5,5),(1,1),(6,6),(1,6),(1,6)], Witness.reference 35 1 false),
([(1,6),(6,6),(1,1),(5,5),(1,6),(1,6)], Witness.reference 35 1 true),
([(1,6),(6,6),(1,1),(6,6),(1,6),(1,6)], Witness.reference 36 1 false),
([(1,2),(1,3),(1,5),(1,4),(1,6),(1,6)], Witness.interval 4 0 true),
([(1,6),(1,6),(1,6),(3,3),(6,6),(1,1)], Witness.reference 11 3 true),
([(1,6),(1,6),(1,6),(5,5),(1,1),(5,5)], Witness.reference 34 3 false),
([(1,6),(1,6),(1,6),(5,5),(1,1),(6,6)], Witness.reference 35 3 false),
([(1,6),(1,6),(1,6),(5,5),(2,2),(3,3)], Witness.reference 29 3 true),
([(1,6),(1,6),(1,6),(6,6),(1,1),(5,5)], Witness.reference 35 3 true),
([(1,6),(1,6),(1,6),(6,6),(1,1),(6,6)], Witness.reference 36 3 false),
([(1,6),(1,6),(1,6),(4,4),(2,2),(3,3)], Witness.reference 28 3 true),
([(1,6),(1,6),(1,6),(4,4),(2,2),(4,4)], Witness.reference 33 3 false),
([(1,6),(1,6),(1,6),(4,4),(3,3),(3,3)], Witness.reference 31 3 true),
([(1,6),(3,3),(2,2),(5,5),(1,6),(1,6)], Witness.reference 29 1 false),
([(1,6),(4,4),(2,2),(4,4),(1,6),(1,6)], Witness.reference 33 1 false),
([(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)], Witness.reference 3 1 false),
([(1,6),(1,6),(1,6),(3,3),(2,2),(4,4)], Witness.reference 28 3 false),
([(1,6),(1,6),(1,6),(3,3),(2,2),(5,5)], Witness.reference 29 3 false),
([(1,6),(1,6),(1,6),(3,3),(3,3),(4,4)], Witness.reference 31 3 false),
([(1,6),(1,6),(1,6),(5,5),(5,5),(1,1)], Witness.reference 8 3 true),
([(1,6),(4,4),(6,6),(1,1),(1,6),(1,6)], Witness.reference 12 1 true),
([(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)], Witness.reference 3 2 true),
([(1,6),(1,6),(1,3),(1,2),(1,5),(1,5)], Witness.interval 6 2 true),
([(1,6),(1,6),(1,6),(4,4),(5,5),(1,1)], Witness.reference 7 3 true),
([(1,6),(4,4),(2,2),(3,3),(1,6),(1,6)], Witness.reference 28 1 true),
([(1,6),(4,4),(3,3),(3,3),(1,6),(1,6)], Witness.reference 31 1 true),
([(1,6),(5,5),(2,2),(3,3),(1,6),(1,6)], Witness.reference 29 1 true),
([(1,4),(1,5),(1,5),(1,2),(1,6),(1,6)], Witness.interval 1 0 true),
([(1,6),(3,3),(2,2),(4,4),(1,6),(1,6)], Witness.reference 28 1 false),
([(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)], Witness.reference 31 1 false),
([(1,6),(1,3),(1,5),(1,3),(1,5),(1,6)], Witness.interval 2 1 false),
([(1,6),(1,1),(2,2),(1,6),(1,6),(1,6)], Witness.reference 1 1 false),
([(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)], Witness.reference 2 1 false),
([(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)], Witness.reference 1 3 true),
([(1,6),(1,6),(1,6),(1,1),(6,6),(4,4)], Witness.reference 12 3 false),
([(1,6),(1,1),(1,1),(1,6),(1,6),(1,6)], Witness.reference 0 1 false),
([(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)], Witness.reference 1 3 false),
([(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)], Witness.reference 2 3 false),
([(1,6),(1,1),(6,6),(3,3),(1,6),(1,6)], Witness.reference 11 1 false),
([(1,6),(1,1),(5,5),(5,5),(1,6),(1,6)], Witness.reference 8 1 false),
([(1,6),(1,1),(6,6),(4,4),(1,6),(1,6)], Witness.reference 12 1 false),
([(1,6),(1,6),(1,6),(3,3),(4,4),(2,2)], Witness.reference 22 3 true),
([(1,6),(1,6),(1,6),(3,3),(4,4),(3,3)], Witness.reference 32 3 false),
([(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)], Witness.reference 6 3 true),
([(1,6),(1,6),(1,6),(3,3),(5,5),(2,2)], Witness.reference 25 3 true),
([(1,6),(1,6),(1,6),(4,4),(4,4),(2,2)], Witness.reference 23 3 true),
([(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)], Witness.reference 1 2 false),
([(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)], Witness.reference 0 3 false),
([(1,1),(5,5),(2,2),(1,6),(1,6),(1,6)], Witness.reference 330 0 false),
([(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)], Witness.reference 331 0 false),
([(1,6),(1,4),(1,5),(1,2),(1,5),(1,6)], Witness.interval 3 1 false),
([(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)], Witness.reference 14 3 true),
([(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)], Witness.reference 27 3 false),
([(1,6),(1,6),(1,6),(3,3),(3,3),(2,2)], Witness.reference 18 3 true),
([(1,6),(1,6),(1,6),(3,3),(3,3),(3,3)], Witness.reference 30 3 false),
([(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)], Witness.reference 15 3 true),
([(1,6),(1,6),(1,6),(4,4),(3,3),(2,2)], Witness.reference 19 3 true),
([(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)], Witness.reference 16 3 true),
([(1,6),(1,6),(1,6),(5,5),(3,3),(2,2)], Witness.reference 20 3 true),
([(1,6),(1,6),(4,4),(5,5),(3,3),(3,3)], Witness.reference 69 2 true),
([(1,6),(1,6),(4,4),(6,6),(2,2),(2,2)], Witness.reference 42 2 true),
([(1,6),(1,6),(5,5),(4,4),(5,5),(2,2)], Witness.reference 53 2 true),
([(1,6),(1,6),(3,3),(5,5),(4,4),(3,3)], Witness.reference 76 2 true),
([(1,6),(1,2),(1,5),(1,5),(1,4),(1,6)], Witness.interval 1 1 false),
([(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)], Witness.reference 16 3 false),
([(1,6),(1,6),(1,6),(2,2),(3,3),(5,5)], Witness.reference 20 3 false),
([(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)], Witness.reference 118 0 true),
([(1,6),(1,6),(4,4),(4,4),(3,3),(4,4)], Witness.reference 94 2 true),
([(1,6),(2,2),(2,2),(6,6),(4,4),(1,6)], Witness.reference 42 1 false),
([(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)], Witness.reference 94 1 false),
([(2,2),(3,3),(4,4),(5,5),(1,6),(1,6)], Witness.reference 117 0 true),
([(1,6),(1,6),(4,4),(3,3),(6,6),(2,2)], Witness.reference 59 2 true),
([(2,2),(4,4),(5,5),(4,4),(1,6),(1,6)], Witness.reference 103 0 true),
([(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)], Witness.reference 1 2 true),
([(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)], Witness.reference 2 2 true),
([(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)], Witness.reference 335 0 false),
([(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)], Witness.reference 336 0 false),
([(2,2),(4,4),(4,4),(4,4),(1,6),(1,6)], Witness.reference 99 0 true),
([(3,3),(3,3),(4,4),(4,4),(1,6),(1,6)], Witness.reference 97 0 true),
([(3,3),(4,4),(4,4),(4,4),(1,6),(1,6)], Witness.reference 100 0 true),
([(4,4),(3,3),(4,4),(4,4),(1,6),(1,6)], Witness.reference 98 0 true),
([(6,6),(1,1),(5,5),(6,6),(1,6),(1,6)], Witness.reference 121 0 true),
([(1,6),(1,6),(2,2),(5,5),(4,4),(3,3)], Witness.reference 75 2 true),
([(1,6),(1,6),(2,2),(5,5),(5,5),(3,3)], Witness.reference 83 2 true),
([(1,6),(1,6),(4,4),(3,3),(4,4),(4,4)], Witness.reference 98 2 true),
([(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)], Witness.reference 0 2 false),
([(1,1),(5,5),(6,6),(3,3),(1,6),(1,6)], Witness.reference 87 0 true),
([(1,6),(2,2),(6,6),(3,3),(4,4),(1,6)], Witness.reference 59 1 false),
([(1,6),(3,3),(3,3),(5,5),(4,4),(1,6)], Witness.reference 69 1 false),
([(1,6),(3,3),(5,5),(5,5),(2,2),(1,6)], Witness.reference 83 1 false),
([(1,6),(1,6),(1,6),(1,1),(5,5),(5,5)], Witness.reference 8 3 false),
([(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)], Witness.reference 104 0 true),
([(2,2),(4,4),(5,5),(3,3),(1,6),(1,6)], Witness.reference 81 0 true),
([(2,2),(5,5),(5,5),(3,3),(1,6),(1,6)], Witness.reference 83 0 true),
([(3,3),(2,2),(6,6),(4,4),(1,6),(1,6)], Witness.reference 105 0 true),
([(3,3),(4,4),(6,6),(2,2),(1,6),(1,6)], Witness.reference 61 0 true),
([(1,6),(1,6),(1,2),(1,3),(1,5),(1,4)], Witness.interval 4 2 true),
([(1,6),(2,2),(2,2),(5,5),(1,6),(1,6)], Witness.reference 16 1 false),
([(1,6),(2,2),(3,3),(5,5),(1,6),(1,6)], Witness.reference 20 1 false),
([(2,2),(2,2),(3,3),(1,6),(1,6),(1,6)], Witness.reference 334 0 false),
([(2,2),(3,3),(2,2),(1,6),(1,6),(1,6)], Witness.reference 337 0 false),
([(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)], Witness.reference 338 0 false),
([(1,1),(6,6),(2,2),(4,4),(1,6),(1,6)], Witness.reference 90 0 true),
([(1,1),(6,6),(4,4),(3,3),(1,6),(1,6)], Witness.reference 77 0 true),
([(1,6),(3,3),(4,4),(5,5),(2,2),(1,6)], Witness.reference 75 1 false),
([(1,6),(3,3),(4,4),(5,5),(3,3),(1,6)], Witness.reference 76 1 false),
([(2,2),(3,3),(3,3),(6,6),(1,6),(1,6)], Witness.reference 120 0 true),
([(2,2),(4,4),(4,4),(3,3),(1,6),(1,6)], Witness.reference 72 0 true),
([(2,2),(5,5),(2,2),(4,4),(1,6),(1,6)], Witness.reference 88 0 true),
([(2,2),(5,5),(3,3),(4,4),(1,6),(1,6)], Witness.reference 95 0 true),
([(2,2),(5,5),(4,4),(3,3),(1,6),(1,6)], Witness.reference 75 0 true),
([(2,2),(6,6),(2,2),(4,4),(1,6),(1,6)], Witness.reference 91 0 true),
([(3,3),(3,3),(2,2),(6,6),(1,6),(1,6)], Witness.reference 119 0 true),
([(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)], Witness.reference 73 0 true),
([(3,3),(5,5),(2,2),(4,4),(1,6),(1,6)], Witness.reference 89 0 true),
([(3,3),(5,5),(4,4),(3,3),(1,6),(1,6)], Witness.reference 76 0 true),
([(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)], Witness.reference 15 3 false),
([(1,6),(1,6),(1,6),(2,2),(3,3),(4,4)], Witness.reference 19 3 false),
([(1,6),(1,6),(1,6),(2,2),(4,4),(4,4)], Witness.reference 23 3 false),
([(1,6),(1,6),(3,3),(3,3),(4,4),(4,4)], Witness.reference 97 2 true),
([(2,2),(4,4),(3,3),(5,5),(1,6),(1,6)], Witness.reference 113 0 true),
([(2,2),(5,5),(3,3),(5,5),(1,6),(1,6)], Witness.reference 114 0 true),
([(1,1),(6,6),(2,2),(5,5),(1,6),(1,6)], Witness.reference 110 0 true),
([(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)], Witness.reference 73 2 true),
([(1,6),(1,6),(3,3),(4,4),(4,4),(4,4)], Witness.reference 100 2 true),
([(2,2),(4,4),(2,2),(5,5),(1,6),(1,6)], Witness.reference 106 0 true),
([(2,2),(5,5),(2,2),(5,5),(1,6),(1,6)], Witness.reference 108 0 true),
([(3,3),(4,4),(2,2),(5,5),(1,6),(1,6)], Witness.reference 107 0 true),
([(3,3),(5,5),(2,2),(5,5),(1,6),(1,6)], Witness.reference 109 0 true),
([(1,6),(1,1),(5,5),(4,4),(1,6),(1,6)], Witness.reference 7 1 false),
([(1,1),(6,6),(3,3),(3,3),(1,6),(1,6)], Witness.reference 70 0 true),
([(2,2),(2,2),(6,6),(3,3),(1,6),(1,6)], Witness.reference 84 0 true),
([(2,2),(5,5),(3,3),(3,3),(1,6),(1,6)], Witness.reference 67 0 true),
([(2,2),(6,6),(3,3),(3,3),(1,6),(1,6)], Witness.reference 71 0 true),
([(3,3),(2,2),(6,6),(3,3),(1,6),(1,6)], Witness.reference 85 0 true),
([(3,3),(5,5),(3,3),(3,3),(1,6),(1,6)], Witness.reference 68 0 true),
([(4,4),(2,2),(6,6),(3,3),(1,6),(1,6)], Witness.reference 86 0 true),
([(4,4),(5,5),(3,3),(3,3),(1,6),(1,6)], Witness.reference 69 0 true),
([(1,6),(1,6),(1,6),(1,1),(5,5),(4,4)], Witness.reference 7 3 false),
([(2,2),(2,2),(2,2),(1,6),(1,6),(1,6)], Witness.reference 333 0 false),
([(3,3),(2,2),(2,2),(1,6),(1,6),(1,6)], Witness.reference 334 0 true),
([(4,4),(2,2),(2,2),(1,6),(1,6),(1,6)], Witness.reference 335 0 true),
([(5,5),(2,2),(2,2),(1,6),(1,6),(1,6)], Witness.reference 336 0 true),
([(1,1),(6,6),(2,2),(3,3),(1,6),(1,6)], Witness.reference 64 0 true),
([(1,6),(1,6),(6,6),(1,1),(5,5),(6,6)], Witness.reference 121 2 true),
([(1,6),(3,3),(5,5),(4,4),(2,2),(1,6)], Witness.reference 81 1 false),
([(1,6),(4,4),(5,5),(4,4),(2,2),(1,6)], Witness.reference 103 1 false),
([(1,6),(6,6),(5,5),(1,1),(6,6),(1,6)], Witness.reference 121 1 false),
([(2,2),(3,3),(3,3),(5,5),(1,6),(1,6)], Witness.reference 111 0 true),
([(2,2),(4,4),(3,3),(4,4),(1,6),(1,6)], Witness.reference 92 0 true),
([(2,2),(6,6),(2,2),(3,3),(1,6),(1,6)], Witness.reference 65 0 true),
([(3,3),(3,3),(3,3),(5,5),(1,6),(1,6)], Witness.reference 112 0 true),
([(3,3),(4,4),(3,3),(4,4),(1,6),(1,6)], Witness.reference 93 0 true),
([(3,3),(6,6),(2,2),(3,3),(1,6),(1,6)], Witness.reference 66 0 true),
([(4,4),(4,4),(3,3),(4,4),(1,6),(1,6)], Witness.reference 94 0 true),
([(1,6),(1,4),(1,5),(1,3),(1,2),(1,6)], Witness.interval 4 1 false),
([(1,6),(1,6),(2,2),(4,4),(4,4),(3,3)], Witness.reference 72 2 true),
([(1,6),(1,6),(2,2),(4,4),(4,4),(4,4)], Witness.reference 99 2 true),
([(1,6),(1,6),(2,2),(4,4),(5,5),(3,3)], Witness.reference 81 2 true),
([(1,6),(1,6),(2,2),(4,4),(5,5),(4,4)], Witness.reference 103 2 true),
([(1,6),(5,5),(5,5),(1,1),(1,6),(1,6)], Witness.reference 8 1 true),
([(1,6),(1,6),(2,2),(2,2),(6,6),(4,4)], Witness.reference 104 2 true),
([(1,6),(1,6),(3,3),(2,2),(6,6),(4,4)], Witness.reference 105 2 true),
([(1,6),(4,4),(4,4),(3,3),(3,3),(1,6)], Witness.reference 97 1 false),
([(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)], Witness.reference 98 1 false),
([(1,6),(4,4),(4,4),(4,4),(2,2),(1,6)], Witness.reference 99 1 false),
([(1,6),(4,4),(4,4),(4,4),(3,3),(1,6)], Witness.reference 100 1 false),
([(4,4),(2,2),(4,4),(5,5),(1,6),(1,6)], Witness.reference 116 0 true),
([(3,3),(2,2),(4,4),(6,6),(5,5),(1,6)], Witness.reference 953 0 false),
([(1,6),(1,1),(5,5),(3,3),(1,6),(1,6)], Witness.reference 6 1 false),
([(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)], Witness.reference 335 2 false),
([(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)], Witness.reference 336 2 false),
([(1,6),(2,2),(4,4),(4,4),(1,6),(1,6)], Witness.reference 23 1 false),
([(1,6),(2,2),(5,5),(3,3),(1,6),(1,6)], Witness.reference 25 1 false),
([(1,6),(1,6),(4,4),(2,2),(4,4),(5,5)], Witness.reference 116 2 true),
([(1,6),(2,2),(6,6),(6,6),(4,4),(2,2)], Witness.reference 201 1 true),
([(1,6),(3,3),(5,5),(6,6),(2,2),(2,2)], Witness.reference 197 1 true),
([(1,6),(3,3),(5,5),(6,6),(3,3),(3,3)], Witness.reference 204 1 true),
([(2,2),(3,3),(4,4),(6,6),(3,3),(1,6)], Witness.reference 894 0 false),
([(2,2),(3,3),(4,4),(6,6),(4,4),(1,6)], Witness.reference 895 0 false),
([(2,2),(3,3),(6,6),(6,6),(2,2),(1,6)], Witness.reference 900 0 false),
([(2,2),(4,4),(4,4),(6,6),(3,3),(1,6)], Witness.reference 909 0 false),
([(2,2),(4,4),(4,4),(6,6),(4,4),(1,6)], Witness.reference 910 0 false),
([(2,2),(4,4),(5,5),(6,6),(2,2),(1,6)], Witness.reference 913 0 false),
([(3,3),(2,2),(4,4),(6,6),(4,4),(1,6)], Witness.reference 952 0 false),
([(3,3),(3,3),(4,4),(6,6),(3,3),(1,6)], Witness.reference 959 0 false),
([(3,3),(3,3),(6,6),(6,6),(2,2),(1,6)], Witness.reference 950 0 true),
([(4,4),(2,2),(4,4),(6,6),(4,4),(1,6)], Witness.reference 985 0 false),
([(4,4),(3,3),(4,4),(6,6),(3,3),(1,6)], Witness.reference 984 0 true),
([(1,6),(1,6),(4,4),(2,2),(2,2),(1,6)], Witness.reference 335 2 true),
([(1,6),(1,6),(5,5),(2,2),(2,2),(1,6)], Witness.reference 336 2 true),
([(1,6),(2,2),(2,2),(3,3),(1,6),(1,6)], Witness.reference 14 1 false),
([(1,6),(2,2),(2,2),(4,4),(1,6),(1,6)], Witness.reference 15 1 false),
([(1,6),(2,2),(3,3),(3,3),(1,6),(1,6)], Witness.reference 18 1 false),
([(1,6),(2,2),(3,3),(4,4),(1,6),(1,6)], Witness.reference 19 1 false),
([(1,6),(2,2),(4,4),(3,3),(1,6),(1,6)], Witness.reference 22 1 false),
([(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)], Witness.reference 27 1 false),
([(1,6),(3,3),(3,3),(3,3),(1,6),(1,6)], Witness.reference 30 1 false),
([(1,6),(3,3),(4,4),(3,3),(1,6),(1,6)], Witness.reference 32 1 false),
([(1,6),(4,4),(5,5),(1,1),(1,6),(1,6)], Witness.reference 7 1 true),
([(1,6),(5,5),(3,3),(2,2),(1,6),(1,6)], Witness.reference 20 1 true),
([(1,6),(2,2),(5,5),(4,4),(5,5),(1,6)], Witness.reference 53 1 false),
([(1,6),(3,3),(4,4),(4,4),(2,2),(1,6)], Witness.reference 72 1 false),
([(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)], Witness.reference 73 1 false),
([(1,1),(5,5),(4,4),(6,6),(2,2),(1,6)], Witness.reference 886 0 false),
([(1,6),(2,2),(4,4),(6,6),(6,6),(2,2)], Witness.reference 201 1 false),
([(1,6),(3,3),(3,3),(6,6),(5,5),(3,3)], Witness.reference 204 1 false),
([(1,6),(3,3),(5,5),(4,4),(3,3),(4,4)], Witness.reference 205 1 false),
([(2,2),(3,3),(4,4),(6,6),(2,2),(1,6)], Witness.reference 893 0 false),
([(2,2),(4,4),(2,2),(6,6),(4,4),(1,6)], Witness.reference 902 0 false),
([(2,2),(4,4),(3,3),(6,6),(4,4),(1,6)], Witness.reference 905 0 false),
([(2,2),(4,4),(4,4),(6,6),(2,2),(1,6)], Witness.reference 908 0 false),
([(2,2),(4,4),(5,5),(5,5),(3,3),(1,6)], Witness.reference 912 0 false),
([(2,2),(5,5),(2,2),(6,6),(4,4),(1,6)], Witness.reference 919 0 false),
([(2,2),(5,5),(2,2),(6,6),(5,5),(1,6)], Witness.reference 920 0 false),
([(2,2),(5,5),(3,3),(6,6),(4,4),(1,6)], Witness.reference 923 0 false),
([(2,2),(5,5),(4,4),(6,6),(2,2),(1,6)], Witness.reference 927 0 false),
([(2,2),(6,6),(2,2),(6,6),(4,4),(1,6)], Witness.reference 934 0 false),
([(2,2),(6,6),(3,3),(4,4),(5,5),(1,6)], Witness.reference 937 0 false),
([(3,3),(3,3),(3,3),(6,6),(4,4),(1,6)], Witness.reference 956 0 false),
([(3,3),(3,3),(4,4),(5,5),(4,4),(1,6)], Witness.reference 957 0 false),
([(3,3),(3,3),(4,4),(5,5),(5,5),(1,6)], Witness.reference 958 0 false),
([(3,3),(3,3),(4,4),(6,6),(2,2),(1,6)], Witness.reference 939 0 true),
([(3,3),(4,4),(2,2),(6,6),(4,4),(1,6)], Witness.reference 962 0 false),
([(3,3),(4,4),(3,3),(5,5),(5,5),(1,6)], Witness.reference 965 0 false),
([(3,3),(4,4),(4,4),(6,6),(2,2),(1,6)], Witness.reference 941 0 true),
([(3,3),(5,5),(3,3),(4,4),(5,5),(1,6)], Witness.reference 970 0 false),
([(4,4),(3,3),(2,2),(6,6),(4,4),(1,6)], Witness.reference 986 0 false),
([(4,4),(3,3),(2,2),(6,6),(5,5),(1,6)], Witness.reference 987 0 false),
([(4,4),(3,3),(3,3),(5,5),(5,5),(1,6)], Witness.reference 988 0 false),
([(4,4),(3,3),(4,4),(6,6),(2,2),(1,6)], Witness.reference 940 0 true),
([(4,4),(3,3),(5,5),(6,6),(2,2),(1,6)], Witness.reference 945 0 true),
([(4,4),(4,4),(2,2),(6,6),(4,4),(1,6)], Witness.reference 991 0 false),
([(5,5),(2,2),(3,3),(6,6),(4,4),(1,6)], Witness.reference 996 0 true),
([(5,5),(3,3),(2,2),(6,6),(4,4),(1,6)], Witness.reference 995 0 true),
([(1,6),(4,4),(4,4),(2,2),(1,6),(1,6)], Witness.reference 23 1 true),
([(1,6),(1,6),(2,2),(3,3),(4,4),(5,5)], Witness.reference 117 2 true),
([(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)], Witness.reference 104 1 false),
([(1,6),(4,4),(6,6),(2,2),(3,3),(1,6)], Witness.reference 105 1 false),
([(1,6),(5,5),(4,4),(3,3),(2,2),(1,6)], Witness.reference 117 1 false),
([(5,5),(4,4),(5,5),(2,2),(1,6),(1,6)], Witness.reference 53 0 true),
([(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)], Witness.reference 898 0 false),
([(2,2),(4,4),(4,4),(5,5),(2,2),(1,6)], Witness.reference 906 0 false),
([(2,2),(4,4),(4,4),(5,5),(3,3),(1,6)], Witness.reference 907 0 false),
([(2,2),(4,4),(5,5),(5,5),(2,2),(1,6)], Witness.reference 911 0 false),
([(2,2),(4,4),(6,6),(3,3),(4,4),(1,6)], Witness.reference 915 0 false),
([(2,2),(5,5),(4,4),(5,5),(2,2),(1,6)], Witness.reference 925 0 false),
([(2,2),(5,5),(4,4),(5,5),(3,3),(1,6)], Witness.reference 926 0 false),
([(2,2),(6,6),(2,2),(5,5),(4,4),(1,6)], Witness.reference 930 0 false),
([(2,2),(6,6),(2,2),(5,5),(5,5),(1,6)], Witness.reference 931 0 false),
([(2,2),(6,6),(4,4),(5,5),(2,2),(1,6)], Witness.reference 927 0 true),
([(2,2),(6,6),(5,5),(3,3),(4,4),(1,6)], Witness.reference 945 0 false),
([(3,3),(4,4),(3,3),(5,5),(4,4),(1,6)], Witness.reference 964 0 false),
([(3,3),(4,4),(4,4),(5,5),(2,2),(1,6)], Witness.reference 924 0 true),
([(3,3),(4,4),(4,4),(5,5),(3,3),(1,6)], Witness.reference 967 0 false),
([(3,3),(5,5),(3,3),(5,5),(4,4),(1,6)], Witness.reference 972 0 false),
([(3,3),(5,5),(4,4),(5,5),(2,2),(1,6)], Witness.reference 926 0 true),
([(3,3),(6,6),(2,2),(5,5),(4,4),(1,6)], Witness.reference 976 0 false),
([(3,3),(6,6),(3,3),(3,3),(5,5),(1,6)], Witness.reference 980 0 false),
([(4,4),(4,4),(2,2),(5,5),(4,4),(1,6)], Witness.reference 989 0 false),
([(4,4),(4,4),(2,2),(5,5),(5,5),(1,6)], Witness.reference 990 0 false),
([(4,4),(5,5),(2,2),(5,5),(4,4),(1,6)], Witness.reference 993 0 false),
([(4,4),(5,5),(2,2),(5,5),(5,5),(1,6)], Witness.reference 994 0 false),
([(5,5),(4,4),(2,2),(5,5),(4,4),(1,6)], Witness.reference 992 0 true),
([(5,5),(4,4),(2,2),(5,5),(5,5),(1,6)], Witness.reference 997 0 false),
([(5,5),(5,5),(2,2),(5,5),(4,4),(1,6)], Witness.reference 994 0 true),
([(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)], Witness.reference 15 1 true),
([(1,6),(4,4),(3,3),(2,2),(1,6),(1,6)], Witness.reference 19 1 true),
([(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)], Witness.reference 16 1 true),
([(3,3),(6,6),(2,2),(2,2),(1,6),(1,6)], Witness.reference 41 0 true),
([(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)], Witness.reference 42 0 true),
([(1,6),(4,4),(3,3),(4,4),(5,5),(3,3)], Witness.reference 205 1 true),
([(2,2),(3,3),(6,6),(3,3),(3,3),(1,6)], Witness.reference 897 0 false),
([(2,2),(3,3),(6,6),(4,4),(2,2),(1,6)], Witness.reference 899 0 false),
([(2,2),(4,4),(6,6),(3,3),(3,3),(1,6)], Witness.reference 914 0 false),
([(2,2),(4,4),(6,6),(4,4),(2,2),(1,6)], Witness.reference 916 0 false),
([(2,2),(5,5),(4,4),(4,4),(2,2),(1,6)], Witness.reference 906 0 true),
([(2,2),(5,5),(4,4),(4,4),(3,3),(1,6)], Witness.reference 924 0 false),
([(2,2),(5,5),(5,5),(4,4),(2,2),(1,6)], Witness.reference 911 0 true),
([(2,2),(6,6),(3,3),(4,4),(4,4),(1,6)], Witness.reference 936 0 false),
([(2,2),(6,6),(4,4),(3,3),(3,3),(1,6)], Witness.reference 939 0 false),
([(2,2),(6,6),(4,4),(3,3),(4,4),(1,6)], Witness.reference 940 0 false),
([(2,2),(6,6),(4,4),(4,4),(2,2),(1,6)], Witness.reference 908 0 true),
([(2,2),(6,6),(4,4),(4,4),(3,3),(1,6)], Witness.reference 941 0 false),
([(2,2),(6,6),(5,5),(4,4),(2,2),(1,6)], Witness.reference 913 0 true),
([(2,2),(6,6),(6,6),(3,3),(3,3),(1,6)], Witness.reference 950 0 false),
([(3,3),(3,3),(6,6),(3,3),(3,3),(1,6)], Witness.reference 960 0 false),
([(3,3),(3,3),(6,6),(4,4),(2,2),(1,6)], Witness.reference 914 0 true),
([(3,3),(5,5),(3,3),(4,4),(4,4),(1,6)], Witness.reference 969 0 false),
([(3,3),(5,5),(4,4),(4,4),(2,2),(1,6)], Witness.reference 907 0 true),
([(3,3),(5,5),(4,4),(4,4),(3,3),(1,6)], Witness.reference 967 0 true),
([(3,3),(5,5),(5,5),(4,4),(2,2),(1,6)], Witness.reference 912 0 true),
([(3,3),(5,5),(6,6),(1,1),(6,6),(1,6)], Witness.reference 974 0 false),
([(3,3),(6,6),(2,2),(4,4),(4,4),(1,6)], Witness.reference 975 0 false),
([(3,3),(6,6),(3,3),(3,3),(4,4),(1,6)], Witness.reference 979 0 false),
([(3,3),(6,6),(3,3),(4,4),(4,4),(1,6)], Witness.reference 981 0 false),
([(3,3),(6,6),(4,4),(2,2),(5,5),(1,6)], Witness.reference 983 0 false),
([(3,3),(6,6),(4,4),(3,3),(3,3),(1,6)], Witness.reference 959 0 true),
([(3,3),(6,6),(4,4),(3,3),(4,4),(1,6)], Witness.reference 984 0 false),
([(3,3),(6,6),(4,4),(4,4),(2,2),(1,6)], Witness.reference 909 0 true),
([(4,4),(3,3),(6,6),(4,4),(2,2),(1,6)], Witness.reference 915 0 true),
([(4,4),(5,5),(2,2),(4,4),(4,4),(1,6)], Witness.reference 989 0 true),
([(4,4),(5,5),(2,2),(4,4),(5,5),(1,6)], Witness.reference 992 0 false),
([(4,4),(5,5),(4,4),(3,3),(3,3),(1,6)], Witness.reference 957 0 true),
([(4,4),(6,6),(2,2),(3,3),(5,5),(1,6)], Witness.reference 995 0 false),
([(4,4),(6,6),(2,2),(4,4),(4,4),(1,6)], Witness.reference 991 0 true),
([(4,4),(6,6),(4,4),(4,4),(2,2),(1,6)], Witness.reference 910 0 true),
([(5,5),(5,5),(2,2),(4,4),(4,4),(1,6)], Witness.reference 990 0 true),
([(5,5),(5,5),(2,2),(4,4),(5,5),(1,6)], Witness.reference 997 0 true),
([(5,5),(5,5),(3,3),(3,3),(4,4),(1,6)], Witness.reference 988 0 true),
([(5,5),(5,5),(4,4),(3,3),(3,3),(1,6)], Witness.reference 958 0 true),
([(1,6),(5,5),(4,4),(2,2),(4,4),(1,6)], Witness.reference 116 1 false),
([(3,3),(6,6),(5,5),(1,1),(1,6),(1,6)], Witness.reference 38 0 true),
([(1,6),(2,2),(2,2),(6,6),(5,5),(3,3)], Witness.reference 197 1 false),
([(2,2),(3,3),(6,6),(3,3),(2,2),(1,6)], Witness.reference 896 0 false),
([(2,2),(4,4),(6,6),(3,3),(2,2),(1,6)], Witness.reference 899 0 true),
([(2,2),(6,6),(4,4),(3,3),(2,2),(1,6)], Witness.reference 893 0 true),
([(2,2),(6,6),(6,6),(3,3),(2,2),(1,6)], Witness.reference 900 0 true),
([(3,3),(3,3),(6,6),(3,3),(2,2),(1,6)], Witness.reference 897 0 true),
([(3,3),(5,5),(6,6),(2,2),(2,2),(1,6)], Witness.reference 891 0 true),
([(3,3),(5,5),(6,6),(2,2),(3,3),(1,6)], Witness.reference 954 0 true),
([(3,3),(6,6),(3,3),(2,2),(4,4),(1,6)], Witness.reference 977 0 false),
([(3,3),(6,6),(3,3),(2,2),(5,5),(1,6)], Witness.reference 978 0 false),
([(3,3),(6,6),(4,4),(2,2),(3,3),(1,6)], Witness.reference 951 0 true),
([(3,3),(6,6),(4,4),(2,2),(4,4),(1,6)], Witness.reference 982 0 false),
([(3,3),(6,6),(4,4),(3,3),(2,2),(1,6)], Witness.reference 894 0 true),
([(4,4),(3,3),(6,6),(3,3),(2,2),(1,6)], Witness.reference 898 0 true),
([(4,4),(6,6),(2,2),(3,3),(4,4),(1,6)], Witness.reference 986 0 true),
([(4,4),(6,6),(3,3),(2,2),(5,5),(1,6)], Witness.reference 996 0 false),
([(4,4),(6,6),(4,4),(2,2),(3,3),(1,6)], Witness.reference 952 0 true),
([(4,4),(6,6),(4,4),(2,2),(4,4),(1,6)], Witness.reference 985 0 true),
([(4,4),(6,6),(4,4),(3,3),(2,2),(1,6)], Witness.reference 895 0 true),
([(5,5),(6,6),(2,2),(3,3),(4,4),(1,6)], Witness.reference 987 0 true),
([(5,5),(6,6),(4,4),(2,2),(3,3),(1,6)], Witness.reference 953 0 true)
]
def boxes000 : List Box := entries000.map Prod.fst
def root000 : Nat := 185
def tree000_0 : CoverTree := CoverTree.reject 23
def tree000_1 : CoverTree := CoverTree.reject 24
def tree000_2 : CoverTree := CoverTree.reject 11
def tree000_3 : CoverTree := CoverTree.reject 12
def tree000_4 : CoverTree := CoverTree.reject 5
def tree000_5 : CoverTree := CoverTree.reject 20
def tree000_6 : CoverTree := CoverTree.reject 15
def tree000_7 : CoverTree := CoverTree.reject 40
def tree000_8 : CoverTree := CoverTree.reject 41
def tree000_9 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_5,tree000_6,tree000_7,tree000_8]
def tree000_10 : CoverTree := CoverTree.reject 89
def tree000_11 : CoverTree := CoverTree.reject 90
def tree000_12 : CoverTree := CoverTree.reject 31
def tree000_13 : CoverTree := CoverTree.reject 107
def tree000_14 : CoverTree := CoverTree.reject 35
def tree000_15 : CoverTree := CoverTree.reject 36
def tree000_16 : CoverTree := CoverTree.reject 28
def tree000_17 : CoverTree := CoverTree.reject 13
def tree000_18 : CoverTree := CoverTree.reject 49
def tree000_19 : CoverTree := CoverTree.reject 50
def tree000_20 : CoverTree := CoverTree.split [tree000_14,tree000_15,tree000_16,tree000_17,tree000_18,tree000_19]
def tree000_21 : CoverTree := CoverTree.reject 245
def tree000_22 : CoverTree := CoverTree.reject 30
def tree000_23 : CoverTree := CoverTree.accept
def tree000_24 : CoverTree := CoverTree.split [tree000_22,tree000_23,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_25 : CoverTree := CoverTree.reject 19
def tree000_26 : CoverTree := CoverTree.split [tree000_25,tree000_23,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_27 : CoverTree := CoverTree.split [tree000_20,tree000_21,tree000_24,tree000_26,tree000_23,tree000_23]
def tree000_28 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_12,tree000_12,tree000_13,tree000_27]
def tree000_29 : CoverTree := CoverTree.reject 7
def tree000_30 : CoverTree := CoverTree.reject 46
def tree000_31 : CoverTree := CoverTree.reject 47
def tree000_32 : CoverTree := CoverTree.split [tree000_29,tree000_29,tree000_16,tree000_17,tree000_30,tree000_31]
def tree000_33 : CoverTree := CoverTree.reject 48
def tree000_34 : CoverTree := CoverTree.split [tree000_29,tree000_29,tree000_33,tree000_23,tree000_23,tree000_23]
def tree000_35 : CoverTree := CoverTree.split [tree000_29,tree000_29,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_36 : CoverTree := CoverTree.reject 60
def tree000_37 : CoverTree := CoverTree.split [tree000_36,tree000_23,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_38 : CoverTree := CoverTree.split [tree000_32,tree000_34,tree000_35,tree000_35,tree000_37,tree000_23]
def tree000_39 : CoverTree := CoverTree.reject 29
def tree000_40 : CoverTree := CoverTree.split [tree000_39,tree000_23,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_41 : CoverTree := CoverTree.split [tree000_20,tree000_40,tree000_24,tree000_26,tree000_23,tree000_23]
def tree000_42 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_12,tree000_12,tree000_38,tree000_41]
def tree000_43 : CoverTree := CoverTree.reject 127
def tree000_44 : CoverTree := CoverTree.reject 16
def tree000_45 : CoverTree := CoverTree.reject 96
def tree000_46 : CoverTree := CoverTree.reject 51
def tree000_47 : CoverTree := CoverTree.reject 52
def tree000_48 : CoverTree := CoverTree.split [tree000_39,tree000_45,tree000_46,tree000_47,tree000_23,tree000_23]
def tree000_49 : CoverTree := CoverTree.reject 97
def tree000_50 : CoverTree := CoverTree.reject 53
def tree000_51 : CoverTree := CoverTree.split [tree000_22,tree000_49,tree000_50,tree000_23,tree000_23,tree000_23]
def tree000_52 : CoverTree := CoverTree.reject 86
def tree000_53 : CoverTree := CoverTree.split [tree000_25,tree000_52,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_54 : CoverTree := CoverTree.reject 64
def tree000_55 : CoverTree := CoverTree.split [tree000_54,tree000_23,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_56 : CoverTree := CoverTree.reject 38
def tree000_57 : CoverTree := CoverTree.split [tree000_56,tree000_23,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_58 : CoverTree := CoverTree.split [tree000_44,tree000_48,tree000_51,tree000_53,tree000_55,tree000_57]
def tree000_59 : CoverTree := CoverTree.split [tree000_14,tree000_15,tree000_16,tree000_17,tree000_30,tree000_31]
def tree000_60 : CoverTree := CoverTree.reject 98
def tree000_61 : CoverTree := CoverTree.split [tree000_39,tree000_60,tree000_33,tree000_23,tree000_23,tree000_23]
def tree000_62 : CoverTree := CoverTree.reject 99
def tree000_63 : CoverTree := CoverTree.split [tree000_22,tree000_62,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_64 : CoverTree := CoverTree.split [tree000_59,tree000_61,tree000_63,tree000_26,tree000_37,tree000_23]
def tree000_65 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_43,tree000_58,tree000_64,tree000_41]
def tree000_66 : CoverTree := CoverTree.split [tree000_9,tree000_10,tree000_11,tree000_28,tree000_42,tree000_65]
def tree000_67 : CoverTree := CoverTree.reject 42
def tree000_68 : CoverTree := CoverTree.reject 43
def tree000_69 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_5,tree000_6,tree000_67,tree000_68]
def tree000_70 : CoverTree := CoverTree.reject 184
def tree000_71 : CoverTree := CoverTree.reject 143
def tree000_72 : CoverTree := CoverTree.reject 163
def tree000_73 : CoverTree := CoverTree.reject 0
def tree000_74 : CoverTree := CoverTree.reject 4
def tree000_75 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_76 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_75,tree000_75,tree000_75]
def tree000_77 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_70,tree000_71,tree000_72,tree000_76]
def tree000_78 : CoverTree := CoverTree.reject 171
def tree000_79 : CoverTree := CoverTree.reject 164
def tree000_80 : CoverTree := CoverTree.reject 165
def tree000_81 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_79,tree000_80,tree000_23,tree000_23]
def tree000_82 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_81,tree000_75,tree000_75]
def tree000_83 : CoverTree := CoverTree.reject 103
def tree000_84 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_83,tree000_23,tree000_23,tree000_23]
def tree000_85 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_84,tree000_75,tree000_75]
def tree000_86 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_78,tree000_82,tree000_85,tree000_76]
def tree000_87 : CoverTree := CoverTree.reject 144
def tree000_88 : CoverTree := CoverTree.split [tree000_29,tree000_29,tree000_46,tree000_47,tree000_23,tree000_23]
def tree000_89 : CoverTree := CoverTree.reject 108
def tree000_90 : CoverTree := CoverTree.split [tree000_29,tree000_29,tree000_50,tree000_89,tree000_23,tree000_23]
def tree000_91 : CoverTree := CoverTree.reject 37
def tree000_92 : CoverTree := CoverTree.split [tree000_91,tree000_91,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_93 : CoverTree := CoverTree.split [tree000_44,tree000_88,tree000_90,tree000_35,tree000_92,tree000_57]
def tree000_94 : CoverTree := CoverTree.reject 100
def tree000_95 : CoverTree := CoverTree.split [tree000_29,tree000_29,tree000_94,tree000_23,tree000_23,tree000_23]
def tree000_96 : CoverTree := CoverTree.split [tree000_32,tree000_34,tree000_95,tree000_35,tree000_92,tree000_23]
def tree000_97 : CoverTree := CoverTree.reject 101
def tree000_98 : CoverTree := CoverTree.split [tree000_39,tree000_97,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_99 : CoverTree := CoverTree.split [tree000_20,tree000_98,tree000_24,tree000_26,tree000_23,tree000_23]
def tree000_100 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_87,tree000_93,tree000_96,tree000_99]
def tree000_101 : CoverTree := CoverTree.reject 21
def tree000_102 : CoverTree := CoverTree.reject 2
def tree000_103 : CoverTree := CoverTree.reject 57
def tree000_104 : CoverTree := CoverTree.reject 58
def tree000_105 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_103,tree000_104,tree000_23]
def tree000_106 : CoverTree := CoverTree.reject 59
def tree000_107 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_106,tree000_23,tree000_23]
def tree000_108 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_23,tree000_23,tree000_23]
def tree000_109 : CoverTree := CoverTree.reject 45
def tree000_110 : CoverTree := CoverTree.split [tree000_109,tree000_23,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_111 : CoverTree := CoverTree.split [tree000_101,tree000_105,tree000_107,tree000_108,tree000_108,tree000_110]
def tree000_112 : CoverTree := CoverTree.split [tree000_29,tree000_29,tree000_50,tree000_23,tree000_23,tree000_23]
def tree000_113 : CoverTree := CoverTree.reject 102
def tree000_114 : CoverTree := CoverTree.split [tree000_54,tree000_113,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_115 : CoverTree := CoverTree.split [tree000_44,tree000_88,tree000_112,tree000_35,tree000_114,tree000_57]
def tree000_116 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_111,tree000_115,tree000_38,tree000_41]
def tree000_117 : CoverTree := CoverTree.reject 92
def tree000_118 : CoverTree := CoverTree.reject 93
def tree000_119 : CoverTree := CoverTree.split [tree000_39,tree000_117,tree000_118,tree000_103,tree000_104,tree000_23]
def tree000_120 : CoverTree := CoverTree.reject 94
def tree000_121 : CoverTree := CoverTree.reject 95
def tree000_122 : CoverTree := CoverTree.split [tree000_22,tree000_120,tree000_121,tree000_106,tree000_23,tree000_23]
def tree000_123 : CoverTree := CoverTree.reject 82
def tree000_124 : CoverTree := CoverTree.reject 83
def tree000_125 : CoverTree := CoverTree.split [tree000_25,tree000_123,tree000_124,tree000_23,tree000_23,tree000_23]
def tree000_126 : CoverTree := CoverTree.reject 84
def tree000_127 : CoverTree := CoverTree.reject 85
def tree000_128 : CoverTree := CoverTree.split [tree000_126,tree000_127,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_129 : CoverTree := CoverTree.split [tree000_101,tree000_119,tree000_122,tree000_125,tree000_128,tree000_110]
def tree000_130 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_129,tree000_58,tree000_64,tree000_41]
def tree000_131 : CoverTree := CoverTree.split [tree000_69,tree000_77,tree000_86,tree000_100,tree000_116,tree000_130]
def tree000_132 : CoverTree := CoverTree.split [tree000_0,tree000_1,tree000_2,tree000_3,tree000_66,tree000_131]
def tree000_133 : CoverTree := CoverTree.reject 25
def tree000_134 : CoverTree := CoverTree.reject 39
def tree000_135 : CoverTree := CoverTree.reject 180
def tree000_136 : CoverTree := CoverTree.reject 140
def tree000_137 : CoverTree := CoverTree.reject 116
def tree000_138 : CoverTree := CoverTree.reject 117
def tree000_139 : CoverTree := CoverTree.reject 1
def tree000_140 : CoverTree := CoverTree.reject 172
def tree000_141 : CoverTree := CoverTree.reject 132
def tree000_142 : CoverTree := CoverTree.reject 3
def tree000_143 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_26,tree000_37,tree000_23]
def tree000_144 : CoverTree := CoverTree.reject 216
def tree000_145 : CoverTree := CoverTree.split [tree000_25,tree000_144,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_146 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_145,tree000_23,tree000_23]
def tree000_147 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_140,tree000_141,tree000_143,tree000_146]
def tree000_148 : CoverTree := CoverTree.split [tree000_134,tree000_135,tree000_136,tree000_137,tree000_138,tree000_147]
def tree000_149 : CoverTree := CoverTree.reject 33
def tree000_150 : CoverTree := CoverTree.reject 141
def tree000_151 : CoverTree := CoverTree.reject 14
def tree000_152 : CoverTree := CoverTree.reject 44
def tree000_153 : CoverTree := CoverTree.reject 189
def tree000_154 : CoverTree := CoverTree.reject 147
def tree000_155 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_152,tree000_153,tree000_154]
def tree000_156 : CoverTree := CoverTree.reject 111
def tree000_157 : CoverTree := CoverTree.reject 249
def tree000_158 : CoverTree := CoverTree.reject 219
def tree000_159 : CoverTree := CoverTree.reject 220
def tree000_160 : CoverTree := CoverTree.split [tree000_20,tree000_157,tree000_158,tree000_159,tree000_23,tree000_23]
def tree000_161 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_152,tree000_156,tree000_160]
def tree000_162 : CoverTree := CoverTree.reject 130
def tree000_163 : CoverTree := CoverTree.split [tree000_32,tree000_162,tree000_35,tree000_35,tree000_37,tree000_23]
def tree000_164 : CoverTree := CoverTree.reject 217
def tree000_165 : CoverTree := CoverTree.split [tree000_39,tree000_164,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_166 : CoverTree := CoverTree.reject 218
def tree000_167 : CoverTree := CoverTree.split [tree000_22,tree000_23,tree000_166,tree000_23,tree000_23,tree000_23]
def tree000_168 : CoverTree := CoverTree.split [tree000_20,tree000_165,tree000_167,tree000_26,tree000_23,tree000_23]
def tree000_169 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_152,tree000_163,tree000_168]
def tree000_170 : CoverTree := CoverTree.reject 355
def tree000_171 : CoverTree := CoverTree.reject 313
def tree000_172 : CoverTree := CoverTree.reject 282
def tree000_173 : CoverTree := CoverTree.split [tree000_101,tree000_170,tree000_171,tree000_172,tree000_128,tree000_110]
def tree000_174 : CoverTree := CoverTree.reject 314
def tree000_175 : CoverTree := CoverTree.split [tree000_44,tree000_174,tree000_51,tree000_53,tree000_55,tree000_57]
def tree000_176 : CoverTree := CoverTree.reject 221
def tree000_177 : CoverTree := CoverTree.split [tree000_20,tree000_176,tree000_24,tree000_26,tree000_23,tree000_23]
def tree000_178 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_173,tree000_175,tree000_64,tree000_177]
def tree000_179 : CoverTree := CoverTree.split [tree000_149,tree000_150,tree000_155,tree000_161,tree000_169,tree000_178]
def tree000_180 : CoverTree := CoverTree.reject 27
def tree000_181 : CoverTree := CoverTree.reject 65
def tree000_182 : CoverTree := CoverTree.reject 55
def tree000_183 : CoverTree := CoverTree.reject 166
def tree000_184 : CoverTree := CoverTree.reject 250
def tree000_185 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_184,tree000_75,tree000_75]
def tree000_186 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_181,tree000_182,tree000_183,tree000_185]
def tree000_187 : CoverTree := CoverTree.reject 66
def tree000_188 : CoverTree := CoverTree.reject 190
def tree000_189 : CoverTree := CoverTree.reject 161
def tree000_190 : CoverTree := CoverTree.reject 251
def tree000_191 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_190,tree000_75,tree000_75]
def tree000_192 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_187,tree000_188,tree000_189,tree000_191]
def tree000_193 : CoverTree := CoverTree.reject 148
def tree000_194 : CoverTree := CoverTree.reject 118
def tree000_195 : CoverTree := CoverTree.reject 283
def tree000_196 : CoverTree := CoverTree.reject 284
def tree000_197 : CoverTree := CoverTree.split [tree000_32,tree000_195,tree000_196,tree000_35,tree000_92,tree000_23]
def tree000_198 : CoverTree := CoverTree.reject 252
def tree000_199 : CoverTree := CoverTree.reject 222
def tree000_200 : CoverTree := CoverTree.reject 223
def tree000_201 : CoverTree := CoverTree.split [tree000_20,tree000_198,tree000_199,tree000_200,tree000_23,tree000_23]
def tree000_202 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_193,tree000_194,tree000_197,tree000_201]
def tree000_203 : CoverTree := CoverTree.reject 133
def tree000_204 : CoverTree := CoverTree.reject 113
def tree000_205 : CoverTree := CoverTree.reject 285
def tree000_206 : CoverTree := CoverTree.reject 253
def tree000_207 : CoverTree := CoverTree.split [tree000_32,tree000_205,tree000_206,tree000_35,tree000_37,tree000_23]
def tree000_208 : CoverTree := CoverTree.reject 224
def tree000_209 : CoverTree := CoverTree.split [tree000_20,tree000_208,tree000_24,tree000_26,tree000_23,tree000_23]
def tree000_210 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_203,tree000_204,tree000_207,tree000_209]
def tree000_211 : CoverTree := CoverTree.reject 356
def tree000_212 : CoverTree := CoverTree.reject 315
def tree000_213 : CoverTree := CoverTree.reject 286
def tree000_214 : CoverTree := CoverTree.split [tree000_101,tree000_211,tree000_212,tree000_213,tree000_128,tree000_110]
def tree000_215 : CoverTree := CoverTree.reject 316
def tree000_216 : CoverTree := CoverTree.split [tree000_44,tree000_215,tree000_51,tree000_53,tree000_55,tree000_57]
def tree000_217 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_214,tree000_216,tree000_64,tree000_41]
def tree000_218 : CoverTree := CoverTree.split [tree000_180,tree000_186,tree000_192,tree000_202,tree000_210,tree000_217]
def tree000_219 : CoverTree := CoverTree.reject 67
def tree000_220 : CoverTree := CoverTree.reject 149
def tree000_221 : CoverTree := CoverTree.reject 167
def tree000_222 : CoverTree := CoverTree.reject 254
def tree000_223 : CoverTree := CoverTree.reject 255
def tree000_224 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_222,tree000_223,tree000_75]
def tree000_225 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_219,tree000_220,tree000_221,tree000_224]
def tree000_226 : CoverTree := CoverTree.reject 173
def tree000_227 : CoverTree := CoverTree.reject 150
def tree000_228 : CoverTree := CoverTree.reject 162
def tree000_229 : CoverTree := CoverTree.reject 256
def tree000_230 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_229,tree000_75,tree000_75]
def tree000_231 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_226,tree000_227,tree000_228,tree000_230]
def tree000_232 : CoverTree := CoverTree.reject 151
def tree000_233 : CoverTree := CoverTree.reject 317
def tree000_234 : CoverTree := CoverTree.reject 318
def tree000_235 : CoverTree := CoverTree.split [tree000_44,tree000_233,tree000_234,tree000_35,tree000_92,tree000_57]
def tree000_236 : CoverTree := CoverTree.reject 287
def tree000_237 : CoverTree := CoverTree.reject 288
def tree000_238 : CoverTree := CoverTree.split [tree000_32,tree000_236,tree000_237,tree000_35,tree000_92,tree000_23]
def tree000_239 : CoverTree := CoverTree.reject 257
def tree000_240 : CoverTree := CoverTree.split [tree000_20,tree000_239,tree000_24,tree000_26,tree000_23,tree000_23]
def tree000_241 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_232,tree000_235,tree000_238,tree000_240]
def tree000_242 : CoverTree := CoverTree.reject 134
def tree000_243 : CoverTree := CoverTree.reject 319
def tree000_244 : CoverTree := CoverTree.split [tree000_44,tree000_243,tree000_112,tree000_35,tree000_114,tree000_57]
def tree000_245 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_242,tree000_244,tree000_38,tree000_41]
def tree000_246 : CoverTree := CoverTree.split [tree000_9,tree000_225,tree000_231,tree000_241,tree000_245,tree000_130]
def tree000_247 : CoverTree := CoverTree.reject 191
def tree000_248 : CoverTree := CoverTree.reject 152
def tree000_249 : CoverTree := CoverTree.reject 289
def tree000_250 : CoverTree := CoverTree.reject 290
def tree000_251 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_249,tree000_250,tree000_75]
def tree000_252 : CoverTree := CoverTree.reject 258
def tree000_253 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_252,tree000_75,tree000_75]
def tree000_254 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_247,tree000_248,tree000_251,tree000_253]
def tree000_255 : CoverTree := CoverTree.reject 174
def tree000_256 : CoverTree := CoverTree.reject 320
def tree000_257 : CoverTree := CoverTree.reject 259
def tree000_258 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_256,tree000_257,tree000_75]
def tree000_259 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_255,tree000_258,tree000_85,tree000_76]
def tree000_260 : CoverTree := CoverTree.reject 357
def tree000_261 : CoverTree := CoverTree.reject 321
def tree000_262 : CoverTree := CoverTree.reject 322
def tree000_263 : CoverTree := CoverTree.reject 112
def tree000_264 : CoverTree := CoverTree.split [tree000_109,tree000_263,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_265 : CoverTree := CoverTree.split [tree000_101,tree000_260,tree000_261,tree000_262,tree000_108,tree000_264]
def tree000_266 : CoverTree := CoverTree.reject 323
def tree000_267 : CoverTree := CoverTree.reject 324
def tree000_268 : CoverTree := CoverTree.split [tree000_44,tree000_266,tree000_267,tree000_35,tree000_92,tree000_57]
def tree000_269 : CoverTree := CoverTree.reject 291
def tree000_270 : CoverTree := CoverTree.split [tree000_32,tree000_269,tree000_95,tree000_35,tree000_92,tree000_23]
def tree000_271 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_265,tree000_268,tree000_270,tree000_99]
def tree000_272 : CoverTree := CoverTree.reject 292
def tree000_273 : CoverTree := CoverTree.split [tree000_101,tree000_105,tree000_107,tree000_272,tree000_108,tree000_110]
def tree000_274 : CoverTree := CoverTree.reject 325
def tree000_275 : CoverTree := CoverTree.split [tree000_44,tree000_274,tree000_112,tree000_35,tree000_114,tree000_57]
def tree000_276 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_273,tree000_275,tree000_38,tree000_41]
def tree000_277 : CoverTree := CoverTree.reject 358
def tree000_278 : CoverTree := CoverTree.reject 326
def tree000_279 : CoverTree := CoverTree.split [tree000_101,tree000_277,tree000_278,tree000_125,tree000_128,tree000_110]
def tree000_280 : CoverTree := CoverTree.split [tree000_4,tree000_4,tree000_279,tree000_58,tree000_64,tree000_41]
def tree000_281 : CoverTree := CoverTree.split [tree000_69,tree000_254,tree000_259,tree000_271,tree000_276,tree000_280]
def tree000_282 : CoverTree := CoverTree.split [tree000_133,tree000_148,tree000_179,tree000_218,tree000_246,tree000_281]
def tree000_283 : CoverTree := CoverTree.reject 26
def tree000_284 : CoverTree := CoverTree.reject 181
def tree000_285 : CoverTree := CoverTree.reject 142
def tree000_286 : CoverTree := CoverTree.reject 6
def tree000_287 : CoverTree := CoverTree.reject 18
def tree000_288 : CoverTree := CoverTree.reject 225
def tree000_289 : CoverTree := CoverTree.reject 209
def tree000_290 : CoverTree := CoverTree.reject 246
def tree000_291 : CoverTree := CoverTree.split [tree000_23,tree000_290,tree000_23,tree000_23,tree000_23,tree000_23]
def tree000_292 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_288,tree000_289,tree000_291]
def tree000_293 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_286,tree000_286,tree000_287,tree000_292]
def tree000_294 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_26,tree000_23,tree000_23]
def tree000_295 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_286,tree000_286,tree000_287,tree000_294]
def tree000_296 : CoverTree := CoverTree.reject 175
def tree000_297 : CoverTree := CoverTree.reject 135
def tree000_298 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_296,tree000_297,tree000_143,tree000_146]
def tree000_299 : CoverTree := CoverTree.split [tree000_134,tree000_284,tree000_285,tree000_293,tree000_295,tree000_298]
def tree000_300 : CoverTree := CoverTree.reject 69
def tree000_301 : CoverTree := CoverTree.reject 54
def tree000_302 : CoverTree := CoverTree.reject 153
def tree000_303 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_300,tree000_301,tree000_302]
def tree000_304 : CoverTree := CoverTree.reject 70
def tree000_305 : CoverTree := CoverTree.reject 192
def tree000_306 : CoverTree := CoverTree.reject 260
def tree000_307 : CoverTree := CoverTree.reject 247
def tree000_308 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_307,tree000_23,tree000_23,tree000_23]
def tree000_309 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_306,tree000_308,tree000_75]
def tree000_310 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_304,tree000_305,tree000_309]
def tree000_311 : CoverTree := CoverTree.reject 119
def tree000_312 : CoverTree := CoverTree.reject 145
def tree000_313 : CoverTree := CoverTree.reject 146
def tree000_314 : CoverTree := CoverTree.reject 261
def tree000_315 : CoverTree := CoverTree.reject 262
def tree000_316 : CoverTree := CoverTree.split [tree000_32,tree000_312,tree000_313,tree000_314,tree000_315,tree000_23]
def tree000_317 : CoverTree := CoverTree.reject 263
def tree000_318 : CoverTree := CoverTree.reject 226
def tree000_319 : CoverTree := CoverTree.split [tree000_20,tree000_317,tree000_318,tree000_26,tree000_23,tree000_23]
def tree000_320 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_311,tree000_316,tree000_319]
def tree000_321 : CoverTree := CoverTree.reject 186
def tree000_322 : CoverTree := CoverTree.reject 248
def tree000_323 : CoverTree := CoverTree.split [tree000_29,tree000_29,tree000_50,tree000_322,tree000_23,tree000_23]
def tree000_324 : CoverTree := CoverTree.split [tree000_44,tree000_321,tree000_323,tree000_35,tree000_114,tree000_57]
def tree000_325 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_324,tree000_163,tree000_168]
def tree000_326 : CoverTree := CoverTree.reject 359
def tree000_327 : CoverTree := CoverTree.reject 327
def tree000_328 : CoverTree := CoverTree.split [tree000_101,tree000_326,tree000_327,tree000_125,tree000_128,tree000_110]
def tree000_329 : CoverTree := CoverTree.reject 328
def tree000_330 : CoverTree := CoverTree.split [tree000_44,tree000_329,tree000_51,tree000_53,tree000_55,tree000_57]
def tree000_331 : CoverTree := CoverTree.reject 227
def tree000_332 : CoverTree := CoverTree.split [tree000_20,tree000_331,tree000_24,tree000_26,tree000_23,tree000_23]
def tree000_333 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_328,tree000_330,tree000_64,tree000_332]
def tree000_334 : CoverTree := CoverTree.split [tree000_149,tree000_303,tree000_310,tree000_320,tree000_325,tree000_333]
def tree000_335 : CoverTree := CoverTree.reject 9
def tree000_336 : CoverTree := CoverTree.reject 168
def tree000_337 : CoverTree := CoverTree.reject 264
def tree000_338 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_337,tree000_75,tree000_75]
def tree000_339 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_181,tree000_182,tree000_336,tree000_338]
def tree000_340 : CoverTree := CoverTree.reject 193
def tree000_341 : CoverTree := CoverTree.reject 293
def tree000_342 : CoverTree := CoverTree.reject 265
def tree000_343 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_341,tree000_342,tree000_75]
def tree000_344 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_187,tree000_340,tree000_343,tree000_76]
def tree000_345 : CoverTree := CoverTree.reject 154
def tree000_346 : CoverTree := CoverTree.reject 120
def tree000_347 : CoverTree := CoverTree.reject 294
def tree000_348 : CoverTree := CoverTree.reject 295
def tree000_349 : CoverTree := CoverTree.split [tree000_32,tree000_347,tree000_348,tree000_35,tree000_92,tree000_23]
def tree000_350 : CoverTree := CoverTree.reject 266
def tree000_351 : CoverTree := CoverTree.split [tree000_20,tree000_350,tree000_24,tree000_26,tree000_23,tree000_23]
def tree000_352 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_345,tree000_346,tree000_349,tree000_351]
def tree000_353 : CoverTree := CoverTree.reject 68
def tree000_354 : CoverTree := CoverTree.reject 196
def tree000_355 : CoverTree := CoverTree.split [tree000_101,tree000_354,tree000_107,tree000_108,tree000_108,tree000_110]
def tree000_356 : CoverTree := CoverTree.reject 187
def tree000_357 : CoverTree := CoverTree.split [tree000_44,tree000_356,tree000_112,tree000_35,tree000_114,tree000_57]
def tree000_358 : CoverTree := CoverTree.split [tree000_353,tree000_353,tree000_355,tree000_357,tree000_38,tree000_41]
def tree000_359 : CoverTree := CoverTree.reject 61
def tree000_360 : CoverTree := CoverTree.reject 136
def tree000_361 : CoverTree := CoverTree.split [tree000_359,tree000_360,tree000_129,tree000_58,tree000_64,tree000_41]
def tree000_362 : CoverTree := CoverTree.split [tree000_180,tree000_339,tree000_344,tree000_352,tree000_358,tree000_361]
def tree000_363 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_5,tree000_6,tree000_7,tree000_8]
def tree000_364 : CoverTree := CoverTree.reject 155
def tree000_365 : CoverTree := CoverTree.reject 169
def tree000_366 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_219,tree000_364,tree000_365,tree000_76]
def tree000_367 : CoverTree := CoverTree.reject 176
def tree000_368 : CoverTree := CoverTree.reject 329
def tree000_369 : CoverTree := CoverTree.reject 267
def tree000_370 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_368,tree000_369,tree000_75]
def tree000_371 : CoverTree := CoverTree.reject 296
def tree000_372 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_371,tree000_75,tree000_75]
def tree000_373 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_367,tree000_370,tree000_372,tree000_76]
def tree000_374 : CoverTree := CoverTree.reject 156
def tree000_375 : CoverTree := CoverTree.reject 330
def tree000_376 : CoverTree := CoverTree.reject 331
def tree000_377 : CoverTree := CoverTree.split [tree000_44,tree000_375,tree000_376,tree000_35,tree000_92,tree000_57]
def tree000_378 : CoverTree := CoverTree.reject 297
def tree000_379 : CoverTree := CoverTree.split [tree000_32,tree000_378,tree000_95,tree000_35,tree000_92,tree000_23]
def tree000_380 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_374,tree000_377,tree000_379,tree000_99]
def tree000_381 : CoverTree := CoverTree.reject 332
def tree000_382 : CoverTree := CoverTree.split [tree000_44,tree000_381,tree000_112,tree000_35,tree000_114,tree000_57]
def tree000_383 : CoverTree := CoverTree.split [tree000_353,tree000_353,tree000_111,tree000_382,tree000_38,tree000_41]
def tree000_384 : CoverTree := CoverTree.reject 88
def tree000_385 : CoverTree := CoverTree.reject 77
def tree000_386 : CoverTree := CoverTree.reject 78
def tree000_387 : CoverTree := CoverTree.reject 34
def tree000_388 : CoverTree := CoverTree.reject 8
def tree000_389 : CoverTree := CoverTree.reject 179
def tree000_390 : CoverTree := CoverTree.reject 131
def tree000_391 : CoverTree := CoverTree.reject 185
def tree000_392 : CoverTree := CoverTree.split [tree000_388,tree000_388,tree000_388,tree000_389,tree000_390,tree000_391]
def tree000_393 : CoverTree := CoverTree.reject 333
def tree000_394 : CoverTree := CoverTree.split [tree000_384,tree000_385,tree000_386,tree000_387,tree000_392,tree000_393]
def tree000_395 : CoverTree := CoverTree.reject 74
def tree000_396 : CoverTree := CoverTree.reject 360
def tree000_397 : CoverTree := CoverTree.reject 361
def tree000_398 : CoverTree := CoverTree.reject 159
def tree000_399 : CoverTree := CoverTree.split [tree000_388,tree000_388,tree000_388,tree000_398,tree000_23,tree000_23]
def tree000_400 : CoverTree := CoverTree.split [tree000_388,tree000_388,tree000_388,tree000_23,tree000_23,tree000_23]
def tree000_401 : CoverTree := CoverTree.split [tree000_395,tree000_396,tree000_397,tree000_399,tree000_400,tree000_400]
def tree000_402 : CoverTree := CoverTree.split [tree000_394,tree000_401,tree000_129,tree000_58,tree000_64,tree000_41]
def tree000_403 : CoverTree := CoverTree.split [tree000_363,tree000_366,tree000_373,tree000_380,tree000_383,tree000_402]
def tree000_404 : CoverTree := CoverTree.reject 126
def tree000_405 : CoverTree := CoverTree.reject 87
def tree000_406 : CoverTree := CoverTree.split [tree000_404,tree000_405,tree000_5,tree000_6,tree000_67,tree000_68]
def tree000_407 : CoverTree := CoverTree.reject 114
def tree000_408 : CoverTree := CoverTree.reject 310
def tree000_409 : CoverTree := CoverTree.reject 194
def tree000_410 : CoverTree := CoverTree.reject 334
def tree000_411 : CoverTree := CoverTree.reject 199
def tree000_412 : CoverTree := CoverTree.reject 200
def tree000_413 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_411,tree000_412,tree000_23,tree000_23]
def tree000_414 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_410,tree000_413,tree000_75]
def tree000_415 : CoverTree := CoverTree.reject 298
def tree000_416 : CoverTree := CoverTree.reject 124
def tree000_417 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_416,tree000_23,tree000_23,tree000_23]
def tree000_418 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_415,tree000_417,tree000_75]
def tree000_419 : CoverTree := CoverTree.split [tree000_407,tree000_408,tree000_409,tree000_414,tree000_418,tree000_76]
def tree000_420 : CoverTree := CoverTree.reject 115
def tree000_421 : CoverTree := CoverTree.reject 362
def tree000_422 : CoverTree := CoverTree.reject 363
def tree000_423 : CoverTree := CoverTree.reject 203
def tree000_424 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_388,tree000_423,tree000_23,tree000_23]
def tree000_425 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_421,tree000_422,tree000_424]
def tree000_426 : CoverTree := CoverTree.reject 335
def tree000_427 : CoverTree := CoverTree.reject 299
def tree000_428 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_426,tree000_427,tree000_75]
def tree000_429 : CoverTree := CoverTree.reject 336
def tree000_430 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_429,tree000_75,tree000_75]
def tree000_431 : CoverTree := CoverTree.split [tree000_420,tree000_425,tree000_428,tree000_430,tree000_85,tree000_76]
def tree000_432 : CoverTree := CoverTree.reject 62
def tree000_433 : CoverTree := CoverTree.reject 230
def tree000_434 : CoverTree := CoverTree.reject 364
def tree000_435 : CoverTree := CoverTree.reject 365
def tree000_436 : CoverTree := CoverTree.reject 337
def tree000_437 : CoverTree := CoverTree.split [tree000_395,tree000_433,tree000_434,tree000_435,tree000_436,tree000_400]
def tree000_438 : CoverTree := CoverTree.reject 366
def tree000_439 : CoverTree := CoverTree.reject 338
def tree000_440 : CoverTree := CoverTree.reject 339
def tree000_441 : CoverTree := CoverTree.split [tree000_101,tree000_438,tree000_439,tree000_440,tree000_108,tree000_264]
def tree000_442 : CoverTree := CoverTree.reject 340
def tree000_443 : CoverTree := CoverTree.split [tree000_44,tree000_442,tree000_90,tree000_35,tree000_92,tree000_57]
def tree000_444 : CoverTree := CoverTree.split [tree000_432,tree000_437,tree000_441,tree000_443,tree000_96,tree000_99]
def tree000_445 : CoverTree := CoverTree.reject 353
def tree000_446 : CoverTree := CoverTree.reject 231
def tree000_447 : CoverTree := CoverTree.reject 17
def tree000_448 : CoverTree := CoverTree.reject 106
def tree000_449 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_447,tree000_448,tree000_23]
def tree000_450 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_447,tree000_23,tree000_23]
def tree000_451 : CoverTree := CoverTree.split [tree000_395,tree000_446,tree000_449,tree000_450,tree000_450,tree000_400]
def tree000_452 : CoverTree := CoverTree.split [tree000_445,tree000_451,tree000_111,tree000_115,tree000_38,tree000_41]
def tree000_453 : CoverTree := CoverTree.reject 75
def tree000_454 : CoverTree := CoverTree.split [tree000_388,tree000_388,tree000_388,tree000_453,tree000_23,tree000_23]
def tree000_455 : CoverTree := CoverTree.split [tree000_384,tree000_385,tree000_386,tree000_387,tree000_392,tree000_454]
def tree000_456 : CoverTree := CoverTree.reject 157
def tree000_457 : CoverTree := CoverTree.reject 105
def tree000_458 : CoverTree := CoverTree.split [tree000_388,tree000_388,tree000_388,tree000_456,tree000_457,tree000_23]
def tree000_459 : CoverTree := CoverTree.reject 158
def tree000_460 : CoverTree := CoverTree.split [tree000_388,tree000_388,tree000_388,tree000_459,tree000_448,tree000_23]
def tree000_461 : CoverTree := CoverTree.split [tree000_395,tree000_458,tree000_460,tree000_399,tree000_400,tree000_400]
def tree000_462 : CoverTree := CoverTree.split [tree000_455,tree000_461,tree000_129,tree000_58,tree000_64,tree000_41]
def tree000_463 : CoverTree := CoverTree.split [tree000_406,tree000_419,tree000_431,tree000_444,tree000_452,tree000_462]
def tree000_464 : CoverTree := CoverTree.split [tree000_283,tree000_299,tree000_334,tree000_362,tree000_403,tree000_463]
def tree000_465 : CoverTree := CoverTree.reject 22
def tree000_466 : CoverTree := CoverTree.reject 182
def tree000_467 : CoverTree := CoverTree.reject 139
def tree000_468 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_286,tree000_286,tree000_467,tree000_76]
def tree000_469 : CoverTree := CoverTree.reject 208
def tree000_470 : CoverTree := CoverTree.reject 228
def tree000_471 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_470,tree000_23,tree000_291]
def tree000_472 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_286,tree000_286,tree000_469,tree000_471]
def tree000_473 : CoverTree := CoverTree.reject 104
def tree000_474 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_473,tree000_37,tree000_23]
def tree000_475 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_286,tree000_286,tree000_474,tree000_294]
def tree000_476 : CoverTree := CoverTree.reject 177
def tree000_477 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_53,tree000_55,tree000_57]
def tree000_478 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_476,tree000_477,tree000_143,tree000_146]
def tree000_479 : CoverTree := CoverTree.split [tree000_134,tree000_466,tree000_468,tree000_472,tree000_475,tree000_478]
def tree000_480 : CoverTree := CoverTree.reject 268
def tree000_481 : CoverTree := CoverTree.reject 269
def tree000_482 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_480,tree000_481,tree000_75]
def tree000_483 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_300,tree000_301,tree000_482]
def tree000_484 : CoverTree := CoverTree.reject 129
def tree000_485 : CoverTree := CoverTree.reject 270
def tree000_486 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_484,tree000_485,tree000_75]
def tree000_487 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_75,tree000_308,tree000_75]
def tree000_488 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_304,tree000_486,tree000_487]
def tree000_489 : CoverTree := CoverTree.reject 121
def tree000_490 : CoverTree := CoverTree.split [tree000_32,tree000_312,tree000_313,tree000_35,tree000_92,tree000_23]
def tree000_491 : CoverTree := CoverTree.reject 271
def tree000_492 : CoverTree := CoverTree.reject 229
def tree000_493 : CoverTree := CoverTree.split [tree000_20,tree000_491,tree000_492,tree000_26,tree000_23,tree000_23]
def tree000_494 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_489,tree000_490,tree000_493]
def tree000_495 : CoverTree := CoverTree.reject 272
def tree000_496 : CoverTree := CoverTree.split [tree000_20,tree000_495,tree000_167,tree000_26,tree000_23,tree000_23]
def tree000_497 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_324,tree000_163,tree000_496]
def tree000_498 : CoverTree := CoverTree.reject 367
def tree000_499 : CoverTree := CoverTree.split [tree000_101,tree000_498,tree000_122,tree000_125,tree000_128,tree000_110]
def tree000_500 : CoverTree := CoverTree.reject 341
def tree000_501 : CoverTree := CoverTree.split [tree000_44,tree000_500,tree000_51,tree000_53,tree000_55,tree000_57]
def tree000_502 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_499,tree000_501,tree000_64,tree000_41]
def tree000_503 : CoverTree := CoverTree.split [tree000_149,tree000_483,tree000_488,tree000_494,tree000_497,tree000_502]
def tree000_504 : CoverTree := CoverTree.reject 300
def tree000_505 : CoverTree := CoverTree.reject 301
def tree000_506 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_504,tree000_505,tree000_75]
def tree000_507 : CoverTree := CoverTree.reject 273
def tree000_508 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_507,tree000_75,tree000_75]
def tree000_509 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_181,tree000_182,tree000_506,tree000_508]
def tree000_510 : CoverTree := CoverTree.reject 195
def tree000_511 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_187,tree000_510,tree000_85,tree000_76]
def tree000_512 : CoverTree := CoverTree.reject 204
def tree000_513 : CoverTree := CoverTree.reject 205
def tree000_514 : CoverTree := CoverTree.split [tree000_101,tree000_354,tree000_512,tree000_513,tree000_108,tree000_264]
def tree000_515 : CoverTree := CoverTree.reject 206
def tree000_516 : CoverTree := CoverTree.reject 207
def tree000_517 : CoverTree := CoverTree.split [tree000_44,tree000_515,tree000_516,tree000_35,tree000_92,tree000_57]
def tree000_518 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_514,tree000_517,tree000_96,tree000_99]
def tree000_519 : CoverTree := CoverTree.reject 278
def tree000_520 : CoverTree := CoverTree.reject 279
def tree000_521 : CoverTree := CoverTree.split [tree000_395,tree000_519,tree000_520,tree000_399,tree000_400,tree000_400]
def tree000_522 : CoverTree := CoverTree.split [tree000_359,tree000_521,tree000_129,tree000_58,tree000_64,tree000_41]
def tree000_523 : CoverTree := CoverTree.split [tree000_180,tree000_509,tree000_511,tree000_518,tree000_358,tree000_522]
def tree000_524 : CoverTree := CoverTree.reject 342
def tree000_525 : CoverTree := CoverTree.reject 343
def tree000_526 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_524,tree000_525,tree000_75]
def tree000_527 : CoverTree := CoverTree.reject 302
def tree000_528 : CoverTree := CoverTree.reject 303
def tree000_529 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_527,tree000_528,tree000_75]
def tree000_530 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_219,tree000_526,tree000_529,tree000_76]
def tree000_531 : CoverTree := CoverTree.reject 178
def tree000_532 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_531,tree000_82,tree000_85,tree000_76]
def tree000_533 : CoverTree := CoverTree.reject 280
def tree000_534 : CoverTree := CoverTree.reject 344
def tree000_535 : CoverTree := CoverTree.reject 125
def tree000_536 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_535,tree000_23,tree000_23]
def tree000_537 : CoverTree := CoverTree.split [tree000_101,tree000_533,tree000_534,tree000_536,tree000_108,tree000_264]
def tree000_538 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_537,tree000_93,tree000_96,tree000_99]
def tree000_539 : CoverTree := CoverTree.split [tree000_353,tree000_353,tree000_111,tree000_115,tree000_38,tree000_41]
def tree000_540 : CoverTree := CoverTree.split [tree000_363,tree000_530,tree000_532,tree000_538,tree000_539,tree000_462]
def tree000_541 : CoverTree := CoverTree.reject 311
def tree000_542 : CoverTree := CoverTree.reject 368
def tree000_543 : CoverTree := CoverTree.reject 345
def tree000_544 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_542,tree000_543,tree000_75]
def tree000_545 : CoverTree := CoverTree.reject 346
def tree000_546 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_545,tree000_413,tree000_75]
def tree000_547 : CoverTree := CoverTree.reject 123
def tree000_548 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_547,tree000_23,tree000_23,tree000_23]
def tree000_549 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_548,tree000_417,tree000_75]
def tree000_550 : CoverTree := CoverTree.split [tree000_407,tree000_541,tree000_544,tree000_546,tree000_549,tree000_76]
def tree000_551 : CoverTree := CoverTree.reject 63
def tree000_552 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_447,tree000_551,tree000_23]
def tree000_553 : CoverTree := CoverTree.reject 369
def tree000_554 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_552,tree000_553,tree000_424]
def tree000_555 : CoverTree := CoverTree.reject 160
def tree000_556 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_555,tree000_23,tree000_23]
def tree000_557 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_556,tree000_108,tree000_75]
def tree000_558 : CoverTree := CoverTree.split [tree000_420,tree000_554,tree000_557,tree000_82,tree000_85,tree000_76]
def tree000_559 : CoverTree := CoverTree.reject 370
def tree000_560 : CoverTree := CoverTree.reject 371
def tree000_561 : CoverTree := CoverTree.split [tree000_395,tree000_433,tree000_559,tree000_560,tree000_450,tree000_400]
def tree000_562 : CoverTree := CoverTree.reject 372
def tree000_563 : CoverTree := CoverTree.split [tree000_101,tree000_562,tree000_107,tree000_536,tree000_108,tree000_264]
def tree000_564 : CoverTree := CoverTree.reject 347
def tree000_565 : CoverTree := CoverTree.split [tree000_44,tree000_564,tree000_90,tree000_35,tree000_92,tree000_57]
def tree000_566 : CoverTree := CoverTree.split [tree000_432,tree000_561,tree000_563,tree000_565,tree000_96,tree000_99]
def tree000_567 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_447,tree000_390,tree000_23]
def tree000_568 : CoverTree := CoverTree.reject 188
def tree000_569 : CoverTree := CoverTree.split [tree000_384,tree000_385,tree000_386,tree000_387,tree000_567,tree000_568]
def tree000_570 : CoverTree := CoverTree.split [tree000_569,tree000_451,tree000_111,tree000_115,tree000_38,tree000_41]
def tree000_571 : CoverTree := CoverTree.split [tree000_406,tree000_550,tree000_558,tree000_566,tree000_570,tree000_462]
def tree000_572 : CoverTree := CoverTree.split [tree000_465,tree000_479,tree000_503,tree000_523,tree000_540,tree000_571]
def tree000_573 : CoverTree := CoverTree.reject 76
def tree000_574 : CoverTree := CoverTree.reject 72
def tree000_575 : CoverTree := CoverTree.reject 73
def tree000_576 : CoverTree := CoverTree.reject 56
def tree000_577 : CoverTree := CoverTree.reject 80
def tree000_578 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_286,tree000_286,tree000_577,tree000_294]
def tree000_579 : CoverTree := CoverTree.reject 79
def tree000_580 : CoverTree := CoverTree.reject 81
def tree000_581 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_579,tree000_580,tree000_143,tree000_294]
def tree000_582 : CoverTree := CoverTree.split [tree000_573,tree000_574,tree000_575,tree000_576,tree000_578,tree000_581]
def tree000_583 : CoverTree := CoverTree.reject 183
def tree000_584 : CoverTree := CoverTree.reject 274
def tree000_585 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_584,tree000_75,tree000_75]
def tree000_586 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_286,tree000_286,tree000_467,tree000_585]
def tree000_587 : CoverTree := CoverTree.reject 10
def tree000_588 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_587,tree000_587,tree000_23]
def tree000_589 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_26,tree000_23,tree000_291]
def tree000_590 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_286,tree000_286,tree000_588,tree000_589]
def tree000_591 : CoverTree := CoverTree.reject 128
def tree000_592 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_591,tree000_128,tree000_110]
def tree000_593 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_592,tree000_477,tree000_143,tree000_146]
def tree000_594 : CoverTree := CoverTree.split [tree000_134,tree000_583,tree000_586,tree000_590,tree000_475,tree000_593]
def tree000_595 : CoverTree := CoverTree.reject 275
def tree000_596 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_595,tree000_75,tree000_75]
def tree000_597 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_300,tree000_301,tree000_596]
def tree000_598 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_484,tree000_75,tree000_75]
def tree000_599 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_304,tree000_598,tree000_487]
def tree000_600 : CoverTree := CoverTree.reject 243
def tree000_601 : CoverTree := CoverTree.reject 244
def tree000_602 : CoverTree := CoverTree.split [tree000_44,tree000_600,tree000_601,tree000_35,tree000_92,tree000_57]
def tree000_603 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_151,tree000_602,tree000_490,tree000_99]
def tree000_604 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_129,tree000_58,tree000_64,tree000_41]
def tree000_605 : CoverTree := CoverTree.split [tree000_149,tree000_597,tree000_599,tree000_603,tree000_325,tree000_604]
def tree000_606 : CoverTree := CoverTree.reject 304
def tree000_607 : CoverTree := CoverTree.reject 305
def tree000_608 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_606,tree000_607,tree000_75]
def tree000_609 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_181,tree000_182,tree000_608,tree000_76]
def tree000_610 : CoverTree := CoverTree.reject 110
def tree000_611 : CoverTree := CoverTree.reject 312
def tree000_612 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_611,tree000_23,tree000_23,tree000_23]
def tree000_613 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_610,tree000_612,tree000_75]
def tree000_614 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_187,tree000_613,tree000_85,tree000_76]
def tree000_615 : CoverTree := CoverTree.reject 240
def tree000_616 : CoverTree := CoverTree.reject 281
def tree000_617 : CoverTree := CoverTree.split [tree000_615,tree000_616,tree000_355,tree000_357,tree000_38,tree000_41]
def tree000_618 : CoverTree := CoverTree.split [tree000_180,tree000_609,tree000_614,tree000_518,tree000_617,tree000_522]
def tree000_619 : CoverTree := CoverTree.reject 348
def tree000_620 : CoverTree := CoverTree.reject 349
def tree000_621 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_619,tree000_620,tree000_75]
def tree000_622 : CoverTree := CoverTree.reject 306
def tree000_623 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_622,tree000_417,tree000_75]
def tree000_624 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_219,tree000_621,tree000_623,tree000_76]
def tree000_625 : CoverTree := CoverTree.reject 350
def tree000_626 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_625,tree000_108,tree000_75]
def tree000_627 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_626,tree000_82,tree000_85,tree000_76]
def tree000_628 : CoverTree := CoverTree.reject 351
def tree000_629 : CoverTree := CoverTree.split [tree000_101,tree000_533,tree000_628,tree000_536,tree000_108,tree000_264]
def tree000_630 : CoverTree := CoverTree.split [tree000_335,tree000_335,tree000_629,tree000_93,tree000_96,tree000_99]
def tree000_631 : CoverTree := CoverTree.reject 201
def tree000_632 : CoverTree := CoverTree.reject 32
def tree000_633 : CoverTree := CoverTree.split [tree000_632,tree000_632,tree000_632,tree000_450,tree000_450,tree000_400]
def tree000_634 : CoverTree := CoverTree.split [tree000_631,tree000_633,tree000_111,tree000_115,tree000_38,tree000_41]
def tree000_635 : CoverTree := CoverTree.split [tree000_363,tree000_624,tree000_627,tree000_630,tree000_634,tree000_462]
def tree000_636 : CoverTree := CoverTree.reject 211
def tree000_637 : CoverTree := CoverTree.reject 212
def tree000_638 : CoverTree := CoverTree.reject 202
def tree000_639 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_388,tree000_638,tree000_23,tree000_23]
def tree000_640 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_636,tree000_637,tree000_639]
def tree000_641 : CoverTree := CoverTree.reject 373
def tree000_642 : CoverTree := CoverTree.reject 137
def tree000_643 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_642,tree000_23,tree000_23]
def tree000_644 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_641,tree000_643,tree000_75]
def tree000_645 : CoverTree := CoverTree.reject 197
def tree000_646 : CoverTree := CoverTree.reject 198
def tree000_647 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_645,tree000_646,tree000_23,tree000_23]
def tree000_648 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_647,tree000_413,tree000_75]
def tree000_649 : CoverTree := CoverTree.split [tree000_407,tree000_640,tree000_644,tree000_648,tree000_549,tree000_76]
def tree000_650 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_552,tree000_552,tree000_424]
def tree000_651 : CoverTree := CoverTree.split [tree000_420,tree000_650,tree000_557,tree000_82,tree000_85,tree000_76]
def tree000_652 : CoverTree := CoverTree.reject 374
def tree000_653 : CoverTree := CoverTree.reject 215
def tree000_654 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_447,tree000_653,tree000_23]
def tree000_655 : CoverTree := CoverTree.split [tree000_395,tree000_433,tree000_652,tree000_654,tree000_450,tree000_400]
def tree000_656 : CoverTree := CoverTree.split [tree000_101,tree000_105,tree000_107,tree000_536,tree000_108,tree000_264]
def tree000_657 : CoverTree := CoverTree.split [tree000_432,tree000_655,tree000_656,tree000_93,tree000_96,tree000_99]
def tree000_658 : CoverTree := CoverTree.split [tree000_406,tree000_649,tree000_651,tree000_657,tree000_570,tree000_462]
def tree000_659 : CoverTree := CoverTree.split [tree000_582,tree000_594,tree000_605,tree000_618,tree000_635,tree000_658]
def tree000_660 : CoverTree := CoverTree.reject 210
def tree000_661 : CoverTree := CoverTree.reject 170
def tree000_662 : CoverTree := CoverTree.reject 122
def tree000_663 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_660,tree000_661,tree000_577,tree000_662]
def tree000_664 : CoverTree := CoverTree.split [tree000_573,tree000_574,tree000_575,tree000_576,tree000_663,tree000_581]
def tree000_665 : CoverTree := CoverTree.reject 232
def tree000_666 : CoverTree := CoverTree.reject 233
def tree000_667 : CoverTree := CoverTree.reject 138
def tree000_668 : CoverTree := CoverTree.reject 109
def tree000_669 : CoverTree := CoverTree.reject 354
def tree000_670 : CoverTree := CoverTree.split [tree000_74,tree000_74,tree000_669,tree000_23,tree000_23,tree000_23]
def tree000_671 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_668,tree000_670,tree000_75]
def tree000_672 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_665,tree000_666,tree000_667,tree000_671]
def tree000_673 : CoverTree := CoverTree.reject 234
def tree000_674 : CoverTree := CoverTree.reject 235
def tree000_675 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_673,tree000_674,tree000_467,tree000_76]
def tree000_676 : CoverTree := CoverTree.reject 236
def tree000_677 : CoverTree := CoverTree.reject 213
def tree000_678 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_676,tree000_677,tree000_588,tree000_589]
def tree000_679 : CoverTree := CoverTree.reject 214
def tree000_680 : CoverTree := CoverTree.reject 242
def tree000_681 : CoverTree := CoverTree.split [tree000_142,tree000_142,tree000_142,tree000_473,tree000_680,tree000_57]
def tree000_682 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_679,tree000_681,tree000_474,tree000_294]
def tree000_683 : CoverTree := CoverTree.split [tree000_134,tree000_672,tree000_675,tree000_678,tree000_682,tree000_593]
def tree000_684 : CoverTree := CoverTree.reject 237
def tree000_685 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_684,tree000_300,tree000_301,tree000_76]
def tree000_686 : CoverTree := CoverTree.reject 238
def tree000_687 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_686,tree000_304,tree000_598,tree000_487]
def tree000_688 : CoverTree := CoverTree.reject 239
def tree000_689 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_688,tree000_602,tree000_490,tree000_99]
def tree000_690 : CoverTree := CoverTree.reject 71
def tree000_691 : CoverTree := CoverTree.split [tree000_101,tree000_690,tree000_690,tree000_690,tree000_690,tree000_110]
def tree000_692 : CoverTree := CoverTree.split [tree000_139,tree000_139,tree000_691,tree000_324,tree000_163,tree000_168]
def tree000_693 : CoverTree := CoverTree.split [tree000_149,tree000_685,tree000_687,tree000_689,tree000_692,tree000_604]
def tree000_694 : CoverTree := CoverTree.reject 307
def tree000_695 : CoverTree := CoverTree.split [tree000_407,tree000_694,tree000_181,tree000_182,tree000_549,tree000_76]
def tree000_696 : CoverTree := CoverTree.reject 308
def tree000_697 : CoverTree := CoverTree.split [tree000_420,tree000_696,tree000_187,tree000_613,tree000_85,tree000_76]
def tree000_698 : CoverTree := CoverTree.reject 276
def tree000_699 : CoverTree := CoverTree.split [tree000_432,tree000_698,tree000_514,tree000_517,tree000_96,tree000_99]
def tree000_700 : CoverTree := CoverTree.reject 91
def tree000_701 : CoverTree := CoverTree.split [tree000_632,tree000_632,tree000_632,tree000_700,tree000_700,tree000_400]
def tree000_702 : CoverTree := CoverTree.split [tree000_615,tree000_701,tree000_355,tree000_357,tree000_38,tree000_41]
def tree000_703 : CoverTree := CoverTree.split [tree000_180,tree000_695,tree000_697,tree000_699,tree000_702,tree000_522]
def tree000_704 : CoverTree := CoverTree.split [tree000_404,tree000_405,tree000_5,tree000_6,tree000_7,tree000_8]
def tree000_705 : CoverTree := CoverTree.reject 309
def tree000_706 : CoverTree := CoverTree.split [tree000_407,tree000_705,tree000_219,tree000_648,tree000_549,tree000_76]
def tree000_707 : CoverTree := CoverTree.reject 241
def tree000_708 : CoverTree := CoverTree.split [tree000_420,tree000_707,tree000_557,tree000_82,tree000_85,tree000_76]
def tree000_709 : CoverTree := CoverTree.reject 352
def tree000_710 : CoverTree := CoverTree.split [tree000_632,tree000_632,tree000_632,tree000_709,tree000_450,tree000_400]
def tree000_711 : CoverTree := CoverTree.split [tree000_101,tree000_533,tree000_107,tree000_536,tree000_108,tree000_264]
def tree000_712 : CoverTree := CoverTree.split [tree000_432,tree000_710,tree000_711,tree000_93,tree000_96,tree000_99]
def tree000_713 : CoverTree := CoverTree.split [tree000_704,tree000_706,tree000_708,tree000_712,tree000_634,tree000_462]
def tree000_714 : CoverTree := CoverTree.reject 277
def tree000_715 : CoverTree := CoverTree.split [tree000_102,tree000_102,tree000_102,tree000_642,tree000_714,tree000_23]
def tree000_716 : CoverTree := CoverTree.split [tree000_73,tree000_73,tree000_73,tree000_715,tree000_643,tree000_75]
def tree000_717 : CoverTree := CoverTree.split [tree000_407,tree000_640,tree000_716,tree000_648,tree000_549,tree000_76]
def tree000_718 : CoverTree := CoverTree.split [tree000_395,tree000_433,tree000_449,tree000_654,tree000_450,tree000_400]
def tree000_719 : CoverTree := CoverTree.split [tree000_432,tree000_718,tree000_656,tree000_93,tree000_96,tree000_99]
def tree000_720 : CoverTree := CoverTree.split [tree000_406,tree000_717,tree000_651,tree000_719,tree000_570,tree000_462]
def tree000_721 : CoverTree := CoverTree.split [tree000_664,tree000_683,tree000_693,tree000_703,tree000_713,tree000_720]
def tree000_722 : CoverTree := CoverTree.split [tree000_132,tree000_282,tree000_464,tree000_572,tree000_659,tree000_721]
def tree000 : CoverTree := tree000_722

end Snake9.Certificate88
