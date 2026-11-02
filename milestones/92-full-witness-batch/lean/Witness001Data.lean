import BatchContextData
import Cover001Data
import Class001WitnessData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Witness90 Snake9.Retained87

def baseBoxes001 : List Box := boxes001

def baseList001 : List Witness := Snake9.Witness90.witnessList001

def baseList002 : List Witness := Snake9.Witness90.witnessList003

def jobs001 : List (Nat × List Witness) := [
(1,baseList001),
(3,baseList002),
(307,baseList002),
(308,baseList002),
(310,baseList001),
(312,baseList002)
]

def contexts001 : List (Nat × Nat × Nat × List Witness) := [
(1,0,0,baseList001),
(3,0,0,baseList002),
(307,0,0,baseList002),
(308,0,0,baseList002),
(310,0,0,baseList001),
(312,0,0,baseList002)
]

def contextKeys001 : List (Nat × Nat) := contexts001.map (fun c => (c.1,c.2.1))

end Snake9.Batch92
