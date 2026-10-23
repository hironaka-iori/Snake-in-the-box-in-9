import LocalWindowModel
set_option maxRecDepth 100000
namespace Snake9.LocalWindow.CycleWindow381
def window : List Nat := [0, 1, 3, 7, 15, 31, 27, 26, 18]
def bounds : List (Nat × Nat) := [(0,1),(0,21),(0,21),(0,21),(0,21),(0,21),(0,21)]
def raw : List (List Nat) := [
[2],
[6],
[14],
[12],
[10],
[7,5,3,15],
[13,11,9,15],
[4,16],
[17,18],
[19,20],
[21,22],
[23,24],
[25,26],
[8,27]
]
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.CycleWindow381
