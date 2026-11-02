import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes108 : List Box := [
[(1,3),(1,6),(1,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,6),(1,3),(1,6)],
[(1,6),(1,2),(1,6),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)],
[(1,6),(1,2),(1,6),(1,6),(1,3),(1,6)],
[(1,6),(1,6),(1,5),(1,5),(1,4),(1,2)],
[(1,3),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,6),(1,6),(1,2)],
[(1,6),(1,3),(1,5),(1,3),(1,5),(1,6)],
[(1,6),(1,2),(1,4),(1,5),(1,5),(1,6)],
[(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,6),(1,5),(1,3),(1,5),(1,3)],
[(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,5),(1,2),(1,5),(1,4)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,3),(1,2),(1,5),(1,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,2),(1,5),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,2)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(6,6),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(6,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(6,6)],
[(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(3,3)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(5,5)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(4,4)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(5,5),(1,1)],
[(1,6),(1,5),(1,5),(1,2),(1,3),(1,6)],
[(1,6),(2,2),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(6,6),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,2),(1,3),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,2),(1,5),(1,5)],
[(1,6),(1,1),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(1,1),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
[(1,6),(1,1),(5,5),(5,5),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,1),(5,5),(6,6),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(5,5),(3,3),(2,2)],
[(1,6),(1,6),(4,4),(5,5),(3,3),(3,3)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(4,4),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(2,2)],
[(1,6),(1,2),(1,5),(1,5),(1,4),(1,6)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(4,4)],
[(2,2),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(2,2),(4,4),(5,5),(4,4),(1,6),(1,6)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(6,6),(2,2)],
[(2,2),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(6,6),(1,1),(5,5),(6,6),(1,6),(1,6)],
[(1,4),(1,5),(1,5),(1,2),(1,6),(1,6)],
[(4,4),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(5,5),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(5,5)],
[(1,6),(3,3),(5,5),(5,5),(2,2),(1,6)],
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(5,5),(3,3),(1,6),(1,6)],
[(3,3),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(3,3)],
[(1,6),(3,3),(4,4),(5,5),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(2,2),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(5,5)],
[(4,4),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,1),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(4,4),(4,4)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(5,5),(5,5),(3,3)],
[(1,6),(3,3),(3,3),(5,5),(4,4),(1,6)],
[(1,6),(3,3),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(5,5),(4,4),(2,2),(1,6)],
[(4,4),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,3),(1,2),(1,6)],
[(1,6),(1,6),(1,2),(1,3),(1,5),(1,4)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(4,4)],
[(1,6),(5,5),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(4,4)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(4,4)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(4,4)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(6,6)],
[(1,6),(4,4),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(6,6),(5,5),(1,1),(6,6),(1,6)],
[(4,4),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(5,5),(1,6)],
[(1,6),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(4,4)],
[(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(6,6),(6,6),(4,4),(2,2)],
[(1,6),(3,3),(5,5),(6,6),(2,2),(2,2)],
[(1,6),(3,3),(5,5),(6,6),(3,3),(3,3)],
[(2,2),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(3,3),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(4,4),(5,5),(6,6),(2,2),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(6,6),(2,2),(1,6)],
[(4,4),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(4,4),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(1,6),(2,2),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(4,4)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(5,5)],
[(1,6),(2,2),(2,2),(6,6),(4,4),(1,6)],
[(1,6),(2,2),(5,5),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(1,1),(5,5),(4,4),(6,6),(2,2),(1,6)],
[(1,6),(2,2),(4,4),(6,6),(6,6),(2,2)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(4,4)],
[(2,2),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(5,5),(5,5),(3,3),(1,6)],
[(2,2),(5,5),(4,4),(6,6),(2,2),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(4,4),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(5,5),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(3,3),(4,4),(4,4),(6,6),(2,2),(1,6)],
[(4,4),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(4,4),(3,3),(2,2),(6,6),(5,5),(1,6)],
[(4,4),(3,3),(3,3),(5,5),(5,5),(1,6)],
[(4,4),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(4,4),(3,3),(5,5),(6,6),(2,2),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(5,5),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(2,2),(1,6)],
[(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(5,5)],
[(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(3,3),(1,6)],
[(1,6),(5,5),(4,4),(3,3),(2,2),(1,6)],
[(5,5),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(6,6),(5,5),(3,3)],
[(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(4,4),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(4,4),(5,5),(5,5),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(6,6),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(6,6),(5,5),(3,3),(4,4),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(2,2),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(3,3),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(5,5),(1,6)],
[(4,4),(5,5),(2,2),(5,5),(4,4),(1,6)],
[(4,4),(5,5),(2,2),(5,5),(5,5),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(5,5),(1,6)],
[(5,5),(5,5),(2,2),(5,5),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(1,6),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(4,4)],
[(1,6),(4,4),(3,3),(4,4),(5,5),(3,3)],
[(2,2),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(4,4),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(5,5),(5,5),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(3,3),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(6,6),(5,5),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(2,2),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(3,3),(5,5),(5,5),(4,4),(2,2),(1,6)],
[(3,3),(6,6),(4,4),(3,3),(3,3),(1,6)],
[(3,3),(6,6),(4,4),(3,3),(4,4),(1,6)],
[(3,3),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(4,4),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(4,4),(5,5),(2,2),(4,4),(4,4),(1,6)],
[(4,4),(5,5),(2,2),(4,4),(5,5),(1,6)],
[(4,4),(5,5),(4,4),(3,3),(3,3),(1,6)],
[(4,4),(6,6),(2,2),(3,3),(5,5),(1,6)],
[(4,4),(6,6),(2,2),(4,4),(4,4),(1,6)],
[(4,4),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(5,5),(5,5),(2,2),(4,4),(4,4),(1,6)],
[(5,5),(5,5),(2,2),(4,4),(5,5),(1,6)],
[(5,5),(5,5),(3,3),(3,3),(4,4),(1,6)],
[(5,5),(5,5),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(5,5),(4,4),(2,2),(4,4),(1,6)],
[(1,6),(2,2),(2,2),(6,6),(5,5),(3,3)],
[(2,2),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(2,2),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(6,6),(4,4),(3,3),(2,2),(1,6)],
[(4,4),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(4,4),(6,6),(2,2),(3,3),(4,4),(1,6)],
[(4,4),(6,6),(3,3),(2,2),(5,5),(1,6)],
[(4,4),(6,6),(4,4),(2,2),(3,3),(1,6)],
[(4,4),(6,6),(4,4),(2,2),(4,4),(1,6)],
[(4,4),(6,6),(4,4),(3,3),(2,2),(1,6)],
[(5,5),(6,6),(2,2),(3,3),(4,4),(1,6)],
[(5,5),(6,6),(4,4),(2,2),(3,3),(1,6)]
]

def root108 : Nat := 3888

def tree108_0 : CoverTree := CoverTree.reject 54
def tree108_1 : CoverTree := CoverTree.reject 33
def tree108_2 : CoverTree := CoverTree.reject 12
def tree108_3 : CoverTree := CoverTree.reject 11
def tree108_4 : CoverTree := CoverTree.reject 0
def tree108_5 : CoverTree := CoverTree.reject 6
def tree108_6 : CoverTree := CoverTree.reject 36
def tree108_7 : CoverTree := CoverTree.reject 102
def tree108_8 : CoverTree := CoverTree.reject 31
def tree108_9 : CoverTree := CoverTree.reject 32
def tree108_10 : CoverTree := CoverTree.reject 24
def tree108_11 : CoverTree := CoverTree.reject 16
def tree108_12 : CoverTree := CoverTree.reject 42
def tree108_13 : CoverTree := CoverTree.reject 43
def tree108_14 : CoverTree := CoverTree.split [tree108_8,tree108_9,tree108_10,tree108_11,tree108_12,tree108_13]
def tree108_15 : CoverTree := CoverTree.reject 201
def tree108_16 : CoverTree := CoverTree.reject 26
def tree108_17 : CoverTree := CoverTree.accept
def tree108_18 : CoverTree := CoverTree.split [tree108_16,tree108_17,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_19 : CoverTree := CoverTree.reject 17
def tree108_20 : CoverTree := CoverTree.split [tree108_19,tree108_17,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_21 : CoverTree := CoverTree.split [tree108_14,tree108_15,tree108_18,tree108_20,tree108_17,tree108_17]
def tree108_22 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_6,tree108_6,tree108_7,tree108_21]
def tree108_23 : CoverTree := CoverTree.reject 5
def tree108_24 : CoverTree := CoverTree.reject 39
def tree108_25 : CoverTree := CoverTree.reject 40
def tree108_26 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_10,tree108_11,tree108_24,tree108_25]
def tree108_27 : CoverTree := CoverTree.reject 41
def tree108_28 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_27,tree108_17,tree108_17,tree108_17]
def tree108_29 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_30 : CoverTree := CoverTree.reject 49
def tree108_31 : CoverTree := CoverTree.split [tree108_30,tree108_17,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_32 : CoverTree := CoverTree.split [tree108_26,tree108_28,tree108_29,tree108_29,tree108_31,tree108_17]
def tree108_33 : CoverTree := CoverTree.reject 25
def tree108_34 : CoverTree := CoverTree.split [tree108_33,tree108_17,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_35 : CoverTree := CoverTree.split [tree108_14,tree108_34,tree108_18,tree108_20,tree108_17,tree108_17]
def tree108_36 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_6,tree108_6,tree108_32,tree108_35]
def tree108_37 : CoverTree := CoverTree.reject 84
def tree108_38 : CoverTree := CoverTree.reject 13
def tree108_39 : CoverTree := CoverTree.reject 85
def tree108_40 : CoverTree := CoverTree.reject 45
def tree108_41 : CoverTree := CoverTree.reject 46
def tree108_42 : CoverTree := CoverTree.split [tree108_33,tree108_39,tree108_40,tree108_41,tree108_17,tree108_17]
def tree108_43 : CoverTree := CoverTree.reject 86
def tree108_44 : CoverTree := CoverTree.reject 47
def tree108_45 : CoverTree := CoverTree.split [tree108_16,tree108_43,tree108_44,tree108_17,tree108_17,tree108_17]
def tree108_46 : CoverTree := CoverTree.reject 81
def tree108_47 : CoverTree := CoverTree.split [tree108_19,tree108_46,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_48 : CoverTree := CoverTree.reject 57
def tree108_49 : CoverTree := CoverTree.split [tree108_48,tree108_17,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_50 : CoverTree := CoverTree.reject 37
def tree108_51 : CoverTree := CoverTree.split [tree108_50,tree108_17,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_52 : CoverTree := CoverTree.split [tree108_38,tree108_42,tree108_45,tree108_47,tree108_49,tree108_51]
def tree108_53 : CoverTree := CoverTree.split [tree108_8,tree108_9,tree108_10,tree108_11,tree108_24,tree108_25]
def tree108_54 : CoverTree := CoverTree.reject 87
def tree108_55 : CoverTree := CoverTree.split [tree108_33,tree108_54,tree108_27,tree108_17,tree108_17,tree108_17]
def tree108_56 : CoverTree := CoverTree.reject 88
def tree108_57 : CoverTree := CoverTree.split [tree108_16,tree108_56,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_58 : CoverTree := CoverTree.split [tree108_53,tree108_55,tree108_57,tree108_20,tree108_31,tree108_17]
def tree108_59 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_37,tree108_52,tree108_58,tree108_35]
def tree108_60 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_22,tree108_36,tree108_59]
def tree108_61 : CoverTree := CoverTree.reject 130
def tree108_62 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_40,tree108_41,tree108_17,tree108_17]
def tree108_63 : CoverTree := CoverTree.reject 103
def tree108_64 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_44,tree108_63,tree108_17,tree108_17]
def tree108_65 : CoverTree := CoverTree.reject 30
def tree108_66 : CoverTree := CoverTree.split [tree108_65,tree108_65,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_67 : CoverTree := CoverTree.split [tree108_38,tree108_62,tree108_64,tree108_29,tree108_66,tree108_51]
def tree108_68 : CoverTree := CoverTree.reject 89
def tree108_69 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_68,tree108_17,tree108_17,tree108_17]
def tree108_70 : CoverTree := CoverTree.split [tree108_26,tree108_28,tree108_69,tree108_29,tree108_66,tree108_17]
def tree108_71 : CoverTree := CoverTree.reject 90
def tree108_72 : CoverTree := CoverTree.split [tree108_33,tree108_71,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_73 : CoverTree := CoverTree.split [tree108_14,tree108_72,tree108_18,tree108_20,tree108_17,tree108_17]
def tree108_74 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_61,tree108_67,tree108_70,tree108_73]
def tree108_75 : CoverTree := CoverTree.reject 18
def tree108_76 : CoverTree := CoverTree.reject 14
def tree108_77 : CoverTree := CoverTree.reject 51
def tree108_78 : CoverTree := CoverTree.reject 52
def tree108_79 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_76,tree108_77,tree108_78,tree108_17]
def tree108_80 : CoverTree := CoverTree.reject 53
def tree108_81 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_76,tree108_80,tree108_17,tree108_17]
def tree108_82 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_76,tree108_17,tree108_17,tree108_17]
def tree108_83 : CoverTree := CoverTree.split [tree108_76,tree108_76,tree108_76,tree108_17,tree108_17,tree108_17]
def tree108_84 : CoverTree := CoverTree.reject 50
def tree108_85 : CoverTree := CoverTree.split [tree108_84,tree108_17,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_86 : CoverTree := CoverTree.split [tree108_75,tree108_79,tree108_81,tree108_82,tree108_83,tree108_85]
def tree108_87 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_44,tree108_17,tree108_17,tree108_17]
def tree108_88 : CoverTree := CoverTree.reject 91
def tree108_89 : CoverTree := CoverTree.split [tree108_48,tree108_88,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_90 : CoverTree := CoverTree.split [tree108_38,tree108_62,tree108_87,tree108_29,tree108_89,tree108_51]
def tree108_91 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_86,tree108_90,tree108_32,tree108_35]
def tree108_92 : CoverTree := CoverTree.reject 92
def tree108_93 : CoverTree := CoverTree.reject 93
def tree108_94 : CoverTree := CoverTree.split [tree108_33,tree108_92,tree108_93,tree108_77,tree108_78,tree108_17]
def tree108_95 : CoverTree := CoverTree.reject 94
def tree108_96 : CoverTree := CoverTree.reject 95
def tree108_97 : CoverTree := CoverTree.split [tree108_16,tree108_95,tree108_96,tree108_80,tree108_17,tree108_17]
def tree108_98 : CoverTree := CoverTree.reject 96
def tree108_99 : CoverTree := CoverTree.reject 97
def tree108_100 : CoverTree := CoverTree.split [tree108_19,tree108_98,tree108_99,tree108_17,tree108_17,tree108_17]
def tree108_101 : CoverTree := CoverTree.reject 98
def tree108_102 : CoverTree := CoverTree.reject 99
def tree108_103 : CoverTree := CoverTree.split [tree108_101,tree108_102,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_104 : CoverTree := CoverTree.split [tree108_75,tree108_94,tree108_97,tree108_100,tree108_103,tree108_85]
def tree108_105 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_104,tree108_52,tree108_58,tree108_35]
def tree108_106 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_74,tree108_91,tree108_105]
def tree108_107 : CoverTree := CoverTree.split [tree108_0,tree108_1,tree108_2,tree108_3,tree108_60,tree108_106]
def tree108_108 : CoverTree := CoverTree.reject 55
def tree108_109 : CoverTree := CoverTree.reject 107
def tree108_110 : CoverTree := CoverTree.reject 108
def tree108_111 : CoverTree := CoverTree.reject 2
def tree108_112 : CoverTree := CoverTree.reject 124
def tree108_113 : CoverTree := CoverTree.reject 4
def tree108_114 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_20,tree108_31,tree108_17]
def tree108_115 : CoverTree := CoverTree.reject 174
def tree108_116 : CoverTree := CoverTree.split [tree108_19,tree108_115,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_117 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_116,tree108_17,tree108_17]
def tree108_118 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_112,tree108_114,tree108_117]
def tree108_119 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_109,tree108_110,tree108_118]
def tree108_120 : CoverTree := CoverTree.reject 44
def tree108_121 : CoverTree := CoverTree.reject 62
def tree108_122 : CoverTree := CoverTree.reject 104
def tree108_123 : CoverTree := CoverTree.reject 204
def tree108_124 : CoverTree := CoverTree.reject 177
def tree108_125 : CoverTree := CoverTree.reject 178
def tree108_126 : CoverTree := CoverTree.split [tree108_14,tree108_123,tree108_124,tree108_125,tree108_17,tree108_17]
def tree108_127 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_120,tree108_121,tree108_122,tree108_126]
def tree108_128 : CoverTree := CoverTree.reject 121
def tree108_129 : CoverTree := CoverTree.split [tree108_26,tree108_128,tree108_29,tree108_29,tree108_31,tree108_17]
def tree108_130 : CoverTree := CoverTree.reject 175
def tree108_131 : CoverTree := CoverTree.split [tree108_33,tree108_130,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_132 : CoverTree := CoverTree.reject 176
def tree108_133 : CoverTree := CoverTree.split [tree108_16,tree108_17,tree108_132,tree108_17,tree108_17,tree108_17]
def tree108_134 : CoverTree := CoverTree.split [tree108_14,tree108_131,tree108_133,tree108_20,tree108_17,tree108_17]
def tree108_135 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_120,tree108_121,tree108_129,tree108_134]
def tree108_136 : CoverTree := CoverTree.reject 288
def tree108_137 : CoverTree := CoverTree.reject 254
def tree108_138 : CoverTree := CoverTree.reject 230
def tree108_139 : CoverTree := CoverTree.split [tree108_75,tree108_136,tree108_137,tree108_138,tree108_103,tree108_85]
def tree108_140 : CoverTree := CoverTree.reject 255
def tree108_141 : CoverTree := CoverTree.split [tree108_38,tree108_140,tree108_45,tree108_47,tree108_49,tree108_51]
def tree108_142 : CoverTree := CoverTree.reject 179
def tree108_143 : CoverTree := CoverTree.split [tree108_14,tree108_142,tree108_18,tree108_20,tree108_17,tree108_17]
def tree108_144 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_139,tree108_141,tree108_58,tree108_143]
def tree108_145 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_127,tree108_135,tree108_144]
def tree108_146 : CoverTree := CoverTree.reject 135
def tree108_147 : CoverTree := CoverTree.reject 110
def tree108_148 : CoverTree := CoverTree.reject 231
def tree108_149 : CoverTree := CoverTree.reject 232
def tree108_150 : CoverTree := CoverTree.split [tree108_26,tree108_148,tree108_149,tree108_29,tree108_66,tree108_17]
def tree108_151 : CoverTree := CoverTree.reject 205
def tree108_152 : CoverTree := CoverTree.reject 180
def tree108_153 : CoverTree := CoverTree.reject 181
def tree108_154 : CoverTree := CoverTree.split [tree108_14,tree108_151,tree108_152,tree108_153,tree108_17,tree108_17]
def tree108_155 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_146,tree108_147,tree108_150,tree108_154]
def tree108_156 : CoverTree := CoverTree.reject 125
def tree108_157 : CoverTree := CoverTree.reject 106
def tree108_158 : CoverTree := CoverTree.reject 233
def tree108_159 : CoverTree := CoverTree.reject 206
def tree108_160 : CoverTree := CoverTree.split [tree108_26,tree108_158,tree108_159,tree108_29,tree108_31,tree108_17]
def tree108_161 : CoverTree := CoverTree.reject 182
def tree108_162 : CoverTree := CoverTree.split [tree108_14,tree108_161,tree108_18,tree108_20,tree108_17,tree108_17]
def tree108_163 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_156,tree108_157,tree108_160,tree108_162]
def tree108_164 : CoverTree := CoverTree.reject 289
def tree108_165 : CoverTree := CoverTree.reject 256
def tree108_166 : CoverTree := CoverTree.reject 234
def tree108_167 : CoverTree := CoverTree.split [tree108_75,tree108_164,tree108_165,tree108_166,tree108_103,tree108_85]
def tree108_168 : CoverTree := CoverTree.reject 257
def tree108_169 : CoverTree := CoverTree.split [tree108_38,tree108_168,tree108_45,tree108_47,tree108_49,tree108_51]
def tree108_170 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_167,tree108_169,tree108_58,tree108_35]
def tree108_171 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_155,tree108_163,tree108_170]
def tree108_172 : CoverTree := CoverTree.reject 136
def tree108_173 : CoverTree := CoverTree.reject 258
def tree108_174 : CoverTree := CoverTree.reject 259
def tree108_175 : CoverTree := CoverTree.split [tree108_38,tree108_173,tree108_174,tree108_29,tree108_66,tree108_51]
def tree108_176 : CoverTree := CoverTree.reject 235
def tree108_177 : CoverTree := CoverTree.reject 236
def tree108_178 : CoverTree := CoverTree.split [tree108_26,tree108_176,tree108_177,tree108_29,tree108_66,tree108_17]
def tree108_179 : CoverTree := CoverTree.reject 207
def tree108_180 : CoverTree := CoverTree.split [tree108_14,tree108_179,tree108_18,tree108_20,tree108_17,tree108_17]
def tree108_181 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_172,tree108_175,tree108_178,tree108_180]
def tree108_182 : CoverTree := CoverTree.reject 126
def tree108_183 : CoverTree := CoverTree.reject 260
def tree108_184 : CoverTree := CoverTree.split [tree108_38,tree108_183,tree108_87,tree108_29,tree108_89,tree108_51]
def tree108_185 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_182,tree108_184,tree108_32,tree108_35]
def tree108_186 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_181,tree108_185,tree108_105]
def tree108_187 : CoverTree := CoverTree.reject 290
def tree108_188 : CoverTree := CoverTree.reject 261
def tree108_189 : CoverTree := CoverTree.reject 262
def tree108_190 : CoverTree := CoverTree.reject 109
def tree108_191 : CoverTree := CoverTree.split [tree108_84,tree108_190,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_192 : CoverTree := CoverTree.split [tree108_75,tree108_187,tree108_188,tree108_189,tree108_83,tree108_191]
def tree108_193 : CoverTree := CoverTree.reject 263
def tree108_194 : CoverTree := CoverTree.reject 264
def tree108_195 : CoverTree := CoverTree.split [tree108_38,tree108_193,tree108_194,tree108_29,tree108_66,tree108_51]
def tree108_196 : CoverTree := CoverTree.reject 237
def tree108_197 : CoverTree := CoverTree.split [tree108_26,tree108_196,tree108_69,tree108_29,tree108_66,tree108_17]
def tree108_198 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_192,tree108_195,tree108_197,tree108_73]
def tree108_199 : CoverTree := CoverTree.reject 238
def tree108_200 : CoverTree := CoverTree.split [tree108_75,tree108_79,tree108_81,tree108_199,tree108_83,tree108_85]
def tree108_201 : CoverTree := CoverTree.reject 265
def tree108_202 : CoverTree := CoverTree.split [tree108_38,tree108_201,tree108_87,tree108_29,tree108_89,tree108_51]
def tree108_203 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_200,tree108_202,tree108_32,tree108_35]
def tree108_204 : CoverTree := CoverTree.reject 291
def tree108_205 : CoverTree := CoverTree.reject 266
def tree108_206 : CoverTree := CoverTree.split [tree108_75,tree108_204,tree108_205,tree108_100,tree108_103,tree108_85]
def tree108_207 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_206,tree108_52,tree108_58,tree108_35]
def tree108_208 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_198,tree108_203,tree108_207]
def tree108_209 : CoverTree := CoverTree.split [tree108_108,tree108_119,tree108_145,tree108_171,tree108_186,tree108_208]
def tree108_210 : CoverTree := CoverTree.reject 56
def tree108_211 : CoverTree := CoverTree.reject 15
def tree108_212 : CoverTree := CoverTree.reject 23
def tree108_213 : CoverTree := CoverTree.reject 183
def tree108_214 : CoverTree := CoverTree.reject 168
def tree108_215 : CoverTree := CoverTree.reject 202
def tree108_216 : CoverTree := CoverTree.split [tree108_17,tree108_215,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_217 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_213,tree108_214,tree108_216]
def tree108_218 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_211,tree108_212,tree108_217]
def tree108_219 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_20,tree108_17,tree108_17]
def tree108_220 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_211,tree108_212,tree108_219]
def tree108_221 : CoverTree := CoverTree.reject 127
def tree108_222 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_221,tree108_114,tree108_117]
def tree108_223 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_218,tree108_220,tree108_222]
def tree108_224 : CoverTree := CoverTree.reject 111
def tree108_225 : CoverTree := CoverTree.reject 132
def tree108_226 : CoverTree := CoverTree.reject 133
def tree108_227 : CoverTree := CoverTree.reject 208
def tree108_228 : CoverTree := CoverTree.reject 209
def tree108_229 : CoverTree := CoverTree.split [tree108_26,tree108_225,tree108_226,tree108_227,tree108_228,tree108_17]
def tree108_230 : CoverTree := CoverTree.reject 210
def tree108_231 : CoverTree := CoverTree.reject 184
def tree108_232 : CoverTree := CoverTree.split [tree108_14,tree108_230,tree108_231,tree108_20,tree108_17,tree108_17]
def tree108_233 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_120,tree108_224,tree108_229,tree108_232]
def tree108_234 : CoverTree := CoverTree.reject 148
def tree108_235 : CoverTree := CoverTree.reject 203
def tree108_236 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_44,tree108_235,tree108_17,tree108_17]
def tree108_237 : CoverTree := CoverTree.split [tree108_38,tree108_234,tree108_236,tree108_29,tree108_89,tree108_51]
def tree108_238 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_120,tree108_237,tree108_129,tree108_134]
def tree108_239 : CoverTree := CoverTree.reject 292
def tree108_240 : CoverTree := CoverTree.reject 267
def tree108_241 : CoverTree := CoverTree.split [tree108_75,tree108_239,tree108_240,tree108_100,tree108_103,tree108_85]
def tree108_242 : CoverTree := CoverTree.reject 268
def tree108_243 : CoverTree := CoverTree.split [tree108_38,tree108_242,tree108_45,tree108_47,tree108_49,tree108_51]
def tree108_244 : CoverTree := CoverTree.reject 185
def tree108_245 : CoverTree := CoverTree.split [tree108_14,tree108_244,tree108_18,tree108_20,tree108_17,tree108_17]
def tree108_246 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_241,tree108_243,tree108_58,tree108_245]
def tree108_247 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_233,tree108_238,tree108_246]
def tree108_248 : CoverTree := CoverTree.reject 137
def tree108_249 : CoverTree := CoverTree.reject 112
def tree108_250 : CoverTree := CoverTree.reject 239
def tree108_251 : CoverTree := CoverTree.reject 240
def tree108_252 : CoverTree := CoverTree.split [tree108_26,tree108_250,tree108_251,tree108_29,tree108_66,tree108_17]
def tree108_253 : CoverTree := CoverTree.reject 211
def tree108_254 : CoverTree := CoverTree.split [tree108_14,tree108_253,tree108_18,tree108_20,tree108_17,tree108_17]
def tree108_255 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_248,tree108_249,tree108_252,tree108_254]
def tree108_256 : CoverTree := CoverTree.reject 151
def tree108_257 : CoverTree := CoverTree.split [tree108_75,tree108_256,tree108_81,tree108_82,tree108_83,tree108_85]
def tree108_258 : CoverTree := CoverTree.reject 149
def tree108_259 : CoverTree := CoverTree.split [tree108_38,tree108_258,tree108_87,tree108_29,tree108_89,tree108_51]
def tree108_260 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_257,tree108_259,tree108_32,tree108_35]
def tree108_261 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_255,tree108_260,tree108_105]
def tree108_262 : CoverTree := CoverTree.reject 138
def tree108_263 : CoverTree := CoverTree.reject 269
def tree108_264 : CoverTree := CoverTree.reject 270
def tree108_265 : CoverTree := CoverTree.split [tree108_38,tree108_263,tree108_264,tree108_29,tree108_66,tree108_51]
def tree108_266 : CoverTree := CoverTree.reject 241
def tree108_267 : CoverTree := CoverTree.split [tree108_26,tree108_266,tree108_69,tree108_29,tree108_66,tree108_17]
def tree108_268 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_262,tree108_265,tree108_267,tree108_73]
def tree108_269 : CoverTree := CoverTree.reject 271
def tree108_270 : CoverTree := CoverTree.split [tree108_38,tree108_269,tree108_87,tree108_29,tree108_89,tree108_51]
def tree108_271 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_86,tree108_270,tree108_32,tree108_35]
def tree108_272 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_268,tree108_271,tree108_105]
def tree108_273 : CoverTree := CoverTree.reject 293
def tree108_274 : CoverTree := CoverTree.reject 272
def tree108_275 : CoverTree := CoverTree.reject 273
def tree108_276 : CoverTree := CoverTree.split [tree108_75,tree108_273,tree108_274,tree108_275,tree108_83,tree108_191]
def tree108_277 : CoverTree := CoverTree.reject 274
def tree108_278 : CoverTree := CoverTree.split [tree108_38,tree108_277,tree108_64,tree108_29,tree108_66,tree108_51]
def tree108_279 : CoverTree := CoverTree.split [tree108_5,tree108_5,tree108_276,tree108_278,tree108_70,tree108_73]
def tree108_280 : CoverTree := CoverTree.split [tree108_4,tree108_4,tree108_4,tree108_279,tree108_91,tree108_105]
def tree108_281 : CoverTree := CoverTree.split [tree108_210,tree108_223,tree108_247,tree108_261,tree108_272,tree108_280]
def tree108_282 : CoverTree := CoverTree.reject 20
def tree108_283 : CoverTree := CoverTree.reject 59
def tree108_284 : CoverTree := CoverTree.reject 116
def tree108_285 : CoverTree := CoverTree.reject 129
def tree108_286 : CoverTree := CoverTree.reject 1
def tree108_287 : CoverTree := CoverTree.reject 7
def tree108_288 : CoverTree := CoverTree.split [tree108_287,tree108_287,tree108_17,tree108_17,tree108_17,tree108_17]
def tree108_289 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_288,tree108_288,tree108_288]
def tree108_290 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_211,tree108_285,tree108_289]
def tree108_291 : CoverTree := CoverTree.reject 167
def tree108_292 : CoverTree := CoverTree.reject 186
def tree108_293 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_292,tree108_17,tree108_216]
def tree108_294 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_211,tree108_291,tree108_293]
def tree108_295 : CoverTree := CoverTree.reject 100
def tree108_296 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_295,tree108_31,tree108_17]
def tree108_297 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_211,tree108_296,tree108_219]
def tree108_298 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_47,tree108_49,tree108_51]
def tree108_299 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_298,tree108_114,tree108_117]
def tree108_300 : CoverTree := CoverTree.split [tree108_283,tree108_284,tree108_290,tree108_294,tree108_297,tree108_299]
def tree108_301 : CoverTree := CoverTree.reject 35
def tree108_302 : CoverTree := CoverTree.reject 10
def tree108_303 : CoverTree := CoverTree.reject 66
def tree108_304 : CoverTree := CoverTree.reject 67
def tree108_305 : CoverTree := CoverTree.reject 212
def tree108_306 : CoverTree := CoverTree.reject 213
def tree108_307 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_305,tree108_306,tree108_288]
def tree108_308 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_120,tree108_303,tree108_304,tree108_307]
def tree108_309 : CoverTree := CoverTree.reject 68
def tree108_310 : CoverTree := CoverTree.reject 147
def tree108_311 : CoverTree := CoverTree.reject 214
def tree108_312 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_310,tree108_311,tree108_288]
def tree108_313 : CoverTree := CoverTree.reject 229
def tree108_314 : CoverTree := CoverTree.split [tree108_287,tree108_287,tree108_313,tree108_17,tree108_17,tree108_17]
def tree108_315 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_288,tree108_314,tree108_288]
def tree108_316 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_120,tree108_309,tree108_312,tree108_315]
def tree108_317 : CoverTree := CoverTree.reject 113
def tree108_318 : CoverTree := CoverTree.split [tree108_26,tree108_225,tree108_226,tree108_29,tree108_66,tree108_17]
def tree108_319 : CoverTree := CoverTree.reject 215
def tree108_320 : CoverTree := CoverTree.reject 187
def tree108_321 : CoverTree := CoverTree.split [tree108_14,tree108_319,tree108_320,tree108_20,tree108_17,tree108_17]
def tree108_322 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_120,tree108_317,tree108_318,tree108_321]
def tree108_323 : CoverTree := CoverTree.reject 22
def tree108_324 : CoverTree := CoverTree.reject 216
def tree108_325 : CoverTree := CoverTree.split [tree108_14,tree108_324,tree108_133,tree108_20,tree108_17,tree108_17]
def tree108_326 : CoverTree := CoverTree.split [tree108_323,tree108_323,tree108_120,tree108_237,tree108_129,tree108_325]
def tree108_327 : CoverTree := CoverTree.reject 294
def tree108_328 : CoverTree := CoverTree.split [tree108_75,tree108_327,tree108_97,tree108_100,tree108_103,tree108_85]
def tree108_329 : CoverTree := CoverTree.reject 275
def tree108_330 : CoverTree := CoverTree.split [tree108_38,tree108_329,tree108_45,tree108_47,tree108_49,tree108_51]
def tree108_331 : CoverTree := CoverTree.split [tree108_323,tree108_323,tree108_328,tree108_330,tree108_58,tree108_35]
def tree108_332 : CoverTree := CoverTree.split [tree108_301,tree108_308,tree108_316,tree108_322,tree108_326,tree108_331]
def tree108_333 : CoverTree := CoverTree.reject 27
def tree108_334 : CoverTree := CoverTree.reject 77
def tree108_335 : CoverTree := CoverTree.reject 69
def tree108_336 : CoverTree := CoverTree.reject 242
def tree108_337 : CoverTree := CoverTree.reject 243
def tree108_338 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_336,tree108_337,tree108_288]
def tree108_339 : CoverTree := CoverTree.reject 217
def tree108_340 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_339,tree108_288,tree108_288]
def tree108_341 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_334,tree108_335,tree108_338,tree108_340]
def tree108_342 : CoverTree := CoverTree.reject 78
def tree108_343 : CoverTree := CoverTree.reject 150
def tree108_344 : CoverTree := CoverTree.reject 131
def tree108_345 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_344,tree108_17,tree108_17,tree108_17]
def tree108_346 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_345,tree108_288,tree108_288]
def tree108_347 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_342,tree108_343,tree108_346,tree108_289]
def tree108_348 : CoverTree := CoverTree.reject 162
def tree108_349 : CoverTree := CoverTree.reject 163
def tree108_350 : CoverTree := CoverTree.split [tree108_75,tree108_256,tree108_348,tree108_349,tree108_83,tree108_191]
def tree108_351 : CoverTree := CoverTree.reject 164
def tree108_352 : CoverTree := CoverTree.reject 165
def tree108_353 : CoverTree := CoverTree.split [tree108_38,tree108_351,tree108_352,tree108_29,tree108_66,tree108_51]
def tree108_354 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_350,tree108_353,tree108_70,tree108_73]
def tree108_355 : CoverTree := CoverTree.reject 115
def tree108_356 : CoverTree := CoverTree.split [tree108_355,tree108_355,tree108_257,tree108_259,tree108_32,tree108_35]
def tree108_357 : CoverTree := CoverTree.reject 60
def tree108_358 : CoverTree := CoverTree.reject 75
def tree108_359 : CoverTree := CoverTree.reject 225
def tree108_360 : CoverTree := CoverTree.reject 226
def tree108_361 : CoverTree := CoverTree.reject 3
def tree108_362 : CoverTree := CoverTree.reject 144
def tree108_363 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_362,tree108_17,tree108_17]
def tree108_364 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_17,tree108_17,tree108_17]
def tree108_365 : CoverTree := CoverTree.split [tree108_358,tree108_359,tree108_360,tree108_363,tree108_364,tree108_364]
def tree108_366 : CoverTree := CoverTree.split [tree108_357,tree108_365,tree108_104,tree108_52,tree108_58,tree108_35]
def tree108_367 : CoverTree := CoverTree.split [tree108_333,tree108_341,tree108_347,tree108_354,tree108_356,tree108_366]
def tree108_368 : CoverTree := CoverTree.reject 48
def tree108_369 : CoverTree := CoverTree.reject 21
def tree108_370 : CoverTree := CoverTree.reject 70
def tree108_371 : CoverTree := CoverTree.reject 71
def tree108_372 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_368,tree108_369,tree108_370,tree108_371]
def tree108_373 : CoverTree := CoverTree.reject 79
def tree108_374 : CoverTree := CoverTree.reject 276
def tree108_375 : CoverTree := CoverTree.reject 277
def tree108_376 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_374,tree108_375,tree108_288]
def tree108_377 : CoverTree := CoverTree.reject 244
def tree108_378 : CoverTree := CoverTree.reject 245
def tree108_379 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_377,tree108_378,tree108_288]
def tree108_380 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_373,tree108_376,tree108_379,tree108_289]
def tree108_381 : CoverTree := CoverTree.reject 140
def tree108_382 : CoverTree := CoverTree.reject 159
def tree108_383 : CoverTree := CoverTree.reject 160
def tree108_384 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_382,tree108_383,tree108_17,tree108_17]
def tree108_385 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_384,tree108_288,tree108_288]
def tree108_386 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_381,tree108_385,tree108_346,tree108_289]
def tree108_387 : CoverTree := CoverTree.reject 227
def tree108_388 : CoverTree := CoverTree.reject 278
def tree108_389 : CoverTree := CoverTree.reject 118
def tree108_390 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_76,tree108_389,tree108_17,tree108_17]
def tree108_391 : CoverTree := CoverTree.split [tree108_75,tree108_387,tree108_388,tree108_390,tree108_83,tree108_191]
def tree108_392 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_391,tree108_67,tree108_70,tree108_73]
def tree108_393 : CoverTree := CoverTree.split [tree108_355,tree108_355,tree108_86,tree108_90,tree108_32,tree108_35]
def tree108_394 : CoverTree := CoverTree.reject 105
def tree108_395 : CoverTree := CoverTree.reject 82
def tree108_396 : CoverTree := CoverTree.reject 83
def tree108_397 : CoverTree := CoverTree.reject 38
def tree108_398 : CoverTree := CoverTree.reject 153
def tree108_399 : CoverTree := CoverTree.reject 139
def tree108_400 : CoverTree := CoverTree.reject 161
def tree108_401 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_398,tree108_399,tree108_400]
def tree108_402 : CoverTree := CoverTree.reject 80
def tree108_403 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_402,tree108_17,tree108_17]
def tree108_404 : CoverTree := CoverTree.split [tree108_394,tree108_395,tree108_396,tree108_397,tree108_401,tree108_403]
def tree108_405 : CoverTree := CoverTree.reject 142
def tree108_406 : CoverTree := CoverTree.reject 119
def tree108_407 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_405,tree108_406,tree108_17]
def tree108_408 : CoverTree := CoverTree.reject 143
def tree108_409 : CoverTree := CoverTree.reject 120
def tree108_410 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_408,tree108_409,tree108_17]
def tree108_411 : CoverTree := CoverTree.split [tree108_358,tree108_407,tree108_410,tree108_363,tree108_364,tree108_364]
def tree108_412 : CoverTree := CoverTree.split [tree108_404,tree108_411,tree108_104,tree108_52,tree108_58,tree108_35]
def tree108_413 : CoverTree := CoverTree.split [tree108_372,tree108_380,tree108_386,tree108_392,tree108_393,tree108_412]
def tree108_414 : CoverTree := CoverTree.reject 128
def tree108_415 : CoverTree := CoverTree.reject 101
def tree108_416 : CoverTree := CoverTree.reject 72
def tree108_417 : CoverTree := CoverTree.reject 73
def tree108_418 : CoverTree := CoverTree.split [tree108_414,tree108_415,tree108_368,tree108_369,tree108_416,tree108_417]
def tree108_419 : CoverTree := CoverTree.reject 122
def tree108_420 : CoverTree := CoverTree.reject 173
def tree108_421 : CoverTree := CoverTree.reject 295
def tree108_422 : CoverTree := CoverTree.reject 279
def tree108_423 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_421,tree108_422,tree108_288]
def tree108_424 : CoverTree := CoverTree.reject 280
def tree108_425 : CoverTree := CoverTree.reject 157
def tree108_426 : CoverTree := CoverTree.reject 158
def tree108_427 : CoverTree := CoverTree.split [tree108_287,tree108_287,tree108_425,tree108_426,tree108_17,tree108_17]
def tree108_428 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_424,tree108_427,tree108_288]
def tree108_429 : CoverTree := CoverTree.reject 145
def tree108_430 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_429,tree108_17,tree108_17,tree108_17]
def tree108_431 : CoverTree := CoverTree.reject 146
def tree108_432 : CoverTree := CoverTree.split [tree108_287,tree108_287,tree108_431,tree108_17,tree108_17,tree108_17]
def tree108_433 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_430,tree108_432,tree108_288]
def tree108_434 : CoverTree := CoverTree.split [tree108_419,tree108_420,tree108_423,tree108_428,tree108_433,tree108_289]
def tree108_435 : CoverTree := CoverTree.reject 123
def tree108_436 : CoverTree := CoverTree.reject 19
def tree108_437 : CoverTree := CoverTree.reject 63
def tree108_438 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_436,tree108_437,tree108_17]
def tree108_439 : CoverTree := CoverTree.reject 296
def tree108_440 : CoverTree := CoverTree.reject 195
def tree108_441 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_440,tree108_17,tree108_17]
def tree108_442 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_438,tree108_439,tree108_441]
def tree108_443 : CoverTree := CoverTree.reject 172
def tree108_444 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_76,tree108_443,tree108_17,tree108_17]
def tree108_445 : CoverTree := CoverTree.split [tree108_287,tree108_287,tree108_76,tree108_17,tree108_17,tree108_17]
def tree108_446 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_444,tree108_445,tree108_288]
def tree108_447 : CoverTree := CoverTree.split [tree108_435,tree108_442,tree108_446,tree108_385,tree108_346,tree108_289]
def tree108_448 : CoverTree := CoverTree.reject 61
def tree108_449 : CoverTree := CoverTree.reject 220
def tree108_450 : CoverTree := CoverTree.reject 297
def tree108_451 : CoverTree := CoverTree.reject 298
def tree108_452 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_436,tree108_17,tree108_17]
def tree108_453 : CoverTree := CoverTree.split [tree108_358,tree108_449,tree108_450,tree108_451,tree108_452,tree108_364]
def tree108_454 : CoverTree := CoverTree.reject 299
def tree108_455 : CoverTree := CoverTree.split [tree108_75,tree108_454,tree108_81,tree108_390,tree108_83,tree108_191]
def tree108_456 : CoverTree := CoverTree.reject 281
def tree108_457 : CoverTree := CoverTree.split [tree108_38,tree108_456,tree108_64,tree108_29,tree108_66,tree108_51]
def tree108_458 : CoverTree := CoverTree.split [tree108_448,tree108_453,tree108_455,tree108_457,tree108_70,tree108_73]
def tree108_459 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_436,tree108_399,tree108_17]
def tree108_460 : CoverTree := CoverTree.reject 166
def tree108_461 : CoverTree := CoverTree.split [tree108_394,tree108_395,tree108_396,tree108_397,tree108_459,tree108_460]
def tree108_462 : CoverTree := CoverTree.reject 221
def tree108_463 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_436,tree108_409,tree108_17]
def tree108_464 : CoverTree := CoverTree.split [tree108_358,tree108_462,tree108_463,tree108_452,tree108_452,tree108_364]
def tree108_465 : CoverTree := CoverTree.split [tree108_461,tree108_464,tree108_86,tree108_90,tree108_32,tree108_35]
def tree108_466 : CoverTree := CoverTree.split [tree108_418,tree108_434,tree108_447,tree108_458,tree108_465,tree108_412]
def tree108_467 : CoverTree := CoverTree.split [tree108_282,tree108_300,tree108_332,tree108_367,tree108_413,tree108_466]
def tree108_468 : CoverTree := CoverTree.reject 74
def tree108_469 : CoverTree := CoverTree.reject 64
def tree108_470 : CoverTree := CoverTree.reject 65
def tree108_471 : CoverTree := CoverTree.reject 28
def tree108_472 : CoverTree := CoverTree.reject 76
def tree108_473 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_211,tree108_472,tree108_219]
def tree108_474 : CoverTree := CoverTree.reject 34
def tree108_475 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_474,tree108_114,tree108_219]
def tree108_476 : CoverTree := CoverTree.split [tree108_468,tree108_469,tree108_470,tree108_471,tree108_473,tree108_475]
def tree108_477 : CoverTree := CoverTree.reject 117
def tree108_478 : CoverTree := CoverTree.reject 218
def tree108_479 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_478,tree108_288,tree108_288]
def tree108_480 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_211,tree108_285,tree108_479]
def tree108_481 : CoverTree := CoverTree.reject 9
def tree108_482 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_481,tree108_481,tree108_17]
def tree108_483 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_20,tree108_17,tree108_216]
def tree108_484 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_211,tree108_482,tree108_483]
def tree108_485 : CoverTree := CoverTree.split [tree108_283,tree108_477,tree108_480,tree108_484,tree108_297,tree108_299]
def tree108_486 : CoverTree := CoverTree.reject 219
def tree108_487 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_486,tree108_288,tree108_288]
def tree108_488 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_120,tree108_303,tree108_304,tree108_487]
def tree108_489 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_310,tree108_288,tree108_288]
def tree108_490 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_120,tree108_309,tree108_489,tree108_315]
def tree108_491 : CoverTree := CoverTree.reject 199
def tree108_492 : CoverTree := CoverTree.reject 200
def tree108_493 : CoverTree := CoverTree.split [tree108_38,tree108_491,tree108_492,tree108_29,tree108_66,tree108_51]
def tree108_494 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_120,tree108_493,tree108_318,tree108_73]
def tree108_495 : CoverTree := CoverTree.split [tree108_323,tree108_323,tree108_120,tree108_237,tree108_129,tree108_134]
def tree108_496 : CoverTree := CoverTree.split [tree108_323,tree108_323,tree108_104,tree108_52,tree108_58,tree108_35]
def tree108_497 : CoverTree := CoverTree.split [tree108_301,tree108_488,tree108_490,tree108_494,tree108_495,tree108_496]
def tree108_498 : CoverTree := CoverTree.reject 246
def tree108_499 : CoverTree := CoverTree.reject 247
def tree108_500 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_498,tree108_499,tree108_288]
def tree108_501 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_334,tree108_335,tree108_500,tree108_289]
def tree108_502 : CoverTree := CoverTree.reject 134
def tree108_503 : CoverTree := CoverTree.reject 253
def tree108_504 : CoverTree := CoverTree.split [tree108_287,tree108_287,tree108_503,tree108_17,tree108_17,tree108_17]
def tree108_505 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_502,tree108_504,tree108_288]
def tree108_506 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_342,tree108_505,tree108_346,tree108_289]
def tree108_507 : CoverTree := CoverTree.reject 194
def tree108_508 : CoverTree := CoverTree.reject 228
def tree108_509 : CoverTree := CoverTree.split [tree108_507,tree108_508,tree108_257,tree108_259,tree108_32,tree108_35]
def tree108_510 : CoverTree := CoverTree.split [tree108_333,tree108_501,tree108_506,tree108_354,tree108_509,tree108_366]
def tree108_511 : CoverTree := CoverTree.reject 282
def tree108_512 : CoverTree := CoverTree.reject 283
def tree108_513 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_511,tree108_512,tree108_288]
def tree108_514 : CoverTree := CoverTree.reject 248
def tree108_515 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_514,tree108_432,tree108_288]
def tree108_516 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_373,tree108_513,tree108_515,tree108_289]
def tree108_517 : CoverTree := CoverTree.reject 284
def tree108_518 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_517,tree108_445,tree108_288]
def tree108_519 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_518,tree108_385,tree108_346,tree108_289]
def tree108_520 : CoverTree := CoverTree.reject 285
def tree108_521 : CoverTree := CoverTree.split [tree108_75,tree108_387,tree108_520,tree108_390,tree108_83,tree108_191]
def tree108_522 : CoverTree := CoverTree.split [tree108_302,tree108_302,tree108_521,tree108_67,tree108_70,tree108_73]
def tree108_523 : CoverTree := CoverTree.reject 154
def tree108_524 : CoverTree := CoverTree.reject 58
def tree108_525 : CoverTree := CoverTree.split [tree108_524,tree108_524,tree108_524,tree108_452,tree108_452,tree108_364]
def tree108_526 : CoverTree := CoverTree.split [tree108_523,tree108_525,tree108_86,tree108_90,tree108_32,tree108_35]
def tree108_527 : CoverTree := CoverTree.split [tree108_372,tree108_516,tree108_519,tree108_522,tree108_526,tree108_412]
def tree108_528 : CoverTree := CoverTree.reject 249
def tree108_529 : CoverTree := CoverTree.reject 250
def tree108_530 : CoverTree := CoverTree.reject 252
def tree108_531 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_530,tree108_17,tree108_17]
def tree108_532 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_528,tree108_529,tree108_531]
def tree108_533 : CoverTree := CoverTree.reject 300
def tree108_534 : CoverTree := CoverTree.reject 152
def tree108_535 : CoverTree := CoverTree.split [tree108_287,tree108_287,tree108_76,tree108_534,tree108_17,tree108_17]
def tree108_536 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_533,tree108_535,tree108_288]
def tree108_537 : CoverTree := CoverTree.reject 155
def tree108_538 : CoverTree := CoverTree.reject 156
def tree108_539 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_537,tree108_538,tree108_17,tree108_17]
def tree108_540 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_539,tree108_427,tree108_288]
def tree108_541 : CoverTree := CoverTree.split [tree108_419,tree108_532,tree108_536,tree108_540,tree108_433,tree108_289]
def tree108_542 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_438,tree108_438,tree108_441]
def tree108_543 : CoverTree := CoverTree.split [tree108_435,tree108_542,tree108_446,tree108_385,tree108_346,tree108_289]
def tree108_544 : CoverTree := CoverTree.reject 301
def tree108_545 : CoverTree := CoverTree.reject 196
def tree108_546 : CoverTree := CoverTree.split [tree108_361,tree108_361,tree108_361,tree108_436,tree108_545,tree108_17]
def tree108_547 : CoverTree := CoverTree.split [tree108_358,tree108_449,tree108_544,tree108_546,tree108_452,tree108_364]
def tree108_548 : CoverTree := CoverTree.split [tree108_75,tree108_79,tree108_81,tree108_390,tree108_83,tree108_191]
def tree108_549 : CoverTree := CoverTree.split [tree108_448,tree108_547,tree108_548,tree108_67,tree108_70,tree108_73]
def tree108_550 : CoverTree := CoverTree.split [tree108_418,tree108_541,tree108_543,tree108_549,tree108_465,tree108_412]
def tree108_551 : CoverTree := CoverTree.split [tree108_476,tree108_485,tree108_497,tree108_510,tree108_527,tree108_550]
def tree108_552 : CoverTree := CoverTree.reject 141
def tree108_553 : CoverTree := CoverTree.reject 114
def tree108_554 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_552,tree108_472,tree108_553]
def tree108_555 : CoverTree := CoverTree.split [tree108_468,tree108_469,tree108_470,tree108_471,tree108_554,tree108_475]
def tree108_556 : CoverTree := CoverTree.reject 188
def tree108_557 : CoverTree := CoverTree.reject 189
def tree108_558 : CoverTree := CoverTree.reject 197
def tree108_559 : CoverTree := CoverTree.reject 287
def tree108_560 : CoverTree := CoverTree.split [tree108_287,tree108_287,tree108_559,tree108_17,tree108_17,tree108_17]
def tree108_561 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_558,tree108_560,tree108_288]
def tree108_562 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_556,tree108_557,tree108_561]
def tree108_563 : CoverTree := CoverTree.reject 190
def tree108_564 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_563,tree108_285,tree108_289]
def tree108_565 : CoverTree := CoverTree.reject 169
def tree108_566 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_565,tree108_482,tree108_483]
def tree108_567 : CoverTree := CoverTree.reject 198
def tree108_568 : CoverTree := CoverTree.split [tree108_113,tree108_113,tree108_113,tree108_295,tree108_567,tree108_51]
def tree108_569 : CoverTree := CoverTree.split [tree108_111,tree108_111,tree108_111,tree108_568,tree108_296,tree108_219]
def tree108_570 : CoverTree := CoverTree.split [tree108_283,tree108_562,tree108_564,tree108_566,tree108_569,tree108_299]
def tree108_571 : CoverTree := CoverTree.reject 191
def tree108_572 : CoverTree := CoverTree.split [tree108_323,tree108_323,tree108_571,tree108_303,tree108_304,tree108_289]
def tree108_573 : CoverTree := CoverTree.reject 192
def tree108_574 : CoverTree := CoverTree.split [tree108_323,tree108_323,tree108_573,tree108_309,tree108_489,tree108_315]
def tree108_575 : CoverTree := CoverTree.reject 193
def tree108_576 : CoverTree := CoverTree.split [tree108_323,tree108_323,tree108_575,tree108_493,tree108_318,tree108_73]
def tree108_577 : CoverTree := CoverTree.reject 8
def tree108_578 : CoverTree := CoverTree.split [tree108_577,tree108_577,tree108_577,tree108_577,tree108_577,tree108_85]
def tree108_579 : CoverTree := CoverTree.split [tree108_323,tree108_323,tree108_578,tree108_237,tree108_129,tree108_134]
def tree108_580 : CoverTree := CoverTree.split [tree108_301,tree108_572,tree108_574,tree108_576,tree108_579,tree108_496]
def tree108_581 : CoverTree := CoverTree.reject 222
def tree108_582 : CoverTree := CoverTree.split [tree108_419,tree108_581,tree108_334,tree108_335,tree108_433,tree108_289]
def tree108_583 : CoverTree := CoverTree.reject 251
def tree108_584 : CoverTree := CoverTree.split [tree108_435,tree108_583,tree108_342,tree108_505,tree108_346,tree108_289]
def tree108_585 : CoverTree := CoverTree.reject 223
def tree108_586 : CoverTree := CoverTree.split [tree108_448,tree108_585,tree108_350,tree108_353,tree108_70,tree108_73]
def tree108_587 : CoverTree := CoverTree.reject 29
def tree108_588 : CoverTree := CoverTree.split [tree108_587,tree108_587,tree108_587,tree108_587,tree108_587,tree108_364]
def tree108_589 : CoverTree := CoverTree.split [tree108_507,tree108_588,tree108_257,tree108_259,tree108_32,tree108_35]
def tree108_590 : CoverTree := CoverTree.split [tree108_333,tree108_582,tree108_584,tree108_586,tree108_589,tree108_366]
def tree108_591 : CoverTree := CoverTree.split [tree108_414,tree108_415,tree108_368,tree108_369,tree108_370,tree108_371]
def tree108_592 : CoverTree := CoverTree.reject 170
def tree108_593 : CoverTree := CoverTree.split [tree108_419,tree108_592,tree108_373,tree108_540,tree108_433,tree108_289]
def tree108_594 : CoverTree := CoverTree.reject 171
def tree108_595 : CoverTree := CoverTree.split [tree108_435,tree108_594,tree108_446,tree108_385,tree108_346,tree108_289]
def tree108_596 : CoverTree := CoverTree.reject 286
def tree108_597 : CoverTree := CoverTree.split [tree108_524,tree108_524,tree108_524,tree108_596,tree108_452,tree108_364]
def tree108_598 : CoverTree := CoverTree.split [tree108_75,tree108_387,tree108_81,tree108_390,tree108_83,tree108_191]
def tree108_599 : CoverTree := CoverTree.split [tree108_448,tree108_597,tree108_598,tree108_67,tree108_70,tree108_73]
def tree108_600 : CoverTree := CoverTree.split [tree108_591,tree108_593,tree108_595,tree108_599,tree108_526,tree108_412]
def tree108_601 : CoverTree := CoverTree.reject 224
def tree108_602 : CoverTree := CoverTree.split [tree108_23,tree108_23,tree108_76,tree108_534,tree108_601,tree108_17]
def tree108_603 : CoverTree := CoverTree.split [tree108_286,tree108_286,tree108_286,tree108_602,tree108_535,tree108_288]
def tree108_604 : CoverTree := CoverTree.split [tree108_419,tree108_532,tree108_603,tree108_540,tree108_433,tree108_289]
def tree108_605 : CoverTree := CoverTree.split [tree108_358,tree108_449,tree108_463,tree108_546,tree108_452,tree108_364]
def tree108_606 : CoverTree := CoverTree.split [tree108_448,tree108_605,tree108_548,tree108_67,tree108_70,tree108_73]
def tree108_607 : CoverTree := CoverTree.split [tree108_418,tree108_604,tree108_543,tree108_606,tree108_465,tree108_412]
def tree108_608 : CoverTree := CoverTree.split [tree108_555,tree108_570,tree108_580,tree108_590,tree108_600,tree108_607]
def tree108_609 : CoverTree := CoverTree.split [tree108_107,tree108_209,tree108_281,tree108_467,tree108_551,tree108_608]
def tree108 : CoverTree := tree108_609

end Snake9.Shared89
