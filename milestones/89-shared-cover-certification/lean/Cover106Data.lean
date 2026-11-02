import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes106 : List Box := [
[(1,3),(1,6),(1,3),(1,6),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,3),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,6),(1,6),(1,2)],
[(1,3),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)],
[(1,6),(1,2),(1,5),(1,5),(1,4),(1,6)],
[(1,6),(1,4),(1,5),(1,5),(1,1),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,6),(1,3)],
[(1,6),(1,3),(1,5),(1,3),(1,5),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,5),(1,5),(1,2),(1,3),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,2),(1,5),(1,6)],
[(1,6),(1,2),(1,4),(1,5),(1,5),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,1)],
[(1,6),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)],
[(1,6),(5,5),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,1),(6,6),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
[(1,6),(2,2),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(6,6),(1,1),(1,6),(1,6)],
[(1,4),(1,5),(1,5),(1,2),(1,6),(1,6)],
[(1,2),(1,3),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(1,6),(1,1),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,3),(1,2),(1,6)],
[(1,6),(1,1),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(3,3),(6,6),(1,1),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(5,5),(1,1),(1,6),(1,6)],
[(1,1),(5,5),(6,6),(3,3),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(5,5),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,6),(1,6),(2,2),(5,5),(1,1)],
[(2,2),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(2,2)],
[(1,6),(3,3),(4,4),(5,5),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(3,3),(5,5),(5,5),(2,2),(1,6)],
[(3,3),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(1,3),(1,2),(1,5),(1,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(1,6),(6,6),(5,5),(1,1),(6,6),(1,6)],
[(4,4),(3,3),(6,6),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(4,4),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(5,5),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(2,2),(6,6),(4,4),(3,3),(1,6)],
[(1,6),(4,4),(2,2),(5,5),(3,3),(1,6)],
[(1,6),(4,4),(2,2),(6,6),(2,2),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(5,5),(2,2),(4,4),(3,3),(1,6)],
[(1,6),(5,5),(2,2),(5,5),(3,3),(1,6)],
[(1,6),(6,6),(2,2),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(4,4),(5,5),(1,1)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(2,2)],
[(1,6),(1,1),(5,5),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(1,1),(1,6)],
[(1,6),(4,4),(5,5),(1,1),(1,6),(1,6)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(1,1),(5,5)],
[(1,6),(1,6),(3,3),(6,6),(1,1),(5,5)],
[(1,6),(3,3),(2,2),(6,6),(2,2),(1,6)],
[(1,6),(3,3),(2,2),(6,6),(3,3),(1,6)],
[(1,6),(3,3),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(3,3),(3,3),(5,5),(3,3),(1,6)],
[(1,6),(3,3),(3,3),(5,5),(4,4),(1,6)],
[(1,6),(3,3),(3,3),(6,6),(2,2),(1,6)],
[(1,6),(4,4),(2,2),(5,5),(2,2),(1,6)],
[(1,6),(4,4),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(3,3),(1,6)],
[(1,6),(5,5),(2,2),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(2,2),(5,5),(2,2),(1,6)],
[(1,6),(5,5),(3,3),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(3,3),(5,5),(2,2),(1,6)],
[(2,2),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(6,6),(1,1),(5,5),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(5,5),(1,1),(5,5)],
[(2,2),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(3,3),(2,2),(5,5)],
[(1,6),(3,3),(4,4),(6,6),(1,1),(1,6)],
[(1,6),(3,3),(6,6),(5,5),(1,1),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(5,5),(3,3),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(2,2)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(3,3),(2,2),(1,6)],
[(1,6),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(1,1)],
[(1,6),(5,5),(4,4),(3,3),(2,2),(1,6)],
[(1,6),(6,6),(3,3),(3,3),(2,2),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(3,3),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(1,1)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(6,6),(2,2),(3,3),(3,3)],
[(1,6),(3,3),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(3,3),(6,6),(2,2),(4,4),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(2,2),(1,6)],
[(1,6),(1,1),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(1,1)],
[(1,6),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(2,2)],
[(1,6),(3,3),(6,6),(2,2),(3,3),(1,6)],
[(1,6),(5,5),(3,3),(3,3),(2,2),(1,6)],
[(5,5),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(4,4),(3,3),(2,2),(5,5)],
[(1,6),(1,6),(5,5),(2,2),(4,4),(2,2)],
[(1,6),(5,5),(4,4),(2,2),(4,4),(1,6)],
[(1,6),(5,5),(4,4),(5,5),(1,1),(1,6)],
[(1,1),(5,5),(4,4),(6,6),(2,2),(1,6)],
[(1,6),(3,3),(6,6),(4,4),(3,3),(3,3)],
[(1,6),(4,4),(4,4),(5,5),(2,2),(3,3)],
[(1,6),(4,4),(6,6),(3,3),(3,3),(2,2)],
[(1,6),(5,5),(4,4),(4,4),(2,2),(3,3)],
[(2,2),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(4,4),(5,5),(5,5),(3,3),(1,6)],
[(2,2),(4,4),(5,5),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(5,5),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(6,6),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(6,6),(5,5),(3,3),(4,4),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(3,3),(4,4),(4,4),(6,6),(2,2),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(3,3),(6,6),(4,4),(3,3),(4,4),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(5,5),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(3,3),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(4,4),(4,4),(3,3),(5,5),(3,3),(1,6)],
[(4,4),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(4,4),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(5,5),(2,2),(4,4),(5,5),(1,6)],
[(4,4),(5,5),(2,2),(5,5),(4,4),(1,6)],
[(4,4),(5,5),(2,2),(5,5),(5,5),(1,6)],
[(4,4),(5,5),(2,2),(6,6),(2,2),(1,6)],
[(4,4),(5,5),(2,2),(6,6),(3,3),(1,6)],
[(4,4),(5,5),(3,3),(4,4),(3,3),(1,6)],
[(4,4),(5,5),(3,3),(5,5),(3,3),(1,6)],
[(4,4),(6,6),(2,2),(3,3),(4,4),(1,6)],
[(4,4),(6,6),(2,2),(3,3),(5,5),(1,6)],
[(4,4),(6,6),(2,2),(4,4),(3,3),(1,6)],
[(4,4),(6,6),(2,2),(6,6),(2,2),(1,6)],
[(4,4),(6,6),(3,3),(2,2),(5,5),(1,6)],
[(4,4),(6,6),(3,3),(3,3),(3,3),(1,6)],
[(4,4),(6,6),(4,4),(2,2),(4,4),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(5,5),(1,6)],
[(5,5),(4,4),(3,3),(5,5),(3,3),(1,6)],
[(5,5),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(5,5),(5,5),(2,2),(4,4),(5,5),(1,6)],
[(5,5),(5,5),(2,2),(5,5),(4,4),(1,6)],
[(5,5),(5,5),(2,2),(6,6),(2,2),(1,6)],
[(5,5),(5,5),(3,3),(3,3),(4,4),(1,6)],
[(5,5),(5,5),(3,3),(4,4),(3,3),(1,6)],
[(5,5),(6,6),(2,2),(3,3),(4,4),(1,6)],
[(1,6),(3,3),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(3,3),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(6,6),(1,1)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(3,3)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(4,4)],
[(1,6),(3,3),(5,5),(4,4),(4,4),(3,3)],
[(2,2),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(3,3),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(3,3),(6,6),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(5,5),(5,5),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(5,5),(5,5),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(3,3),(1,6)],
[(2,2),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(6,6),(5,5),(4,4),(2,2),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(4,4),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(5,5),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(6,6),(2,2),(1,6)],
[(3,3),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(3,3),(5,5),(5,5),(4,4),(2,2),(1,6)],
[(3,3),(6,6),(4,4),(3,3),(3,3),(1,6)],
[(3,3),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(4,4),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(4,4),(3,3),(2,2),(6,6),(5,5),(1,6)],
[(4,4),(3,3),(3,3),(5,5),(5,5),(1,6)],
[(4,4),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(4,4),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(4,4),(3,3),(5,5),(6,6),(2,2),(1,6)],
[(4,4),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(4,4),(5,5),(2,2),(4,4),(4,4),(1,6)],
[(4,4),(5,5),(4,4),(3,3),(3,3),(1,6)],
[(4,4),(6,6),(2,2),(4,4),(2,2),(1,6)],
[(4,4),(6,6),(2,2),(4,4),(4,4),(1,6)],
[(4,4),(6,6),(2,2),(5,5),(2,2),(1,6)],
[(4,4),(6,6),(3,3),(4,4),(2,2),(1,6)],
[(4,4),(6,6),(3,3),(5,5),(2,2),(1,6)],
[(4,4),(6,6),(4,4),(2,2),(3,3),(1,6)],
[(4,4),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(5,5),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(5,5),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(5,5),(5,5),(2,2),(4,4),(4,4),(1,6)],
[(5,5),(5,5),(4,4),(3,3),(3,3),(1,6)],
[(5,5),(6,6),(2,2),(5,5),(2,2),(1,6)],
[(5,5),(6,6),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(2,2),(1,6)],
[(1,6),(2,2),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,1),(5,5),(6,6),(3,3),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(3,3),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(3,3)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(4,4)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(3,3)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(4,4)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(5,5)],
[(1,6),(2,2),(2,2),(6,6),(3,3),(1,6)],
[(1,6),(2,2),(2,2),(6,6),(4,4),(1,6)],
[(1,6),(2,2),(5,5),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(2,2),(6,6),(1,1),(1,6)],
[(1,6),(3,3),(3,3),(6,6),(1,1),(1,6)],
[(1,6),(4,4),(2,2),(6,6),(1,1),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)],
[(1,6),(5,5),(2,2),(6,6),(1,1),(1,6)],
[(4,4),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(4,4)],
[(1,6),(3,3),(3,3),(6,6),(5,5),(3,3)],
[(1,6),(4,4),(2,2),(6,6),(5,5),(2,2)],
[(1,6),(4,4),(3,3),(5,5),(4,4),(2,2)],
[(1,6),(4,4),(3,3),(5,5),(6,6),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(1,1),(6,6)],
[(1,6),(4,4),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(4,4),(4,4),(3,3),(5,5),(2,2)],
[(1,6),(4,4),(4,4),(3,3),(5,5),(3,3)],
[(1,6),(4,4),(4,4),(3,3),(6,6),(2,2)],
[(1,6),(4,4),(6,6),(2,2),(4,4),(2,2)],
[(1,6),(5,5),(2,2),(6,6),(4,4),(2,2)],
[(1,6),(5,5),(3,3),(4,4),(4,4),(2,2)],
[(1,6),(5,5),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(5,5),(4,4),(3,3),(4,4),(2,2)],
[(1,6),(5,5),(6,6),(2,2),(4,4),(2,2)],
[(1,6),(6,6),(2,2),(6,6),(1,1),(6,6)],
[(1,6),(6,6),(2,2),(6,6),(3,3),(2,2)],
[(1,6),(6,6),(3,3),(2,2),(4,4),(4,4)],
[(1,6),(6,6),(3,3),(2,2),(4,4),(5,5)],
[(1,6),(6,6),(3,3),(2,2),(4,4),(6,6)],
[(1,6),(6,6),(3,3),(4,4),(3,3),(2,2)],
[(1,6),(6,6),(3,3),(6,6),(2,2),(2,2)],
[(2,2),(2,2),(6,6),(5,5),(3,3),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(3,3),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(5,5),(1,6)],
[(3,3),(2,2),(6,6),(5,5),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(2,2),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(2,2),(1,6)],
[(4,4),(2,2),(4,4),(6,6),(3,3),(1,6)],
[(4,4),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(4,4),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(5,5),(2,2),(4,4),(6,6),(3,3),(1,6)],
[(6,6),(1,1),(6,6),(5,5),(3,3),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(2,2),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(2,2),(4,4),(2,2),(5,5)],
[(1,6),(1,6),(2,2),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(2,2)],
[(1,6),(3,3),(6,6),(2,2),(2,2),(1,6)],
[(1,6),(4,4),(2,2),(6,6),(3,3),(2,2)],
[(1,6),(4,4),(2,2),(6,6),(3,3),(3,3)],
[(1,6),(4,4),(2,2),(6,6),(4,4),(2,2)],
[(1,6),(4,4),(3,3),(4,4),(5,5),(3,3)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(5,5),(2,2),(6,6),(3,3),(2,2)],
[(1,6),(5,5),(3,3),(3,3),(5,5),(2,2)],
[(1,6),(5,5),(3,3),(3,3),(5,5),(3,3)],
[(1,6),(6,6),(2,2),(4,4),(3,3),(3,3)],
[(1,6),(6,6),(2,2),(6,6),(2,2),(2,2)],
[(1,6),(6,6),(2,2),(6,6),(2,2),(3,3)],
[(2,2),(6,6),(4,4),(3,3),(2,2),(1,6)],
[(3,3),(6,6),(4,4),(3,3),(2,2),(1,6)],
[(4,4),(2,2),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(6,6),(4,4),(3,3),(2,2),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(3,3),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(2,2),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(3,3)],
[(1,6),(2,2),(2,2),(6,6),(5,5),(4,4)],
[(1,6),(4,4),(2,2),(5,5),(4,4),(2,2)],
[(1,6),(4,4),(2,2),(5,5),(4,4),(3,3)],
[(1,6),(4,4),(3,3),(5,5),(3,3),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(5,5),(2,2),(4,4),(4,4),(4,4)],
[(1,6),(5,5),(2,2),(6,6),(2,2),(2,2)],
[(1,6),(5,5),(3,3),(4,4),(3,3),(2,2)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(2,2)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(3,3)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(4,4)],
[(2,2),(6,6),(4,4),(5,5),(1,1),(1,6)]
]

def root106 : Nat := 3862

def tree106_0 : CoverTree := CoverTree.reject 61
def tree106_1 : CoverTree := CoverTree.reject 41
def tree106_2 : CoverTree := CoverTree.reject 18
def tree106_3 : CoverTree := CoverTree.reject 11
def tree106_4 : CoverTree := CoverTree.reject 0
def tree106_5 : CoverTree := CoverTree.reject 3
def tree106_6 : CoverTree := CoverTree.reject 31
def tree106_7 : CoverTree := CoverTree.reject 73
def tree106_8 : CoverTree := CoverTree.reject 24
def tree106_9 : CoverTree := CoverTree.reject 25
def tree106_10 : CoverTree := CoverTree.reject 19
def tree106_11 : CoverTree := CoverTree.reject 20
def tree106_12 : CoverTree := CoverTree.accept
def tree106_13 : CoverTree := CoverTree.split [tree106_8,tree106_9,tree106_10,tree106_11,tree106_12,tree106_12]
def tree106_14 : CoverTree := CoverTree.reject 187
def tree106_15 : CoverTree := CoverTree.reject 16
def tree106_16 : CoverTree := CoverTree.split [tree106_15,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_17 : CoverTree := CoverTree.reject 14
def tree106_18 : CoverTree := CoverTree.split [tree106_17,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_19 : CoverTree := CoverTree.split [tree106_13,tree106_14,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_20 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_6,tree106_6,tree106_7,tree106_19]
def tree106_21 : CoverTree := CoverTree.reject 15
def tree106_22 : CoverTree := CoverTree.reject 42
def tree106_23 : CoverTree := CoverTree.split [tree106_21,tree106_22,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_24 : CoverTree := CoverTree.split [tree106_13,tree106_23,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_25 : CoverTree := CoverTree.split [tree106_21,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_26 : CoverTree := CoverTree.split [tree106_13,tree106_25,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_27 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_6,tree106_6,tree106_24,tree106_26]
def tree106_28 : CoverTree := CoverTree.reject 82
def tree106_29 : CoverTree := CoverTree.reject 13
def tree106_30 : CoverTree := CoverTree.reject 50
def tree106_31 : CoverTree := CoverTree.split [tree106_21,tree106_30,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_32 : CoverTree := CoverTree.split [tree106_29,tree106_31,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_33 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_28,tree106_32,tree106_24,tree106_26]
def tree106_34 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_20,tree106_27,tree106_33]
def tree106_35 : CoverTree := CoverTree.reject 83
def tree106_36 : CoverTree := CoverTree.reject 118
def tree106_37 : CoverTree := CoverTree.split [tree106_36,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_38 : CoverTree := CoverTree.split [tree106_29,tree106_31,tree106_16,tree106_18,tree106_37,tree106_12]
def tree106_39 : CoverTree := CoverTree.reject 145
def tree106_40 : CoverTree := CoverTree.split [tree106_8,tree106_9,tree106_10,tree106_11,tree106_39,tree106_12]
def tree106_41 : CoverTree := CoverTree.split [tree106_40,tree106_23,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_42 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_35,tree106_38,tree106_41,tree106_26]
def tree106_43 : CoverTree := CoverTree.reject 12
def tree106_44 : CoverTree := CoverTree.reject 56
def tree106_45 : CoverTree := CoverTree.reject 51
def tree106_46 : CoverTree := CoverTree.reject 148
def tree106_47 : CoverTree := CoverTree.split [tree106_21,tree106_44,tree106_45,tree106_12,tree106_46,tree106_12]
def tree106_48 : CoverTree := CoverTree.reject 119
def tree106_49 : CoverTree := CoverTree.split [tree106_15,tree106_48,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_50 : CoverTree := CoverTree.reject 58
def tree106_51 : CoverTree := CoverTree.split [tree106_50,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_52 : CoverTree := CoverTree.split [tree106_43,tree106_47,tree106_49,tree106_18,tree106_51,tree106_12]
def tree106_53 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_52,tree106_32,tree106_24,tree106_26]
def tree106_54 : CoverTree := CoverTree.split [tree106_21,tree106_44,tree106_45,tree106_12,tree106_12,tree106_12]
def tree106_55 : CoverTree := CoverTree.split [tree106_43,tree106_54,tree106_16,tree106_18,tree106_51,tree106_12]
def tree106_56 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_55,tree106_32,tree106_24,tree106_26]
def tree106_57 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_42,tree106_53,tree106_56]
def tree106_58 : CoverTree := CoverTree.split [tree106_0,tree106_1,tree106_2,tree106_3,tree106_34,tree106_57]
def tree106_59 : CoverTree := CoverTree.reject 62
def tree106_60 : CoverTree := CoverTree.reject 125
def tree106_61 : CoverTree := CoverTree.reject 126
def tree106_62 : CoverTree := CoverTree.reject 1
def tree106_63 : CoverTree := CoverTree.reject 162
def tree106_64 : CoverTree := CoverTree.reject 9
def tree106_65 : CoverTree := CoverTree.reject 351
def tree106_66 : CoverTree := CoverTree.reject 2
def tree106_67 : CoverTree := CoverTree.reject 7
def tree106_68 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_67,tree106_12,tree106_12,tree106_12]
def tree106_69 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_65,tree106_68,tree106_68,tree106_68]
def tree106_70 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_68,tree106_68,tree106_68,tree106_68]
def tree106_71 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_63,tree106_69,tree106_70]
def tree106_72 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_60,tree106_61,tree106_71]
def tree106_73 : CoverTree := CoverTree.reject 47
def tree106_74 : CoverTree := CoverTree.reject 66
def tree106_75 : CoverTree := CoverTree.reject 143
def tree106_76 : CoverTree := CoverTree.reject 149
def tree106_77 : CoverTree := CoverTree.reject 253
def tree106_78 : CoverTree := CoverTree.reject 254
def tree106_79 : CoverTree := CoverTree.reject 255
def tree106_80 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_81 : CoverTree := CoverTree.split [tree106_76,tree106_77,tree106_78,tree106_79,tree106_80,tree106_80]
def tree106_82 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_73,tree106_74,tree106_75,tree106_81]
def tree106_83 : CoverTree := CoverTree.reject 6
def tree106_84 : CoverTree := CoverTree.reject 97
def tree106_85 : CoverTree := CoverTree.split [tree106_83,tree106_84,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_86 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_10,tree106_11,tree106_12,tree106_12]
def tree106_87 : CoverTree := CoverTree.split [tree106_86,tree106_80,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_88 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_73,tree106_74,tree106_85,tree106_87]
def tree106_89 : CoverTree := CoverTree.reject 352
def tree106_90 : CoverTree := CoverTree.reject 256
def tree106_91 : CoverTree := CoverTree.reject 257
def tree106_92 : CoverTree := CoverTree.split [tree106_43,tree106_89,tree106_90,tree106_91,tree106_80,tree106_80]
def tree106_93 : CoverTree := CoverTree.reject 258
def tree106_94 : CoverTree := CoverTree.reject 188
def tree106_95 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_94,tree106_12,tree106_12,tree106_12]
def tree106_96 : CoverTree := CoverTree.split [tree106_29,tree106_93,tree106_95,tree106_80,tree106_80,tree106_80]
def tree106_97 : CoverTree := CoverTree.reject 150
def tree106_98 : CoverTree := CoverTree.split [tree106_97,tree106_80,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_99 : CoverTree := CoverTree.reject 259
def tree106_100 : CoverTree := CoverTree.split [tree106_86,tree106_99,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_101 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_92,tree106_96,tree106_98,tree106_100]
def tree106_102 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_82,tree106_88,tree106_101]
def tree106_103 : CoverTree := CoverTree.reject 146
def tree106_104 : CoverTree := CoverTree.reject 74
def tree106_105 : CoverTree := CoverTree.reject 353
def tree106_106 : CoverTree := CoverTree.reject 192
def tree106_107 : CoverTree := CoverTree.split [tree106_83,tree106_105,tree106_106,tree106_18,tree106_12,tree106_12]
def tree106_108 : CoverTree := CoverTree.reject 193
def tree106_109 : CoverTree := CoverTree.reject 194
def tree106_110 : CoverTree := CoverTree.reject 195
def tree106_111 : CoverTree := CoverTree.split [tree106_13,tree106_108,tree106_109,tree106_110,tree106_12,tree106_12]
def tree106_112 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_103,tree106_104,tree106_107,tree106_111]
def tree106_113 : CoverTree := CoverTree.reject 92
def tree106_114 : CoverTree := CoverTree.reject 75
def tree106_115 : CoverTree := CoverTree.reject 260
def tree106_116 : CoverTree := CoverTree.reject 196
def tree106_117 : CoverTree := CoverTree.split [tree106_83,tree106_115,tree106_116,tree106_18,tree106_12,tree106_12]
def tree106_118 : CoverTree := CoverTree.reject 197
def tree106_119 : CoverTree := CoverTree.split [tree106_13,tree106_118,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_120 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_113,tree106_114,tree106_117,tree106_119]
def tree106_121 : CoverTree := CoverTree.reject 354
def tree106_122 : CoverTree := CoverTree.reject 261
def tree106_123 : CoverTree := CoverTree.reject 198
def tree106_124 : CoverTree := CoverTree.split [tree106_43,tree106_121,tree106_122,tree106_123,tree106_51,tree106_12]
def tree106_125 : CoverTree := CoverTree.reject 262
def tree106_126 : CoverTree := CoverTree.split [tree106_29,tree106_125,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_127 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_124,tree106_126,tree106_24,tree106_26]
def tree106_128 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_112,tree106_120,tree106_127]
def tree106_129 : CoverTree := CoverTree.reject 84
def tree106_130 : CoverTree := CoverTree.reject 355
def tree106_131 : CoverTree := CoverTree.reject 199
def tree106_132 : CoverTree := CoverTree.split [tree106_29,tree106_130,tree106_131,tree106_18,tree106_37,tree106_12]
def tree106_133 : CoverTree := CoverTree.reject 186
def tree106_134 : CoverTree := CoverTree.reject 263
def tree106_135 : CoverTree := CoverTree.reject 200
def tree106_136 : CoverTree := CoverTree.split [tree106_133,tree106_134,tree106_135,tree106_18,tree106_12,tree106_12]
def tree106_137 : CoverTree := CoverTree.reject 201
def tree106_138 : CoverTree := CoverTree.split [tree106_13,tree106_137,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_139 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_129,tree106_132,tree106_136,tree106_138]
def tree106_140 : CoverTree := CoverTree.reject 85
def tree106_141 : CoverTree := CoverTree.reject 264
def tree106_142 : CoverTree := CoverTree.split [tree106_29,tree106_141,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_143 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_140,tree106_142,tree106_24,tree106_26]
def tree106_144 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_139,tree106_143,tree106_56]
def tree106_145 : CoverTree := CoverTree.reject 392
def tree106_146 : CoverTree := CoverTree.reject 265
def tree106_147 : CoverTree := CoverTree.reject 202
def tree106_148 : CoverTree := CoverTree.split [tree106_43,tree106_145,tree106_146,tree106_147,tree106_51,tree106_12]
def tree106_149 : CoverTree := CoverTree.reject 266
def tree106_150 : CoverTree := CoverTree.reject 203
def tree106_151 : CoverTree := CoverTree.split [tree106_29,tree106_149,tree106_150,tree106_18,tree106_37,tree106_12]
def tree106_152 : CoverTree := CoverTree.reject 411
def tree106_153 : CoverTree := CoverTree.reject 267
def tree106_154 : CoverTree := CoverTree.split [tree106_152,tree106_153,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_155 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_148,tree106_151,tree106_154,tree106_26]
def tree106_156 : CoverTree := CoverTree.reject 204
def tree106_157 : CoverTree := CoverTree.split [tree106_43,tree106_47,tree106_49,tree106_156,tree106_51,tree106_12]
def tree106_158 : CoverTree := CoverTree.reject 268
def tree106_159 : CoverTree := CoverTree.split [tree106_29,tree106_158,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_160 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_157,tree106_159,tree106_24,tree106_26]
def tree106_161 : CoverTree := CoverTree.reject 356
def tree106_162 : CoverTree := CoverTree.reject 205
def tree106_163 : CoverTree := CoverTree.split [tree106_43,tree106_161,tree106_162,tree106_18,tree106_51,tree106_12]
def tree106_164 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_163,tree106_32,tree106_24,tree106_26]
def tree106_165 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_155,tree106_160,tree106_164]
def tree106_166 : CoverTree := CoverTree.split [tree106_59,tree106_72,tree106_102,tree106_128,tree106_144,tree106_165]
def tree106_167 : CoverTree := CoverTree.reject 63
def tree106_168 : CoverTree := CoverTree.reject 23
def tree106_169 : CoverTree := CoverTree.reject 100
def tree106_170 : CoverTree := CoverTree.reject 357
def tree106_171 : CoverTree := CoverTree.reject 358
def tree106_172 : CoverTree := CoverTree.reject 359
def tree106_173 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_170,tree106_171,tree106_172,tree106_68]
def tree106_174 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_168,tree106_169,tree106_173]
def tree106_175 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_168,tree106_169,tree106_70]
def tree106_176 : CoverTree := CoverTree.reject 163
def tree106_177 : CoverTree := CoverTree.reject 360
def tree106_178 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_177,tree106_68,tree106_68,tree106_68]
def tree106_179 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_176,tree106_178,tree106_70]
def tree106_180 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_174,tree106_175,tree106_179]
def tree106_181 : CoverTree := CoverTree.reject 98
def tree106_182 : CoverTree := CoverTree.reject 95
def tree106_183 : CoverTree := CoverTree.reject 96
def tree106_184 : CoverTree := CoverTree.reject 269
def tree106_185 : CoverTree := CoverTree.reject 270
def tree106_186 : CoverTree := CoverTree.split [tree106_83,tree106_182,tree106_183,tree106_184,tree106_185,tree106_80]
def tree106_187 : CoverTree := CoverTree.reject 271
def tree106_188 : CoverTree := CoverTree.reject 272
def tree106_189 : CoverTree := CoverTree.split [tree106_76,tree106_187,tree106_188,tree106_80,tree106_80,tree106_80]
def tree106_190 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_73,tree106_181,tree106_186,tree106_189]
def tree106_191 : CoverTree := CoverTree.reject 105
def tree106_192 : CoverTree := CoverTree.reject 250
def tree106_193 : CoverTree := CoverTree.reject 251
def tree106_194 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_192,tree106_193,tree106_12,tree106_12]
def tree106_195 : CoverTree := CoverTree.reject 252
def tree106_196 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_195,tree106_12,tree106_12,tree106_12]
def tree106_197 : CoverTree := CoverTree.split [tree106_83,tree106_191,tree106_194,tree106_196,tree106_80,tree106_80]
def tree106_198 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_73,tree106_197,tree106_85,tree106_87]
def tree106_199 : CoverTree := CoverTree.reject 361
def tree106_200 : CoverTree := CoverTree.reject 273
def tree106_201 : CoverTree := CoverTree.split [tree106_43,tree106_199,tree106_200,tree106_80,tree106_80,tree106_80]
def tree106_202 : CoverTree := CoverTree.reject 274
def tree106_203 : CoverTree := CoverTree.split [tree106_29,tree106_202,tree106_95,tree106_80,tree106_80,tree106_80]
def tree106_204 : CoverTree := CoverTree.reject 275
def tree106_205 : CoverTree := CoverTree.split [tree106_86,tree106_204,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_206 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_201,tree106_203,tree106_98,tree106_205]
def tree106_207 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_190,tree106_198,tree106_206]
def tree106_208 : CoverTree := CoverTree.reject 147
def tree106_209 : CoverTree := CoverTree.reject 76
def tree106_210 : CoverTree := CoverTree.reject 362
def tree106_211 : CoverTree := CoverTree.reject 206
def tree106_212 : CoverTree := CoverTree.split [tree106_83,tree106_210,tree106_211,tree106_18,tree106_12,tree106_12]
def tree106_213 : CoverTree := CoverTree.reject 207
def tree106_214 : CoverTree := CoverTree.split [tree106_13,tree106_213,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_215 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_208,tree106_209,tree106_212,tree106_214]
def tree106_216 : CoverTree := CoverTree.reject 70
def tree106_217 : CoverTree := CoverTree.split [tree106_83,tree106_216,tree106_49,tree106_18,tree106_51,tree106_12]
def tree106_218 : CoverTree := CoverTree.reject 106
def tree106_219 : CoverTree := CoverTree.split [tree106_83,tree106_218,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_220 : CoverTree := CoverTree.split [tree106_83,tree106_23,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_221 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_217,tree106_219,tree106_220,tree106_26]
def tree106_222 : CoverTree := CoverTree.reject 190
def tree106_223 : CoverTree := CoverTree.split [tree106_15,tree106_222,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_224 : CoverTree := CoverTree.split [tree106_43,tree106_54,tree106_223,tree106_18,tree106_51,tree106_12]
def tree106_225 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_224,tree106_32,tree106_24,tree106_26]
def tree106_226 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_215,tree106_221,tree106_225]
def tree106_227 : CoverTree := CoverTree.reject 86
def tree106_228 : CoverTree := CoverTree.reject 363
def tree106_229 : CoverTree := CoverTree.reject 208
def tree106_230 : CoverTree := CoverTree.split [tree106_29,tree106_228,tree106_229,tree106_18,tree106_37,tree106_12]
def tree106_231 : CoverTree := CoverTree.reject 276
def tree106_232 : CoverTree := CoverTree.split [tree106_133,tree106_231,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_233 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_227,tree106_230,tree106_232,tree106_26]
def tree106_234 : CoverTree := CoverTree.reject 277
def tree106_235 : CoverTree := CoverTree.split [tree106_29,tree106_234,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_236 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_52,tree106_235,tree106_24,tree106_26]
def tree106_237 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_233,tree106_236,tree106_56]
def tree106_238 : CoverTree := CoverTree.reject 393
def tree106_239 : CoverTree := CoverTree.reject 278
def tree106_240 : CoverTree := CoverTree.reject 209
def tree106_241 : CoverTree := CoverTree.split [tree106_43,tree106_238,tree106_239,tree106_240,tree106_51,tree106_12]
def tree106_242 : CoverTree := CoverTree.reject 279
def tree106_243 : CoverTree := CoverTree.split [tree106_29,tree106_242,tree106_16,tree106_18,tree106_37,tree106_12]
def tree106_244 : CoverTree := CoverTree.split [tree106_5,tree106_5,tree106_241,tree106_243,tree106_41,tree106_26]
def tree106_245 : CoverTree := CoverTree.split [tree106_4,tree106_4,tree106_4,tree106_244,tree106_53,tree106_56]
def tree106_246 : CoverTree := CoverTree.split [tree106_167,tree106_180,tree106_207,tree106_226,tree106_237,tree106_245]
def tree106_247 : CoverTree := CoverTree.reject 29
def tree106_248 : CoverTree := CoverTree.reject 60
def tree106_249 : CoverTree := CoverTree.reject 109
def tree106_250 : CoverTree := CoverTree.reject 158
def tree106_251 : CoverTree := CoverTree.reject 394
def tree106_252 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_251,tree106_68,tree106_68,tree106_68]
def tree106_253 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_168,tree106_250,tree106_252]
def tree106_254 : CoverTree := CoverTree.reject 327
def tree106_255 : CoverTree := CoverTree.reject 364
def tree106_256 : CoverTree := CoverTree.reject 365
def tree106_257 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_255,tree106_256,tree106_68,tree106_68]
def tree106_258 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_168,tree106_254,tree106_257]
def tree106_259 : CoverTree := CoverTree.reject 5
def tree106_260 : CoverTree := CoverTree.split [tree106_259,tree106_259,tree106_259,tree106_259,tree106_68,tree106_68]
def tree106_261 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_168,tree106_260,tree106_70]
def tree106_262 : CoverTree := CoverTree.reject 111
def tree106_263 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_262,tree106_68,tree106_68,tree106_68]
def tree106_264 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_263,tree106_70,tree106_70]
def tree106_265 : CoverTree := CoverTree.split [tree106_248,tree106_249,tree106_253,tree106_258,tree106_261,tree106_264]
def tree106_266 : CoverTree := CoverTree.reject 26
def tree106_267 : CoverTree := CoverTree.reject 4
def tree106_268 : CoverTree := CoverTree.reject 53
def tree106_269 : CoverTree := CoverTree.reject 54
def tree106_270 : CoverTree := CoverTree.reject 322
def tree106_271 : CoverTree := CoverTree.reject 129
def tree106_272 : CoverTree := CoverTree.reject 130
def tree106_273 : CoverTree := CoverTree.reject 280
def tree106_274 : CoverTree := CoverTree.reject 281
def tree106_275 : CoverTree := CoverTree.split [tree106_270,tree106_271,tree106_272,tree106_273,tree106_274,tree106_80]
def tree106_276 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_73,tree106_268,tree106_269,tree106_275]
def tree106_277 : CoverTree := CoverTree.reject 55
def tree106_278 : CoverTree := CoverTree.reject 131
def tree106_279 : CoverTree := CoverTree.reject 132
def tree106_280 : CoverTree := CoverTree.reject 133
def tree106_281 : CoverTree := CoverTree.reject 282
def tree106_282 : CoverTree := CoverTree.split [tree106_83,tree106_278,tree106_279,tree106_280,tree106_281,tree106_80]
def tree106_283 : CoverTree := CoverTree.reject 323
def tree106_284 : CoverTree := CoverTree.reject 134
def tree106_285 : CoverTree := CoverTree.reject 283
def tree106_286 : CoverTree := CoverTree.reject 329
def tree106_287 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_286,tree106_12,tree106_12,tree106_12]
def tree106_288 : CoverTree := CoverTree.split [tree106_283,tree106_284,tree106_285,tree106_80,tree106_287,tree106_80]
def tree106_289 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_73,tree106_277,tree106_282,tree106_288]
def tree106_290 : CoverTree := CoverTree.reject 99
def tree106_291 : CoverTree := CoverTree.split [tree106_83,tree106_182,tree106_183,tree106_80,tree106_80,tree106_80]
def tree106_292 : CoverTree := CoverTree.reject 284
def tree106_293 : CoverTree := CoverTree.reject 285
def tree106_294 : CoverTree := CoverTree.split [tree106_76,tree106_292,tree106_293,tree106_80,tree106_80,tree106_80]
def tree106_295 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_73,tree106_290,tree106_291,tree106_294]
def tree106_296 : CoverTree := CoverTree.reject 286
def tree106_297 : CoverTree := CoverTree.split [tree106_86,tree106_296,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_298 : CoverTree := CoverTree.split [tree106_73,tree106_73,tree106_73,tree106_197,tree106_85,tree106_297]
def tree106_299 : CoverTree := CoverTree.reject 72
def tree106_300 : CoverTree := CoverTree.reject 103
def tree106_301 : CoverTree := CoverTree.reject 366
def tree106_302 : CoverTree := CoverTree.split [tree106_43,tree106_301,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_303 : CoverTree := CoverTree.reject 287
def tree106_304 : CoverTree := CoverTree.split [tree106_29,tree106_303,tree106_95,tree106_80,tree106_80,tree106_80]
def tree106_305 : CoverTree := CoverTree.split [tree106_299,tree106_300,tree106_302,tree106_304,tree106_98,tree106_87]
def tree106_306 : CoverTree := CoverTree.split [tree106_266,tree106_276,tree106_289,tree106_295,tree106_298,tree106_305]
def tree106_307 : CoverTree := CoverTree.reject 21
def tree106_308 : CoverTree := CoverTree.reject 38
def tree106_309 : CoverTree := CoverTree.reject 39
def tree106_310 : CoverTree := CoverTree.reject 135
def tree106_311 : CoverTree := CoverTree.reject 112
def tree106_312 : CoverTree := CoverTree.reject 210
def tree106_313 : CoverTree := CoverTree.reject 211
def tree106_314 : CoverTree := CoverTree.reject 34
def tree106_315 : CoverTree := CoverTree.split [tree106_314,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_316 : CoverTree := CoverTree.split [tree106_83,tree106_310,tree106_311,tree106_312,tree106_313,tree106_315]
def tree106_317 : CoverTree := CoverTree.reject 324
def tree106_318 : CoverTree := CoverTree.reject 113
def tree106_319 : CoverTree := CoverTree.reject 212
def tree106_320 : CoverTree := CoverTree.reject 213
def tree106_321 : CoverTree := CoverTree.reject 330
def tree106_322 : CoverTree := CoverTree.split [tree106_314,tree106_321,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_323 : CoverTree := CoverTree.split [tree106_317,tree106_318,tree106_319,tree106_320,tree106_322,tree106_315]
def tree106_324 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_308,tree106_309,tree106_316,tree106_323]
def tree106_325 : CoverTree := CoverTree.reject 35
def tree106_326 : CoverTree := CoverTree.reject 77
def tree106_327 : CoverTree := CoverTree.reject 136
def tree106_328 : CoverTree := CoverTree.reject 214
def tree106_329 : CoverTree := CoverTree.reject 331
def tree106_330 : CoverTree := CoverTree.split [tree106_17,tree106_329,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_331 : CoverTree := CoverTree.reject 159
def tree106_332 : CoverTree := CoverTree.split [tree106_331,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_333 : CoverTree := CoverTree.reject 332
def tree106_334 : CoverTree := CoverTree.split [tree106_12,tree106_333,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_335 : CoverTree := CoverTree.split [tree106_83,tree106_327,tree106_328,tree106_330,tree106_332,tree106_334]
def tree106_336 : CoverTree := CoverTree.reject 128
def tree106_337 : CoverTree := CoverTree.reject 333
def tree106_338 : CoverTree := CoverTree.split [tree106_8,tree106_9,tree106_10,tree106_11,tree106_336,tree106_337]
def tree106_339 : CoverTree := CoverTree.reject 215
def tree106_340 : CoverTree := CoverTree.reject 216
def tree106_341 : CoverTree := CoverTree.reject 334
def tree106_342 : CoverTree := CoverTree.split [tree106_17,tree106_341,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_343 : CoverTree := CoverTree.split [tree106_338,tree106_339,tree106_340,tree106_342,tree106_12,tree106_12]
def tree106_344 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_325,tree106_326,tree106_335,tree106_343]
def tree106_345 : CoverTree := CoverTree.reject 78
def tree106_346 : CoverTree := CoverTree.reject 79
def tree106_347 : CoverTree := CoverTree.reject 335
def tree106_348 : CoverTree := CoverTree.reject 336
def tree106_349 : CoverTree := CoverTree.split [tree106_50,tree106_347,tree106_348,tree106_12,tree106_12,tree106_12]
def tree106_350 : CoverTree := CoverTree.reject 337
def tree106_351 : CoverTree := CoverTree.split [tree106_12,tree106_350,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_352 : CoverTree := CoverTree.split [tree106_83,tree106_216,tree106_345,tree106_346,tree106_349,tree106_351]
def tree106_353 : CoverTree := CoverTree.reject 137
def tree106_354 : CoverTree := CoverTree.reject 114
def tree106_355 : CoverTree := CoverTree.split [tree106_83,tree106_353,tree106_354,tree106_18,tree106_37,tree106_12]
def tree106_356 : CoverTree := CoverTree.reject 189
def tree106_357 : CoverTree := CoverTree.split [tree106_21,tree106_22,tree106_356,tree106_12,tree106_12,tree106_12]
def tree106_358 : CoverTree := CoverTree.split [tree106_83,tree106_357,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_359 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_352,tree106_355,tree106_358,tree106_26]
def tree106_360 : CoverTree := CoverTree.reject 65
def tree106_361 : CoverTree := CoverTree.split [tree106_360,tree106_360,tree106_217,tree106_219,tree106_220,tree106_26]
def tree106_362 : CoverTree := CoverTree.reject 64
def tree106_363 : CoverTree := CoverTree.reject 59
def tree106_364 : CoverTree := CoverTree.reject 325
def tree106_365 : CoverTree := CoverTree.reject 138
def tree106_366 : CoverTree := CoverTree.reject 338
def tree106_367 : CoverTree := CoverTree.split [tree106_17,tree106_366,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_368 : CoverTree := CoverTree.reject 91
def tree106_369 : CoverTree := CoverTree.split [tree106_368,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_370 : CoverTree := CoverTree.split [tree106_363,tree106_364,tree106_365,tree106_367,tree106_369,tree106_12]
def tree106_371 : CoverTree := CoverTree.split [tree106_362,tree106_370,tree106_224,tree106_32,tree106_24,tree106_26]
def tree106_372 : CoverTree := CoverTree.split [tree106_307,tree106_324,tree106_344,tree106_359,tree106_361,tree106_371]
def tree106_373 : CoverTree := CoverTree.reject 30
def tree106_374 : CoverTree := CoverTree.reject 17
def tree106_375 : CoverTree := CoverTree.reject 43
def tree106_376 : CoverTree := CoverTree.reject 44
def tree106_377 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_373,tree106_374,tree106_375,tree106_376]
def tree106_378 : CoverTree := CoverTree.reject 40
def tree106_379 : CoverTree := CoverTree.reject 139
def tree106_380 : CoverTree := CoverTree.reject 115
def tree106_381 : CoverTree := CoverTree.reject 288
def tree106_382 : CoverTree := CoverTree.reject 217
def tree106_383 : CoverTree := CoverTree.split [tree106_29,tree106_379,tree106_380,tree106_381,tree106_382,tree106_315]
def tree106_384 : CoverTree := CoverTree.reject 121
def tree106_385 : CoverTree := CoverTree.reject 140
def tree106_386 : CoverTree := CoverTree.reject 116
def tree106_387 : CoverTree := CoverTree.reject 218
def tree106_388 : CoverTree := CoverTree.reject 219
def tree106_389 : CoverTree := CoverTree.split [tree106_384,tree106_385,tree106_386,tree106_387,tree106_388,tree106_315]
def tree106_390 : CoverTree := CoverTree.reject 326
def tree106_391 : CoverTree := CoverTree.reject 220
def tree106_392 : CoverTree := CoverTree.reject 221
def tree106_393 : CoverTree := CoverTree.reject 339
def tree106_394 : CoverTree := CoverTree.split [tree106_17,tree106_393,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_395 : CoverTree := CoverTree.split [tree106_390,tree106_391,tree106_392,tree106_394,tree106_315,tree106_315]
def tree106_396 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_378,tree106_383,tree106_389,tree106_395]
def tree106_397 : CoverTree := CoverTree.reject 87
def tree106_398 : CoverTree := CoverTree.reject 141
def tree106_399 : CoverTree := CoverTree.reject 222
def tree106_400 : CoverTree := CoverTree.reject 340
def tree106_401 : CoverTree := CoverTree.split [tree106_17,tree106_400,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_402 : CoverTree := CoverTree.reject 165
def tree106_403 : CoverTree := CoverTree.split [tree106_402,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_404 : CoverTree := CoverTree.split [tree106_29,tree106_398,tree106_399,tree106_401,tree106_403,tree106_12]
def tree106_405 : CoverTree := CoverTree.reject 123
def tree106_406 : CoverTree := CoverTree.reject 142
def tree106_407 : CoverTree := CoverTree.reject 223
def tree106_408 : CoverTree := CoverTree.split [tree106_405,tree106_406,tree106_407,tree106_18,tree106_332,tree106_12]
def tree106_409 : CoverTree := CoverTree.split [tree106_8,tree106_9,tree106_10,tree106_11,tree106_336,tree106_12]
def tree106_410 : CoverTree := CoverTree.reject 341
def tree106_411 : CoverTree := CoverTree.split [tree106_21,tree106_410,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_412 : CoverTree := CoverTree.split [tree106_409,tree106_411,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_413 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_397,tree106_404,tree106_408,tree106_412]
def tree106_414 : CoverTree := CoverTree.reject 160
def tree106_415 : CoverTree := CoverTree.reject 289
def tree106_416 : CoverTree := CoverTree.reject 342
def tree106_417 : CoverTree := CoverTree.split [tree106_17,tree106_416,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_418 : CoverTree := CoverTree.split [tree106_43,tree106_414,tree106_415,tree106_417,tree106_51,tree106_12]
def tree106_419 : CoverTree := CoverTree.reject 191
def tree106_420 : CoverTree := CoverTree.split [tree106_21,tree106_30,tree106_419,tree106_12,tree106_12,tree106_12]
def tree106_421 : CoverTree := CoverTree.split [tree106_29,tree106_420,tree106_16,tree106_18,tree106_37,tree106_12]
def tree106_422 : CoverTree := CoverTree.split [tree106_133,tree106_23,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_423 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_418,tree106_421,tree106_422,tree106_26]
def tree106_424 : CoverTree := CoverTree.split [tree106_360,tree106_360,tree106_52,tree106_32,tree106_24,tree106_26]
def tree106_425 : CoverTree := CoverTree.reject 101
def tree106_426 : CoverTree := CoverTree.reject 27
def tree106_427 : CoverTree := CoverTree.reject 28
def tree106_428 : CoverTree := CoverTree.reject 22
def tree106_429 : CoverTree := CoverTree.reject 154
def tree106_430 : CoverTree := CoverTree.reject 155
def tree106_431 : CoverTree := CoverTree.reject 156
def tree106_432 : CoverTree := CoverTree.split [tree106_429,tree106_430,tree106_431,tree106_12,tree106_12,tree106_12]
def tree106_433 : CoverTree := CoverTree.reject 173
def tree106_434 : CoverTree := CoverTree.split [tree106_433,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_435 : CoverTree := CoverTree.split [tree106_425,tree106_426,tree106_427,tree106_428,tree106_432,tree106_434]
def tree106_436 : CoverTree := CoverTree.reject 93
def tree106_437 : CoverTree := CoverTree.reject 88
def tree106_438 : CoverTree := CoverTree.reject 89
def tree106_439 : CoverTree := CoverTree.reject 90
def tree106_440 : CoverTree := CoverTree.split [tree106_21,tree106_436,tree106_437,tree106_438,tree106_439,tree106_12]
def tree106_441 : CoverTree := CoverTree.reject 94
def tree106_442 : CoverTree := CoverTree.reject 167
def tree106_443 : CoverTree := CoverTree.split [tree106_15,tree106_441,tree106_442,tree106_12,tree106_12,tree106_12]
def tree106_444 : CoverTree := CoverTree.reject 343
def tree106_445 : CoverTree := CoverTree.split [tree106_17,tree106_444,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_446 : CoverTree := CoverTree.split [tree106_363,tree106_440,tree106_443,tree106_445,tree106_369,tree106_12]
def tree106_447 : CoverTree := CoverTree.split [tree106_435,tree106_446,tree106_55,tree106_32,tree106_24,tree106_26]
def tree106_448 : CoverTree := CoverTree.split [tree106_377,tree106_396,tree106_413,tree106_423,tree106_424,tree106_447]
def tree106_449 : CoverTree := CoverTree.reject 67
def tree106_450 : CoverTree := CoverTree.reject 37
def tree106_451 : CoverTree := CoverTree.reject 45
def tree106_452 : CoverTree := CoverTree.reject 46
def tree106_453 : CoverTree := CoverTree.split [tree106_449,tree106_450,tree106_373,tree106_374,tree106_451,tree106_452]
def tree106_454 : CoverTree := CoverTree.reject 57
def tree106_455 : CoverTree := CoverTree.reject 80
def tree106_456 : CoverTree := CoverTree.reject 157
def tree106_457 : CoverTree := CoverTree.reject 117
def tree106_458 : CoverTree := CoverTree.reject 224
def tree106_459 : CoverTree := CoverTree.reject 225
def tree106_460 : CoverTree := CoverTree.split [tree106_43,tree106_456,tree106_457,tree106_458,tree106_459,tree106_315]
def tree106_461 : CoverTree := CoverTree.reject 290
def tree106_462 : CoverTree := CoverTree.reject 226
def tree106_463 : CoverTree := CoverTree.reject 291
def tree106_464 : CoverTree := CoverTree.split [tree106_29,tree106_461,tree106_462,tree106_463,tree106_315,tree106_315]
def tree106_465 : CoverTree := CoverTree.reject 292
def tree106_466 : CoverTree := CoverTree.reject 311
def tree106_467 : CoverTree := CoverTree.split [tree106_15,tree106_466,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_468 : CoverTree := CoverTree.split [tree106_384,tree106_465,tree106_467,tree106_18,tree106_315,tree106_315]
def tree106_469 : CoverTree := CoverTree.reject 127
def tree106_470 : CoverTree := CoverTree.reject 344
def tree106_471 : CoverTree := CoverTree.split [tree106_8,tree106_9,tree106_10,tree106_11,tree106_469,tree106_470]
def tree106_472 : CoverTree := CoverTree.reject 227
def tree106_473 : CoverTree := CoverTree.reject 345
def tree106_474 : CoverTree := CoverTree.split [tree106_15,tree106_473,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_475 : CoverTree := CoverTree.split [tree106_471,tree106_472,tree106_474,tree106_18,tree106_315,tree106_315]
def tree106_476 : CoverTree := CoverTree.split [tree106_454,tree106_455,tree106_460,tree106_464,tree106_468,tree106_475]
def tree106_477 : CoverTree := CoverTree.reject 48
def tree106_478 : CoverTree := CoverTree.reject 303
def tree106_479 : CoverTree := CoverTree.reject 122
def tree106_480 : CoverTree := CoverTree.reject 312
def tree106_481 : CoverTree := CoverTree.reject 313
def tree106_482 : CoverTree := CoverTree.reject 346
def tree106_483 : CoverTree := CoverTree.reject 347
def tree106_484 : CoverTree := CoverTree.reject 348
def tree106_485 : CoverTree := CoverTree.split [tree106_17,tree106_480,tree106_481,tree106_482,tree106_483,tree106_484]
def tree106_486 : CoverTree := CoverTree.reject 228
def tree106_487 : CoverTree := CoverTree.reject 314
def tree106_488 : CoverTree := CoverTree.split [tree106_487,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_489 : CoverTree := CoverTree.split [tree106_363,tree106_478,tree106_479,tree106_485,tree106_486,tree106_488]
def tree106_490 : CoverTree := CoverTree.reject 161
def tree106_491 : CoverTree := CoverTree.reject 229
def tree106_492 : CoverTree := CoverTree.reject 182
def tree106_493 : CoverTree := CoverTree.split [tree106_492,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_494 : CoverTree := CoverTree.split [tree106_43,tree106_490,tree106_491,tree106_18,tree106_51,tree106_493]
def tree106_495 : CoverTree := CoverTree.reject 293
def tree106_496 : CoverTree := CoverTree.reject 349
def tree106_497 : CoverTree := CoverTree.split [tree106_15,tree106_496,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_498 : CoverTree := CoverTree.split [tree106_29,tree106_495,tree106_497,tree106_18,tree106_403,tree106_12]
def tree106_499 : CoverTree := CoverTree.reject 294
def tree106_500 : CoverTree := CoverTree.split [tree106_405,tree106_499,tree106_16,tree106_18,tree106_332,tree106_12]
def tree106_501 : CoverTree := CoverTree.reject 350
def tree106_502 : CoverTree := CoverTree.split [tree106_21,tree106_501,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_503 : CoverTree := CoverTree.split [tree106_409,tree106_502,tree106_16,tree106_18,tree106_12,tree106_12]
def tree106_504 : CoverTree := CoverTree.split [tree106_477,tree106_489,tree106_494,tree106_498,tree106_500,tree106_503]
def tree106_505 : CoverTree := CoverTree.reject 49
def tree106_506 : CoverTree := CoverTree.reject 304
def tree106_507 : CoverTree := CoverTree.reject 295
def tree106_508 : CoverTree := CoverTree.reject 230
def tree106_509 : CoverTree := CoverTree.reject 249
def tree106_510 : CoverTree := CoverTree.split [tree106_509,tree106_12,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_511 : CoverTree := CoverTree.split [tree106_363,tree106_506,tree106_507,tree106_508,tree106_369,tree106_510]
def tree106_512 : CoverTree := CoverTree.reject 395
def tree106_513 : CoverTree := CoverTree.reject 166
def tree106_514 : CoverTree := CoverTree.split [tree106_15,tree106_513,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_515 : CoverTree := CoverTree.split [tree106_43,tree106_512,tree106_514,tree106_18,tree106_51,tree106_12]
def tree106_516 : CoverTree := CoverTree.reject 296
def tree106_517 : CoverTree := CoverTree.split [tree106_29,tree106_516,tree106_16,tree106_18,tree106_37,tree106_12]
def tree106_518 : CoverTree := CoverTree.split [tree106_505,tree106_511,tree106_515,tree106_517,tree106_41,tree106_26]
def tree106_519 : CoverTree := CoverTree.reject 315
def tree106_520 : CoverTree := CoverTree.split [tree106_429,tree106_430,tree106_431,tree106_519,tree106_12,tree106_12]
def tree106_521 : CoverTree := CoverTree.reject 102
def tree106_522 : CoverTree := CoverTree.split [tree106_425,tree106_426,tree106_427,tree106_428,tree106_520,tree106_521]
def tree106_523 : CoverTree := CoverTree.reject 305
def tree106_524 : CoverTree := CoverTree.reject 316
def tree106_525 : CoverTree := CoverTree.reject 317
def tree106_526 : CoverTree := CoverTree.reject 318
def tree106_527 : CoverTree := CoverTree.split [tree106_15,tree106_441,tree106_524,tree106_525,tree106_526,tree106_12]
def tree106_528 : CoverTree := CoverTree.reject 184
def tree106_529 : CoverTree := CoverTree.split [tree106_17,tree106_528,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_530 : CoverTree := CoverTree.split [tree106_363,tree106_523,tree106_527,tree106_529,tree106_369,tree106_12]
def tree106_531 : CoverTree := CoverTree.split [tree106_522,tree106_530,tree106_52,tree106_32,tree106_24,tree106_26]
def tree106_532 : CoverTree := CoverTree.split [tree106_363,tree106_440,tree106_443,tree106_18,tree106_369,tree106_12]
def tree106_533 : CoverTree := CoverTree.split [tree106_435,tree106_532,tree106_55,tree106_32,tree106_24,tree106_26]
def tree106_534 : CoverTree := CoverTree.split [tree106_453,tree106_476,tree106_504,tree106_518,tree106_531,tree106_533]
def tree106_535 : CoverTree := CoverTree.split [tree106_247,tree106_265,tree106_306,tree106_372,tree106_448,tree106_534]
def tree106_536 : CoverTree := CoverTree.reject 71
def tree106_537 : CoverTree := CoverTree.reject 68
def tree106_538 : CoverTree := CoverTree.reject 69
def tree106_539 : CoverTree := CoverTree.reject 36
def tree106_540 : CoverTree := CoverTree.reject 120
def tree106_541 : CoverTree := CoverTree.reject 310
def tree106_542 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_541,tree106_68,tree106_68,tree106_68]
def tree106_543 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_168,tree106_540,tree106_542]
def tree106_544 : CoverTree := CoverTree.reject 52
def tree106_545 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_544,tree106_70,tree106_70]
def tree106_546 : CoverTree := CoverTree.split [tree106_536,tree106_537,tree106_538,tree106_539,tree106_543,tree106_545]
def tree106_547 : CoverTree := CoverTree.reject 110
def tree106_548 : CoverTree := CoverTree.reject 396
def tree106_549 : CoverTree := CoverTree.reject 367
def tree106_550 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_548,tree106_549,tree106_68,tree106_68]
def tree106_551 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_168,tree106_250,tree106_550]
def tree106_552 : CoverTree := CoverTree.reject 33
def tree106_553 : CoverTree := CoverTree.split [tree106_259,tree106_259,tree106_259,tree106_259,tree106_552,tree106_68]
def tree106_554 : CoverTree := CoverTree.reject 368
def tree106_555 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_554,tree106_68,tree106_68,tree106_68]
def tree106_556 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_168,tree106_553,tree106_555]
def tree106_557 : CoverTree := CoverTree.split [tree106_248,tree106_547,tree106_551,tree106_556,tree106_261,tree106_264]
def tree106_558 : CoverTree := CoverTree.reject 297
def tree106_559 : CoverTree := CoverTree.split [tree106_270,tree106_271,tree106_272,tree106_558,tree106_80,tree106_80]
def tree106_560 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_73,tree106_268,tree106_269,tree106_559]
def tree106_561 : CoverTree := CoverTree.split [tree106_83,tree106_278,tree106_279,tree106_280,tree106_80,tree106_80]
def tree106_562 : CoverTree := CoverTree.reject 298
def tree106_563 : CoverTree := CoverTree.split [tree106_283,tree106_284,tree106_562,tree106_80,tree106_287,tree106_80]
def tree106_564 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_73,tree106_277,tree106_561,tree106_563]
def tree106_565 : CoverTree := CoverTree.reject 168
def tree106_566 : CoverTree := CoverTree.reject 169
def tree106_567 : CoverTree := CoverTree.split [tree106_83,tree106_565,tree106_566,tree106_80,tree106_80,tree106_80]
def tree106_568 : CoverTree := CoverTree.split [tree106_76,tree106_80,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_569 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_73,tree106_567,tree106_291,tree106_568]
def tree106_570 : CoverTree := CoverTree.split [tree106_73,tree106_73,tree106_73,tree106_197,tree106_85,tree106_87]
def tree106_571 : CoverTree := CoverTree.reject 380
def tree106_572 : CoverTree := CoverTree.reject 177
def tree106_573 : CoverTree := CoverTree.reject 170
def tree106_574 : CoverTree := CoverTree.split [tree106_363,tree106_571,tree106_572,tree106_573,tree106_80,tree106_80]
def tree106_575 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_45,tree106_12,tree106_12,tree106_12]
def tree106_576 : CoverTree := CoverTree.split [tree106_43,tree106_575,tree106_80,tree106_80,tree106_80,tree106_80]
def tree106_577 : CoverTree := CoverTree.split [tree106_29,tree106_80,tree106_95,tree106_80,tree106_80,tree106_80]
def tree106_578 : CoverTree := CoverTree.split [tree106_299,tree106_574,tree106_576,tree106_577,tree106_98,tree106_87]
def tree106_579 : CoverTree := CoverTree.split [tree106_266,tree106_560,tree106_564,tree106_569,tree106_570,tree106_578]
def tree106_580 : CoverTree := CoverTree.reject 231
def tree106_581 : CoverTree := CoverTree.reject 232
def tree106_582 : CoverTree := CoverTree.split [tree106_83,tree106_310,tree106_311,tree106_580,tree106_581,tree106_315]
def tree106_583 : CoverTree := CoverTree.reject 381
def tree106_584 : CoverTree := CoverTree.reject 382
def tree106_585 : CoverTree := CoverTree.split [tree106_15,tree106_583,tree106_584,tree106_12,tree106_12,tree106_12]
def tree106_586 : CoverTree := CoverTree.reject 383
def tree106_587 : CoverTree := CoverTree.split [tree106_17,tree106_586,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_588 : CoverTree := CoverTree.split [tree106_317,tree106_318,tree106_585,tree106_587,tree106_322,tree106_315]
def tree106_589 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_308,tree106_309,tree106_582,tree106_588]
def tree106_590 : CoverTree := CoverTree.reject 171
def tree106_591 : CoverTree := CoverTree.reject 151
def tree106_592 : CoverTree := CoverTree.reject 152
def tree106_593 : CoverTree := CoverTree.reject 384
def tree106_594 : CoverTree := CoverTree.split [tree106_402,tree106_12,tree106_593,tree106_12,tree106_12,tree106_12]
def tree106_595 : CoverTree := CoverTree.split [tree106_83,tree106_590,tree106_591,tree106_592,tree106_594,tree106_12]
def tree106_596 : CoverTree := CoverTree.reject 233
def tree106_597 : CoverTree := CoverTree.split [tree106_83,tree106_327,tree106_596,tree106_330,tree106_332,tree106_334]
def tree106_598 : CoverTree := CoverTree.reject 234
def tree106_599 : CoverTree := CoverTree.reject 385
def tree106_600 : CoverTree := CoverTree.split [tree106_15,tree106_599,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_601 : CoverTree := CoverTree.split [tree106_338,tree106_598,tree106_600,tree106_342,tree106_12,tree106_12]
def tree106_602 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_325,tree106_595,tree106_597,tree106_601]
def tree106_603 : CoverTree := CoverTree.reject 124
def tree106_604 : CoverTree := CoverTree.reject 179
def tree106_605 : CoverTree := CoverTree.split [tree106_603,tree106_604,tree106_217,tree106_219,tree106_220,tree106_26]
def tree106_606 : CoverTree := CoverTree.split [tree106_307,tree106_589,tree106_602,tree106_359,tree106_605,tree106_371]
def tree106_607 : CoverTree := CoverTree.reject 299
def tree106_608 : CoverTree := CoverTree.reject 235
def tree106_609 : CoverTree := CoverTree.split [tree106_29,tree106_379,tree106_380,tree106_607,tree106_608,tree106_315]
def tree106_610 : CoverTree := CoverTree.reject 236
def tree106_611 : CoverTree := CoverTree.split [tree106_384,tree106_385,tree106_386,tree106_610,tree106_315,tree106_315]
def tree106_612 : CoverTree := CoverTree.reject 237
def tree106_613 : CoverTree := CoverTree.reject 386
def tree106_614 : CoverTree := CoverTree.split [tree106_15,tree106_613,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_615 : CoverTree := CoverTree.split [tree106_390,tree106_612,tree106_614,tree106_394,tree106_315,tree106_315]
def tree106_616 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_378,tree106_609,tree106_611,tree106_615]
def tree106_617 : CoverTree := CoverTree.reject 178
def tree106_618 : CoverTree := CoverTree.reject 153
def tree106_619 : CoverTree := CoverTree.reject 238
def tree106_620 : CoverTree := CoverTree.reject 387
def tree106_621 : CoverTree := CoverTree.reject 388
def tree106_622 : CoverTree := CoverTree.split [tree106_50,tree106_620,tree106_621,tree106_12,tree106_12,tree106_12]
def tree106_623 : CoverTree := CoverTree.split [tree106_43,tree106_617,tree106_618,tree106_619,tree106_622,tree106_493]
def tree106_624 : CoverTree := CoverTree.reject 239
def tree106_625 : CoverTree := CoverTree.split [tree106_29,tree106_398,tree106_624,tree106_401,tree106_403,tree106_12]
def tree106_626 : CoverTree := CoverTree.split [tree106_405,tree106_406,tree106_16,tree106_18,tree106_332,tree106_12]
def tree106_627 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_623,tree106_625,tree106_626,tree106_412]
def tree106_628 : CoverTree := CoverTree.reject 300
def tree106_629 : CoverTree := CoverTree.split [tree106_43,tree106_414,tree106_628,tree106_417,tree106_51,tree106_12]
def tree106_630 : CoverTree := CoverTree.split [tree106_267,tree106_267,tree106_629,tree106_421,tree106_422,tree106_26]
def tree106_631 : CoverTree := CoverTree.reject 81
def tree106_632 : CoverTree := CoverTree.reject 10
def tree106_633 : CoverTree := CoverTree.split [tree106_632,tree106_632,tree106_632,tree106_529,tree106_369,tree106_12]
def tree106_634 : CoverTree := CoverTree.split [tree106_631,tree106_633,tree106_52,tree106_32,tree106_24,tree106_26]
def tree106_635 : CoverTree := CoverTree.split [tree106_377,tree106_616,tree106_627,tree106_630,tree106_634,tree106_447]
def tree106_636 : CoverTree := CoverTree.reject 370
def tree106_637 : CoverTree := CoverTree.reject 164
def tree106_638 : CoverTree := CoverTree.reject 107
def tree106_639 : CoverTree := CoverTree.reject 108
def tree106_640 : CoverTree := CoverTree.split [tree106_363,tree106_636,tree106_637,tree106_638,tree106_639,tree106_315]
def tree106_641 : CoverTree := CoverTree.reject 240
def tree106_642 : CoverTree := CoverTree.reject 371
def tree106_643 : CoverTree := CoverTree.split [tree106_314,tree106_642,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_644 : CoverTree := CoverTree.split [tree106_43,tree106_456,tree106_457,tree106_641,tree106_643,tree106_315]
def tree106_645 : CoverTree := CoverTree.reject 372
def tree106_646 : CoverTree := CoverTree.reject 373
def tree106_647 : CoverTree := CoverTree.reject 374
def tree106_648 : CoverTree := CoverTree.split [tree106_21,tree106_30,tree106_645,tree106_646,tree106_647,tree106_12]
def tree106_649 : CoverTree := CoverTree.reject 375
def tree106_650 : CoverTree := CoverTree.reject 389
def tree106_651 : CoverTree := CoverTree.split [tree106_15,tree106_649,tree106_650,tree106_12,tree106_12,tree106_12]
def tree106_652 : CoverTree := CoverTree.reject 176
def tree106_653 : CoverTree := CoverTree.split [tree106_17,tree106_652,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_654 : CoverTree := CoverTree.split [tree106_29,tree106_648,tree106_651,tree106_653,tree106_315,tree106_315]
def tree106_655 : CoverTree := CoverTree.reject 301
def tree106_656 : CoverTree := CoverTree.split [tree106_384,tree106_655,tree106_467,tree106_18,tree106_315,tree106_315]
def tree106_657 : CoverTree := CoverTree.reject 390
def tree106_658 : CoverTree := CoverTree.reject 391
def tree106_659 : CoverTree := CoverTree.split [tree106_21,tree106_657,tree106_658,tree106_12,tree106_12,tree106_12]
def tree106_660 : CoverTree := CoverTree.split [tree106_471,tree106_659,tree106_474,tree106_18,tree106_315,tree106_315]
def tree106_661 : CoverTree := CoverTree.split [tree106_454,tree106_640,tree106_644,tree106_654,tree106_656,tree106_660]
def tree106_662 : CoverTree := CoverTree.reject 376
def tree106_663 : CoverTree := CoverTree.split [tree106_368,tree106_662,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_664 : CoverTree := CoverTree.split [tree106_363,tree106_478,tree106_479,tree106_485,tree106_663,tree106_488]
def tree106_665 : CoverTree := CoverTree.reject 377
def tree106_666 : CoverTree := CoverTree.split [tree106_15,tree106_665,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_667 : CoverTree := CoverTree.split [tree106_43,tree106_490,tree106_666,tree106_18,tree106_51,tree106_493]
def tree106_668 : CoverTree := CoverTree.reject 378
def tree106_669 : CoverTree := CoverTree.split [tree106_21,tree106_30,tree106_668,tree106_12,tree106_12,tree106_12]
def tree106_670 : CoverTree := CoverTree.split [tree106_29,tree106_669,tree106_497,tree106_18,tree106_403,tree106_12]
def tree106_671 : CoverTree := CoverTree.split [tree106_405,tree106_23,tree106_16,tree106_18,tree106_332,tree106_12]
def tree106_672 : CoverTree := CoverTree.split [tree106_477,tree106_664,tree106_667,tree106_670,tree106_671,tree106_503]
def tree106_673 : CoverTree := CoverTree.reject 302
def tree106_674 : CoverTree := CoverTree.reject 379
def tree106_675 : CoverTree := CoverTree.split [tree106_17,tree106_674,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_676 : CoverTree := CoverTree.split [tree106_363,tree106_506,tree106_673,tree106_675,tree106_369,tree106_510]
def tree106_677 : CoverTree := CoverTree.reject 183
def tree106_678 : CoverTree := CoverTree.split [tree106_21,tree106_44,tree106_45,tree106_12,tree106_677,tree106_12]
def tree106_679 : CoverTree := CoverTree.split [tree106_43,tree106_678,tree106_514,tree106_18,tree106_51,tree106_12]
def tree106_680 : CoverTree := CoverTree.split [tree106_505,tree106_676,tree106_679,tree106_38,tree106_41,tree106_26]
def tree106_681 : CoverTree := CoverTree.split [tree106_453,tree106_661,tree106_672,tree106_680,tree106_531,tree106_533]
def tree106_682 : CoverTree := CoverTree.split [tree106_546,tree106_557,tree106_579,tree106_606,tree106_635,tree106_681]
def tree106_683 : CoverTree := CoverTree.reject 172
def tree106_684 : CoverTree := CoverTree.reject 144
def tree106_685 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_683,tree106_540,tree106_684]
def tree106_686 : CoverTree := CoverTree.reject 369
def tree106_687 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_686,tree106_68,tree106_68,tree106_68]
def tree106_688 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_544,tree106_687,tree106_70]
def tree106_689 : CoverTree := CoverTree.split [tree106_536,tree106_537,tree106_538,tree106_539,tree106_685,tree106_688]
def tree106_690 : CoverTree := CoverTree.reject 306
def tree106_691 : CoverTree := CoverTree.reject 307
def tree106_692 : CoverTree := CoverTree.reject 319
def tree106_693 : CoverTree := CoverTree.reject 320
def tree106_694 : CoverTree := CoverTree.reject 400
def tree106_695 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_67,tree106_694,tree106_12,tree106_12]
def tree106_696 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_692,tree106_693,tree106_695,tree106_68]
def tree106_697 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_690,tree106_691,tree106_696]
def tree106_698 : CoverTree := CoverTree.reject 308
def tree106_699 : CoverTree := CoverTree.reject 328
def tree106_700 : CoverTree := CoverTree.split [tree106_66,tree106_66,tree106_67,tree106_699,tree106_12,tree106_12]
def tree106_701 : CoverTree := CoverTree.split [tree106_64,tree106_64,tree106_700,tree106_68,tree106_68,tree106_68]
def tree106_702 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_698,tree106_250,tree106_701]
def tree106_703 : CoverTree := CoverTree.reject 309
def tree106_704 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_703,tree106_553,tree106_70]
def tree106_705 : CoverTree := CoverTree.reject 321
def tree106_706 : CoverTree := CoverTree.split [tree106_259,tree106_259,tree106_259,tree106_259,tree106_705,tree106_68]
def tree106_707 : CoverTree := CoverTree.split [tree106_62,tree106_62,tree106_62,tree106_706,tree106_260,tree106_70]
def tree106_708 : CoverTree := CoverTree.split [tree106_248,tree106_697,tree106_702,tree106_704,tree106_707,tree106_264]
def tree106_709 : CoverTree := CoverTree.reject 241
def tree106_710 : CoverTree := CoverTree.reject 242
def tree106_711 : CoverTree := CoverTree.split [tree106_270,tree106_271,tree106_272,tree106_80,tree106_80,tree106_80]
def tree106_712 : CoverTree := CoverTree.split [tree106_454,tree106_709,tree106_710,tree106_268,tree106_269,tree106_711]
def tree106_713 : CoverTree := CoverTree.reject 243
def tree106_714 : CoverTree := CoverTree.reject 244
def tree106_715 : CoverTree := CoverTree.split [tree106_283,tree106_284,tree106_80,tree106_80,tree106_287,tree106_80]
def tree106_716 : CoverTree := CoverTree.split [tree106_477,tree106_713,tree106_714,tree106_277,tree106_561,tree106_715]
def tree106_717 : CoverTree := CoverTree.reject 245
def tree106_718 : CoverTree := CoverTree.reject 246
def tree106_719 : CoverTree := CoverTree.split [tree106_505,tree106_717,tree106_718,tree106_567,tree106_291,tree106_568]
def tree106_720 : CoverTree := CoverTree.reject 247
def tree106_721 : CoverTree := CoverTree.reject 248
def tree106_722 : CoverTree := CoverTree.reject 8
def tree106_723 : CoverTree := CoverTree.split [tree106_83,tree106_722,tree106_722,tree106_722,tree106_722,tree106_80]
def tree106_724 : CoverTree := CoverTree.split [tree106_720,tree106_721,tree106_723,tree106_197,tree106_85,tree106_87]
def tree106_725 : CoverTree := CoverTree.split [tree106_266,tree106_712,tree106_716,tree106_719,tree106_724,tree106_578]
def tree106_726 : CoverTree := CoverTree.reject 180
def tree106_727 : CoverTree := CoverTree.reject 401
def tree106_728 : CoverTree := CoverTree.reject 402
def tree106_729 : CoverTree := CoverTree.split [tree106_17,tree106_727,tree106_728,tree106_12,tree106_12,tree106_12]
def tree106_730 : CoverTree := CoverTree.split [tree106_83,tree106_310,tree106_311,tree106_729,tree106_315,tree106_315]
def tree106_731 : CoverTree := CoverTree.split [tree106_454,tree106_726,tree106_308,tree106_309,tree106_730,tree106_588]
def tree106_732 : CoverTree := CoverTree.reject 174
def tree106_733 : CoverTree := CoverTree.reject 403
def tree106_734 : CoverTree := CoverTree.split [tree106_15,tree106_733,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_735 : CoverTree := CoverTree.split [tree106_83,tree106_327,tree106_734,tree106_330,tree106_332,tree106_334]
def tree106_736 : CoverTree := CoverTree.reject 404
def tree106_737 : CoverTree := CoverTree.split [tree106_21,tree106_736,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_738 : CoverTree := CoverTree.split [tree106_338,tree106_737,tree106_600,tree106_342,tree106_12,tree106_12]
def tree106_739 : CoverTree := CoverTree.split [tree106_477,tree106_732,tree106_325,tree106_595,tree106_735,tree106_738]
def tree106_740 : CoverTree := CoverTree.reject 175
def tree106_741 : CoverTree := CoverTree.split [tree106_505,tree106_740,tree106_352,tree106_355,tree106_358,tree106_26]
def tree106_742 : CoverTree := CoverTree.reject 32
def tree106_743 : CoverTree := CoverTree.split [tree106_83,tree106_632,tree106_632,tree106_742,tree106_742,tree106_12]
def tree106_744 : CoverTree := CoverTree.split [tree106_603,tree106_743,tree106_217,tree106_219,tree106_220,tree106_26]
def tree106_745 : CoverTree := CoverTree.split [tree106_307,tree106_731,tree106_739,tree106_741,tree106_744,tree106_371]
def tree106_746 : CoverTree := CoverTree.split [tree106_449,tree106_450,tree106_373,tree106_374,tree106_375,tree106_376]
def tree106_747 : CoverTree := CoverTree.reject 181
def tree106_748 : CoverTree := CoverTree.reject 405
def tree106_749 : CoverTree := CoverTree.split [tree106_17,tree106_652,tree106_12,tree106_748,tree106_12,tree106_12]
def tree106_750 : CoverTree := CoverTree.split [tree106_29,tree106_379,tree106_380,tree106_749,tree106_315,tree106_315]
def tree106_751 : CoverTree := CoverTree.split [tree106_384,tree106_385,tree106_386,tree106_18,tree106_315,tree106_315]
def tree106_752 : CoverTree := CoverTree.reject 406
def tree106_753 : CoverTree := CoverTree.split [tree106_21,tree106_752,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_754 : CoverTree := CoverTree.split [tree106_390,tree106_753,tree106_614,tree106_394,tree106_315,tree106_315]
def tree106_755 : CoverTree := CoverTree.split [tree106_454,tree106_747,tree106_378,tree106_750,tree106_751,tree106_754]
def tree106_756 : CoverTree := CoverTree.reject 104
def tree106_757 : CoverTree := CoverTree.split [tree106_43,tree106_617,tree106_618,tree106_18,tree106_622,tree106_493]
def tree106_758 : CoverTree := CoverTree.reject 407
def tree106_759 : CoverTree := CoverTree.split [tree106_15,tree106_758,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_760 : CoverTree := CoverTree.split [tree106_29,tree106_398,tree106_759,tree106_401,tree106_403,tree106_12]
def tree106_761 : CoverTree := CoverTree.split [tree106_477,tree106_756,tree106_757,tree106_760,tree106_626,tree106_412]
def tree106_762 : CoverTree := CoverTree.reject 185
def tree106_763 : CoverTree := CoverTree.reject 408
def tree106_764 : CoverTree := CoverTree.reject 409
def tree106_765 : CoverTree := CoverTree.reject 410
def tree106_766 : CoverTree := CoverTree.split [tree106_368,tree106_763,tree106_764,tree106_765,tree106_12,tree106_12]
def tree106_767 : CoverTree := CoverTree.split [tree106_632,tree106_632,tree106_632,tree106_762,tree106_766,tree106_510]
def tree106_768 : CoverTree := CoverTree.split [tree106_43,tree106_414,tree106_514,tree106_417,tree106_51,tree106_12]
def tree106_769 : CoverTree := CoverTree.split [tree106_505,tree106_767,tree106_768,tree106_421,tree106_422,tree106_26]
def tree106_770 : CoverTree := CoverTree.split [tree106_746,tree106_755,tree106_761,tree106_769,tree106_634,tree106_447]
def tree106_771 : CoverTree := CoverTree.reject 397
def tree106_772 : CoverTree := CoverTree.split [tree106_17,tree106_771,tree106_12,tree106_12,tree106_12,tree106_12]
def tree106_773 : CoverTree := CoverTree.split [tree106_43,tree106_456,tree106_457,tree106_772,tree106_643,tree106_315]
def tree106_774 : CoverTree := CoverTree.reject 398
def tree106_775 : CoverTree := CoverTree.split [tree106_21,tree106_22,tree106_774,tree106_12,tree106_12,tree106_12]
def tree106_776 : CoverTree := CoverTree.split [tree106_384,tree106_775,tree106_467,tree106_18,tree106_315,tree106_315]
def tree106_777 : CoverTree := CoverTree.split [tree106_454,tree106_640,tree106_773,tree106_654,tree106_776,tree106_660]
def tree106_778 : CoverTree := CoverTree.reject 399
def tree106_779 : CoverTree := CoverTree.split [tree106_15,tree106_441,tree106_778,tree106_12,tree106_12,tree106_12]
def tree106_780 : CoverTree := CoverTree.split [tree106_363,tree106_506,tree106_779,tree106_675,tree106_369,tree106_510]
def tree106_781 : CoverTree := CoverTree.split [tree106_505,tree106_780,tree106_679,tree106_38,tree106_41,tree106_26]
def tree106_782 : CoverTree := CoverTree.split [tree106_453,tree106_777,tree106_672,tree106_781,tree106_531,tree106_533]
def tree106_783 : CoverTree := CoverTree.split [tree106_689,tree106_708,tree106_725,tree106_745,tree106_770,tree106_782]
def tree106_784 : CoverTree := CoverTree.split [tree106_58,tree106_166,tree106_246,tree106_535,tree106_682,tree106_783]
def tree106 : CoverTree := tree106_784

end Snake9.Shared89
