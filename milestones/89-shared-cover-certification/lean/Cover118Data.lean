import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes118 : List Box := [
[(1,6),(1,6),(1,3),(1,6),(1,3),(1,6)],
[(1,6),(1,2),(1,6),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)],
[(1,6),(1,6),(1,3),(1,6),(1,6),(1,2)],
[(1,6),(1,2),(1,6),(1,6),(1,3),(1,6)],
[(1,4),(1,5),(1,5),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,5),(1,5),(1,4),(1,2)],
[(1,2),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,2),(1,4),(1,5),(1,5),(1,6)],
[(1,6),(1,3),(1,5),(1,3),(1,5),(1,6)],
[(1,2),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,3),(1,2),(1,5),(1,5),(1,6),(1,6)],
[(1,6),(1,6),(1,5),(1,3),(1,5),(1,3)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,6),(1,5),(1,2),(1,5),(1,4)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,2)],
[(1,6),(1,1),(6,6),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(6,6),(1,1)],
[(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,5),(1,5),(1,2),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(6,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(6,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(3,3)],
[(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(6,6),(1,1)],
[(1,6),(4,4),(6,6),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(5,5)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(4,4)],
[(1,6),(1,6),(1,3),(1,2),(1,5),(1,5)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(5,5),(1,1)],
[(1,6),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
[(1,6),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(1,2),(1,3),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(4,4)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,1),(5,5),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(6,6),(3,3),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,2),(1,5),(1,6)],
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
[(1,6),(1,6),(3,3),(5,5),(4,4),(3,3)],
[(1,6),(1,2),(1,5),(1,5),(1,4),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(5,5)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(4,4)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(2,2),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(6,6),(2,2)],
[(2,2),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(6,6),(1,1),(5,5),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(4,4)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(5,5),(4,4),(1,6)],
[(1,6),(3,3),(5,5),(5,5),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(5,5)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(5,5),(3,3),(1,6),(1,6)],
[(3,3),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(6,6),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(5,5),(5,5),(3,3)],
[(1,6),(3,3),(4,4),(5,5),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(3,3),(3,3),(6,6),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(3,3),(2,2),(6,6),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(4,4),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(4,4),(4,4)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(4,4)],
[(2,2),(4,4),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(4,4)],
[(3,3),(4,4),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(1,1),(5,5),(4,4),(1,6),(1,6)],
[(1,1),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(2,2),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(4,4),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(4,4)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(6,6)],
[(1,6),(3,3),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(6,6),(5,5),(1,1),(6,6),(1,6)],
[(2,2),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,3),(1,2),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(4,4)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(4,4)],
[(1,6),(1,6),(1,2),(1,3),(1,5),(1,4)],
[(1,6),(5,5),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(4,4)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(4,4)],
[(1,6),(4,4),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(3,3),(1,6)],
[(4,4),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(5,5),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(1,6),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(5,5)],
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
[(1,6),(1,6),(4,4),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(2,2),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(5,5),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(1,1),(5,5),(4,4),(6,6),(2,2),(1,6)],
[(1,6),(2,2),(4,4),(6,6),(6,6),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(5,5),(3,3)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(4,4)],
[(2,2),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(3,3),(6,6),(4,4),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(5,5),(5,5),(3,3),(1,6)],
[(2,2),(5,5),(3,3),(6,6),(4,4),(1,6)],
[(2,2),(5,5),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(6,6),(3,3),(4,4),(5,5),(1,6)],
[(3,3),(3,3),(3,3),(6,6),(4,4),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(4,4),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(5,5),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(3,3),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(3,3),(4,4),(3,3),(5,5),(5,5),(1,6)],
[(3,3),(4,4),(4,4),(6,6),(2,2),(1,6)],
[(3,3),(5,5),(3,3),(4,4),(5,5),(1,6)],
[(4,4),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(4,4),(3,3),(2,2),(6,6),(5,5),(1,6)],
[(4,4),(3,3),(3,3),(5,5),(5,5),(1,6)],
[(4,4),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(4,4),(3,3),(5,5),(6,6),(2,2),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(5,5),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(1,6),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(5,5)],
[(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(3,3),(1,6)],
[(1,6),(5,5),(4,4),(3,3),(2,2),(1,6)],
[(5,5),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(4,4),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(4,4),(5,5),(5,5),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(6,6),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(6,6),(5,5),(3,3),(4,4),(1,6)],
[(3,3),(4,4),(3,3),(5,5),(4,4),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(2,2),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(3,3),(5,5),(3,3),(5,5),(4,4),(1,6)],
[(3,3),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(3,3),(6,6),(2,2),(5,5),(4,4),(1,6)],
[(3,3),(6,6),(3,3),(3,3),(5,5),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(5,5),(1,6)],
[(4,4),(5,5),(2,2),(5,5),(4,4),(1,6)],
[(4,4),(5,5),(2,2),(5,5),(5,5),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(5,5),(1,6)],
[(5,5),(5,5),(2,2),(5,5),(4,4),(1,6)],
[(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)],
[(3,3),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(5,5),(3,3)],
[(2,2),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(4,4),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(5,5),(5,5),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(3,3),(4,4),(4,4),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(3,3),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(6,6),(5,5),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(3,3),(5,5),(3,3),(4,4),(4,4),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(2,2),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(3,3),(5,5),(5,5),(4,4),(2,2),(1,6)],
[(3,3),(5,5),(6,6),(1,1),(6,6),(1,6)],
[(3,3),(6,6),(2,2),(4,4),(4,4),(1,6)],
[(3,3),(6,6),(3,3),(3,3),(4,4),(1,6)],
[(3,3),(6,6),(3,3),(4,4),(4,4),(1,6)],
[(3,3),(6,6),(4,4),(2,2),(5,5),(1,6)],
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
[(3,3),(6,6),(5,5),(1,1),(1,6),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(2,2),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(5,5),(6,6),(2,2),(2,2),(1,6)],
[(3,3),(5,5),(6,6),(2,2),(3,3),(1,6)],
[(3,3),(6,6),(3,3),(2,2),(4,4),(1,6)],
[(3,3),(6,6),(3,3),(2,2),(5,5),(1,6)],
[(3,3),(6,6),(4,4),(2,2),(3,3),(1,6)],
[(3,3),(6,6),(4,4),(2,2),(4,4),(1,6)],
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

def root118 : Nat := 3934

def tree118_0 : CoverTree := CoverTree.reject 61
def tree118_1 : CoverTree := CoverTree.reject 32
def tree118_2 : CoverTree := CoverTree.reject 12
def tree118_3 : CoverTree := CoverTree.reject 11
def tree118_4 : CoverTree := CoverTree.reject 7
def tree118_5 : CoverTree := CoverTree.reject 84
def tree118_6 : CoverTree := CoverTree.reject 5
def tree118_7 : CoverTree := CoverTree.reject 30
def tree118_8 : CoverTree := CoverTree.reject 106
def tree118_9 : CoverTree := CoverTree.reject 34
def tree118_10 : CoverTree := CoverTree.reject 35
def tree118_11 : CoverTree := CoverTree.reject 25
def tree118_12 : CoverTree := CoverTree.reject 15
def tree118_13 : CoverTree := CoverTree.reject 46
def tree118_14 : CoverTree := CoverTree.reject 47
def tree118_15 : CoverTree := CoverTree.split [tree118_9,tree118_10,tree118_11,tree118_12,tree118_13,tree118_14]
def tree118_16 : CoverTree := CoverTree.reject 218
def tree118_17 : CoverTree := CoverTree.reject 27
def tree118_18 : CoverTree := CoverTree.accept
def tree118_19 : CoverTree := CoverTree.split [tree118_17,tree118_18,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_20 : CoverTree := CoverTree.reject 21
def tree118_21 : CoverTree := CoverTree.split [tree118_20,tree118_18,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_22 : CoverTree := CoverTree.split [tree118_15,tree118_16,tree118_19,tree118_21,tree118_18,tree118_18]
def tree118_23 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_7,tree118_7,tree118_8,tree118_22]
def tree118_24 : CoverTree := CoverTree.reject 6
def tree118_25 : CoverTree := CoverTree.reject 43
def tree118_26 : CoverTree := CoverTree.reject 44
def tree118_27 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_11,tree118_12,tree118_25,tree118_26]
def tree118_28 : CoverTree := CoverTree.reject 45
def tree118_29 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_28,tree118_18,tree118_18,tree118_18]
def tree118_30 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_31 : CoverTree := CoverTree.reject 53
def tree118_32 : CoverTree := CoverTree.split [tree118_31,tree118_18,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_33 : CoverTree := CoverTree.split [tree118_27,tree118_29,tree118_30,tree118_30,tree118_32,tree118_18]
def tree118_34 : CoverTree := CoverTree.reject 26
def tree118_35 : CoverTree := CoverTree.split [tree118_34,tree118_18,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_36 : CoverTree := CoverTree.split [tree118_15,tree118_35,tree118_19,tree118_21,tree118_18,tree118_18]
def tree118_37 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_7,tree118_7,tree118_33,tree118_36]
def tree118_38 : CoverTree := CoverTree.reject 10
def tree118_39 : CoverTree := CoverTree.reject 85
def tree118_40 : CoverTree := CoverTree.reject 17
def tree118_41 : CoverTree := CoverTree.reject 87
def tree118_42 : CoverTree := CoverTree.reject 48
def tree118_43 : CoverTree := CoverTree.reject 49
def tree118_44 : CoverTree := CoverTree.split [tree118_34,tree118_41,tree118_42,tree118_43,tree118_18,tree118_18]
def tree118_45 : CoverTree := CoverTree.reject 88
def tree118_46 : CoverTree := CoverTree.reject 50
def tree118_47 : CoverTree := CoverTree.split [tree118_17,tree118_45,tree118_46,tree118_18,tree118_18,tree118_18]
def tree118_48 : CoverTree := CoverTree.reject 81
def tree118_49 : CoverTree := CoverTree.split [tree118_20,tree118_48,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_50 : CoverTree := CoverTree.reject 64
def tree118_51 : CoverTree := CoverTree.split [tree118_50,tree118_18,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_52 : CoverTree := CoverTree.reject 39
def tree118_53 : CoverTree := CoverTree.split [tree118_52,tree118_18,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_54 : CoverTree := CoverTree.split [tree118_40,tree118_44,tree118_47,tree118_49,tree118_51,tree118_53]
def tree118_55 : CoverTree := CoverTree.split [tree118_9,tree118_10,tree118_11,tree118_12,tree118_25,tree118_26]
def tree118_56 : CoverTree := CoverTree.reject 89
def tree118_57 : CoverTree := CoverTree.split [tree118_34,tree118_56,tree118_28,tree118_18,tree118_18,tree118_18]
def tree118_58 : CoverTree := CoverTree.reject 90
def tree118_59 : CoverTree := CoverTree.split [tree118_17,tree118_58,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_60 : CoverTree := CoverTree.split [tree118_55,tree118_57,tree118_59,tree118_21,tree118_32,tree118_18]
def tree118_61 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_39,tree118_54,tree118_60,tree118_36]
def tree118_62 : CoverTree := CoverTree.split [tree118_4,tree118_4,tree118_5,tree118_23,tree118_37,tree118_61]
def tree118_63 : CoverTree := CoverTree.reject 159
def tree118_64 : CoverTree := CoverTree.reject 0
def tree118_65 : CoverTree := CoverTree.reject 3
def tree118_66 : CoverTree := CoverTree.reject 153
def tree118_67 : CoverTree := CoverTree.reject 154
def tree118_68 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_66,tree118_67,tree118_18,tree118_18]
def tree118_69 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_70 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_68,tree118_69,tree118_69]
def tree118_71 : CoverTree := CoverTree.reject 102
def tree118_72 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_71,tree118_18,tree118_18,tree118_18]
def tree118_73 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_72,tree118_69,tree118_69]
def tree118_74 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_69,tree118_69,tree118_69]
def tree118_75 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_63,tree118_70,tree118_73,tree118_74]
def tree118_76 : CoverTree := CoverTree.reject 134
def tree118_77 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_42,tree118_43,tree118_18,tree118_18]
def tree118_78 : CoverTree := CoverTree.reject 107
def tree118_79 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_46,tree118_78,tree118_18,tree118_18]
def tree118_80 : CoverTree := CoverTree.reject 36
def tree118_81 : CoverTree := CoverTree.split [tree118_80,tree118_80,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_82 : CoverTree := CoverTree.split [tree118_40,tree118_77,tree118_79,tree118_30,tree118_81,tree118_53]
def tree118_83 : CoverTree := CoverTree.reject 91
def tree118_84 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_83,tree118_18,tree118_18,tree118_18]
def tree118_85 : CoverTree := CoverTree.split [tree118_27,tree118_29,tree118_84,tree118_30,tree118_81,tree118_18]
def tree118_86 : CoverTree := CoverTree.reject 92
def tree118_87 : CoverTree := CoverTree.split [tree118_34,tree118_86,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_88 : CoverTree := CoverTree.split [tree118_15,tree118_87,tree118_19,tree118_21,tree118_18,tree118_18]
def tree118_89 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_76,tree118_82,tree118_85,tree118_88]
def tree118_90 : CoverTree := CoverTree.reject 22
def tree118_91 : CoverTree := CoverTree.reject 14
def tree118_92 : CoverTree := CoverTree.reject 57
def tree118_93 : CoverTree := CoverTree.reject 58
def tree118_94 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_91,tree118_92,tree118_93,tree118_18]
def tree118_95 : CoverTree := CoverTree.reject 59
def tree118_96 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_91,tree118_95,tree118_18,tree118_18]
def tree118_97 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_91,tree118_18,tree118_18,tree118_18]
def tree118_98 : CoverTree := CoverTree.split [tree118_91,tree118_91,tree118_91,tree118_18,tree118_18,tree118_18]
def tree118_99 : CoverTree := CoverTree.reject 54
def tree118_100 : CoverTree := CoverTree.split [tree118_99,tree118_18,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_101 : CoverTree := CoverTree.split [tree118_90,tree118_94,tree118_96,tree118_97,tree118_98,tree118_100]
def tree118_102 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_46,tree118_18,tree118_18,tree118_18]
def tree118_103 : CoverTree := CoverTree.reject 93
def tree118_104 : CoverTree := CoverTree.split [tree118_50,tree118_103,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_105 : CoverTree := CoverTree.split [tree118_40,tree118_77,tree118_102,tree118_30,tree118_104,tree118_53]
def tree118_106 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_101,tree118_105,tree118_33,tree118_36]
def tree118_107 : CoverTree := CoverTree.reject 94
def tree118_108 : CoverTree := CoverTree.reject 95
def tree118_109 : CoverTree := CoverTree.split [tree118_34,tree118_107,tree118_108,tree118_92,tree118_93,tree118_18]
def tree118_110 : CoverTree := CoverTree.reject 96
def tree118_111 : CoverTree := CoverTree.reject 97
def tree118_112 : CoverTree := CoverTree.split [tree118_17,tree118_110,tree118_111,tree118_95,tree118_18,tree118_18]
def tree118_113 : CoverTree := CoverTree.reject 98
def tree118_114 : CoverTree := CoverTree.reject 99
def tree118_115 : CoverTree := CoverTree.split [tree118_20,tree118_113,tree118_114,tree118_18,tree118_18,tree118_18]
def tree118_116 : CoverTree := CoverTree.reject 100
def tree118_117 : CoverTree := CoverTree.reject 101
def tree118_118 : CoverTree := CoverTree.split [tree118_116,tree118_117,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_119 : CoverTree := CoverTree.split [tree118_90,tree118_109,tree118_112,tree118_115,tree118_118,tree118_100]
def tree118_120 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_119,tree118_54,tree118_60,tree118_36]
def tree118_121 : CoverTree := CoverTree.split [tree118_4,tree118_4,tree118_75,tree118_89,tree118_106,tree118_120]
def tree118_122 : CoverTree := CoverTree.split [tree118_0,tree118_1,tree118_2,tree118_3,tree118_62,tree118_121]
def tree118_123 : CoverTree := CoverTree.reject 62
def tree118_124 : CoverTree := CoverTree.reject 132
def tree118_125 : CoverTree := CoverTree.reject 113
def tree118_126 : CoverTree := CoverTree.reject 114
def tree118_127 : CoverTree := CoverTree.reject 1
def tree118_128 : CoverTree := CoverTree.reject 126
def tree118_129 : CoverTree := CoverTree.reject 4
def tree118_130 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_21,tree118_32,tree118_18]
def tree118_131 : CoverTree := CoverTree.reject 193
def tree118_132 : CoverTree := CoverTree.split [tree118_20,tree118_131,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_133 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_132,tree118_18,tree118_18]
def tree118_134 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_128,tree118_130,tree118_133]
def tree118_135 : CoverTree := CoverTree.split [tree118_4,tree118_4,tree118_124,tree118_125,tree118_126,tree118_134]
def tree118_136 : CoverTree := CoverTree.reject 40
def tree118_137 : CoverTree := CoverTree.reject 52
def tree118_138 : CoverTree := CoverTree.reject 169
def tree118_139 : CoverTree := CoverTree.reject 139
def tree118_140 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_137,tree118_138,tree118_139]
def tree118_141 : CoverTree := CoverTree.reject 76
def tree118_142 : CoverTree := CoverTree.reject 109
def tree118_143 : CoverTree := CoverTree.reject 222
def tree118_144 : CoverTree := CoverTree.reject 196
def tree118_145 : CoverTree := CoverTree.reject 197
def tree118_146 : CoverTree := CoverTree.split [tree118_15,tree118_143,tree118_144,tree118_145,tree118_18,tree118_18]
def tree118_147 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_141,tree118_142,tree118_146]
def tree118_148 : CoverTree := CoverTree.reject 124
def tree118_149 : CoverTree := CoverTree.split [tree118_27,tree118_148,tree118_30,tree118_30,tree118_32,tree118_18]
def tree118_150 : CoverTree := CoverTree.reject 194
def tree118_151 : CoverTree := CoverTree.split [tree118_34,tree118_150,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_152 : CoverTree := CoverTree.reject 195
def tree118_153 : CoverTree := CoverTree.split [tree118_17,tree118_18,tree118_152,tree118_18,tree118_18,tree118_18]
def tree118_154 : CoverTree := CoverTree.split [tree118_15,tree118_151,tree118_153,tree118_21,tree118_18,tree118_18]
def tree118_155 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_141,tree118_149,tree118_154]
def tree118_156 : CoverTree := CoverTree.reject 321
def tree118_157 : CoverTree := CoverTree.reject 280
def tree118_158 : CoverTree := CoverTree.reject 251
def tree118_159 : CoverTree := CoverTree.split [tree118_90,tree118_156,tree118_157,tree118_158,tree118_118,tree118_100]
def tree118_160 : CoverTree := CoverTree.reject 281
def tree118_161 : CoverTree := CoverTree.split [tree118_40,tree118_160,tree118_47,tree118_49,tree118_51,tree118_53]
def tree118_162 : CoverTree := CoverTree.reject 198
def tree118_163 : CoverTree := CoverTree.split [tree118_15,tree118_162,tree118_19,tree118_21,tree118_18,tree118_18]
def tree118_164 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_159,tree118_161,tree118_60,tree118_163]
def tree118_165 : CoverTree := CoverTree.split [tree118_4,tree118_4,tree118_140,tree118_147,tree118_155,tree118_164]
def tree118_166 : CoverTree := CoverTree.reject 65
def tree118_167 : CoverTree := CoverTree.reject 170
def tree118_168 : CoverTree := CoverTree.reject 151
def tree118_169 : CoverTree := CoverTree.reject 223
def tree118_170 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_169,tree118_69,tree118_69]
def tree118_171 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_166,tree118_167,tree118_168,tree118_170]
def tree118_172 : CoverTree := CoverTree.reject 140
def tree118_173 : CoverTree := CoverTree.reject 116
def tree118_174 : CoverTree := CoverTree.reject 252
def tree118_175 : CoverTree := CoverTree.reject 253
def tree118_176 : CoverTree := CoverTree.split [tree118_27,tree118_174,tree118_175,tree118_30,tree118_81,tree118_18]
def tree118_177 : CoverTree := CoverTree.reject 224
def tree118_178 : CoverTree := CoverTree.reject 199
def tree118_179 : CoverTree := CoverTree.reject 200
def tree118_180 : CoverTree := CoverTree.split [tree118_15,tree118_177,tree118_178,tree118_179,tree118_18,tree118_18]
def tree118_181 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_172,tree118_173,tree118_176,tree118_180]
def tree118_182 : CoverTree := CoverTree.reject 127
def tree118_183 : CoverTree := CoverTree.reject 110
def tree118_184 : CoverTree := CoverTree.reject 254
def tree118_185 : CoverTree := CoverTree.reject 225
def tree118_186 : CoverTree := CoverTree.split [tree118_27,tree118_184,tree118_185,tree118_30,tree118_32,tree118_18]
def tree118_187 : CoverTree := CoverTree.reject 201
def tree118_188 : CoverTree := CoverTree.split [tree118_15,tree118_187,tree118_19,tree118_21,tree118_18,tree118_18]
def tree118_189 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_182,tree118_183,tree118_186,tree118_188]
def tree118_190 : CoverTree := CoverTree.reject 322
def tree118_191 : CoverTree := CoverTree.reject 282
def tree118_192 : CoverTree := CoverTree.reject 255
def tree118_193 : CoverTree := CoverTree.split [tree118_90,tree118_190,tree118_191,tree118_192,tree118_118,tree118_100]
def tree118_194 : CoverTree := CoverTree.reject 283
def tree118_195 : CoverTree := CoverTree.split [tree118_40,tree118_194,tree118_47,tree118_49,tree118_51,tree118_53]
def tree118_196 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_193,tree118_195,tree118_60,tree118_36]
def tree118_197 : CoverTree := CoverTree.split [tree118_4,tree118_4,tree118_171,tree118_181,tree118_189,tree118_196]
def tree118_198 : CoverTree := CoverTree.reject 160
def tree118_199 : CoverTree := CoverTree.reject 141
def tree118_200 : CoverTree := CoverTree.reject 152
def tree118_201 : CoverTree := CoverTree.reject 226
def tree118_202 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_201,tree118_69,tree118_69]
def tree118_203 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_198,tree118_199,tree118_200,tree118_202]
def tree118_204 : CoverTree := CoverTree.reject 142
def tree118_205 : CoverTree := CoverTree.reject 284
def tree118_206 : CoverTree := CoverTree.reject 285
def tree118_207 : CoverTree := CoverTree.split [tree118_40,tree118_205,tree118_206,tree118_30,tree118_81,tree118_53]
def tree118_208 : CoverTree := CoverTree.reject 256
def tree118_209 : CoverTree := CoverTree.reject 257
def tree118_210 : CoverTree := CoverTree.split [tree118_27,tree118_208,tree118_209,tree118_30,tree118_81,tree118_18]
def tree118_211 : CoverTree := CoverTree.reject 227
def tree118_212 : CoverTree := CoverTree.split [tree118_15,tree118_211,tree118_19,tree118_21,tree118_18,tree118_18]
def tree118_213 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_204,tree118_207,tree118_210,tree118_212]
def tree118_214 : CoverTree := CoverTree.reject 128
def tree118_215 : CoverTree := CoverTree.reject 286
def tree118_216 : CoverTree := CoverTree.split [tree118_40,tree118_215,tree118_102,tree118_30,tree118_104,tree118_53]
def tree118_217 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_214,tree118_216,tree118_33,tree118_36]
def tree118_218 : CoverTree := CoverTree.split [tree118_4,tree118_4,tree118_203,tree118_213,tree118_217,tree118_120]
def tree118_219 : CoverTree := CoverTree.reject 161
def tree118_220 : CoverTree := CoverTree.reject 287
def tree118_221 : CoverTree := CoverTree.reject 228
def tree118_222 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_220,tree118_221,tree118_69]
def tree118_223 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_219,tree118_222,tree118_73,tree118_74]
def tree118_224 : CoverTree := CoverTree.reject 323
def tree118_225 : CoverTree := CoverTree.reject 288
def tree118_226 : CoverTree := CoverTree.reject 289
def tree118_227 : CoverTree := CoverTree.reject 115
def tree118_228 : CoverTree := CoverTree.split [tree118_99,tree118_227,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_229 : CoverTree := CoverTree.split [tree118_90,tree118_224,tree118_225,tree118_226,tree118_98,tree118_228]
def tree118_230 : CoverTree := CoverTree.reject 290
def tree118_231 : CoverTree := CoverTree.reject 291
def tree118_232 : CoverTree := CoverTree.split [tree118_40,tree118_230,tree118_231,tree118_30,tree118_81,tree118_53]
def tree118_233 : CoverTree := CoverTree.reject 258
def tree118_234 : CoverTree := CoverTree.split [tree118_27,tree118_233,tree118_84,tree118_30,tree118_81,tree118_18]
def tree118_235 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_229,tree118_232,tree118_234,tree118_88]
def tree118_236 : CoverTree := CoverTree.reject 259
def tree118_237 : CoverTree := CoverTree.split [tree118_90,tree118_94,tree118_96,tree118_236,tree118_98,tree118_100]
def tree118_238 : CoverTree := CoverTree.reject 292
def tree118_239 : CoverTree := CoverTree.split [tree118_40,tree118_238,tree118_102,tree118_30,tree118_104,tree118_53]
def tree118_240 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_237,tree118_239,tree118_33,tree118_36]
def tree118_241 : CoverTree := CoverTree.reject 324
def tree118_242 : CoverTree := CoverTree.reject 293
def tree118_243 : CoverTree := CoverTree.split [tree118_90,tree118_241,tree118_242,tree118_115,tree118_118,tree118_100]
def tree118_244 : CoverTree := CoverTree.split [tree118_38,tree118_38,tree118_243,tree118_54,tree118_60,tree118_36]
def tree118_245 : CoverTree := CoverTree.split [tree118_4,tree118_4,tree118_223,tree118_235,tree118_240,tree118_244]
def tree118_246 : CoverTree := CoverTree.split [tree118_123,tree118_135,tree118_165,tree118_197,tree118_218,tree118_245]
def tree118_247 : CoverTree := CoverTree.reject 63
def tree118_248 : CoverTree := CoverTree.reject 16
def tree118_249 : CoverTree := CoverTree.reject 133
def tree118_250 : CoverTree := CoverTree.reject 13
def tree118_251 : CoverTree := CoverTree.reject 202
def tree118_252 : CoverTree := CoverTree.reject 188
def tree118_253 : CoverTree := CoverTree.reject 219
def tree118_254 : CoverTree := CoverTree.split [tree118_18,tree118_253,tree118_18,tree118_18,tree118_18,tree118_18]
def tree118_255 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_251,tree118_252,tree118_254]
def tree118_256 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_250,tree118_250,tree118_255]
def tree118_257 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_21,tree118_18,tree118_18]
def tree118_258 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_250,tree118_250,tree118_257]
def tree118_259 : CoverTree := CoverTree.reject 129
def tree118_260 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_259,tree118_130,tree118_133]
def tree118_261 : CoverTree := CoverTree.split [tree118_248,tree118_248,tree118_249,tree118_256,tree118_258,tree118_260]
def tree118_262 : CoverTree := CoverTree.reject 23
def tree118_263 : CoverTree := CoverTree.reject 66
def tree118_264 : CoverTree := CoverTree.reject 67
def tree118_265 : CoverTree := CoverTree.reject 143
def tree118_266 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_263,tree118_264,tree118_265]
def tree118_267 : CoverTree := CoverTree.reject 171
def tree118_268 : CoverTree := CoverTree.reject 229
def tree118_269 : CoverTree := CoverTree.reject 220
def tree118_270 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_269,tree118_18,tree118_18,tree118_18]
def tree118_271 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_268,tree118_270,tree118_69]
def tree118_272 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_137,tree118_267,tree118_271]
def tree118_273 : CoverTree := CoverTree.reject 117
def tree118_274 : CoverTree := CoverTree.reject 137
def tree118_275 : CoverTree := CoverTree.reject 138
def tree118_276 : CoverTree := CoverTree.reject 230
def tree118_277 : CoverTree := CoverTree.reject 231
def tree118_278 : CoverTree := CoverTree.split [tree118_27,tree118_274,tree118_275,tree118_276,tree118_277,tree118_18]
def tree118_279 : CoverTree := CoverTree.reject 232
def tree118_280 : CoverTree := CoverTree.reject 203
def tree118_281 : CoverTree := CoverTree.split [tree118_15,tree118_279,tree118_280,tree118_21,tree118_18,tree118_18]
def tree118_282 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_273,tree118_278,tree118_281]
def tree118_283 : CoverTree := CoverTree.reject 166
def tree118_284 : CoverTree := CoverTree.reject 221
def tree118_285 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_46,tree118_284,tree118_18,tree118_18]
def tree118_286 : CoverTree := CoverTree.split [tree118_40,tree118_283,tree118_285,tree118_30,tree118_104,tree118_53]
def tree118_287 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_286,tree118_149,tree118_154]
def tree118_288 : CoverTree := CoverTree.reject 20
def tree118_289 : CoverTree := CoverTree.reject 325
def tree118_290 : CoverTree := CoverTree.reject 294
def tree118_291 : CoverTree := CoverTree.split [tree118_90,tree118_289,tree118_290,tree118_115,tree118_118,tree118_100]
def tree118_292 : CoverTree := CoverTree.reject 295
def tree118_293 : CoverTree := CoverTree.split [tree118_40,tree118_292,tree118_47,tree118_49,tree118_51,tree118_53]
def tree118_294 : CoverTree := CoverTree.reject 204
def tree118_295 : CoverTree := CoverTree.split [tree118_15,tree118_294,tree118_19,tree118_21,tree118_18,tree118_18]
def tree118_296 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_291,tree118_293,tree118_60,tree118_295]
def tree118_297 : CoverTree := CoverTree.split [tree118_262,tree118_266,tree118_272,tree118_282,tree118_287,tree118_296]
def tree118_298 : CoverTree := CoverTree.reject 19
def tree118_299 : CoverTree := CoverTree.reject 74
def tree118_300 : CoverTree := CoverTree.reject 68
def tree118_301 : CoverTree := CoverTree.reject 155
def tree118_302 : CoverTree := CoverTree.reject 233
def tree118_303 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_302,tree118_69,tree118_69]
def tree118_304 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_299,tree118_300,tree118_301,tree118_303]
def tree118_305 : CoverTree := CoverTree.reject 172
def tree118_306 : CoverTree := CoverTree.reject 260
def tree118_307 : CoverTree := CoverTree.reject 234
def tree118_308 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_306,tree118_307,tree118_69]
def tree118_309 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_166,tree118_305,tree118_308,tree118_74]
def tree118_310 : CoverTree := CoverTree.reject 144
def tree118_311 : CoverTree := CoverTree.reject 118
def tree118_312 : CoverTree := CoverTree.reject 261
def tree118_313 : CoverTree := CoverTree.reject 262
def tree118_314 : CoverTree := CoverTree.split [tree118_27,tree118_312,tree118_313,tree118_30,tree118_81,tree118_18]
def tree118_315 : CoverTree := CoverTree.reject 235
def tree118_316 : CoverTree := CoverTree.split [tree118_15,tree118_315,tree118_19,tree118_21,tree118_18,tree118_18]
def tree118_317 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_310,tree118_311,tree118_314,tree118_316]
def tree118_318 : CoverTree := CoverTree.reject 174
def tree118_319 : CoverTree := CoverTree.split [tree118_90,tree118_318,tree118_96,tree118_97,tree118_98,tree118_100]
def tree118_320 : CoverTree := CoverTree.reject 167
def tree118_321 : CoverTree := CoverTree.split [tree118_40,tree118_320,tree118_102,tree118_30,tree118_104,tree118_53]
def tree118_322 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_319,tree118_321,tree118_33,tree118_36]
def tree118_323 : CoverTree := CoverTree.reject 55
def tree118_324 : CoverTree := CoverTree.reject 130
def tree118_325 : CoverTree := CoverTree.split [tree118_323,tree118_324,tree118_119,tree118_54,tree118_60,tree118_36]
def tree118_326 : CoverTree := CoverTree.split [tree118_298,tree118_304,tree118_309,tree118_317,tree118_322,tree118_325]
def tree118_327 : CoverTree := CoverTree.reject 38
def tree118_328 : CoverTree := CoverTree.reject 33
def tree118_329 : CoverTree := CoverTree.reject 69
def tree118_330 : CoverTree := CoverTree.reject 70
def tree118_331 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_327,tree118_328,tree118_329,tree118_330]
def tree118_332 : CoverTree := CoverTree.reject 75
def tree118_333 : CoverTree := CoverTree.reject 145
def tree118_334 : CoverTree := CoverTree.reject 156
def tree118_335 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_332,tree118_333,tree118_334,tree118_74]
def tree118_336 : CoverTree := CoverTree.reject 162
def tree118_337 : CoverTree := CoverTree.reject 296
def tree118_338 : CoverTree := CoverTree.reject 236
def tree118_339 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_337,tree118_338,tree118_69]
def tree118_340 : CoverTree := CoverTree.reject 263
def tree118_341 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_340,tree118_69,tree118_69]
def tree118_342 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_336,tree118_339,tree118_341,tree118_74]
def tree118_343 : CoverTree := CoverTree.reject 146
def tree118_344 : CoverTree := CoverTree.reject 297
def tree118_345 : CoverTree := CoverTree.reject 298
def tree118_346 : CoverTree := CoverTree.split [tree118_40,tree118_344,tree118_345,tree118_30,tree118_81,tree118_53]
def tree118_347 : CoverTree := CoverTree.reject 264
def tree118_348 : CoverTree := CoverTree.split [tree118_27,tree118_347,tree118_84,tree118_30,tree118_81,tree118_18]
def tree118_349 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_343,tree118_346,tree118_348,tree118_88]
def tree118_350 : CoverTree := CoverTree.reject 299
def tree118_351 : CoverTree := CoverTree.split [tree118_40,tree118_350,tree118_102,tree118_30,tree118_104,tree118_53]
def tree118_352 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_101,tree118_351,tree118_33,tree118_36]
def tree118_353 : CoverTree := CoverTree.reject 83
def tree118_354 : CoverTree := CoverTree.reject 78
def tree118_355 : CoverTree := CoverTree.reject 79
def tree118_356 : CoverTree := CoverTree.reject 31
def tree118_357 : CoverTree := CoverTree.reject 2
def tree118_358 : CoverTree := CoverTree.reject 164
def tree118_359 : CoverTree := CoverTree.reject 125
def tree118_360 : CoverTree := CoverTree.reject 165
def tree118_361 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_358,tree118_359,tree118_360]
def tree118_362 : CoverTree := CoverTree.reject 300
def tree118_363 : CoverTree := CoverTree.split [tree118_353,tree118_354,tree118_355,tree118_356,tree118_361,tree118_362]
def tree118_364 : CoverTree := CoverTree.reject 73
def tree118_365 : CoverTree := CoverTree.reject 326
def tree118_366 : CoverTree := CoverTree.reject 327
def tree118_367 : CoverTree := CoverTree.reject 149
def tree118_368 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_367,tree118_18,tree118_18]
def tree118_369 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_18,tree118_18,tree118_18]
def tree118_370 : CoverTree := CoverTree.split [tree118_364,tree118_365,tree118_366,tree118_368,tree118_369,tree118_369]
def tree118_371 : CoverTree := CoverTree.split [tree118_363,tree118_370,tree118_119,tree118_54,tree118_60,tree118_36]
def tree118_372 : CoverTree := CoverTree.split [tree118_331,tree118_335,tree118_342,tree118_349,tree118_352,tree118_371]
def tree118_373 : CoverTree := CoverTree.reject 122
def tree118_374 : CoverTree := CoverTree.reject 82
def tree118_375 : CoverTree := CoverTree.reject 71
def tree118_376 : CoverTree := CoverTree.reject 72
def tree118_377 : CoverTree := CoverTree.split [tree118_373,tree118_374,tree118_327,tree118_328,tree118_375,tree118_376]
def tree118_378 : CoverTree := CoverTree.reject 111
def tree118_379 : CoverTree := CoverTree.reject 277
def tree118_380 : CoverTree := CoverTree.reject 157
def tree118_381 : CoverTree := CoverTree.reject 301
def tree118_382 : CoverTree := CoverTree.reject 177
def tree118_383 : CoverTree := CoverTree.reject 178
def tree118_384 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_382,tree118_383,tree118_18,tree118_18]
def tree118_385 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_381,tree118_384,tree118_69]
def tree118_386 : CoverTree := CoverTree.reject 265
def tree118_387 : CoverTree := CoverTree.reject 136
def tree118_388 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_387,tree118_18,tree118_18,tree118_18]
def tree118_389 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_386,tree118_388,tree118_69]
def tree118_390 : CoverTree := CoverTree.split [tree118_378,tree118_379,tree118_380,tree118_385,tree118_389,tree118_74]
def tree118_391 : CoverTree := CoverTree.reject 112
def tree118_392 : CoverTree := CoverTree.reject 328
def tree118_393 : CoverTree := CoverTree.reject 329
def tree118_394 : CoverTree := CoverTree.reject 182
def tree118_395 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_394,tree118_18,tree118_18]
def tree118_396 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_392,tree118_393,tree118_395]
def tree118_397 : CoverTree := CoverTree.reject 302
def tree118_398 : CoverTree := CoverTree.reject 266
def tree118_399 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_397,tree118_398,tree118_69]
def tree118_400 : CoverTree := CoverTree.reject 303
def tree118_401 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_400,tree118_69,tree118_69]
def tree118_402 : CoverTree := CoverTree.split [tree118_391,tree118_396,tree118_399,tree118_401,tree118_73,tree118_74]
def tree118_403 : CoverTree := CoverTree.reject 56
def tree118_404 : CoverTree := CoverTree.reject 207
def tree118_405 : CoverTree := CoverTree.reject 330
def tree118_406 : CoverTree := CoverTree.reject 331
def tree118_407 : CoverTree := CoverTree.reject 304
def tree118_408 : CoverTree := CoverTree.split [tree118_364,tree118_404,tree118_405,tree118_406,tree118_407,tree118_369]
def tree118_409 : CoverTree := CoverTree.reject 332
def tree118_410 : CoverTree := CoverTree.reject 305
def tree118_411 : CoverTree := CoverTree.reject 306
def tree118_412 : CoverTree := CoverTree.split [tree118_90,tree118_409,tree118_410,tree118_411,tree118_98,tree118_228]
def tree118_413 : CoverTree := CoverTree.reject 307
def tree118_414 : CoverTree := CoverTree.split [tree118_40,tree118_413,tree118_79,tree118_30,tree118_81,tree118_53]
def tree118_415 : CoverTree := CoverTree.split [tree118_403,tree118_408,tree118_412,tree118_414,tree118_85,tree118_88]
def tree118_416 : CoverTree := CoverTree.reject 320
def tree118_417 : CoverTree := CoverTree.reject 208
def tree118_418 : CoverTree := CoverTree.reject 18
def tree118_419 : CoverTree := CoverTree.reject 105
def tree118_420 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_418,tree118_419,tree118_18]
def tree118_421 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_418,tree118_18,tree118_18]
def tree118_422 : CoverTree := CoverTree.split [tree118_364,tree118_417,tree118_420,tree118_421,tree118_421,tree118_369]
def tree118_423 : CoverTree := CoverTree.split [tree118_416,tree118_422,tree118_101,tree118_105,tree118_33,tree118_36]
def tree118_424 : CoverTree := CoverTree.reject 77
def tree118_425 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_424,tree118_18,tree118_18]
def tree118_426 : CoverTree := CoverTree.split [tree118_353,tree118_354,tree118_355,tree118_356,tree118_361,tree118_425]
def tree118_427 : CoverTree := CoverTree.reject 147
def tree118_428 : CoverTree := CoverTree.reject 104
def tree118_429 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_427,tree118_428,tree118_18]
def tree118_430 : CoverTree := CoverTree.reject 148
def tree118_431 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_430,tree118_419,tree118_18]
def tree118_432 : CoverTree := CoverTree.split [tree118_364,tree118_429,tree118_431,tree118_368,tree118_369,tree118_369]
def tree118_433 : CoverTree := CoverTree.split [tree118_426,tree118_432,tree118_119,tree118_54,tree118_60,tree118_36]
def tree118_434 : CoverTree := CoverTree.split [tree118_377,tree118_390,tree118_402,tree118_415,tree118_423,tree118_433]
def tree118_435 : CoverTree := CoverTree.split [tree118_247,tree118_261,tree118_297,tree118_326,tree118_372,tree118_434]
def tree118_436 : CoverTree := CoverTree.reject 24
def tree118_437 : CoverTree := CoverTree.reject 51
def tree118_438 : CoverTree := CoverTree.reject 131
def tree118_439 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_437,tree118_438,tree118_74]
def tree118_440 : CoverTree := CoverTree.reject 187
def tree118_441 : CoverTree := CoverTree.reject 205
def tree118_442 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_441,tree118_18,tree118_254]
def tree118_443 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_437,tree118_440,tree118_442]
def tree118_444 : CoverTree := CoverTree.reject 103
def tree118_445 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_444,tree118_32,tree118_18]
def tree118_446 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_437,tree118_445,tree118_257]
def tree118_447 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_49,tree118_51,tree118_53]
def tree118_448 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_447,tree118_130,tree118_133]
def tree118_449 : CoverTree := CoverTree.split [tree118_248,tree118_248,tree118_439,tree118_443,tree118_446,tree118_448]
def tree118_450 : CoverTree := CoverTree.reject 237
def tree118_451 : CoverTree := CoverTree.reject 238
def tree118_452 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_450,tree118_451,tree118_69]
def tree118_453 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_263,tree118_264,tree118_452]
def tree118_454 : CoverTree := CoverTree.reject 123
def tree118_455 : CoverTree := CoverTree.reject 239
def tree118_456 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_454,tree118_455,tree118_69]
def tree118_457 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_69,tree118_270,tree118_69]
def tree118_458 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_137,tree118_456,tree118_457]
def tree118_459 : CoverTree := CoverTree.reject 119
def tree118_460 : CoverTree := CoverTree.split [tree118_27,tree118_274,tree118_275,tree118_30,tree118_81,tree118_18]
def tree118_461 : CoverTree := CoverTree.reject 240
def tree118_462 : CoverTree := CoverTree.reject 206
def tree118_463 : CoverTree := CoverTree.split [tree118_15,tree118_461,tree118_462,tree118_21,tree118_18,tree118_18]
def tree118_464 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_459,tree118_460,tree118_463]
def tree118_465 : CoverTree := CoverTree.reject 241
def tree118_466 : CoverTree := CoverTree.split [tree118_15,tree118_465,tree118_153,tree118_21,tree118_18,tree118_18]
def tree118_467 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_136,tree118_286,tree118_149,tree118_466]
def tree118_468 : CoverTree := CoverTree.reject 333
def tree118_469 : CoverTree := CoverTree.split [tree118_90,tree118_468,tree118_112,tree118_115,tree118_118,tree118_100]
def tree118_470 : CoverTree := CoverTree.reject 308
def tree118_471 : CoverTree := CoverTree.split [tree118_40,tree118_470,tree118_47,tree118_49,tree118_51,tree118_53]
def tree118_472 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_469,tree118_471,tree118_60,tree118_36]
def tree118_473 : CoverTree := CoverTree.split [tree118_262,tree118_453,tree118_458,tree118_464,tree118_467,tree118_472]
def tree118_474 : CoverTree := CoverTree.reject 267
def tree118_475 : CoverTree := CoverTree.reject 268
def tree118_476 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_474,tree118_475,tree118_69]
def tree118_477 : CoverTree := CoverTree.reject 242
def tree118_478 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_477,tree118_69,tree118_69]
def tree118_479 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_299,tree118_300,tree118_476,tree118_478]
def tree118_480 : CoverTree := CoverTree.reject 173
def tree118_481 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_166,tree118_480,tree118_73,tree118_74]
def tree118_482 : CoverTree := CoverTree.reject 183
def tree118_483 : CoverTree := CoverTree.reject 184
def tree118_484 : CoverTree := CoverTree.split [tree118_90,tree118_318,tree118_482,tree118_483,tree118_98,tree118_228]
def tree118_485 : CoverTree := CoverTree.reject 185
def tree118_486 : CoverTree := CoverTree.reject 186
def tree118_487 : CoverTree := CoverTree.split [tree118_40,tree118_485,tree118_486,tree118_30,tree118_81,tree118_53]
def tree118_488 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_484,tree118_487,tree118_85,tree118_88]
def tree118_489 : CoverTree := CoverTree.reject 247
def tree118_490 : CoverTree := CoverTree.reject 248
def tree118_491 : CoverTree := CoverTree.split [tree118_364,tree118_489,tree118_490,tree118_368,tree118_369,tree118_369]
def tree118_492 : CoverTree := CoverTree.split [tree118_323,tree118_491,tree118_119,tree118_54,tree118_60,tree118_36]
def tree118_493 : CoverTree := CoverTree.split [tree118_298,tree118_479,tree118_481,tree118_488,tree118_322,tree118_492]
def tree118_494 : CoverTree := CoverTree.reject 309
def tree118_495 : CoverTree := CoverTree.reject 310
def tree118_496 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_494,tree118_495,tree118_69]
def tree118_497 : CoverTree := CoverTree.reject 269
def tree118_498 : CoverTree := CoverTree.reject 270
def tree118_499 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_497,tree118_498,tree118_69]
def tree118_500 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_332,tree118_496,tree118_499,tree118_74]
def tree118_501 : CoverTree := CoverTree.reject 163
def tree118_502 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_501,tree118_70,tree118_73,tree118_74]
def tree118_503 : CoverTree := CoverTree.reject 249
def tree118_504 : CoverTree := CoverTree.reject 311
def tree118_505 : CoverTree := CoverTree.reject 121
def tree118_506 : CoverTree := CoverTree.split [tree118_24,tree118_24,tree118_91,tree118_505,tree118_18,tree118_18]
def tree118_507 : CoverTree := CoverTree.split [tree118_90,tree118_503,tree118_504,tree118_506,tree118_98,tree118_228]
def tree118_508 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_507,tree118_82,tree118_85,tree118_88]
def tree118_509 : CoverTree := CoverTree.split [tree118_6,tree118_6,tree118_101,tree118_105,tree118_33,tree118_36]
def tree118_510 : CoverTree := CoverTree.split [tree118_331,tree118_500,tree118_502,tree118_508,tree118_509,tree118_433]
def tree118_511 : CoverTree := CoverTree.reject 278
def tree118_512 : CoverTree := CoverTree.reject 334
def tree118_513 : CoverTree := CoverTree.reject 312
def tree118_514 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_512,tree118_513,tree118_69]
def tree118_515 : CoverTree := CoverTree.reject 313
def tree118_516 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_515,tree118_384,tree118_69]
def tree118_517 : CoverTree := CoverTree.reject 135
def tree118_518 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_517,tree118_18,tree118_18,tree118_18]
def tree118_519 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_518,tree118_388,tree118_69]
def tree118_520 : CoverTree := CoverTree.split [tree118_378,tree118_511,tree118_514,tree118_516,tree118_519,tree118_74]
def tree118_521 : CoverTree := CoverTree.reject 60
def tree118_522 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_418,tree118_521,tree118_18]
def tree118_523 : CoverTree := CoverTree.reject 335
def tree118_524 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_522,tree118_523,tree118_395]
def tree118_525 : CoverTree := CoverTree.reject 150
def tree118_526 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_91,tree118_525,tree118_18,tree118_18]
def tree118_527 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_91,tree118_18,tree118_18,tree118_18]
def tree118_528 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_526,tree118_527,tree118_69]
def tree118_529 : CoverTree := CoverTree.split [tree118_391,tree118_524,tree118_528,tree118_70,tree118_73,tree118_74]
def tree118_530 : CoverTree := CoverTree.reject 336
def tree118_531 : CoverTree := CoverTree.reject 337
def tree118_532 : CoverTree := CoverTree.split [tree118_364,tree118_404,tree118_530,tree118_531,tree118_421,tree118_369]
def tree118_533 : CoverTree := CoverTree.reject 338
def tree118_534 : CoverTree := CoverTree.split [tree118_90,tree118_533,tree118_96,tree118_506,tree118_98,tree118_228]
def tree118_535 : CoverTree := CoverTree.reject 314
def tree118_536 : CoverTree := CoverTree.split [tree118_40,tree118_535,tree118_79,tree118_30,tree118_81,tree118_53]
def tree118_537 : CoverTree := CoverTree.split [tree118_403,tree118_532,tree118_534,tree118_536,tree118_85,tree118_88]
def tree118_538 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_418,tree118_359,tree118_18]
def tree118_539 : CoverTree := CoverTree.reject 168
def tree118_540 : CoverTree := CoverTree.split [tree118_353,tree118_354,tree118_355,tree118_356,tree118_538,tree118_539]
def tree118_541 : CoverTree := CoverTree.split [tree118_540,tree118_422,tree118_101,tree118_105,tree118_33,tree118_36]
def tree118_542 : CoverTree := CoverTree.split [tree118_377,tree118_520,tree118_529,tree118_537,tree118_541,tree118_433]
def tree118_543 : CoverTree := CoverTree.split [tree118_436,tree118_449,tree118_473,tree118_493,tree118_510,tree118_542]
def tree118_544 : CoverTree := CoverTree.reject 41
def tree118_545 : CoverTree := CoverTree.reject 29
def tree118_546 : CoverTree := CoverTree.reject 80
def tree118_547 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_437,tree118_546,tree118_257]
def tree118_548 : CoverTree := CoverTree.reject 37
def tree118_549 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_548,tree118_130,tree118_257]
def tree118_550 : CoverTree := CoverTree.split [tree118_248,tree118_248,tree118_544,tree118_545,tree118_547,tree118_549]
def tree118_551 : CoverTree := CoverTree.reject 243
def tree118_552 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_551,tree118_69,tree118_69]
def tree118_553 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_437,tree118_438,tree118_552]
def tree118_554 : CoverTree := CoverTree.reject 8
def tree118_555 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_554,tree118_554,tree118_18]
def tree118_556 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_21,tree118_18,tree118_254]
def tree118_557 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_437,tree118_555,tree118_556]
def tree118_558 : CoverTree := CoverTree.split [tree118_248,tree118_248,tree118_553,tree118_557,tree118_446,tree118_448]
def tree118_559 : CoverTree := CoverTree.reject 244
def tree118_560 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_559,tree118_69,tree118_69]
def tree118_561 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_136,tree118_263,tree118_264,tree118_560]
def tree118_562 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_454,tree118_69,tree118_69]
def tree118_563 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_136,tree118_137,tree118_562,tree118_457]
def tree118_564 : CoverTree := CoverTree.reject 216
def tree118_565 : CoverTree := CoverTree.reject 217
def tree118_566 : CoverTree := CoverTree.split [tree118_40,tree118_564,tree118_565,tree118_30,tree118_81,tree118_53]
def tree118_567 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_136,tree118_566,tree118_460,tree118_88]
def tree118_568 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_136,tree118_286,tree118_149,tree118_154]
def tree118_569 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_119,tree118_54,tree118_60,tree118_36]
def tree118_570 : CoverTree := CoverTree.split [tree118_262,tree118_561,tree118_563,tree118_567,tree118_568,tree118_569]
def tree118_571 : CoverTree := CoverTree.reject 28
def tree118_572 : CoverTree := CoverTree.reject 271
def tree118_573 : CoverTree := CoverTree.reject 272
def tree118_574 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_572,tree118_573,tree118_69]
def tree118_575 : CoverTree := CoverTree.split [tree118_571,tree118_571,tree118_299,tree118_300,tree118_574,tree118_74]
def tree118_576 : CoverTree := CoverTree.reject 108
def tree118_577 : CoverTree := CoverTree.reject 279
def tree118_578 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_577,tree118_18,tree118_18,tree118_18]
def tree118_579 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_576,tree118_578,tree118_69]
def tree118_580 : CoverTree := CoverTree.split [tree118_571,tree118_571,tree118_166,tree118_579,tree118_73,tree118_74]
def tree118_581 : CoverTree := CoverTree.split [tree118_571,tree118_571,tree118_484,tree118_487,tree118_85,tree118_88]
def tree118_582 : CoverTree := CoverTree.reject 213
def tree118_583 : CoverTree := CoverTree.reject 250
def tree118_584 : CoverTree := CoverTree.split [tree118_582,tree118_583,tree118_319,tree118_321,tree118_33,tree118_36]
def tree118_585 : CoverTree := CoverTree.split [tree118_298,tree118_575,tree118_580,tree118_581,tree118_584,tree118_492]
def tree118_586 : CoverTree := CoverTree.split [tree118_571,tree118_571,tree118_327,tree118_328,tree118_329,tree118_330]
def tree118_587 : CoverTree := CoverTree.reject 315
def tree118_588 : CoverTree := CoverTree.reject 316
def tree118_589 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_587,tree118_588,tree118_69]
def tree118_590 : CoverTree := CoverTree.reject 273
def tree118_591 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_590,tree118_388,tree118_69]
def tree118_592 : CoverTree := CoverTree.split [tree118_571,tree118_571,tree118_332,tree118_589,tree118_591,tree118_74]
def tree118_593 : CoverTree := CoverTree.reject 317
def tree118_594 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_593,tree118_527,tree118_69]
def tree118_595 : CoverTree := CoverTree.split [tree118_571,tree118_571,tree118_594,tree118_70,tree118_73,tree118_74]
def tree118_596 : CoverTree := CoverTree.reject 318
def tree118_597 : CoverTree := CoverTree.split [tree118_90,tree118_503,tree118_596,tree118_506,tree118_98,tree118_228]
def tree118_598 : CoverTree := CoverTree.split [tree118_571,tree118_571,tree118_597,tree118_82,tree118_85,tree118_88]
def tree118_599 : CoverTree := CoverTree.reject 180
def tree118_600 : CoverTree := CoverTree.reject 42
def tree118_601 : CoverTree := CoverTree.split [tree118_600,tree118_600,tree118_600,tree118_421,tree118_421,tree118_369]
def tree118_602 : CoverTree := CoverTree.split [tree118_599,tree118_601,tree118_101,tree118_105,tree118_33,tree118_36]
def tree118_603 : CoverTree := CoverTree.split [tree118_586,tree118_592,tree118_595,tree118_598,tree118_602,tree118_433]
def tree118_604 : CoverTree := CoverTree.reject 189
def tree118_605 : CoverTree := CoverTree.reject 190
def tree118_606 : CoverTree := CoverTree.reject 181
def tree118_607 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_606,tree118_18,tree118_18]
def tree118_608 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_604,tree118_605,tree118_607]
def tree118_609 : CoverTree := CoverTree.reject 339
def tree118_610 : CoverTree := CoverTree.reject 179
def tree118_611 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_91,tree118_610,tree118_18,tree118_18]
def tree118_612 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_609,tree118_611,tree118_69]
def tree118_613 : CoverTree := CoverTree.reject 175
def tree118_614 : CoverTree := CoverTree.reject 176
def tree118_615 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_613,tree118_614,tree118_18,tree118_18]
def tree118_616 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_615,tree118_384,tree118_69]
def tree118_617 : CoverTree := CoverTree.split [tree118_378,tree118_608,tree118_612,tree118_616,tree118_519,tree118_74]
def tree118_618 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_522,tree118_522,tree118_395]
def tree118_619 : CoverTree := CoverTree.split [tree118_391,tree118_618,tree118_528,tree118_70,tree118_73,tree118_74]
def tree118_620 : CoverTree := CoverTree.reject 340
def tree118_621 : CoverTree := CoverTree.reject 192
def tree118_622 : CoverTree := CoverTree.split [tree118_357,tree118_357,tree118_357,tree118_418,tree118_621,tree118_18]
def tree118_623 : CoverTree := CoverTree.split [tree118_364,tree118_404,tree118_620,tree118_622,tree118_421,tree118_369]
def tree118_624 : CoverTree := CoverTree.split [tree118_90,tree118_94,tree118_96,tree118_506,tree118_98,tree118_228]
def tree118_625 : CoverTree := CoverTree.split [tree118_403,tree118_623,tree118_624,tree118_82,tree118_85,tree118_88]
def tree118_626 : CoverTree := CoverTree.split [tree118_377,tree118_617,tree118_619,tree118_625,tree118_541,tree118_433]
def tree118_627 : CoverTree := CoverTree.split [tree118_550,tree118_558,tree118_570,tree118_585,tree118_603,tree118_626]
def tree118_628 : CoverTree := CoverTree.reject 158
def tree118_629 : CoverTree := CoverTree.reject 120
def tree118_630 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_628,tree118_546,tree118_629]
def tree118_631 : CoverTree := CoverTree.split [tree118_248,tree118_248,tree118_544,tree118_545,tree118_630,tree118_549]
def tree118_632 : CoverTree := CoverTree.reject 209
def tree118_633 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_632,tree118_438,tree118_74]
def tree118_634 : CoverTree := CoverTree.reject 191
def tree118_635 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_634,tree118_555,tree118_556]
def tree118_636 : CoverTree := CoverTree.reject 215
def tree118_637 : CoverTree := CoverTree.split [tree118_129,tree118_129,tree118_129,tree118_444,tree118_636,tree118_53]
def tree118_638 : CoverTree := CoverTree.split [tree118_127,tree118_127,tree118_127,tree118_637,tree118_445,tree118_257]
def tree118_639 : CoverTree := CoverTree.split [tree118_248,tree118_248,tree118_633,tree118_635,tree118_638,tree118_448]
def tree118_640 : CoverTree := CoverTree.reject 210
def tree118_641 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_640,tree118_263,tree118_264,tree118_74]
def tree118_642 : CoverTree := CoverTree.reject 211
def tree118_643 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_642,tree118_137,tree118_562,tree118_457]
def tree118_644 : CoverTree := CoverTree.reject 212
def tree118_645 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_644,tree118_566,tree118_460,tree118_88]
def tree118_646 : CoverTree := CoverTree.reject 9
def tree118_647 : CoverTree := CoverTree.split [tree118_646,tree118_646,tree118_646,tree118_646,tree118_646,tree118_100]
def tree118_648 : CoverTree := CoverTree.split [tree118_288,tree118_288,tree118_647,tree118_286,tree118_149,tree118_154]
def tree118_649 : CoverTree := CoverTree.split [tree118_262,tree118_641,tree118_643,tree118_645,tree118_648,tree118_569]
def tree118_650 : CoverTree := CoverTree.reject 274
def tree118_651 : CoverTree := CoverTree.split [tree118_378,tree118_650,tree118_299,tree118_300,tree118_519,tree118_74]
def tree118_652 : CoverTree := CoverTree.reject 275
def tree118_653 : CoverTree := CoverTree.split [tree118_391,tree118_652,tree118_166,tree118_579,tree118_73,tree118_74]
def tree118_654 : CoverTree := CoverTree.reject 245
def tree118_655 : CoverTree := CoverTree.split [tree118_403,tree118_654,tree118_484,tree118_487,tree118_85,tree118_88]
def tree118_656 : CoverTree := CoverTree.reject 86
def tree118_657 : CoverTree := CoverTree.split [tree118_600,tree118_600,tree118_600,tree118_656,tree118_656,tree118_369]
def tree118_658 : CoverTree := CoverTree.split [tree118_582,tree118_657,tree118_319,tree118_321,tree118_33,tree118_36]
def tree118_659 : CoverTree := CoverTree.split [tree118_298,tree118_651,tree118_653,tree118_655,tree118_658,tree118_492]
def tree118_660 : CoverTree := CoverTree.split [tree118_373,tree118_374,tree118_327,tree118_328,tree118_329,tree118_330]
def tree118_661 : CoverTree := CoverTree.reject 276
def tree118_662 : CoverTree := CoverTree.split [tree118_378,tree118_661,tree118_332,tree118_616,tree118_519,tree118_74]
def tree118_663 : CoverTree := CoverTree.reject 214
def tree118_664 : CoverTree := CoverTree.split [tree118_391,tree118_663,tree118_528,tree118_70,tree118_73,tree118_74]
def tree118_665 : CoverTree := CoverTree.reject 319
def tree118_666 : CoverTree := CoverTree.split [tree118_600,tree118_600,tree118_600,tree118_665,tree118_421,tree118_369]
def tree118_667 : CoverTree := CoverTree.split [tree118_90,tree118_503,tree118_96,tree118_506,tree118_98,tree118_228]
def tree118_668 : CoverTree := CoverTree.split [tree118_403,tree118_666,tree118_667,tree118_82,tree118_85,tree118_88]
def tree118_669 : CoverTree := CoverTree.split [tree118_660,tree118_662,tree118_664,tree118_668,tree118_602,tree118_433]
def tree118_670 : CoverTree := CoverTree.reject 246
def tree118_671 : CoverTree := CoverTree.split [tree118_65,tree118_65,tree118_91,tree118_610,tree118_670,tree118_18]
def tree118_672 : CoverTree := CoverTree.split [tree118_64,tree118_64,tree118_64,tree118_671,tree118_611,tree118_69]
def tree118_673 : CoverTree := CoverTree.split [tree118_378,tree118_608,tree118_672,tree118_616,tree118_519,tree118_74]
def tree118_674 : CoverTree := CoverTree.split [tree118_364,tree118_404,tree118_420,tree118_622,tree118_421,tree118_369]
def tree118_675 : CoverTree := CoverTree.split [tree118_403,tree118_674,tree118_624,tree118_82,tree118_85,tree118_88]
def tree118_676 : CoverTree := CoverTree.split [tree118_377,tree118_673,tree118_619,tree118_675,tree118_541,tree118_433]
def tree118_677 : CoverTree := CoverTree.split [tree118_631,tree118_639,tree118_649,tree118_659,tree118_669,tree118_676]
def tree118_678 : CoverTree := CoverTree.split [tree118_122,tree118_246,tree118_435,tree118_543,tree118_627,tree118_677]
def tree118 : CoverTree := tree118_678

end Snake9.Shared89
