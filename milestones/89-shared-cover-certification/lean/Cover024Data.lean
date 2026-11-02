import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes024 : List Box := [
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
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,6),(1,5),(1,2),(1,5),(1,4)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,2)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(6,6),(1,1)],
[(1,6),(1,5),(1,5),(1,2),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(6,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(6,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(3,3)],
[(1,6),(2,2),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(1,6),(5,5),(5,5),(1,1)],
[(1,6),(4,4),(6,6),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(5,5)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(5,5),(1,1)],
[(1,6),(1,6),(1,3),(1,2),(1,5),(1,5)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
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
[(1,6),(1,1),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(4,4)],
[(1,6),(1,1),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,1),(5,5),(5,5),(1,6),(1,6)],
[(1,6),(1,1),(6,6),(4,4),(1,6),(1,6)],
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
[(4,4),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(5,5),(2,2),(2,2),(1,6),(1,6),(1,6)],
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
[(3,3),(2,2),(2,2),(1,6),(1,6),(1,6)],
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
[(1,6),(2,2),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(2,2),(6,6),(4,4),(1,6)],
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
[(1,6),(2,2),(2,2),(6,6),(5,5),(3,3)],
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

def root024 : Nat := 2570

def tree024_0 : CoverTree := CoverTree.reject 32
def tree024_1 : CoverTree := CoverTree.reject 33
def tree024_2 : CoverTree := CoverTree.reject 12
def tree024_3 : CoverTree := CoverTree.reject 11
def tree024_4 : CoverTree := CoverTree.reject 7
def tree024_5 : CoverTree := CoverTree.reject 86
def tree024_6 : CoverTree := CoverTree.reject 5
def tree024_7 : CoverTree := CoverTree.reject 30
def tree024_8 : CoverTree := CoverTree.reject 108
def tree024_9 : CoverTree := CoverTree.reject 36
def tree024_10 : CoverTree := CoverTree.reject 37
def tree024_11 : CoverTree := CoverTree.reject 24
def tree024_12 : CoverTree := CoverTree.reject 15
def tree024_13 : CoverTree := CoverTree.reject 46
def tree024_14 : CoverTree := CoverTree.reject 47
def tree024_15 : CoverTree := CoverTree.split [tree024_9,tree024_10,tree024_11,tree024_12,tree024_13,tree024_14]
def tree024_16 : CoverTree := CoverTree.reject 226
def tree024_17 : CoverTree := CoverTree.reject 26
def tree024_18 : CoverTree := CoverTree.accept
def tree024_19 : CoverTree := CoverTree.split [tree024_17,tree024_18,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_20 : CoverTree := CoverTree.reject 20
def tree024_21 : CoverTree := CoverTree.split [tree024_20,tree024_18,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_22 : CoverTree := CoverTree.split [tree024_15,tree024_16,tree024_19,tree024_21,tree024_18,tree024_18]
def tree024_23 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_7,tree024_7,tree024_8,tree024_22]
def tree024_24 : CoverTree := CoverTree.reject 6
def tree024_25 : CoverTree := CoverTree.reject 43
def tree024_26 : CoverTree := CoverTree.reject 44
def tree024_27 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_11,tree024_12,tree024_25,tree024_26]
def tree024_28 : CoverTree := CoverTree.reject 45
def tree024_29 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_28,tree024_18,tree024_18,tree024_18]
def tree024_30 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_31 : CoverTree := CoverTree.reject 54
def tree024_32 : CoverTree := CoverTree.split [tree024_31,tree024_18,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_33 : CoverTree := CoverTree.split [tree024_27,tree024_29,tree024_30,tree024_30,tree024_32,tree024_18]
def tree024_34 : CoverTree := CoverTree.reject 25
def tree024_35 : CoverTree := CoverTree.split [tree024_34,tree024_18,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_36 : CoverTree := CoverTree.split [tree024_15,tree024_35,tree024_19,tree024_21,tree024_18,tree024_18]
def tree024_37 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_7,tree024_7,tree024_33,tree024_36]
def tree024_38 : CoverTree := CoverTree.reject 10
def tree024_39 : CoverTree := CoverTree.reject 87
def tree024_40 : CoverTree := CoverTree.reject 16
def tree024_41 : CoverTree := CoverTree.reject 89
def tree024_42 : CoverTree := CoverTree.reject 48
def tree024_43 : CoverTree := CoverTree.reject 49
def tree024_44 : CoverTree := CoverTree.split [tree024_34,tree024_41,tree024_42,tree024_43,tree024_18,tree024_18]
def tree024_45 : CoverTree := CoverTree.reject 90
def tree024_46 : CoverTree := CoverTree.reject 50
def tree024_47 : CoverTree := CoverTree.split [tree024_17,tree024_45,tree024_46,tree024_18,tree024_18,tree024_18]
def tree024_48 : CoverTree := CoverTree.reject 83
def tree024_49 : CoverTree := CoverTree.split [tree024_20,tree024_48,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_50 : CoverTree := CoverTree.reject 60
def tree024_51 : CoverTree := CoverTree.split [tree024_50,tree024_18,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_52 : CoverTree := CoverTree.reject 41
def tree024_53 : CoverTree := CoverTree.split [tree024_52,tree024_18,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_54 : CoverTree := CoverTree.split [tree024_40,tree024_44,tree024_47,tree024_49,tree024_51,tree024_53]
def tree024_55 : CoverTree := CoverTree.split [tree024_9,tree024_10,tree024_11,tree024_12,tree024_25,tree024_26]
def tree024_56 : CoverTree := CoverTree.reject 91
def tree024_57 : CoverTree := CoverTree.split [tree024_34,tree024_56,tree024_28,tree024_18,tree024_18,tree024_18]
def tree024_58 : CoverTree := CoverTree.reject 92
def tree024_59 : CoverTree := CoverTree.split [tree024_17,tree024_58,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_60 : CoverTree := CoverTree.split [tree024_55,tree024_57,tree024_59,tree024_21,tree024_32,tree024_18]
def tree024_61 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_39,tree024_54,tree024_60,tree024_36]
def tree024_62 : CoverTree := CoverTree.split [tree024_4,tree024_4,tree024_5,tree024_23,tree024_37,tree024_61]
def tree024_63 : CoverTree := CoverTree.reject 164
def tree024_64 : CoverTree := CoverTree.reject 0
def tree024_65 : CoverTree := CoverTree.reject 3
def tree024_66 : CoverTree := CoverTree.reject 158
def tree024_67 : CoverTree := CoverTree.reject 159
def tree024_68 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_66,tree024_67,tree024_18,tree024_18]
def tree024_69 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_70 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_68,tree024_69,tree024_69]
def tree024_71 : CoverTree := CoverTree.reject 104
def tree024_72 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_71,tree024_18,tree024_18,tree024_18]
def tree024_73 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_72,tree024_69,tree024_69]
def tree024_74 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_69,tree024_69,tree024_69]
def tree024_75 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_63,tree024_70,tree024_73,tree024_74]
def tree024_76 : CoverTree := CoverTree.reject 139
def tree024_77 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_42,tree024_43,tree024_18,tree024_18]
def tree024_78 : CoverTree := CoverTree.reject 109
def tree024_79 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_46,tree024_78,tree024_18,tree024_18]
def tree024_80 : CoverTree := CoverTree.reject 38
def tree024_81 : CoverTree := CoverTree.split [tree024_80,tree024_80,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_82 : CoverTree := CoverTree.split [tree024_40,tree024_77,tree024_79,tree024_30,tree024_81,tree024_53]
def tree024_83 : CoverTree := CoverTree.reject 93
def tree024_84 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_83,tree024_18,tree024_18,tree024_18]
def tree024_85 : CoverTree := CoverTree.split [tree024_27,tree024_29,tree024_84,tree024_30,tree024_81,tree024_18]
def tree024_86 : CoverTree := CoverTree.reject 94
def tree024_87 : CoverTree := CoverTree.split [tree024_34,tree024_86,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_88 : CoverTree := CoverTree.split [tree024_15,tree024_87,tree024_19,tree024_21,tree024_18,tree024_18]
def tree024_89 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_76,tree024_82,tree024_85,tree024_88]
def tree024_90 : CoverTree := CoverTree.reject 22
def tree024_91 : CoverTree := CoverTree.reject 14
def tree024_92 : CoverTree := CoverTree.reject 57
def tree024_93 : CoverTree := CoverTree.reject 58
def tree024_94 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_91,tree024_92,tree024_93,tree024_18]
def tree024_95 : CoverTree := CoverTree.reject 59
def tree024_96 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_91,tree024_95,tree024_18,tree024_18]
def tree024_97 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_91,tree024_18,tree024_18,tree024_18]
def tree024_98 : CoverTree := CoverTree.split [tree024_91,tree024_91,tree024_91,tree024_18,tree024_18,tree024_18]
def tree024_99 : CoverTree := CoverTree.reject 53
def tree024_100 : CoverTree := CoverTree.split [tree024_99,tree024_18,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_101 : CoverTree := CoverTree.split [tree024_90,tree024_94,tree024_96,tree024_97,tree024_98,tree024_100]
def tree024_102 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_46,tree024_18,tree024_18,tree024_18]
def tree024_103 : CoverTree := CoverTree.reject 95
def tree024_104 : CoverTree := CoverTree.split [tree024_50,tree024_103,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_105 : CoverTree := CoverTree.split [tree024_40,tree024_77,tree024_102,tree024_30,tree024_104,tree024_53]
def tree024_106 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_101,tree024_105,tree024_33,tree024_36]
def tree024_107 : CoverTree := CoverTree.reject 96
def tree024_108 : CoverTree := CoverTree.reject 97
def tree024_109 : CoverTree := CoverTree.split [tree024_34,tree024_107,tree024_108,tree024_92,tree024_93,tree024_18]
def tree024_110 : CoverTree := CoverTree.reject 98
def tree024_111 : CoverTree := CoverTree.reject 99
def tree024_112 : CoverTree := CoverTree.split [tree024_17,tree024_110,tree024_111,tree024_95,tree024_18,tree024_18]
def tree024_113 : CoverTree := CoverTree.reject 100
def tree024_114 : CoverTree := CoverTree.reject 101
def tree024_115 : CoverTree := CoverTree.split [tree024_20,tree024_113,tree024_114,tree024_18,tree024_18,tree024_18]
def tree024_116 : CoverTree := CoverTree.reject 102
def tree024_117 : CoverTree := CoverTree.reject 103
def tree024_118 : CoverTree := CoverTree.split [tree024_116,tree024_117,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_119 : CoverTree := CoverTree.split [tree024_90,tree024_109,tree024_112,tree024_115,tree024_118,tree024_100]
def tree024_120 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_119,tree024_54,tree024_60,tree024_36]
def tree024_121 : CoverTree := CoverTree.split [tree024_4,tree024_4,tree024_75,tree024_89,tree024_106,tree024_120]
def tree024_122 : CoverTree := CoverTree.split [tree024_0,tree024_1,tree024_2,tree024_3,tree024_62,tree024_121]
def tree024_123 : CoverTree := CoverTree.reject 34
def tree024_124 : CoverTree := CoverTree.reject 136
def tree024_125 : CoverTree := CoverTree.reject 115
def tree024_126 : CoverTree := CoverTree.reject 116
def tree024_127 : CoverTree := CoverTree.reject 1
def tree024_128 : CoverTree := CoverTree.reject 130
def tree024_129 : CoverTree := CoverTree.reject 4
def tree024_130 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_21,tree024_32,tree024_18]
def tree024_131 : CoverTree := CoverTree.reject 198
def tree024_132 : CoverTree := CoverTree.split [tree024_20,tree024_131,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_133 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_132,tree024_18,tree024_18]
def tree024_134 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_128,tree024_130,tree024_133]
def tree024_135 : CoverTree := CoverTree.split [tree024_4,tree024_4,tree024_124,tree024_125,tree024_126,tree024_134]
def tree024_136 : CoverTree := CoverTree.reject 40
def tree024_137 : CoverTree := CoverTree.reject 52
def tree024_138 : CoverTree := CoverTree.reject 174
def tree024_139 : CoverTree := CoverTree.reject 144
def tree024_140 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_137,tree024_138,tree024_139]
def tree024_141 : CoverTree := CoverTree.reject 74
def tree024_142 : CoverTree := CoverTree.reject 111
def tree024_143 : CoverTree := CoverTree.reject 230
def tree024_144 : CoverTree := CoverTree.reject 201
def tree024_145 : CoverTree := CoverTree.reject 202
def tree024_146 : CoverTree := CoverTree.split [tree024_15,tree024_143,tree024_144,tree024_145,tree024_18,tree024_18]
def tree024_147 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_141,tree024_142,tree024_146]
def tree024_148 : CoverTree := CoverTree.reject 128
def tree024_149 : CoverTree := CoverTree.split [tree024_27,tree024_148,tree024_30,tree024_30,tree024_32,tree024_18]
def tree024_150 : CoverTree := CoverTree.reject 199
def tree024_151 : CoverTree := CoverTree.split [tree024_34,tree024_150,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_152 : CoverTree := CoverTree.reject 200
def tree024_153 : CoverTree := CoverTree.split [tree024_17,tree024_18,tree024_152,tree024_18,tree024_18,tree024_18]
def tree024_154 : CoverTree := CoverTree.split [tree024_15,tree024_151,tree024_153,tree024_21,tree024_18,tree024_18]
def tree024_155 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_141,tree024_149,tree024_154]
def tree024_156 : CoverTree := CoverTree.reject 330
def tree024_157 : CoverTree := CoverTree.reject 288
def tree024_158 : CoverTree := CoverTree.reject 259
def tree024_159 : CoverTree := CoverTree.split [tree024_90,tree024_156,tree024_157,tree024_158,tree024_118,tree024_100]
def tree024_160 : CoverTree := CoverTree.reject 289
def tree024_161 : CoverTree := CoverTree.split [tree024_40,tree024_160,tree024_47,tree024_49,tree024_51,tree024_53]
def tree024_162 : CoverTree := CoverTree.reject 203
def tree024_163 : CoverTree := CoverTree.split [tree024_15,tree024_162,tree024_19,tree024_21,tree024_18,tree024_18]
def tree024_164 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_159,tree024_161,tree024_60,tree024_163]
def tree024_165 : CoverTree := CoverTree.split [tree024_4,tree024_4,tree024_140,tree024_147,tree024_155,tree024_164]
def tree024_166 : CoverTree := CoverTree.reject 63
def tree024_167 : CoverTree := CoverTree.reject 175
def tree024_168 : CoverTree := CoverTree.reject 156
def tree024_169 : CoverTree := CoverTree.reject 231
def tree024_170 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_169,tree024_69,tree024_69]
def tree024_171 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_166,tree024_167,tree024_168,tree024_170]
def tree024_172 : CoverTree := CoverTree.reject 145
def tree024_173 : CoverTree := CoverTree.reject 118
def tree024_174 : CoverTree := CoverTree.reject 260
def tree024_175 : CoverTree := CoverTree.reject 261
def tree024_176 : CoverTree := CoverTree.split [tree024_27,tree024_174,tree024_175,tree024_30,tree024_81,tree024_18]
def tree024_177 : CoverTree := CoverTree.reject 232
def tree024_178 : CoverTree := CoverTree.reject 204
def tree024_179 : CoverTree := CoverTree.reject 205
def tree024_180 : CoverTree := CoverTree.split [tree024_15,tree024_177,tree024_178,tree024_179,tree024_18,tree024_18]
def tree024_181 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_172,tree024_173,tree024_176,tree024_180]
def tree024_182 : CoverTree := CoverTree.reject 131
def tree024_183 : CoverTree := CoverTree.reject 112
def tree024_184 : CoverTree := CoverTree.reject 262
def tree024_185 : CoverTree := CoverTree.reject 233
def tree024_186 : CoverTree := CoverTree.split [tree024_27,tree024_184,tree024_185,tree024_30,tree024_32,tree024_18]
def tree024_187 : CoverTree := CoverTree.reject 206
def tree024_188 : CoverTree := CoverTree.split [tree024_15,tree024_187,tree024_19,tree024_21,tree024_18,tree024_18]
def tree024_189 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_182,tree024_183,tree024_186,tree024_188]
def tree024_190 : CoverTree := CoverTree.reject 331
def tree024_191 : CoverTree := CoverTree.reject 290
def tree024_192 : CoverTree := CoverTree.reject 263
def tree024_193 : CoverTree := CoverTree.split [tree024_90,tree024_190,tree024_191,tree024_192,tree024_118,tree024_100]
def tree024_194 : CoverTree := CoverTree.reject 291
def tree024_195 : CoverTree := CoverTree.split [tree024_40,tree024_194,tree024_47,tree024_49,tree024_51,tree024_53]
def tree024_196 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_193,tree024_195,tree024_60,tree024_36]
def tree024_197 : CoverTree := CoverTree.split [tree024_4,tree024_4,tree024_171,tree024_181,tree024_189,tree024_196]
def tree024_198 : CoverTree := CoverTree.reject 165
def tree024_199 : CoverTree := CoverTree.reject 146
def tree024_200 : CoverTree := CoverTree.reject 157
def tree024_201 : CoverTree := CoverTree.reject 234
def tree024_202 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_201,tree024_69,tree024_69]
def tree024_203 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_198,tree024_199,tree024_200,tree024_202]
def tree024_204 : CoverTree := CoverTree.reject 147
def tree024_205 : CoverTree := CoverTree.reject 292
def tree024_206 : CoverTree := CoverTree.reject 293
def tree024_207 : CoverTree := CoverTree.split [tree024_40,tree024_205,tree024_206,tree024_30,tree024_81,tree024_53]
def tree024_208 : CoverTree := CoverTree.reject 264
def tree024_209 : CoverTree := CoverTree.reject 265
def tree024_210 : CoverTree := CoverTree.split [tree024_27,tree024_208,tree024_209,tree024_30,tree024_81,tree024_18]
def tree024_211 : CoverTree := CoverTree.reject 235
def tree024_212 : CoverTree := CoverTree.split [tree024_15,tree024_211,tree024_19,tree024_21,tree024_18,tree024_18]
def tree024_213 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_204,tree024_207,tree024_210,tree024_212]
def tree024_214 : CoverTree := CoverTree.reject 132
def tree024_215 : CoverTree := CoverTree.reject 294
def tree024_216 : CoverTree := CoverTree.split [tree024_40,tree024_215,tree024_102,tree024_30,tree024_104,tree024_53]
def tree024_217 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_214,tree024_216,tree024_33,tree024_36]
def tree024_218 : CoverTree := CoverTree.split [tree024_4,tree024_4,tree024_203,tree024_213,tree024_217,tree024_120]
def tree024_219 : CoverTree := CoverTree.reject 166
def tree024_220 : CoverTree := CoverTree.reject 295
def tree024_221 : CoverTree := CoverTree.reject 236
def tree024_222 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_220,tree024_221,tree024_69]
def tree024_223 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_219,tree024_222,tree024_73,tree024_74]
def tree024_224 : CoverTree := CoverTree.reject 332
def tree024_225 : CoverTree := CoverTree.reject 296
def tree024_226 : CoverTree := CoverTree.reject 297
def tree024_227 : CoverTree := CoverTree.reject 117
def tree024_228 : CoverTree := CoverTree.split [tree024_99,tree024_227,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_229 : CoverTree := CoverTree.split [tree024_90,tree024_224,tree024_225,tree024_226,tree024_98,tree024_228]
def tree024_230 : CoverTree := CoverTree.reject 298
def tree024_231 : CoverTree := CoverTree.reject 299
def tree024_232 : CoverTree := CoverTree.split [tree024_40,tree024_230,tree024_231,tree024_30,tree024_81,tree024_53]
def tree024_233 : CoverTree := CoverTree.reject 266
def tree024_234 : CoverTree := CoverTree.split [tree024_27,tree024_233,tree024_84,tree024_30,tree024_81,tree024_18]
def tree024_235 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_229,tree024_232,tree024_234,tree024_88]
def tree024_236 : CoverTree := CoverTree.reject 267
def tree024_237 : CoverTree := CoverTree.split [tree024_90,tree024_94,tree024_96,tree024_236,tree024_98,tree024_100]
def tree024_238 : CoverTree := CoverTree.reject 300
def tree024_239 : CoverTree := CoverTree.split [tree024_40,tree024_238,tree024_102,tree024_30,tree024_104,tree024_53]
def tree024_240 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_237,tree024_239,tree024_33,tree024_36]
def tree024_241 : CoverTree := CoverTree.reject 333
def tree024_242 : CoverTree := CoverTree.reject 301
def tree024_243 : CoverTree := CoverTree.split [tree024_90,tree024_241,tree024_242,tree024_115,tree024_118,tree024_100]
def tree024_244 : CoverTree := CoverTree.split [tree024_38,tree024_38,tree024_243,tree024_54,tree024_60,tree024_36]
def tree024_245 : CoverTree := CoverTree.split [tree024_4,tree024_4,tree024_223,tree024_235,tree024_240,tree024_244]
def tree024_246 : CoverTree := CoverTree.split [tree024_123,tree024_135,tree024_165,tree024_197,tree024_218,tree024_245]
def tree024_247 : CoverTree := CoverTree.reject 28
def tree024_248 : CoverTree := CoverTree.reject 51
def tree024_249 : CoverTree := CoverTree.reject 137
def tree024_250 : CoverTree := CoverTree.reject 138
def tree024_251 : CoverTree := CoverTree.reject 13
def tree024_252 : CoverTree := CoverTree.reject 207
def tree024_253 : CoverTree := CoverTree.reject 193
def tree024_254 : CoverTree := CoverTree.reject 227
def tree024_255 : CoverTree := CoverTree.split [tree024_18,tree024_254,tree024_18,tree024_18,tree024_18,tree024_18]
def tree024_256 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_252,tree024_253,tree024_255]
def tree024_257 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_251,tree024_251,tree024_256]
def tree024_258 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_21,tree024_18,tree024_18]
def tree024_259 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_251,tree024_251,tree024_258]
def tree024_260 : CoverTree := CoverTree.reject 133
def tree024_261 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_260,tree024_130,tree024_133]
def tree024_262 : CoverTree := CoverTree.split [tree024_248,tree024_249,tree024_250,tree024_257,tree024_259,tree024_261]
def tree024_263 : CoverTree := CoverTree.reject 29
def tree024_264 : CoverTree := CoverTree.reject 64
def tree024_265 : CoverTree := CoverTree.reject 65
def tree024_266 : CoverTree := CoverTree.reject 148
def tree024_267 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_264,tree024_265,tree024_266]
def tree024_268 : CoverTree := CoverTree.reject 176
def tree024_269 : CoverTree := CoverTree.reject 237
def tree024_270 : CoverTree := CoverTree.reject 228
def tree024_271 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_270,tree024_18,tree024_18,tree024_18]
def tree024_272 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_269,tree024_271,tree024_69]
def tree024_273 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_137,tree024_268,tree024_272]
def tree024_274 : CoverTree := CoverTree.reject 119
def tree024_275 : CoverTree := CoverTree.reject 142
def tree024_276 : CoverTree := CoverTree.reject 143
def tree024_277 : CoverTree := CoverTree.reject 238
def tree024_278 : CoverTree := CoverTree.reject 239
def tree024_279 : CoverTree := CoverTree.split [tree024_27,tree024_275,tree024_276,tree024_277,tree024_278,tree024_18]
def tree024_280 : CoverTree := CoverTree.reject 240
def tree024_281 : CoverTree := CoverTree.reject 208
def tree024_282 : CoverTree := CoverTree.split [tree024_15,tree024_280,tree024_281,tree024_21,tree024_18,tree024_18]
def tree024_283 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_274,tree024_279,tree024_282]
def tree024_284 : CoverTree := CoverTree.reject 171
def tree024_285 : CoverTree := CoverTree.reject 229
def tree024_286 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_46,tree024_285,tree024_18,tree024_18]
def tree024_287 : CoverTree := CoverTree.split [tree024_40,tree024_284,tree024_286,tree024_30,tree024_104,tree024_53]
def tree024_288 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_287,tree024_149,tree024_154]
def tree024_289 : CoverTree := CoverTree.reject 19
def tree024_290 : CoverTree := CoverTree.reject 334
def tree024_291 : CoverTree := CoverTree.reject 302
def tree024_292 : CoverTree := CoverTree.split [tree024_90,tree024_290,tree024_291,tree024_115,tree024_118,tree024_100]
def tree024_293 : CoverTree := CoverTree.reject 303
def tree024_294 : CoverTree := CoverTree.split [tree024_40,tree024_293,tree024_47,tree024_49,tree024_51,tree024_53]
def tree024_295 : CoverTree := CoverTree.reject 209
def tree024_296 : CoverTree := CoverTree.split [tree024_15,tree024_295,tree024_19,tree024_21,tree024_18,tree024_18]
def tree024_297 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_292,tree024_294,tree024_60,tree024_296]
def tree024_298 : CoverTree := CoverTree.split [tree024_263,tree024_267,tree024_273,tree024_283,tree024_288,tree024_297]
def tree024_299 : CoverTree := CoverTree.reject 23
def tree024_300 : CoverTree := CoverTree.reject 72
def tree024_301 : CoverTree := CoverTree.reject 66
def tree024_302 : CoverTree := CoverTree.reject 160
def tree024_303 : CoverTree := CoverTree.reject 241
def tree024_304 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_303,tree024_69,tree024_69]
def tree024_305 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_300,tree024_301,tree024_302,tree024_304]
def tree024_306 : CoverTree := CoverTree.reject 177
def tree024_307 : CoverTree := CoverTree.reject 268
def tree024_308 : CoverTree := CoverTree.reject 242
def tree024_309 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_307,tree024_308,tree024_69]
def tree024_310 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_166,tree024_306,tree024_309,tree024_74]
def tree024_311 : CoverTree := CoverTree.reject 149
def tree024_312 : CoverTree := CoverTree.reject 120
def tree024_313 : CoverTree := CoverTree.reject 269
def tree024_314 : CoverTree := CoverTree.reject 270
def tree024_315 : CoverTree := CoverTree.split [tree024_27,tree024_313,tree024_314,tree024_30,tree024_81,tree024_18]
def tree024_316 : CoverTree := CoverTree.reject 243
def tree024_317 : CoverTree := CoverTree.split [tree024_15,tree024_316,tree024_19,tree024_21,tree024_18,tree024_18]
def tree024_318 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_311,tree024_312,tree024_315,tree024_317]
def tree024_319 : CoverTree := CoverTree.reject 179
def tree024_320 : CoverTree := CoverTree.split [tree024_90,tree024_319,tree024_96,tree024_97,tree024_98,tree024_100]
def tree024_321 : CoverTree := CoverTree.reject 172
def tree024_322 : CoverTree := CoverTree.split [tree024_40,tree024_321,tree024_102,tree024_30,tree024_104,tree024_53]
def tree024_323 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_320,tree024_322,tree024_33,tree024_36]
def tree024_324 : CoverTree := CoverTree.reject 55
def tree024_325 : CoverTree := CoverTree.reject 134
def tree024_326 : CoverTree := CoverTree.split [tree024_324,tree024_325,tree024_119,tree024_54,tree024_60,tree024_36]
def tree024_327 : CoverTree := CoverTree.split [tree024_299,tree024_305,tree024_310,tree024_318,tree024_323,tree024_326]
def tree024_328 : CoverTree := CoverTree.reject 39
def tree024_329 : CoverTree := CoverTree.reject 18
def tree024_330 : CoverTree := CoverTree.reject 67
def tree024_331 : CoverTree := CoverTree.reject 68
def tree024_332 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_328,tree024_329,tree024_330,tree024_331]
def tree024_333 : CoverTree := CoverTree.reject 73
def tree024_334 : CoverTree := CoverTree.reject 150
def tree024_335 : CoverTree := CoverTree.reject 161
def tree024_336 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_333,tree024_334,tree024_335,tree024_74]
def tree024_337 : CoverTree := CoverTree.reject 167
def tree024_338 : CoverTree := CoverTree.reject 304
def tree024_339 : CoverTree := CoverTree.reject 244
def tree024_340 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_338,tree024_339,tree024_69]
def tree024_341 : CoverTree := CoverTree.reject 271
def tree024_342 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_341,tree024_69,tree024_69]
def tree024_343 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_337,tree024_340,tree024_342,tree024_74]
def tree024_344 : CoverTree := CoverTree.reject 151
def tree024_345 : CoverTree := CoverTree.reject 305
def tree024_346 : CoverTree := CoverTree.reject 306
def tree024_347 : CoverTree := CoverTree.split [tree024_40,tree024_345,tree024_346,tree024_30,tree024_81,tree024_53]
def tree024_348 : CoverTree := CoverTree.reject 272
def tree024_349 : CoverTree := CoverTree.split [tree024_27,tree024_348,tree024_84,tree024_30,tree024_81,tree024_18]
def tree024_350 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_344,tree024_347,tree024_349,tree024_88]
def tree024_351 : CoverTree := CoverTree.reject 307
def tree024_352 : CoverTree := CoverTree.split [tree024_40,tree024_351,tree024_102,tree024_30,tree024_104,tree024_53]
def tree024_353 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_101,tree024_352,tree024_33,tree024_36]
def tree024_354 : CoverTree := CoverTree.reject 85
def tree024_355 : CoverTree := CoverTree.reject 79
def tree024_356 : CoverTree := CoverTree.reject 80
def tree024_357 : CoverTree := CoverTree.reject 31
def tree024_358 : CoverTree := CoverTree.reject 2
def tree024_359 : CoverTree := CoverTree.reject 169
def tree024_360 : CoverTree := CoverTree.reject 129
def tree024_361 : CoverTree := CoverTree.reject 170
def tree024_362 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_359,tree024_360,tree024_361]
def tree024_363 : CoverTree := CoverTree.reject 308
def tree024_364 : CoverTree := CoverTree.split [tree024_354,tree024_355,tree024_356,tree024_357,tree024_362,tree024_363]
def tree024_365 : CoverTree := CoverTree.reject 71
def tree024_366 : CoverTree := CoverTree.reject 335
def tree024_367 : CoverTree := CoverTree.reject 336
def tree024_368 : CoverTree := CoverTree.reject 154
def tree024_369 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_368,tree024_18,tree024_18]
def tree024_370 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_18,tree024_18,tree024_18]
def tree024_371 : CoverTree := CoverTree.split [tree024_365,tree024_366,tree024_367,tree024_369,tree024_370,tree024_370]
def tree024_372 : CoverTree := CoverTree.split [tree024_364,tree024_371,tree024_119,tree024_54,tree024_60,tree024_36]
def tree024_373 : CoverTree := CoverTree.split [tree024_332,tree024_336,tree024_343,tree024_350,tree024_353,tree024_372]
def tree024_374 : CoverTree := CoverTree.reject 126
def tree024_375 : CoverTree := CoverTree.reject 84
def tree024_376 : CoverTree := CoverTree.reject 69
def tree024_377 : CoverTree := CoverTree.reject 70
def tree024_378 : CoverTree := CoverTree.split [tree024_374,tree024_375,tree024_328,tree024_329,tree024_376,tree024_377]
def tree024_379 : CoverTree := CoverTree.reject 113
def tree024_380 : CoverTree := CoverTree.reject 285
def tree024_381 : CoverTree := CoverTree.reject 162
def tree024_382 : CoverTree := CoverTree.reject 309
def tree024_383 : CoverTree := CoverTree.reject 182
def tree024_384 : CoverTree := CoverTree.reject 183
def tree024_385 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_383,tree024_384,tree024_18,tree024_18]
def tree024_386 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_382,tree024_385,tree024_69]
def tree024_387 : CoverTree := CoverTree.reject 273
def tree024_388 : CoverTree := CoverTree.reject 141
def tree024_389 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_388,tree024_18,tree024_18,tree024_18]
def tree024_390 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_387,tree024_389,tree024_69]
def tree024_391 : CoverTree := CoverTree.split [tree024_379,tree024_380,tree024_381,tree024_386,tree024_390,tree024_74]
def tree024_392 : CoverTree := CoverTree.reject 114
def tree024_393 : CoverTree := CoverTree.reject 337
def tree024_394 : CoverTree := CoverTree.reject 338
def tree024_395 : CoverTree := CoverTree.reject 187
def tree024_396 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_395,tree024_18,tree024_18]
def tree024_397 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_393,tree024_394,tree024_396]
def tree024_398 : CoverTree := CoverTree.reject 310
def tree024_399 : CoverTree := CoverTree.reject 274
def tree024_400 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_398,tree024_399,tree024_69]
def tree024_401 : CoverTree := CoverTree.reject 311
def tree024_402 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_401,tree024_69,tree024_69]
def tree024_403 : CoverTree := CoverTree.split [tree024_392,tree024_397,tree024_400,tree024_402,tree024_73,tree024_74]
def tree024_404 : CoverTree := CoverTree.reject 56
def tree024_405 : CoverTree := CoverTree.reject 212
def tree024_406 : CoverTree := CoverTree.reject 339
def tree024_407 : CoverTree := CoverTree.reject 340
def tree024_408 : CoverTree := CoverTree.reject 312
def tree024_409 : CoverTree := CoverTree.split [tree024_365,tree024_405,tree024_406,tree024_407,tree024_408,tree024_370]
def tree024_410 : CoverTree := CoverTree.reject 341
def tree024_411 : CoverTree := CoverTree.reject 313
def tree024_412 : CoverTree := CoverTree.reject 314
def tree024_413 : CoverTree := CoverTree.split [tree024_90,tree024_410,tree024_411,tree024_412,tree024_98,tree024_228]
def tree024_414 : CoverTree := CoverTree.reject 315
def tree024_415 : CoverTree := CoverTree.split [tree024_40,tree024_414,tree024_79,tree024_30,tree024_81,tree024_53]
def tree024_416 : CoverTree := CoverTree.split [tree024_404,tree024_409,tree024_413,tree024_415,tree024_85,tree024_88]
def tree024_417 : CoverTree := CoverTree.reject 328
def tree024_418 : CoverTree := CoverTree.reject 213
def tree024_419 : CoverTree := CoverTree.reject 17
def tree024_420 : CoverTree := CoverTree.reject 107
def tree024_421 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_419,tree024_420,tree024_18]
def tree024_422 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_419,tree024_18,tree024_18]
def tree024_423 : CoverTree := CoverTree.split [tree024_365,tree024_418,tree024_421,tree024_422,tree024_422,tree024_370]
def tree024_424 : CoverTree := CoverTree.split [tree024_417,tree024_423,tree024_101,tree024_105,tree024_33,tree024_36]
def tree024_425 : CoverTree := CoverTree.reject 77
def tree024_426 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_425,tree024_18,tree024_18]
def tree024_427 : CoverTree := CoverTree.split [tree024_354,tree024_355,tree024_356,tree024_357,tree024_362,tree024_426]
def tree024_428 : CoverTree := CoverTree.reject 152
def tree024_429 : CoverTree := CoverTree.reject 106
def tree024_430 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_428,tree024_429,tree024_18]
def tree024_431 : CoverTree := CoverTree.reject 153
def tree024_432 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_431,tree024_420,tree024_18]
def tree024_433 : CoverTree := CoverTree.split [tree024_365,tree024_430,tree024_432,tree024_369,tree024_370,tree024_370]
def tree024_434 : CoverTree := CoverTree.split [tree024_427,tree024_433,tree024_119,tree024_54,tree024_60,tree024_36]
def tree024_435 : CoverTree := CoverTree.split [tree024_378,tree024_391,tree024_403,tree024_416,tree024_424,tree024_434]
def tree024_436 : CoverTree := CoverTree.split [tree024_247,tree024_262,tree024_298,tree024_327,tree024_373,tree024_435]
def tree024_437 : CoverTree := CoverTree.reject 21
def tree024_438 : CoverTree := CoverTree.reject 123
def tree024_439 : CoverTree := CoverTree.reject 35
def tree024_440 : CoverTree := CoverTree.reject 135
def tree024_441 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_439,tree024_440,tree024_74]
def tree024_442 : CoverTree := CoverTree.reject 192
def tree024_443 : CoverTree := CoverTree.reject 210
def tree024_444 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_443,tree024_18,tree024_255]
def tree024_445 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_439,tree024_442,tree024_444]
def tree024_446 : CoverTree := CoverTree.reject 105
def tree024_447 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_446,tree024_32,tree024_18]
def tree024_448 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_439,tree024_447,tree024_258]
def tree024_449 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_49,tree024_51,tree024_53]
def tree024_450 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_449,tree024_130,tree024_133]
def tree024_451 : CoverTree := CoverTree.split [tree024_248,tree024_438,tree024_441,tree024_445,tree024_448,tree024_450]
def tree024_452 : CoverTree := CoverTree.reject 245
def tree024_453 : CoverTree := CoverTree.reject 246
def tree024_454 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_452,tree024_453,tree024_69]
def tree024_455 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_264,tree024_265,tree024_454]
def tree024_456 : CoverTree := CoverTree.reject 127
def tree024_457 : CoverTree := CoverTree.reject 247
def tree024_458 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_456,tree024_457,tree024_69]
def tree024_459 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_69,tree024_271,tree024_69]
def tree024_460 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_137,tree024_458,tree024_459]
def tree024_461 : CoverTree := CoverTree.reject 121
def tree024_462 : CoverTree := CoverTree.split [tree024_27,tree024_275,tree024_276,tree024_30,tree024_81,tree024_18]
def tree024_463 : CoverTree := CoverTree.reject 248
def tree024_464 : CoverTree := CoverTree.reject 211
def tree024_465 : CoverTree := CoverTree.split [tree024_15,tree024_463,tree024_464,tree024_21,tree024_18,tree024_18]
def tree024_466 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_461,tree024_462,tree024_465]
def tree024_467 : CoverTree := CoverTree.reject 249
def tree024_468 : CoverTree := CoverTree.split [tree024_15,tree024_467,tree024_153,tree024_21,tree024_18,tree024_18]
def tree024_469 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_136,tree024_287,tree024_149,tree024_468]
def tree024_470 : CoverTree := CoverTree.reject 342
def tree024_471 : CoverTree := CoverTree.split [tree024_90,tree024_470,tree024_112,tree024_115,tree024_118,tree024_100]
def tree024_472 : CoverTree := CoverTree.reject 316
def tree024_473 : CoverTree := CoverTree.split [tree024_40,tree024_472,tree024_47,tree024_49,tree024_51,tree024_53]
def tree024_474 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_471,tree024_473,tree024_60,tree024_36]
def tree024_475 : CoverTree := CoverTree.split [tree024_263,tree024_455,tree024_460,tree024_466,tree024_469,tree024_474]
def tree024_476 : CoverTree := CoverTree.reject 275
def tree024_477 : CoverTree := CoverTree.reject 276
def tree024_478 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_476,tree024_477,tree024_69]
def tree024_479 : CoverTree := CoverTree.reject 250
def tree024_480 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_479,tree024_69,tree024_69]
def tree024_481 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_300,tree024_301,tree024_478,tree024_480]
def tree024_482 : CoverTree := CoverTree.reject 178
def tree024_483 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_166,tree024_482,tree024_73,tree024_74]
def tree024_484 : CoverTree := CoverTree.reject 188
def tree024_485 : CoverTree := CoverTree.reject 189
def tree024_486 : CoverTree := CoverTree.split [tree024_90,tree024_319,tree024_484,tree024_485,tree024_98,tree024_228]
def tree024_487 : CoverTree := CoverTree.reject 190
def tree024_488 : CoverTree := CoverTree.reject 191
def tree024_489 : CoverTree := CoverTree.split [tree024_40,tree024_487,tree024_488,tree024_30,tree024_81,tree024_53]
def tree024_490 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_486,tree024_489,tree024_85,tree024_88]
def tree024_491 : CoverTree := CoverTree.reject 255
def tree024_492 : CoverTree := CoverTree.reject 256
def tree024_493 : CoverTree := CoverTree.split [tree024_365,tree024_491,tree024_492,tree024_369,tree024_370,tree024_370]
def tree024_494 : CoverTree := CoverTree.split [tree024_324,tree024_493,tree024_119,tree024_54,tree024_60,tree024_36]
def tree024_495 : CoverTree := CoverTree.split [tree024_299,tree024_481,tree024_483,tree024_490,tree024_323,tree024_494]
def tree024_496 : CoverTree := CoverTree.reject 317
def tree024_497 : CoverTree := CoverTree.reject 318
def tree024_498 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_496,tree024_497,tree024_69]
def tree024_499 : CoverTree := CoverTree.reject 277
def tree024_500 : CoverTree := CoverTree.reject 278
def tree024_501 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_499,tree024_500,tree024_69]
def tree024_502 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_333,tree024_498,tree024_501,tree024_74]
def tree024_503 : CoverTree := CoverTree.reject 168
def tree024_504 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_503,tree024_70,tree024_73,tree024_74]
def tree024_505 : CoverTree := CoverTree.reject 257
def tree024_506 : CoverTree := CoverTree.reject 319
def tree024_507 : CoverTree := CoverTree.reject 125
def tree024_508 : CoverTree := CoverTree.split [tree024_24,tree024_24,tree024_91,tree024_507,tree024_18,tree024_18]
def tree024_509 : CoverTree := CoverTree.split [tree024_90,tree024_505,tree024_506,tree024_508,tree024_98,tree024_228]
def tree024_510 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_509,tree024_82,tree024_85,tree024_88]
def tree024_511 : CoverTree := CoverTree.split [tree024_6,tree024_6,tree024_101,tree024_105,tree024_33,tree024_36]
def tree024_512 : CoverTree := CoverTree.split [tree024_332,tree024_502,tree024_504,tree024_510,tree024_511,tree024_434]
def tree024_513 : CoverTree := CoverTree.reject 286
def tree024_514 : CoverTree := CoverTree.reject 343
def tree024_515 : CoverTree := CoverTree.reject 320
def tree024_516 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_514,tree024_515,tree024_69]
def tree024_517 : CoverTree := CoverTree.reject 321
def tree024_518 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_517,tree024_385,tree024_69]
def tree024_519 : CoverTree := CoverTree.reject 140
def tree024_520 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_519,tree024_18,tree024_18,tree024_18]
def tree024_521 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_520,tree024_389,tree024_69]
def tree024_522 : CoverTree := CoverTree.split [tree024_379,tree024_513,tree024_516,tree024_518,tree024_521,tree024_74]
def tree024_523 : CoverTree := CoverTree.reject 61
def tree024_524 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_419,tree024_523,tree024_18]
def tree024_525 : CoverTree := CoverTree.reject 344
def tree024_526 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_524,tree024_525,tree024_396]
def tree024_527 : CoverTree := CoverTree.reject 155
def tree024_528 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_91,tree024_527,tree024_18,tree024_18]
def tree024_529 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_91,tree024_18,tree024_18,tree024_18]
def tree024_530 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_528,tree024_529,tree024_69]
def tree024_531 : CoverTree := CoverTree.split [tree024_392,tree024_526,tree024_530,tree024_70,tree024_73,tree024_74]
def tree024_532 : CoverTree := CoverTree.reject 345
def tree024_533 : CoverTree := CoverTree.reject 346
def tree024_534 : CoverTree := CoverTree.split [tree024_365,tree024_405,tree024_532,tree024_533,tree024_422,tree024_370]
def tree024_535 : CoverTree := CoverTree.reject 347
def tree024_536 : CoverTree := CoverTree.split [tree024_90,tree024_535,tree024_96,tree024_508,tree024_98,tree024_228]
def tree024_537 : CoverTree := CoverTree.reject 322
def tree024_538 : CoverTree := CoverTree.split [tree024_40,tree024_537,tree024_79,tree024_30,tree024_81,tree024_53]
def tree024_539 : CoverTree := CoverTree.split [tree024_404,tree024_534,tree024_536,tree024_538,tree024_85,tree024_88]
def tree024_540 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_419,tree024_360,tree024_18]
def tree024_541 : CoverTree := CoverTree.reject 173
def tree024_542 : CoverTree := CoverTree.split [tree024_354,tree024_355,tree024_356,tree024_357,tree024_540,tree024_541]
def tree024_543 : CoverTree := CoverTree.split [tree024_542,tree024_423,tree024_101,tree024_105,tree024_33,tree024_36]
def tree024_544 : CoverTree := CoverTree.split [tree024_378,tree024_522,tree024_531,tree024_539,tree024_543,tree024_434]
def tree024_545 : CoverTree := CoverTree.split [tree024_437,tree024_451,tree024_475,tree024_495,tree024_512,tree024_544]
def tree024_546 : CoverTree := CoverTree.reject 78
def tree024_547 : CoverTree := CoverTree.reject 75
def tree024_548 : CoverTree := CoverTree.reject 76
def tree024_549 : CoverTree := CoverTree.reject 62
def tree024_550 : CoverTree := CoverTree.reject 81
def tree024_551 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_439,tree024_550,tree024_258]
def tree024_552 : CoverTree := CoverTree.reject 82
def tree024_553 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_552,tree024_130,tree024_258]
def tree024_554 : CoverTree := CoverTree.split [tree024_546,tree024_547,tree024_548,tree024_549,tree024_551,tree024_553]
def tree024_555 : CoverTree := CoverTree.reject 124
def tree024_556 : CoverTree := CoverTree.reject 251
def tree024_557 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_556,tree024_69,tree024_69]
def tree024_558 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_439,tree024_440,tree024_557]
def tree024_559 : CoverTree := CoverTree.reject 8
def tree024_560 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_559,tree024_559,tree024_18]
def tree024_561 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_21,tree024_18,tree024_255]
def tree024_562 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_439,tree024_560,tree024_561]
def tree024_563 : CoverTree := CoverTree.split [tree024_248,tree024_555,tree024_558,tree024_562,tree024_448,tree024_450]
def tree024_564 : CoverTree := CoverTree.reject 252
def tree024_565 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_564,tree024_69,tree024_69]
def tree024_566 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_136,tree024_264,tree024_265,tree024_565]
def tree024_567 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_456,tree024_69,tree024_69]
def tree024_568 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_136,tree024_137,tree024_567,tree024_459]
def tree024_569 : CoverTree := CoverTree.reject 224
def tree024_570 : CoverTree := CoverTree.reject 225
def tree024_571 : CoverTree := CoverTree.split [tree024_40,tree024_569,tree024_570,tree024_30,tree024_81,tree024_53]
def tree024_572 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_136,tree024_571,tree024_462,tree024_88]
def tree024_573 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_136,tree024_287,tree024_149,tree024_154]
def tree024_574 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_119,tree024_54,tree024_60,tree024_36]
def tree024_575 : CoverTree := CoverTree.split [tree024_263,tree024_566,tree024_568,tree024_572,tree024_573,tree024_574]
def tree024_576 : CoverTree := CoverTree.reject 27
def tree024_577 : CoverTree := CoverTree.reject 279
def tree024_578 : CoverTree := CoverTree.reject 280
def tree024_579 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_577,tree024_578,tree024_69]
def tree024_580 : CoverTree := CoverTree.split [tree024_576,tree024_576,tree024_300,tree024_301,tree024_579,tree024_74]
def tree024_581 : CoverTree := CoverTree.reject 110
def tree024_582 : CoverTree := CoverTree.reject 287
def tree024_583 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_582,tree024_18,tree024_18,tree024_18]
def tree024_584 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_581,tree024_583,tree024_69]
def tree024_585 : CoverTree := CoverTree.split [tree024_576,tree024_576,tree024_166,tree024_584,tree024_73,tree024_74]
def tree024_586 : CoverTree := CoverTree.split [tree024_576,tree024_576,tree024_486,tree024_489,tree024_85,tree024_88]
def tree024_587 : CoverTree := CoverTree.reject 220
def tree024_588 : CoverTree := CoverTree.reject 258
def tree024_589 : CoverTree := CoverTree.split [tree024_587,tree024_588,tree024_320,tree024_322,tree024_33,tree024_36]
def tree024_590 : CoverTree := CoverTree.split [tree024_299,tree024_580,tree024_585,tree024_586,tree024_589,tree024_494]
def tree024_591 : CoverTree := CoverTree.split [tree024_576,tree024_576,tree024_328,tree024_329,tree024_330,tree024_331]
def tree024_592 : CoverTree := CoverTree.reject 323
def tree024_593 : CoverTree := CoverTree.reject 324
def tree024_594 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_592,tree024_593,tree024_69]
def tree024_595 : CoverTree := CoverTree.reject 281
def tree024_596 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_595,tree024_389,tree024_69]
def tree024_597 : CoverTree := CoverTree.split [tree024_576,tree024_576,tree024_333,tree024_594,tree024_596,tree024_74]
def tree024_598 : CoverTree := CoverTree.reject 325
def tree024_599 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_598,tree024_529,tree024_69]
def tree024_600 : CoverTree := CoverTree.split [tree024_576,tree024_576,tree024_599,tree024_70,tree024_73,tree024_74]
def tree024_601 : CoverTree := CoverTree.reject 326
def tree024_602 : CoverTree := CoverTree.split [tree024_90,tree024_505,tree024_601,tree024_508,tree024_98,tree024_228]
def tree024_603 : CoverTree := CoverTree.split [tree024_576,tree024_576,tree024_602,tree024_82,tree024_85,tree024_88]
def tree024_604 : CoverTree := CoverTree.reject 185
def tree024_605 : CoverTree := CoverTree.reject 42
def tree024_606 : CoverTree := CoverTree.split [tree024_605,tree024_605,tree024_605,tree024_422,tree024_422,tree024_370]
def tree024_607 : CoverTree := CoverTree.split [tree024_604,tree024_606,tree024_101,tree024_105,tree024_33,tree024_36]
def tree024_608 : CoverTree := CoverTree.split [tree024_591,tree024_597,tree024_600,tree024_603,tree024_607,tree024_434]
def tree024_609 : CoverTree := CoverTree.reject 194
def tree024_610 : CoverTree := CoverTree.reject 195
def tree024_611 : CoverTree := CoverTree.reject 186
def tree024_612 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_611,tree024_18,tree024_18]
def tree024_613 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_609,tree024_610,tree024_612]
def tree024_614 : CoverTree := CoverTree.reject 348
def tree024_615 : CoverTree := CoverTree.reject 184
def tree024_616 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_91,tree024_615,tree024_18,tree024_18]
def tree024_617 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_614,tree024_616,tree024_69]
def tree024_618 : CoverTree := CoverTree.reject 180
def tree024_619 : CoverTree := CoverTree.reject 181
def tree024_620 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_618,tree024_619,tree024_18,tree024_18]
def tree024_621 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_620,tree024_385,tree024_69]
def tree024_622 : CoverTree := CoverTree.split [tree024_379,tree024_613,tree024_617,tree024_621,tree024_521,tree024_74]
def tree024_623 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_524,tree024_524,tree024_396]
def tree024_624 : CoverTree := CoverTree.split [tree024_392,tree024_623,tree024_530,tree024_70,tree024_73,tree024_74]
def tree024_625 : CoverTree := CoverTree.reject 349
def tree024_626 : CoverTree := CoverTree.reject 197
def tree024_627 : CoverTree := CoverTree.split [tree024_358,tree024_358,tree024_358,tree024_419,tree024_626,tree024_18]
def tree024_628 : CoverTree := CoverTree.split [tree024_365,tree024_405,tree024_625,tree024_627,tree024_422,tree024_370]
def tree024_629 : CoverTree := CoverTree.split [tree024_90,tree024_94,tree024_96,tree024_508,tree024_98,tree024_228]
def tree024_630 : CoverTree := CoverTree.split [tree024_404,tree024_628,tree024_629,tree024_82,tree024_85,tree024_88]
def tree024_631 : CoverTree := CoverTree.split [tree024_378,tree024_622,tree024_624,tree024_630,tree024_543,tree024_434]
def tree024_632 : CoverTree := CoverTree.split [tree024_554,tree024_563,tree024_575,tree024_590,tree024_608,tree024_631]
def tree024_633 : CoverTree := CoverTree.reject 163
def tree024_634 : CoverTree := CoverTree.reject 122
def tree024_635 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_633,tree024_550,tree024_634]
def tree024_636 : CoverTree := CoverTree.split [tree024_546,tree024_547,tree024_548,tree024_549,tree024_635,tree024_553]
def tree024_637 : CoverTree := CoverTree.reject 214
def tree024_638 : CoverTree := CoverTree.reject 215
def tree024_639 : CoverTree := CoverTree.reject 222
def tree024_640 : CoverTree := CoverTree.reject 329
def tree024_641 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_640,tree024_18,tree024_18,tree024_18]
def tree024_642 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_639,tree024_641,tree024_69]
def tree024_643 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_637,tree024_638,tree024_642]
def tree024_644 : CoverTree := CoverTree.reject 216
def tree024_645 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_644,tree024_440,tree024_74]
def tree024_646 : CoverTree := CoverTree.reject 196
def tree024_647 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_646,tree024_560,tree024_561]
def tree024_648 : CoverTree := CoverTree.reject 223
def tree024_649 : CoverTree := CoverTree.split [tree024_129,tree024_129,tree024_129,tree024_446,tree024_648,tree024_53]
def tree024_650 : CoverTree := CoverTree.split [tree024_127,tree024_127,tree024_127,tree024_649,tree024_447,tree024_258]
def tree024_651 : CoverTree := CoverTree.split [tree024_248,tree024_643,tree024_645,tree024_647,tree024_650,tree024_450]
def tree024_652 : CoverTree := CoverTree.reject 217
def tree024_653 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_652,tree024_264,tree024_265,tree024_74]
def tree024_654 : CoverTree := CoverTree.reject 218
def tree024_655 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_654,tree024_137,tree024_567,tree024_459]
def tree024_656 : CoverTree := CoverTree.reject 219
def tree024_657 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_656,tree024_571,tree024_462,tree024_88]
def tree024_658 : CoverTree := CoverTree.reject 9
def tree024_659 : CoverTree := CoverTree.split [tree024_658,tree024_658,tree024_658,tree024_658,tree024_658,tree024_100]
def tree024_660 : CoverTree := CoverTree.split [tree024_289,tree024_289,tree024_659,tree024_287,tree024_149,tree024_154]
def tree024_661 : CoverTree := CoverTree.split [tree024_263,tree024_653,tree024_655,tree024_657,tree024_660,tree024_574]
def tree024_662 : CoverTree := CoverTree.reject 282
def tree024_663 : CoverTree := CoverTree.split [tree024_379,tree024_662,tree024_300,tree024_301,tree024_521,tree024_74]
def tree024_664 : CoverTree := CoverTree.reject 283
def tree024_665 : CoverTree := CoverTree.split [tree024_392,tree024_664,tree024_166,tree024_584,tree024_73,tree024_74]
def tree024_666 : CoverTree := CoverTree.reject 253
def tree024_667 : CoverTree := CoverTree.split [tree024_404,tree024_666,tree024_486,tree024_489,tree024_85,tree024_88]
def tree024_668 : CoverTree := CoverTree.reject 88
def tree024_669 : CoverTree := CoverTree.split [tree024_605,tree024_605,tree024_605,tree024_668,tree024_668,tree024_370]
def tree024_670 : CoverTree := CoverTree.split [tree024_587,tree024_669,tree024_320,tree024_322,tree024_33,tree024_36]
def tree024_671 : CoverTree := CoverTree.split [tree024_299,tree024_663,tree024_665,tree024_667,tree024_670,tree024_494]
def tree024_672 : CoverTree := CoverTree.split [tree024_374,tree024_375,tree024_328,tree024_329,tree024_330,tree024_331]
def tree024_673 : CoverTree := CoverTree.reject 284
def tree024_674 : CoverTree := CoverTree.split [tree024_379,tree024_673,tree024_333,tree024_621,tree024_521,tree024_74]
def tree024_675 : CoverTree := CoverTree.reject 221
def tree024_676 : CoverTree := CoverTree.split [tree024_392,tree024_675,tree024_530,tree024_70,tree024_73,tree024_74]
def tree024_677 : CoverTree := CoverTree.reject 327
def tree024_678 : CoverTree := CoverTree.split [tree024_605,tree024_605,tree024_605,tree024_677,tree024_422,tree024_370]
def tree024_679 : CoverTree := CoverTree.split [tree024_90,tree024_505,tree024_96,tree024_508,tree024_98,tree024_228]
def tree024_680 : CoverTree := CoverTree.split [tree024_404,tree024_678,tree024_679,tree024_82,tree024_85,tree024_88]
def tree024_681 : CoverTree := CoverTree.split [tree024_672,tree024_674,tree024_676,tree024_680,tree024_607,tree024_434]
def tree024_682 : CoverTree := CoverTree.reject 254
def tree024_683 : CoverTree := CoverTree.split [tree024_65,tree024_65,tree024_91,tree024_615,tree024_682,tree024_18]
def tree024_684 : CoverTree := CoverTree.split [tree024_64,tree024_64,tree024_64,tree024_683,tree024_616,tree024_69]
def tree024_685 : CoverTree := CoverTree.split [tree024_379,tree024_613,tree024_684,tree024_621,tree024_521,tree024_74]
def tree024_686 : CoverTree := CoverTree.split [tree024_365,tree024_405,tree024_421,tree024_627,tree024_422,tree024_370]
def tree024_687 : CoverTree := CoverTree.split [tree024_404,tree024_686,tree024_629,tree024_82,tree024_85,tree024_88]
def tree024_688 : CoverTree := CoverTree.split [tree024_378,tree024_685,tree024_624,tree024_687,tree024_543,tree024_434]
def tree024_689 : CoverTree := CoverTree.split [tree024_636,tree024_651,tree024_661,tree024_671,tree024_681,tree024_688]
def tree024_690 : CoverTree := CoverTree.split [tree024_122,tree024_246,tree024_436,tree024_545,tree024_632,tree024_689]
def tree024 : CoverTree := tree024_690

end Snake9.Shared89
