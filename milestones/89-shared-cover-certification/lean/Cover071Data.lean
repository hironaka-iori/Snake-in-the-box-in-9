import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes071 : List Box := [
[(1,6),(1,6),(1,3),(1,6),(1,3),(1,6)],
[(1,6),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)],
[(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,6),(1,6),(1,2)],
[(1,6),(1,6),(1,5),(1,5),(1,4),(1,2)],
[(1,2),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,3),(1,6)],
[(1,2),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,2),(1,4),(1,5),(1,5),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,5),(1,3),(1,5),(1,3)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,6),(1,5),(1,2),(1,5),(1,4)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,5),(1,5),(1,2),(1,3),(1,6)],
[(1,6),(1,2),(1,6),(1,3),(1,6),(1,6)],
[(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,2)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(6,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(6,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(3,3)],
[(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(5,5)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(4,4)],
[(1,6),(1,6),(1,6),(3,3),(6,6),(1,1)],
[(1,6),(4,4),(6,6),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(5,5),(1,1)],
[(1,6),(1,6),(1,3),(1,2),(1,5),(1,5)],
[(1,3),(1,2),(1,5),(1,5),(1,6),(1,6)],
[(1,6),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(5,5),(1,1)],
[(1,4),(1,5),(1,5),(1,2),(1,6),(1,6)],
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
[(1,6),(1,3),(1,5),(1,3),(1,5),(1,6)],
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
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(4,4),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(3,3)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(2,2)],
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
[(1,6),(1,2),(1,5),(1,5),(1,4),(1,6)],
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

def root071 : Nat := 3504

def tree071_0 : CoverTree := CoverTree.reject 1
def tree071_1 : CoverTree := CoverTree.reject 20
def tree071_2 : CoverTree := CoverTree.reject 13
def tree071_3 : CoverTree := CoverTree.reject 11
def tree071_4 : CoverTree := CoverTree.reject 8
def tree071_5 : CoverTree := CoverTree.reject 77
def tree071_6 : CoverTree := CoverTree.reject 6
def tree071_7 : CoverTree := CoverTree.reject 29
def tree071_8 : CoverTree := CoverTree.reject 98
def tree071_9 : CoverTree := CoverTree.reject 33
def tree071_10 : CoverTree := CoverTree.reject 34
def tree071_11 : CoverTree := CoverTree.reject 24
def tree071_12 : CoverTree := CoverTree.reject 15
def tree071_13 : CoverTree := CoverTree.reject 41
def tree071_14 : CoverTree := CoverTree.reject 42
def tree071_15 : CoverTree := CoverTree.split [tree071_9,tree071_10,tree071_11,tree071_12,tree071_13,tree071_14]
def tree071_16 : CoverTree := CoverTree.reject 209
def tree071_17 : CoverTree := CoverTree.reject 26
def tree071_18 : CoverTree := CoverTree.accept
def tree071_19 : CoverTree := CoverTree.split [tree071_17,tree071_18,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_20 : CoverTree := CoverTree.reject 21
def tree071_21 : CoverTree := CoverTree.split [tree071_20,tree071_18,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_22 : CoverTree := CoverTree.split [tree071_15,tree071_16,tree071_19,tree071_21,tree071_18,tree071_18]
def tree071_23 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_7,tree071_7,tree071_8,tree071_22]
def tree071_24 : CoverTree := CoverTree.reject 5
def tree071_25 : CoverTree := CoverTree.reject 38
def tree071_26 : CoverTree := CoverTree.reject 39
def tree071_27 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_11,tree071_12,tree071_25,tree071_26]
def tree071_28 : CoverTree := CoverTree.reject 40
def tree071_29 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_28,tree071_18,tree071_18,tree071_18]
def tree071_30 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_31 : CoverTree := CoverTree.reject 53
def tree071_32 : CoverTree := CoverTree.split [tree071_31,tree071_18,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_33 : CoverTree := CoverTree.split [tree071_27,tree071_29,tree071_30,tree071_30,tree071_32,tree071_18]
def tree071_34 : CoverTree := CoverTree.reject 25
def tree071_35 : CoverTree := CoverTree.split [tree071_34,tree071_18,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_36 : CoverTree := CoverTree.split [tree071_15,tree071_35,tree071_19,tree071_21,tree071_18,tree071_18]
def tree071_37 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_7,tree071_7,tree071_33,tree071_36]
def tree071_38 : CoverTree := CoverTree.reject 78
def tree071_39 : CoverTree := CoverTree.reject 16
def tree071_40 : CoverTree := CoverTree.reject 80
def tree071_41 : CoverTree := CoverTree.reject 43
def tree071_42 : CoverTree := CoverTree.reject 44
def tree071_43 : CoverTree := CoverTree.split [tree071_34,tree071_40,tree071_41,tree071_42,tree071_18,tree071_18]
def tree071_44 : CoverTree := CoverTree.reject 81
def tree071_45 : CoverTree := CoverTree.reject 45
def tree071_46 : CoverTree := CoverTree.split [tree071_17,tree071_44,tree071_45,tree071_18,tree071_18,tree071_18]
def tree071_47 : CoverTree := CoverTree.reject 74
def tree071_48 : CoverTree := CoverTree.split [tree071_20,tree071_47,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_49 : CoverTree := CoverTree.reject 57
def tree071_50 : CoverTree := CoverTree.split [tree071_49,tree071_18,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_51 : CoverTree := CoverTree.reject 37
def tree071_52 : CoverTree := CoverTree.split [tree071_51,tree071_18,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_53 : CoverTree := CoverTree.split [tree071_39,tree071_43,tree071_46,tree071_48,tree071_50,tree071_52]
def tree071_54 : CoverTree := CoverTree.split [tree071_9,tree071_10,tree071_11,tree071_12,tree071_25,tree071_26]
def tree071_55 : CoverTree := CoverTree.reject 82
def tree071_56 : CoverTree := CoverTree.split [tree071_34,tree071_55,tree071_28,tree071_18,tree071_18,tree071_18]
def tree071_57 : CoverTree := CoverTree.reject 83
def tree071_58 : CoverTree := CoverTree.split [tree071_17,tree071_57,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_59 : CoverTree := CoverTree.split [tree071_54,tree071_56,tree071_58,tree071_21,tree071_32,tree071_18]
def tree071_60 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_38,tree071_53,tree071_59,tree071_36]
def tree071_61 : CoverTree := CoverTree.split [tree071_4,tree071_4,tree071_5,tree071_23,tree071_37,tree071_60]
def tree071_62 : CoverTree := CoverTree.reject 150
def tree071_63 : CoverTree := CoverTree.reject 0
def tree071_64 : CoverTree := CoverTree.reject 4
def tree071_65 : CoverTree := CoverTree.reject 145
def tree071_66 : CoverTree := CoverTree.reject 146
def tree071_67 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_65,tree071_66,tree071_18,tree071_18]
def tree071_68 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_69 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_67,tree071_68,tree071_68]
def tree071_70 : CoverTree := CoverTree.reject 94
def tree071_71 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_70,tree071_18,tree071_18,tree071_18]
def tree071_72 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_71,tree071_68,tree071_68]
def tree071_73 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_68,tree071_68,tree071_68]
def tree071_74 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_62,tree071_69,tree071_72,tree071_73]
def tree071_75 : CoverTree := CoverTree.reject 126
def tree071_76 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_41,tree071_42,tree071_18,tree071_18]
def tree071_77 : CoverTree := CoverTree.reject 99
def tree071_78 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_45,tree071_77,tree071_18,tree071_18]
def tree071_79 : CoverTree := CoverTree.reject 35
def tree071_80 : CoverTree := CoverTree.split [tree071_79,tree071_79,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_81 : CoverTree := CoverTree.split [tree071_39,tree071_76,tree071_78,tree071_30,tree071_80,tree071_52]
def tree071_82 : CoverTree := CoverTree.reject 84
def tree071_83 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_82,tree071_18,tree071_18,tree071_18]
def tree071_84 : CoverTree := CoverTree.split [tree071_27,tree071_29,tree071_83,tree071_30,tree071_80,tree071_18]
def tree071_85 : CoverTree := CoverTree.reject 85
def tree071_86 : CoverTree := CoverTree.split [tree071_34,tree071_85,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_87 : CoverTree := CoverTree.split [tree071_15,tree071_86,tree071_19,tree071_21,tree071_18,tree071_18]
def tree071_88 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_75,tree071_81,tree071_84,tree071_87]
def tree071_89 : CoverTree := CoverTree.reject 19
def tree071_90 : CoverTree := CoverTree.reject 14
def tree071_91 : CoverTree := CoverTree.reject 47
def tree071_92 : CoverTree := CoverTree.reject 48
def tree071_93 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_90,tree071_91,tree071_92,tree071_18]
def tree071_94 : CoverTree := CoverTree.reject 49
def tree071_95 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_90,tree071_94,tree071_18,tree071_18]
def tree071_96 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_90,tree071_18,tree071_18,tree071_18]
def tree071_97 : CoverTree := CoverTree.split [tree071_90,tree071_90,tree071_90,tree071_18,tree071_18,tree071_18]
def tree071_98 : CoverTree := CoverTree.reject 50
def tree071_99 : CoverTree := CoverTree.split [tree071_98,tree071_18,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_100 : CoverTree := CoverTree.split [tree071_89,tree071_93,tree071_95,tree071_96,tree071_97,tree071_99]
def tree071_101 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_45,tree071_18,tree071_18,tree071_18]
def tree071_102 : CoverTree := CoverTree.reject 95
def tree071_103 : CoverTree := CoverTree.split [tree071_49,tree071_102,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_104 : CoverTree := CoverTree.split [tree071_39,tree071_76,tree071_101,tree071_30,tree071_103,tree071_52]
def tree071_105 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_100,tree071_104,tree071_33,tree071_36]
def tree071_106 : CoverTree := CoverTree.reject 86
def tree071_107 : CoverTree := CoverTree.reject 87
def tree071_108 : CoverTree := CoverTree.split [tree071_34,tree071_106,tree071_107,tree071_91,tree071_92,tree071_18]
def tree071_109 : CoverTree := CoverTree.reject 88
def tree071_110 : CoverTree := CoverTree.reject 89
def tree071_111 : CoverTree := CoverTree.split [tree071_17,tree071_109,tree071_110,tree071_94,tree071_18,tree071_18]
def tree071_112 : CoverTree := CoverTree.reject 90
def tree071_113 : CoverTree := CoverTree.reject 91
def tree071_114 : CoverTree := CoverTree.split [tree071_20,tree071_112,tree071_113,tree071_18,tree071_18,tree071_18]
def tree071_115 : CoverTree := CoverTree.reject 92
def tree071_116 : CoverTree := CoverTree.reject 93
def tree071_117 : CoverTree := CoverTree.split [tree071_115,tree071_116,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_118 : CoverTree := CoverTree.split [tree071_89,tree071_108,tree071_111,tree071_114,tree071_117,tree071_99]
def tree071_119 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_118,tree071_53,tree071_59,tree071_36]
def tree071_120 : CoverTree := CoverTree.split [tree071_4,tree071_4,tree071_74,tree071_88,tree071_105,tree071_119]
def tree071_121 : CoverTree := CoverTree.split [tree071_0,tree071_1,tree071_2,tree071_3,tree071_61,tree071_120]
def tree071_122 : CoverTree := CoverTree.reject 124
def tree071_123 : CoverTree := CoverTree.reject 105
def tree071_124 : CoverTree := CoverTree.reject 106
def tree071_125 : CoverTree := CoverTree.reject 28
def tree071_126 : CoverTree := CoverTree.reject 118
def tree071_127 : CoverTree := CoverTree.reject 7
def tree071_128 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_21,tree071_32,tree071_18]
def tree071_129 : CoverTree := CoverTree.reject 184
def tree071_130 : CoverTree := CoverTree.split [tree071_20,tree071_129,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_131 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_130,tree071_18,tree071_18]
def tree071_132 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_125,tree071_126,tree071_128,tree071_131]
def tree071_133 : CoverTree := CoverTree.split [tree071_4,tree071_4,tree071_122,tree071_123,tree071_124,tree071_132]
def tree071_134 : CoverTree := CoverTree.reject 3
def tree071_135 : CoverTree := CoverTree.reject 46
def tree071_136 : CoverTree := CoverTree.reject 160
def tree071_137 : CoverTree := CoverTree.reject 131
def tree071_138 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_135,tree071_136,tree071_137]
def tree071_139 : CoverTree := CoverTree.reject 69
def tree071_140 : CoverTree := CoverTree.reject 101
def tree071_141 : CoverTree := CoverTree.reject 213
def tree071_142 : CoverTree := CoverTree.reject 187
def tree071_143 : CoverTree := CoverTree.reject 188
def tree071_144 : CoverTree := CoverTree.split [tree071_15,tree071_141,tree071_142,tree071_143,tree071_18,tree071_18]
def tree071_145 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_139,tree071_140,tree071_144]
def tree071_146 : CoverTree := CoverTree.reject 116
def tree071_147 : CoverTree := CoverTree.split [tree071_27,tree071_146,tree071_30,tree071_30,tree071_32,tree071_18]
def tree071_148 : CoverTree := CoverTree.reject 185
def tree071_149 : CoverTree := CoverTree.split [tree071_34,tree071_148,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_150 : CoverTree := CoverTree.reject 186
def tree071_151 : CoverTree := CoverTree.split [tree071_17,tree071_18,tree071_150,tree071_18,tree071_18,tree071_18]
def tree071_152 : CoverTree := CoverTree.split [tree071_15,tree071_149,tree071_151,tree071_21,tree071_18,tree071_18]
def tree071_153 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_139,tree071_147,tree071_152]
def tree071_154 : CoverTree := CoverTree.reject 312
def tree071_155 : CoverTree := CoverTree.reject 271
def tree071_156 : CoverTree := CoverTree.reject 242
def tree071_157 : CoverTree := CoverTree.split [tree071_89,tree071_154,tree071_155,tree071_156,tree071_117,tree071_99]
def tree071_158 : CoverTree := CoverTree.reject 272
def tree071_159 : CoverTree := CoverTree.split [tree071_39,tree071_158,tree071_46,tree071_48,tree071_50,tree071_52]
def tree071_160 : CoverTree := CoverTree.reject 189
def tree071_161 : CoverTree := CoverTree.split [tree071_15,tree071_160,tree071_19,tree071_21,tree071_18,tree071_18]
def tree071_162 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_157,tree071_159,tree071_59,tree071_161]
def tree071_163 : CoverTree := CoverTree.split [tree071_4,tree071_4,tree071_138,tree071_145,tree071_153,tree071_162]
def tree071_164 : CoverTree := CoverTree.reject 56
def tree071_165 : CoverTree := CoverTree.reject 161
def tree071_166 : CoverTree := CoverTree.reject 143
def tree071_167 : CoverTree := CoverTree.reject 214
def tree071_168 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_167,tree071_68,tree071_68]
def tree071_169 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_164,tree071_165,tree071_166,tree071_168]
def tree071_170 : CoverTree := CoverTree.reject 132
def tree071_171 : CoverTree := CoverTree.reject 108
def tree071_172 : CoverTree := CoverTree.reject 243
def tree071_173 : CoverTree := CoverTree.reject 244
def tree071_174 : CoverTree := CoverTree.split [tree071_27,tree071_172,tree071_173,tree071_30,tree071_80,tree071_18]
def tree071_175 : CoverTree := CoverTree.reject 215
def tree071_176 : CoverTree := CoverTree.reject 190
def tree071_177 : CoverTree := CoverTree.reject 191
def tree071_178 : CoverTree := CoverTree.split [tree071_15,tree071_175,tree071_176,tree071_177,tree071_18,tree071_18]
def tree071_179 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_170,tree071_171,tree071_174,tree071_178]
def tree071_180 : CoverTree := CoverTree.reject 119
def tree071_181 : CoverTree := CoverTree.reject 102
def tree071_182 : CoverTree := CoverTree.reject 245
def tree071_183 : CoverTree := CoverTree.reject 216
def tree071_184 : CoverTree := CoverTree.split [tree071_27,tree071_182,tree071_183,tree071_30,tree071_32,tree071_18]
def tree071_185 : CoverTree := CoverTree.reject 192
def tree071_186 : CoverTree := CoverTree.split [tree071_15,tree071_185,tree071_19,tree071_21,tree071_18,tree071_18]
def tree071_187 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_180,tree071_181,tree071_184,tree071_186]
def tree071_188 : CoverTree := CoverTree.reject 313
def tree071_189 : CoverTree := CoverTree.reject 273
def tree071_190 : CoverTree := CoverTree.reject 246
def tree071_191 : CoverTree := CoverTree.split [tree071_89,tree071_188,tree071_189,tree071_190,tree071_117,tree071_99]
def tree071_192 : CoverTree := CoverTree.reject 274
def tree071_193 : CoverTree := CoverTree.split [tree071_39,tree071_192,tree071_46,tree071_48,tree071_50,tree071_52]
def tree071_194 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_191,tree071_193,tree071_59,tree071_36]
def tree071_195 : CoverTree := CoverTree.split [tree071_4,tree071_4,tree071_169,tree071_179,tree071_187,tree071_194]
def tree071_196 : CoverTree := CoverTree.reject 151
def tree071_197 : CoverTree := CoverTree.reject 133
def tree071_198 : CoverTree := CoverTree.reject 144
def tree071_199 : CoverTree := CoverTree.reject 217
def tree071_200 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_199,tree071_68,tree071_68]
def tree071_201 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_196,tree071_197,tree071_198,tree071_200]
def tree071_202 : CoverTree := CoverTree.reject 134
def tree071_203 : CoverTree := CoverTree.reject 275
def tree071_204 : CoverTree := CoverTree.reject 276
def tree071_205 : CoverTree := CoverTree.split [tree071_39,tree071_203,tree071_204,tree071_30,tree071_80,tree071_52]
def tree071_206 : CoverTree := CoverTree.reject 247
def tree071_207 : CoverTree := CoverTree.reject 248
def tree071_208 : CoverTree := CoverTree.split [tree071_27,tree071_206,tree071_207,tree071_30,tree071_80,tree071_18]
def tree071_209 : CoverTree := CoverTree.reject 218
def tree071_210 : CoverTree := CoverTree.split [tree071_15,tree071_209,tree071_19,tree071_21,tree071_18,tree071_18]
def tree071_211 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_202,tree071_205,tree071_208,tree071_210]
def tree071_212 : CoverTree := CoverTree.reject 120
def tree071_213 : CoverTree := CoverTree.reject 277
def tree071_214 : CoverTree := CoverTree.split [tree071_39,tree071_213,tree071_101,tree071_30,tree071_103,tree071_52]
def tree071_215 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_212,tree071_214,tree071_33,tree071_36]
def tree071_216 : CoverTree := CoverTree.split [tree071_4,tree071_4,tree071_201,tree071_211,tree071_215,tree071_119]
def tree071_217 : CoverTree := CoverTree.reject 152
def tree071_218 : CoverTree := CoverTree.reject 278
def tree071_219 : CoverTree := CoverTree.reject 219
def tree071_220 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_218,tree071_219,tree071_68]
def tree071_221 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_217,tree071_220,tree071_72,tree071_73]
def tree071_222 : CoverTree := CoverTree.reject 314
def tree071_223 : CoverTree := CoverTree.reject 279
def tree071_224 : CoverTree := CoverTree.reject 280
def tree071_225 : CoverTree := CoverTree.reject 107
def tree071_226 : CoverTree := CoverTree.split [tree071_98,tree071_225,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_227 : CoverTree := CoverTree.split [tree071_89,tree071_222,tree071_223,tree071_224,tree071_97,tree071_226]
def tree071_228 : CoverTree := CoverTree.reject 281
def tree071_229 : CoverTree := CoverTree.reject 282
def tree071_230 : CoverTree := CoverTree.split [tree071_39,tree071_228,tree071_229,tree071_30,tree071_80,tree071_52]
def tree071_231 : CoverTree := CoverTree.reject 249
def tree071_232 : CoverTree := CoverTree.split [tree071_27,tree071_231,tree071_83,tree071_30,tree071_80,tree071_18]
def tree071_233 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_227,tree071_230,tree071_232,tree071_87]
def tree071_234 : CoverTree := CoverTree.reject 250
def tree071_235 : CoverTree := CoverTree.split [tree071_89,tree071_93,tree071_95,tree071_234,tree071_97,tree071_99]
def tree071_236 : CoverTree := CoverTree.reject 283
def tree071_237 : CoverTree := CoverTree.split [tree071_39,tree071_236,tree071_101,tree071_30,tree071_103,tree071_52]
def tree071_238 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_235,tree071_237,tree071_33,tree071_36]
def tree071_239 : CoverTree := CoverTree.reject 315
def tree071_240 : CoverTree := CoverTree.reject 284
def tree071_241 : CoverTree := CoverTree.split [tree071_89,tree071_239,tree071_240,tree071_114,tree071_117,tree071_99]
def tree071_242 : CoverTree := CoverTree.split [tree071_6,tree071_6,tree071_241,tree071_53,tree071_59,tree071_36]
def tree071_243 : CoverTree := CoverTree.split [tree071_4,tree071_4,tree071_221,tree071_233,tree071_238,tree071_242]
def tree071_244 : CoverTree := CoverTree.split [tree071_0,tree071_133,tree071_163,tree071_195,tree071_216,tree071_243]
def tree071_245 : CoverTree := CoverTree.reject 22
def tree071_246 : CoverTree := CoverTree.reject 125
def tree071_247 : CoverTree := CoverTree.reject 32
def tree071_248 : CoverTree := CoverTree.reject 55
def tree071_249 : CoverTree := CoverTree.reject 193
def tree071_250 : CoverTree := CoverTree.reject 179
def tree071_251 : CoverTree := CoverTree.reject 210
def tree071_252 : CoverTree := CoverTree.split [tree071_18,tree071_251,tree071_18,tree071_18,tree071_18,tree071_18]
def tree071_253 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_249,tree071_250,tree071_252]
def tree071_254 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_247,tree071_248,tree071_253]
def tree071_255 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_21,tree071_18,tree071_18]
def tree071_256 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_247,tree071_248,tree071_255]
def tree071_257 : CoverTree := CoverTree.reject 10
def tree071_258 : CoverTree := CoverTree.reject 121
def tree071_259 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_125,tree071_258,tree071_128,tree071_131]
def tree071_260 : CoverTree := CoverTree.split [tree071_245,tree071_245,tree071_246,tree071_254,tree071_256,tree071_259]
def tree071_261 : CoverTree := CoverTree.reject 31
def tree071_262 : CoverTree := CoverTree.reject 59
def tree071_263 : CoverTree := CoverTree.reject 60
def tree071_264 : CoverTree := CoverTree.reject 135
def tree071_265 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_262,tree071_263,tree071_264]
def tree071_266 : CoverTree := CoverTree.reject 162
def tree071_267 : CoverTree := CoverTree.reject 220
def tree071_268 : CoverTree := CoverTree.reject 211
def tree071_269 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_268,tree071_18,tree071_18,tree071_18]
def tree071_270 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_267,tree071_269,tree071_68]
def tree071_271 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_135,tree071_266,tree071_270]
def tree071_272 : CoverTree := CoverTree.reject 109
def tree071_273 : CoverTree := CoverTree.reject 129
def tree071_274 : CoverTree := CoverTree.reject 130
def tree071_275 : CoverTree := CoverTree.reject 221
def tree071_276 : CoverTree := CoverTree.reject 222
def tree071_277 : CoverTree := CoverTree.split [tree071_27,tree071_273,tree071_274,tree071_275,tree071_276,tree071_18]
def tree071_278 : CoverTree := CoverTree.reject 223
def tree071_279 : CoverTree := CoverTree.reject 194
def tree071_280 : CoverTree := CoverTree.split [tree071_15,tree071_278,tree071_279,tree071_21,tree071_18,tree071_18]
def tree071_281 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_272,tree071_277,tree071_280]
def tree071_282 : CoverTree := CoverTree.reject 157
def tree071_283 : CoverTree := CoverTree.reject 212
def tree071_284 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_45,tree071_283,tree071_18,tree071_18]
def tree071_285 : CoverTree := CoverTree.split [tree071_39,tree071_282,tree071_284,tree071_30,tree071_103,tree071_52]
def tree071_286 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_285,tree071_147,tree071_152]
def tree071_287 : CoverTree := CoverTree.reject 316
def tree071_288 : CoverTree := CoverTree.reject 285
def tree071_289 : CoverTree := CoverTree.split [tree071_89,tree071_287,tree071_288,tree071_114,tree071_117,tree071_99]
def tree071_290 : CoverTree := CoverTree.reject 286
def tree071_291 : CoverTree := CoverTree.split [tree071_39,tree071_290,tree071_46,tree071_48,tree071_50,tree071_52]
def tree071_292 : CoverTree := CoverTree.reject 195
def tree071_293 : CoverTree := CoverTree.split [tree071_15,tree071_292,tree071_19,tree071_21,tree071_18,tree071_18]
def tree071_294 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_289,tree071_291,tree071_59,tree071_293]
def tree071_295 : CoverTree := CoverTree.split [tree071_261,tree071_265,tree071_271,tree071_281,tree071_286,tree071_294]
def tree071_296 : CoverTree := CoverTree.reject 23
def tree071_297 : CoverTree := CoverTree.reject 9
def tree071_298 : CoverTree := CoverTree.reject 67
def tree071_299 : CoverTree := CoverTree.reject 61
def tree071_300 : CoverTree := CoverTree.reject 147
def tree071_301 : CoverTree := CoverTree.reject 224
def tree071_302 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_301,tree071_68,tree071_68]
def tree071_303 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_298,tree071_299,tree071_300,tree071_302]
def tree071_304 : CoverTree := CoverTree.reject 163
def tree071_305 : CoverTree := CoverTree.reject 251
def tree071_306 : CoverTree := CoverTree.reject 225
def tree071_307 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_305,tree071_306,tree071_68]
def tree071_308 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_164,tree071_304,tree071_307,tree071_73]
def tree071_309 : CoverTree := CoverTree.reject 136
def tree071_310 : CoverTree := CoverTree.reject 110
def tree071_311 : CoverTree := CoverTree.reject 252
def tree071_312 : CoverTree := CoverTree.reject 253
def tree071_313 : CoverTree := CoverTree.split [tree071_27,tree071_311,tree071_312,tree071_30,tree071_80,tree071_18]
def tree071_314 : CoverTree := CoverTree.reject 226
def tree071_315 : CoverTree := CoverTree.split [tree071_15,tree071_314,tree071_19,tree071_21,tree071_18,tree071_18]
def tree071_316 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_309,tree071_310,tree071_313,tree071_315]
def tree071_317 : CoverTree := CoverTree.reject 58
def tree071_318 : CoverTree := CoverTree.reject 165
def tree071_319 : CoverTree := CoverTree.split [tree071_89,tree071_318,tree071_95,tree071_96,tree071_97,tree071_99]
def tree071_320 : CoverTree := CoverTree.reject 158
def tree071_321 : CoverTree := CoverTree.split [tree071_39,tree071_320,tree071_101,tree071_30,tree071_103,tree071_52]
def tree071_322 : CoverTree := CoverTree.split [tree071_317,tree071_317,tree071_319,tree071_321,tree071_33,tree071_36]
def tree071_323 : CoverTree := CoverTree.reject 51
def tree071_324 : CoverTree := CoverTree.reject 122
def tree071_325 : CoverTree := CoverTree.split [tree071_323,tree071_324,tree071_118,tree071_53,tree071_59,tree071_36]
def tree071_326 : CoverTree := CoverTree.split [tree071_296,tree071_303,tree071_308,tree071_316,tree071_322,tree071_325]
def tree071_327 : CoverTree := CoverTree.reject 36
def tree071_328 : CoverTree := CoverTree.reject 18
def tree071_329 : CoverTree := CoverTree.reject 62
def tree071_330 : CoverTree := CoverTree.reject 63
def tree071_331 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_327,tree071_328,tree071_329,tree071_330]
def tree071_332 : CoverTree := CoverTree.reject 68
def tree071_333 : CoverTree := CoverTree.reject 137
def tree071_334 : CoverTree := CoverTree.reject 148
def tree071_335 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_332,tree071_333,tree071_334,tree071_73]
def tree071_336 : CoverTree := CoverTree.reject 153
def tree071_337 : CoverTree := CoverTree.reject 287
def tree071_338 : CoverTree := CoverTree.reject 227
def tree071_339 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_337,tree071_338,tree071_68]
def tree071_340 : CoverTree := CoverTree.reject 254
def tree071_341 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_340,tree071_68,tree071_68]
def tree071_342 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_336,tree071_339,tree071_341,tree071_73]
def tree071_343 : CoverTree := CoverTree.reject 138
def tree071_344 : CoverTree := CoverTree.reject 288
def tree071_345 : CoverTree := CoverTree.reject 289
def tree071_346 : CoverTree := CoverTree.split [tree071_39,tree071_344,tree071_345,tree071_30,tree071_80,tree071_52]
def tree071_347 : CoverTree := CoverTree.reject 255
def tree071_348 : CoverTree := CoverTree.split [tree071_27,tree071_347,tree071_83,tree071_30,tree071_80,tree071_18]
def tree071_349 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_343,tree071_346,tree071_348,tree071_87]
def tree071_350 : CoverTree := CoverTree.reject 290
def tree071_351 : CoverTree := CoverTree.split [tree071_39,tree071_350,tree071_101,tree071_30,tree071_103,tree071_52]
def tree071_352 : CoverTree := CoverTree.split [tree071_317,tree071_317,tree071_100,tree071_351,tree071_33,tree071_36]
def tree071_353 : CoverTree := CoverTree.reject 76
def tree071_354 : CoverTree := CoverTree.reject 71
def tree071_355 : CoverTree := CoverTree.reject 72
def tree071_356 : CoverTree := CoverTree.reject 30
def tree071_357 : CoverTree := CoverTree.reject 2
def tree071_358 : CoverTree := CoverTree.reject 155
def tree071_359 : CoverTree := CoverTree.reject 117
def tree071_360 : CoverTree := CoverTree.reject 156
def tree071_361 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_358,tree071_359,tree071_360]
def tree071_362 : CoverTree := CoverTree.reject 291
def tree071_363 : CoverTree := CoverTree.split [tree071_353,tree071_354,tree071_355,tree071_356,tree071_361,tree071_362]
def tree071_364 : CoverTree := CoverTree.reject 66
def tree071_365 : CoverTree := CoverTree.reject 317
def tree071_366 : CoverTree := CoverTree.reject 318
def tree071_367 : CoverTree := CoverTree.reject 141
def tree071_368 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_367,tree071_18,tree071_18]
def tree071_369 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_18,tree071_18,tree071_18]
def tree071_370 : CoverTree := CoverTree.split [tree071_364,tree071_365,tree071_366,tree071_368,tree071_369,tree071_369]
def tree071_371 : CoverTree := CoverTree.split [tree071_363,tree071_370,tree071_118,tree071_53,tree071_59,tree071_36]
def tree071_372 : CoverTree := CoverTree.split [tree071_331,tree071_335,tree071_342,tree071_349,tree071_352,tree071_371]
def tree071_373 : CoverTree := CoverTree.reject 114
def tree071_374 : CoverTree := CoverTree.reject 75
def tree071_375 : CoverTree := CoverTree.reject 64
def tree071_376 : CoverTree := CoverTree.reject 65
def tree071_377 : CoverTree := CoverTree.split [tree071_373,tree071_374,tree071_327,tree071_328,tree071_375,tree071_376]
def tree071_378 : CoverTree := CoverTree.reject 103
def tree071_379 : CoverTree := CoverTree.reject 268
def tree071_380 : CoverTree := CoverTree.reject 149
def tree071_381 : CoverTree := CoverTree.reject 292
def tree071_382 : CoverTree := CoverTree.reject 168
def tree071_383 : CoverTree := CoverTree.reject 169
def tree071_384 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_382,tree071_383,tree071_18,tree071_18]
def tree071_385 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_381,tree071_384,tree071_68]
def tree071_386 : CoverTree := CoverTree.reject 256
def tree071_387 : CoverTree := CoverTree.reject 128
def tree071_388 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_387,tree071_18,tree071_18,tree071_18]
def tree071_389 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_386,tree071_388,tree071_68]
def tree071_390 : CoverTree := CoverTree.split [tree071_378,tree071_379,tree071_380,tree071_385,tree071_389,tree071_73]
def tree071_391 : CoverTree := CoverTree.reject 104
def tree071_392 : CoverTree := CoverTree.reject 319
def tree071_393 : CoverTree := CoverTree.reject 320
def tree071_394 : CoverTree := CoverTree.reject 173
def tree071_395 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_394,tree071_18,tree071_18]
def tree071_396 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_392,tree071_393,tree071_395]
def tree071_397 : CoverTree := CoverTree.reject 293
def tree071_398 : CoverTree := CoverTree.reject 257
def tree071_399 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_397,tree071_398,tree071_68]
def tree071_400 : CoverTree := CoverTree.reject 294
def tree071_401 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_400,tree071_68,tree071_68]
def tree071_402 : CoverTree := CoverTree.split [tree071_391,tree071_396,tree071_399,tree071_401,tree071_72,tree071_73]
def tree071_403 : CoverTree := CoverTree.reject 52
def tree071_404 : CoverTree := CoverTree.reject 198
def tree071_405 : CoverTree := CoverTree.reject 321
def tree071_406 : CoverTree := CoverTree.reject 322
def tree071_407 : CoverTree := CoverTree.reject 295
def tree071_408 : CoverTree := CoverTree.split [tree071_364,tree071_404,tree071_405,tree071_406,tree071_407,tree071_369]
def tree071_409 : CoverTree := CoverTree.reject 323
def tree071_410 : CoverTree := CoverTree.reject 296
def tree071_411 : CoverTree := CoverTree.reject 297
def tree071_412 : CoverTree := CoverTree.split [tree071_89,tree071_409,tree071_410,tree071_411,tree071_97,tree071_226]
def tree071_413 : CoverTree := CoverTree.reject 298
def tree071_414 : CoverTree := CoverTree.split [tree071_39,tree071_413,tree071_78,tree071_30,tree071_80,tree071_52]
def tree071_415 : CoverTree := CoverTree.split [tree071_403,tree071_408,tree071_412,tree071_414,tree071_84,tree071_87]
def tree071_416 : CoverTree := CoverTree.reject 311
def tree071_417 : CoverTree := CoverTree.reject 199
def tree071_418 : CoverTree := CoverTree.reject 17
def tree071_419 : CoverTree := CoverTree.reject 97
def tree071_420 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_418,tree071_419,tree071_18]
def tree071_421 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_418,tree071_18,tree071_18]
def tree071_422 : CoverTree := CoverTree.split [tree071_364,tree071_417,tree071_420,tree071_421,tree071_421,tree071_369]
def tree071_423 : CoverTree := CoverTree.split [tree071_416,tree071_422,tree071_100,tree071_104,tree071_33,tree071_36]
def tree071_424 : CoverTree := CoverTree.reject 70
def tree071_425 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_424,tree071_18,tree071_18]
def tree071_426 : CoverTree := CoverTree.split [tree071_353,tree071_354,tree071_355,tree071_356,tree071_361,tree071_425]
def tree071_427 : CoverTree := CoverTree.reject 139
def tree071_428 : CoverTree := CoverTree.reject 96
def tree071_429 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_427,tree071_428,tree071_18]
def tree071_430 : CoverTree := CoverTree.reject 140
def tree071_431 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_430,tree071_419,tree071_18]
def tree071_432 : CoverTree := CoverTree.split [tree071_364,tree071_429,tree071_431,tree071_368,tree071_369,tree071_369]
def tree071_433 : CoverTree := CoverTree.split [tree071_426,tree071_432,tree071_118,tree071_53,tree071_59,tree071_36]
def tree071_434 : CoverTree := CoverTree.split [tree071_377,tree071_390,tree071_402,tree071_415,tree071_423,tree071_433]
def tree071_435 : CoverTree := CoverTree.split [tree071_0,tree071_260,tree071_295,tree071_326,tree071_372,tree071_434]
def tree071_436 : CoverTree := CoverTree.reject 123
def tree071_437 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_247,tree071_436,tree071_73]
def tree071_438 : CoverTree := CoverTree.reject 178
def tree071_439 : CoverTree := CoverTree.reject 196
def tree071_440 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_439,tree071_18,tree071_252]
def tree071_441 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_247,tree071_438,tree071_440]
def tree071_442 : CoverTree := CoverTree.reject 112
def tree071_443 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_442,tree071_32,tree071_18]
def tree071_444 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_247,tree071_443,tree071_255]
def tree071_445 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_48,tree071_50,tree071_52]
def tree071_446 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_125,tree071_445,tree071_128,tree071_131]
def tree071_447 : CoverTree := CoverTree.split [tree071_245,tree071_245,tree071_437,tree071_441,tree071_444,tree071_446]
def tree071_448 : CoverTree := CoverTree.reject 228
def tree071_449 : CoverTree := CoverTree.reject 229
def tree071_450 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_448,tree071_449,tree071_68]
def tree071_451 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_262,tree071_263,tree071_450]
def tree071_452 : CoverTree := CoverTree.reject 115
def tree071_453 : CoverTree := CoverTree.reject 230
def tree071_454 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_452,tree071_453,tree071_68]
def tree071_455 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_68,tree071_269,tree071_68]
def tree071_456 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_135,tree071_454,tree071_455]
def tree071_457 : CoverTree := CoverTree.reject 111
def tree071_458 : CoverTree := CoverTree.split [tree071_27,tree071_273,tree071_274,tree071_30,tree071_80,tree071_18]
def tree071_459 : CoverTree := CoverTree.reject 231
def tree071_460 : CoverTree := CoverTree.reject 197
def tree071_461 : CoverTree := CoverTree.split [tree071_15,tree071_459,tree071_460,tree071_21,tree071_18,tree071_18]
def tree071_462 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_457,tree071_458,tree071_461]
def tree071_463 : CoverTree := CoverTree.reject 232
def tree071_464 : CoverTree := CoverTree.split [tree071_15,tree071_463,tree071_151,tree071_21,tree071_18,tree071_18]
def tree071_465 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_285,tree071_147,tree071_464]
def tree071_466 : CoverTree := CoverTree.reject 324
def tree071_467 : CoverTree := CoverTree.split [tree071_89,tree071_466,tree071_111,tree071_114,tree071_117,tree071_99]
def tree071_468 : CoverTree := CoverTree.reject 299
def tree071_469 : CoverTree := CoverTree.split [tree071_39,tree071_468,tree071_46,tree071_48,tree071_50,tree071_52]
def tree071_470 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_467,tree071_469,tree071_59,tree071_36]
def tree071_471 : CoverTree := CoverTree.split [tree071_261,tree071_451,tree071_456,tree071_462,tree071_465,tree071_470]
def tree071_472 : CoverTree := CoverTree.reject 258
def tree071_473 : CoverTree := CoverTree.reject 259
def tree071_474 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_472,tree071_473,tree071_68]
def tree071_475 : CoverTree := CoverTree.reject 233
def tree071_476 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_475,tree071_68,tree071_68]
def tree071_477 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_298,tree071_299,tree071_474,tree071_476]
def tree071_478 : CoverTree := CoverTree.reject 164
def tree071_479 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_164,tree071_478,tree071_72,tree071_73]
def tree071_480 : CoverTree := CoverTree.reject 174
def tree071_481 : CoverTree := CoverTree.reject 175
def tree071_482 : CoverTree := CoverTree.split [tree071_89,tree071_318,tree071_480,tree071_481,tree071_97,tree071_226]
def tree071_483 : CoverTree := CoverTree.reject 176
def tree071_484 : CoverTree := CoverTree.reject 177
def tree071_485 : CoverTree := CoverTree.split [tree071_39,tree071_483,tree071_484,tree071_30,tree071_80,tree071_52]
def tree071_486 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_482,tree071_485,tree071_84,tree071_87]
def tree071_487 : CoverTree := CoverTree.reject 238
def tree071_488 : CoverTree := CoverTree.reject 239
def tree071_489 : CoverTree := CoverTree.split [tree071_364,tree071_487,tree071_488,tree071_368,tree071_369,tree071_369]
def tree071_490 : CoverTree := CoverTree.split [tree071_323,tree071_489,tree071_118,tree071_53,tree071_59,tree071_36]
def tree071_491 : CoverTree := CoverTree.split [tree071_296,tree071_477,tree071_479,tree071_486,tree071_322,tree071_490]
def tree071_492 : CoverTree := CoverTree.reject 300
def tree071_493 : CoverTree := CoverTree.reject 301
def tree071_494 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_492,tree071_493,tree071_68]
def tree071_495 : CoverTree := CoverTree.reject 260
def tree071_496 : CoverTree := CoverTree.reject 261
def tree071_497 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_495,tree071_496,tree071_68]
def tree071_498 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_332,tree071_494,tree071_497,tree071_73]
def tree071_499 : CoverTree := CoverTree.reject 154
def tree071_500 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_499,tree071_69,tree071_72,tree071_73]
def tree071_501 : CoverTree := CoverTree.reject 240
def tree071_502 : CoverTree := CoverTree.reject 302
def tree071_503 : CoverTree := CoverTree.reject 113
def tree071_504 : CoverTree := CoverTree.split [tree071_24,tree071_24,tree071_90,tree071_503,tree071_18,tree071_18]
def tree071_505 : CoverTree := CoverTree.split [tree071_89,tree071_501,tree071_502,tree071_504,tree071_97,tree071_226]
def tree071_506 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_505,tree071_81,tree071_84,tree071_87]
def tree071_507 : CoverTree := CoverTree.split [tree071_317,tree071_317,tree071_100,tree071_104,tree071_33,tree071_36]
def tree071_508 : CoverTree := CoverTree.split [tree071_331,tree071_498,tree071_500,tree071_506,tree071_507,tree071_433]
def tree071_509 : CoverTree := CoverTree.reject 269
def tree071_510 : CoverTree := CoverTree.reject 325
def tree071_511 : CoverTree := CoverTree.reject 303
def tree071_512 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_510,tree071_511,tree071_68]
def tree071_513 : CoverTree := CoverTree.reject 304
def tree071_514 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_513,tree071_384,tree071_68]
def tree071_515 : CoverTree := CoverTree.reject 127
def tree071_516 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_515,tree071_18,tree071_18,tree071_18]
def tree071_517 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_516,tree071_388,tree071_68]
def tree071_518 : CoverTree := CoverTree.split [tree071_378,tree071_509,tree071_512,tree071_514,tree071_517,tree071_73]
def tree071_519 : CoverTree := CoverTree.reject 54
def tree071_520 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_418,tree071_519,tree071_18]
def tree071_521 : CoverTree := CoverTree.reject 326
def tree071_522 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_520,tree071_521,tree071_395]
def tree071_523 : CoverTree := CoverTree.reject 142
def tree071_524 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_90,tree071_523,tree071_18,tree071_18]
def tree071_525 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_90,tree071_18,tree071_18,tree071_18]
def tree071_526 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_524,tree071_525,tree071_68]
def tree071_527 : CoverTree := CoverTree.split [tree071_391,tree071_522,tree071_526,tree071_69,tree071_72,tree071_73]
def tree071_528 : CoverTree := CoverTree.reject 327
def tree071_529 : CoverTree := CoverTree.reject 328
def tree071_530 : CoverTree := CoverTree.split [tree071_364,tree071_404,tree071_528,tree071_529,tree071_421,tree071_369]
def tree071_531 : CoverTree := CoverTree.reject 329
def tree071_532 : CoverTree := CoverTree.split [tree071_89,tree071_531,tree071_95,tree071_504,tree071_97,tree071_226]
def tree071_533 : CoverTree := CoverTree.reject 305
def tree071_534 : CoverTree := CoverTree.split [tree071_39,tree071_533,tree071_78,tree071_30,tree071_80,tree071_52]
def tree071_535 : CoverTree := CoverTree.split [tree071_403,tree071_530,tree071_532,tree071_534,tree071_84,tree071_87]
def tree071_536 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_418,tree071_359,tree071_18]
def tree071_537 : CoverTree := CoverTree.reject 159
def tree071_538 : CoverTree := CoverTree.split [tree071_353,tree071_354,tree071_355,tree071_356,tree071_536,tree071_537]
def tree071_539 : CoverTree := CoverTree.split [tree071_538,tree071_422,tree071_100,tree071_104,tree071_33,tree071_36]
def tree071_540 : CoverTree := CoverTree.split [tree071_377,tree071_518,tree071_527,tree071_535,tree071_539,tree071_433]
def tree071_541 : CoverTree := CoverTree.split [tree071_0,tree071_447,tree071_471,tree071_491,tree071_508,tree071_540]
def tree071_542 : CoverTree := CoverTree.reject 234
def tree071_543 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_542,tree071_68,tree071_68]
def tree071_544 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_247,tree071_436,tree071_543]
def tree071_545 : CoverTree := CoverTree.reject 12
def tree071_546 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_545,tree071_545,tree071_18]
def tree071_547 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_21,tree071_18,tree071_252]
def tree071_548 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_247,tree071_546,tree071_547]
def tree071_549 : CoverTree := CoverTree.split [tree071_245,tree071_245,tree071_544,tree071_548,tree071_444,tree071_446]
def tree071_550 : CoverTree := CoverTree.reject 235
def tree071_551 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_550,tree071_68,tree071_68]
def tree071_552 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_262,tree071_263,tree071_551]
def tree071_553 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_452,tree071_68,tree071_68]
def tree071_554 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_135,tree071_553,tree071_455]
def tree071_555 : CoverTree := CoverTree.reject 207
def tree071_556 : CoverTree := CoverTree.reject 208
def tree071_557 : CoverTree := CoverTree.split [tree071_39,tree071_555,tree071_556,tree071_30,tree071_80,tree071_52]
def tree071_558 : CoverTree := CoverTree.split [tree071_134,tree071_134,tree071_134,tree071_557,tree071_458,tree071_87]
def tree071_559 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_118,tree071_53,tree071_59,tree071_36]
def tree071_560 : CoverTree := CoverTree.split [tree071_261,tree071_552,tree071_554,tree071_558,tree071_286,tree071_559]
def tree071_561 : CoverTree := CoverTree.reject 262
def tree071_562 : CoverTree := CoverTree.reject 263
def tree071_563 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_561,tree071_562,tree071_68]
def tree071_564 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_298,tree071_299,tree071_563,tree071_73]
def tree071_565 : CoverTree := CoverTree.reject 100
def tree071_566 : CoverTree := CoverTree.reject 270
def tree071_567 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_566,tree071_18,tree071_18,tree071_18]
def tree071_568 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_565,tree071_567,tree071_68]
def tree071_569 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_164,tree071_568,tree071_72,tree071_73]
def tree071_570 : CoverTree := CoverTree.reject 204
def tree071_571 : CoverTree := CoverTree.reject 241
def tree071_572 : CoverTree := CoverTree.split [tree071_570,tree071_571,tree071_319,tree071_321,tree071_33,tree071_36]
def tree071_573 : CoverTree := CoverTree.split [tree071_296,tree071_564,tree071_569,tree071_486,tree071_572,tree071_490]
def tree071_574 : CoverTree := CoverTree.reject 306
def tree071_575 : CoverTree := CoverTree.reject 307
def tree071_576 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_574,tree071_575,tree071_68]
def tree071_577 : CoverTree := CoverTree.reject 264
def tree071_578 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_577,tree071_388,tree071_68]
def tree071_579 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_332,tree071_576,tree071_578,tree071_73]
def tree071_580 : CoverTree := CoverTree.reject 308
def tree071_581 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_580,tree071_525,tree071_68]
def tree071_582 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_581,tree071_69,tree071_72,tree071_73]
def tree071_583 : CoverTree := CoverTree.reject 309
def tree071_584 : CoverTree := CoverTree.split [tree071_89,tree071_501,tree071_583,tree071_504,tree071_97,tree071_226]
def tree071_585 : CoverTree := CoverTree.split [tree071_297,tree071_297,tree071_584,tree071_81,tree071_84,tree071_87]
def tree071_586 : CoverTree := CoverTree.reject 171
def tree071_587 : CoverTree := CoverTree.reject 27
def tree071_588 : CoverTree := CoverTree.split [tree071_587,tree071_587,tree071_587,tree071_421,tree071_421,tree071_369]
def tree071_589 : CoverTree := CoverTree.split [tree071_586,tree071_588,tree071_100,tree071_104,tree071_33,tree071_36]
def tree071_590 : CoverTree := CoverTree.split [tree071_331,tree071_579,tree071_582,tree071_585,tree071_589,tree071_433]
def tree071_591 : CoverTree := CoverTree.reject 180
def tree071_592 : CoverTree := CoverTree.reject 181
def tree071_593 : CoverTree := CoverTree.reject 172
def tree071_594 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_593,tree071_18,tree071_18]
def tree071_595 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_591,tree071_592,tree071_594]
def tree071_596 : CoverTree := CoverTree.reject 330
def tree071_597 : CoverTree := CoverTree.reject 170
def tree071_598 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_90,tree071_597,tree071_18,tree071_18]
def tree071_599 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_596,tree071_598,tree071_68]
def tree071_600 : CoverTree := CoverTree.reject 166
def tree071_601 : CoverTree := CoverTree.reject 167
def tree071_602 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_600,tree071_601,tree071_18,tree071_18]
def tree071_603 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_602,tree071_384,tree071_68]
def tree071_604 : CoverTree := CoverTree.split [tree071_378,tree071_595,tree071_599,tree071_603,tree071_517,tree071_73]
def tree071_605 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_520,tree071_520,tree071_395]
def tree071_606 : CoverTree := CoverTree.split [tree071_391,tree071_605,tree071_526,tree071_69,tree071_72,tree071_73]
def tree071_607 : CoverTree := CoverTree.reject 331
def tree071_608 : CoverTree := CoverTree.reject 183
def tree071_609 : CoverTree := CoverTree.split [tree071_357,tree071_357,tree071_357,tree071_418,tree071_608,tree071_18]
def tree071_610 : CoverTree := CoverTree.split [tree071_364,tree071_404,tree071_607,tree071_609,tree071_421,tree071_369]
def tree071_611 : CoverTree := CoverTree.split [tree071_89,tree071_93,tree071_95,tree071_504,tree071_97,tree071_226]
def tree071_612 : CoverTree := CoverTree.split [tree071_403,tree071_610,tree071_611,tree071_81,tree071_84,tree071_87]
def tree071_613 : CoverTree := CoverTree.split [tree071_377,tree071_604,tree071_606,tree071_612,tree071_539,tree071_433]
def tree071_614 : CoverTree := CoverTree.split [tree071_0,tree071_549,tree071_560,tree071_573,tree071_590,tree071_613]
def tree071_615 : CoverTree := CoverTree.reject 200
def tree071_616 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_125,tree071_615,tree071_436,tree071_73]
def tree071_617 : CoverTree := CoverTree.reject 182
def tree071_618 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_125,tree071_617,tree071_546,tree071_547]
def tree071_619 : CoverTree := CoverTree.reject 206
def tree071_620 : CoverTree := CoverTree.split [tree071_127,tree071_127,tree071_127,tree071_442,tree071_619,tree071_52]
def tree071_621 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_125,tree071_620,tree071_443,tree071_255]
def tree071_622 : CoverTree := CoverTree.split [tree071_245,tree071_245,tree071_616,tree071_618,tree071_621,tree071_446]
def tree071_623 : CoverTree := CoverTree.reject 201
def tree071_624 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_623,tree071_262,tree071_263,tree071_73]
def tree071_625 : CoverTree := CoverTree.reject 202
def tree071_626 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_625,tree071_135,tree071_553,tree071_455]
def tree071_627 : CoverTree := CoverTree.reject 203
def tree071_628 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_627,tree071_557,tree071_458,tree071_87]
def tree071_629 : CoverTree := CoverTree.reject 73
def tree071_630 : CoverTree := CoverTree.split [tree071_89,tree071_629,tree071_629,tree071_629,tree071_629,tree071_99]
def tree071_631 : CoverTree := CoverTree.split [tree071_257,tree071_257,tree071_630,tree071_285,tree071_147,tree071_152]
def tree071_632 : CoverTree := CoverTree.split [tree071_261,tree071_624,tree071_626,tree071_628,tree071_631,tree071_559]
def tree071_633 : CoverTree := CoverTree.reject 265
def tree071_634 : CoverTree := CoverTree.split [tree071_378,tree071_633,tree071_298,tree071_299,tree071_517,tree071_73]
def tree071_635 : CoverTree := CoverTree.reject 266
def tree071_636 : CoverTree := CoverTree.split [tree071_391,tree071_635,tree071_164,tree071_568,tree071_72,tree071_73]
def tree071_637 : CoverTree := CoverTree.reject 236
def tree071_638 : CoverTree := CoverTree.split [tree071_403,tree071_637,tree071_482,tree071_485,tree071_84,tree071_87]
def tree071_639 : CoverTree := CoverTree.reject 79
def tree071_640 : CoverTree := CoverTree.split [tree071_587,tree071_587,tree071_587,tree071_639,tree071_639,tree071_369]
def tree071_641 : CoverTree := CoverTree.split [tree071_570,tree071_640,tree071_319,tree071_321,tree071_33,tree071_36]
def tree071_642 : CoverTree := CoverTree.split [tree071_296,tree071_634,tree071_636,tree071_638,tree071_641,tree071_490]
def tree071_643 : CoverTree := CoverTree.split [tree071_373,tree071_374,tree071_327,tree071_328,tree071_329,tree071_330]
def tree071_644 : CoverTree := CoverTree.reject 267
def tree071_645 : CoverTree := CoverTree.split [tree071_378,tree071_644,tree071_332,tree071_603,tree071_517,tree071_73]
def tree071_646 : CoverTree := CoverTree.reject 205
def tree071_647 : CoverTree := CoverTree.split [tree071_391,tree071_646,tree071_526,tree071_69,tree071_72,tree071_73]
def tree071_648 : CoverTree := CoverTree.reject 310
def tree071_649 : CoverTree := CoverTree.split [tree071_587,tree071_587,tree071_587,tree071_648,tree071_421,tree071_369]
def tree071_650 : CoverTree := CoverTree.split [tree071_89,tree071_501,tree071_95,tree071_504,tree071_97,tree071_226]
def tree071_651 : CoverTree := CoverTree.split [tree071_403,tree071_649,tree071_650,tree071_81,tree071_84,tree071_87]
def tree071_652 : CoverTree := CoverTree.split [tree071_643,tree071_645,tree071_647,tree071_651,tree071_589,tree071_433]
def tree071_653 : CoverTree := CoverTree.reject 237
def tree071_654 : CoverTree := CoverTree.split [tree071_64,tree071_64,tree071_90,tree071_597,tree071_653,tree071_18]
def tree071_655 : CoverTree := CoverTree.split [tree071_63,tree071_63,tree071_63,tree071_654,tree071_598,tree071_68]
def tree071_656 : CoverTree := CoverTree.split [tree071_378,tree071_595,tree071_655,tree071_603,tree071_517,tree071_73]
def tree071_657 : CoverTree := CoverTree.split [tree071_364,tree071_404,tree071_420,tree071_609,tree071_421,tree071_369]
def tree071_658 : CoverTree := CoverTree.split [tree071_403,tree071_657,tree071_611,tree071_81,tree071_84,tree071_87]
def tree071_659 : CoverTree := CoverTree.split [tree071_377,tree071_656,tree071_606,tree071_658,tree071_539,tree071_433]
def tree071_660 : CoverTree := CoverTree.split [tree071_0,tree071_622,tree071_632,tree071_642,tree071_652,tree071_659]
def tree071_661 : CoverTree := CoverTree.split [tree071_121,tree071_244,tree071_435,tree071_541,tree071_614,tree071_660]
def tree071 : CoverTree := tree071_661

end Snake9.Shared89
