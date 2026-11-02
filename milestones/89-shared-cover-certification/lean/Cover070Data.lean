import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes070 : List Box := [
[(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,6),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,3),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,2),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,6),(1,3)],
[(1,4),(1,5),(1,5),(1,2),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,2),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,2),(1,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)],
[(1,6),(1,2),(1,4),(1,5),(1,5),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,2),(1,5),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,3),(1,5),(1,3),(1,5),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,2),(1,6),(1,3),(1,6),(1,6)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(1,2),(1,3),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(6,6),(1,1),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(5,5),(1,1)],
[(1,6),(1,2),(1,5),(1,5),(1,4),(1,6)],
[(1,6),(1,4),(1,5),(1,3),(1,2),(1,6)],
[(2,2),(3,3),(3,3),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(2,2)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(4,4),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(5,5),(3,3),(3,3),(3,3),(1,6)],
[(1,6),(5,5),(5,5),(1,1),(1,6),(1,6)],
[(1,1),(5,5),(6,6),(3,3),(1,6),(1,6)],
[(1,1),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(6,6),(5,5),(1,1),(6,6),(1,6)],
[(2,2),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(5,5),(3,3),(1,6),(1,6)],
[(2,2),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(6,6),(1,1),(5,5)],
[(1,6),(1,6),(4,4),(6,6),(1,1),(6,6)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(5,5),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(5,5),(5,5),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(6,6),(1,1),(6,6)],
[(1,6),(1,6),(6,6),(3,3),(3,3),(2,2)],
[(2,2),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(6,6),(1,1),(5,5)],
[(1,6),(1,6),(3,3),(6,6),(1,1),(6,6)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(4,4),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(4,4),(5,5),(3,3),(2,2)],
[(1,6),(1,6),(4,4),(5,5),(5,5),(1,1)],
[(3,3),(4,4),(6,6),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(5,5),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(5,5),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(4,4),(3,3),(3,3)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(1,1)],
[(2,2),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(4,4),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(4,4)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(5,5)],
[(1,6),(1,6),(3,3),(5,5),(3,3),(2,2)],
[(1,6),(1,6),(3,3),(5,5),(3,3),(3,3)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(1,1)],
[(1,6),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(4,4),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(4,4),(4,4),(2,2),(5,5)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(3,3)],
[(1,6),(1,6),(4,4),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(4,4),(5,5),(1,1)],
[(1,6),(3,3),(3,3),(6,6),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(5,5),(3,3),(4,4),(2,2),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(3,3),(5,5),(5,5),(2,2),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(3,3)],
[(1,6),(1,6),(5,5),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(3,3),(5,5),(2,2)],
[(1,6),(1,5),(1,5),(1,2),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(2,2)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(3,3)],
[(1,6),(4,4),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(4,4),(2,2)],
[(1,6),(1,6),(2,2),(6,6),(5,5),(1,1)],
[(1,6),(1,6),(3,3),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(3,3),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(3,3),(4,4)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(1,1)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(5,5),(5,5),(1,1),(5,5)],
[(1,6),(1,6),(5,5),(5,5),(1,1),(6,6)],
[(1,6),(2,2),(6,6),(4,4),(3,3),(1,6)],
[(1,6),(3,3),(3,3),(5,5),(4,4),(1,6)],
[(1,6),(3,3),(4,4),(5,5),(2,2),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(3,3),(1,6)],
[(1,6),(6,6),(3,3),(3,3),(2,2),(1,6)],
[(1,6),(1,6),(4,4),(5,5),(1,1),(5,5)],
[(1,6),(1,6),(4,4),(5,5),(1,1),(6,6)],
[(1,6),(1,6),(6,6),(2,2),(4,4),(2,2)],
[(1,6),(1,6),(6,6),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(5,5),(3,3),(2,2),(4,4)],
[(1,6),(1,6),(5,5),(3,3),(2,2),(5,5)],
[(1,6),(3,3),(6,6),(5,5),(1,1),(1,6)],
[(1,3),(1,2),(1,5),(1,5),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(2,2)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(5,5),(5,5),(1,1)],
[(1,6),(1,6),(2,2),(5,5),(5,5),(2,2)],
[(1,6),(3,3),(3,3),(5,5),(3,3),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(5,5),(4,4),(3,3),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(3,3),(4,4),(2,2),(5,5)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(3,3)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(4,4)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(3,3)],
[(1,6),(1,6),(5,5),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(4,4)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(5,5)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(2,2)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(3,3)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(4,4)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(5,5)],
[(1,6),(3,3),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(4,4),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(1,1)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(4,4)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(1,1)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(2,2)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(2,2),(4,4),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(3,3)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(4,4)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(5,5)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(3,3)],
[(1,6),(1,6),(5,5),(2,2),(4,4),(2,2)],
[(1,6),(1,6),(5,5),(2,2),(4,4),(3,3)],
[(1,6),(1,6),(5,5),(2,2),(4,4),(4,4)],
[(1,6),(1,6),(5,5),(2,2),(5,5),(2,2)],
[(1,6),(1,6),(5,5),(2,2),(5,5),(3,3)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(5,5),(3,3),(3,3),(2,2),(1,6)],
[(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(3,3)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(4,4)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(5,5)],
[(1,6),(1,6),(4,4),(2,2),(5,5),(2,2)],
[(1,6),(1,6),(4,4),(2,2),(5,5),(3,3)],
[(1,6),(1,6),(4,4),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(4,4),(3,3),(2,2),(4,4)],
[(1,6),(1,6),(4,4),(3,3),(2,2),(5,5)],
[(5,5),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(6,6),(2,2),(3,3)],
[(1,6),(3,3),(4,4),(6,6),(2,2),(4,4)],
[(1,6),(3,3),(4,4),(6,6),(3,3),(2,2)],
[(1,6),(3,3),(4,4),(6,6),(3,3),(3,3)],
[(1,6),(3,3),(4,4),(6,6),(3,3),(4,4)],
[(1,6),(3,3),(4,4),(6,6),(4,4),(2,2)],
[(1,6),(3,3),(5,5),(5,5),(3,3),(3,3)],
[(1,6),(3,3),(5,5),(6,6),(2,2),(3,3)],
[(1,6),(3,3),(6,6),(3,3),(2,2),(4,4)],
[(1,6),(3,3),(6,6),(3,3),(2,2),(5,5)],
[(1,6),(3,3),(6,6),(3,3),(3,3),(3,3)],
[(1,6),(3,3),(6,6),(3,3),(3,3),(4,4)],
[(1,6),(3,3),(6,6),(3,3),(3,3),(5,5)],
[(1,6),(3,3),(6,6),(3,3),(4,4),(2,2)],
[(1,6),(3,3),(6,6),(3,3),(4,4),(3,3)],
[(1,6),(3,3),(6,6),(3,3),(4,4),(4,4)],
[(1,6),(3,3),(6,6),(3,3),(5,5),(2,2)],
[(1,6),(3,3),(6,6),(3,3),(5,5),(3,3)],
[(1,6),(3,3),(6,6),(3,3),(6,6),(2,2)],
[(1,6),(3,3),(6,6),(4,4),(2,2),(4,4)],
[(1,6),(3,3),(6,6),(4,4),(3,3),(2,2)],
[(1,6),(3,3),(6,6),(4,4),(3,3),(3,3)],
[(1,6),(3,3),(6,6),(4,4),(3,3),(4,4)],
[(1,6),(3,3),(6,6),(4,4),(4,4),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(2,2),(3,3)],
[(1,6),(4,4),(3,3),(6,6),(2,2),(4,4)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(4,4),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(4,4),(4,4),(5,5),(2,2),(4,4)],
[(1,6),(4,4),(4,4),(5,5),(2,2),(5,5)],
[(1,6),(4,4),(4,4),(5,5),(3,3),(3,3)],
[(1,6),(4,4),(4,4),(5,5),(3,3),(4,4)],
[(1,6),(4,4),(6,6),(3,3),(2,2),(4,4)],
[(1,6),(4,4),(6,6),(3,3),(2,2),(5,5)],
[(1,6),(4,4),(6,6),(3,3),(3,3),(3,3)],
[(1,6),(4,4),(6,6),(3,3),(3,3),(4,4)],
[(1,6),(4,4),(6,6),(3,3),(4,4),(3,3)],
[(1,6),(4,4),(6,6),(3,3),(5,5),(2,2)],
[(1,6),(4,4),(6,6),(3,3),(5,5),(3,3)],
[(1,6),(4,4),(6,6),(3,3),(6,6),(2,2)],
[(1,6),(4,4),(6,6),(4,4),(2,2),(3,3)],
[(1,6),(4,4),(6,6),(4,4),(2,2),(4,4)],
[(1,6),(4,4),(6,6),(4,4),(3,3),(2,2)],
[(1,6),(4,4),(6,6),(4,4),(3,3),(3,3)],
[(1,6),(4,4),(6,6),(4,4),(4,4),(2,2)],
[(1,6),(4,4),(6,6),(5,5),(1,1),(6,6)],
[(1,6),(5,5),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(5,5),(6,6),(3,3),(2,2),(4,4)],
[(1,6),(5,5),(6,6),(3,3),(3,3),(3,3)],
[(2,2),(3,3),(6,6),(6,6),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(6,6),(2,2),(1,6)],
[(4,4),(6,6),(2,2),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(3,3)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(4,4)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(5,5)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(4,4)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(5,5)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(3,3)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(4,4)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(5,5)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(3,3)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(4,4)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(5,5)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(4,4)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(5,5)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(3,3)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(4,4)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(5,5)],
[(1,6),(4,4),(3,3),(4,4),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(5,5),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(4,4)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(5,5),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(5,5),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(6,6),(2,2)],
[(1,6),(3,3),(4,4),(5,5),(4,4),(2,2)],
[(1,6),(3,3),(4,4),(5,5),(4,4),(3,3)],
[(1,6),(3,3),(4,4),(5,5),(4,4),(4,4)],
[(1,6),(3,3),(4,4),(5,5),(5,5),(2,2)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(4,4)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(5,5)],
[(1,6),(3,3),(5,5),(4,4),(4,4),(2,2)],
[(1,6),(3,3),(5,5),(4,4),(4,4),(3,3)],
[(1,6),(3,3),(5,5),(4,4),(4,4),(4,4)],
[(1,6),(4,4),(3,3),(5,5),(3,3),(4,4)],
[(1,6),(4,4),(3,3),(5,5),(6,6),(2,2)],
[(1,6),(4,4),(5,5),(3,3),(4,4),(3,3)],
[(1,6),(5,5),(5,5),(3,3),(4,4),(3,3)],
[(1,6),(5,5),(6,6),(2,2),(3,3),(3,3)],
[(1,6),(5,5),(6,6),(2,2),(3,3),(4,4)],
[(1,6),(5,5),(6,6),(2,2),(3,3),(5,5)],
[(1,6),(5,5),(6,6),(2,2),(4,4),(3,3)],
[(1,6),(5,5),(6,6),(2,2),(4,4),(4,4)],
[(2,2),(4,4),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(3,3),(1,6)],
[(4,4),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(4,4)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(5,5)],
[(1,6),(1,6),(2,2),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(2,2),(3,3),(6,6),(2,2)],
[(1,6),(2,2),(5,5),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(2,2),(1,6)],
[(4,4),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(4,4)],
[(1,6),(3,3),(2,2),(6,6),(5,5),(2,2)],
[(1,6),(3,3),(2,2),(6,6),(6,6),(2,2)],
[(1,6),(3,3),(3,3),(5,5),(6,6),(2,2)],
[(1,6),(4,4),(2,2),(5,5),(4,4),(4,4)],
[(1,6),(4,4),(2,2),(5,5),(4,4),(5,5)],
[(1,6),(4,4),(2,2),(5,5),(5,5),(3,3)],
[(1,6),(4,4),(2,2),(6,6),(5,5),(2,2)],
[(1,6),(4,4),(4,4),(3,3),(5,5),(3,3)],
[(1,6),(4,4),(4,4),(3,3),(6,6),(2,2)],
[(1,6),(4,4),(6,6),(2,2),(4,4),(3,3)],
[(1,6),(4,4),(6,6),(2,2),(4,4),(4,4)],
[(1,6),(4,4),(6,6),(2,2),(5,5),(2,2)],
[(1,6),(4,4),(6,6),(2,2),(5,5),(3,3)],
[(2,2),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(4,4),(3,3),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(4,4),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(2,2)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(3,3)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(4,4)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(4,4)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(5,5)],
[(1,6),(3,3),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(2,2),(1,6)],
[(1,6),(3,3),(2,2),(6,6),(4,4),(3,3)],
[(1,6),(4,4),(3,3),(4,4),(5,5),(3,3)],
[(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(6,6),(4,4),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(3,3),(4,4),(6,6),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(4,4),(2,2),(4,4),(1,6)],
[(3,3),(6,6),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(4,4)],
[(2,2),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(4,4),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(4,4),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(5,5),(6,6),(2,2),(5,5),(2,2)],
[(3,3),(5,5),(6,6),(2,2),(5,5),(3,3)]
]

def root070 : Nat := 3500

def tree070_0 : CoverTree := CoverTree.reject 2
def tree070_1 : CoverTree := CoverTree.reject 12
def tree070_2 : CoverTree := CoverTree.reject 18
def tree070_3 : CoverTree := CoverTree.reject 19
def tree070_4 : CoverTree := CoverTree.reject 3
def tree070_5 : CoverTree := CoverTree.reject 45
def tree070_6 : CoverTree := CoverTree.reject 6
def tree070_7 : CoverTree := CoverTree.reject 10
def tree070_8 : CoverTree := CoverTree.reject 65
def tree070_9 : CoverTree := CoverTree.reject 25
def tree070_10 : CoverTree := CoverTree.reject 26
def tree070_11 : CoverTree := CoverTree.reject 27
def tree070_12 : CoverTree := CoverTree.reject 28
def tree070_13 : CoverTree := CoverTree.reject 92
def tree070_14 : CoverTree := CoverTree.reject 93
def tree070_15 : CoverTree := CoverTree.split [tree070_9,tree070_10,tree070_11,tree070_12,tree070_13,tree070_14]
def tree070_16 : CoverTree := CoverTree.reject 13
def tree070_17 : CoverTree := CoverTree.reject 94
def tree070_18 : CoverTree := CoverTree.accept
def tree070_19 : CoverTree := CoverTree.split [tree070_16,tree070_17,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_20 : CoverTree := CoverTree.reject 11
def tree070_21 : CoverTree := CoverTree.split [tree070_20,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_22 : CoverTree := CoverTree.reject 8
def tree070_23 : CoverTree := CoverTree.split [tree070_22,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_24 : CoverTree := CoverTree.split [tree070_15,tree070_19,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_25 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_7,tree070_7,tree070_8,tree070_24]
def tree070_26 : CoverTree := CoverTree.reject 158
def tree070_27 : CoverTree := CoverTree.reject 159
def tree070_28 : CoverTree := CoverTree.split [tree070_9,tree070_10,tree070_11,tree070_12,tree070_26,tree070_27]
def tree070_29 : CoverTree := CoverTree.reject 34
def tree070_30 : CoverTree := CoverTree.reject 95
def tree070_31 : CoverTree := CoverTree.split [tree070_16,tree070_29,tree070_30,tree070_18,tree070_18,tree070_18]
def tree070_32 : CoverTree := CoverTree.reject 96
def tree070_33 : CoverTree := CoverTree.split [tree070_20,tree070_32,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_34 : CoverTree := CoverTree.split [tree070_28,tree070_31,tree070_33,tree070_23,tree070_18,tree070_18]
def tree070_35 : CoverTree := CoverTree.reject 97
def tree070_36 : CoverTree := CoverTree.split [tree070_9,tree070_10,tree070_11,tree070_12,tree070_18,tree070_35]
def tree070_37 : CoverTree := CoverTree.split [tree070_16,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_38 : CoverTree := CoverTree.split [tree070_36,tree070_37,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_39 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_7,tree070_7,tree070_34,tree070_38]
def tree070_40 : CoverTree := CoverTree.reject 9
def tree070_41 : CoverTree := CoverTree.reject 84
def tree070_42 : CoverTree := CoverTree.reject 15
def tree070_43 : CoverTree := CoverTree.reject 37
def tree070_44 : CoverTree := CoverTree.split [tree070_16,tree070_43,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_45 : CoverTree := CoverTree.split [tree070_42,tree070_44,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_46 : CoverTree := CoverTree.split [tree070_9,tree070_10,tree070_11,tree070_12,tree070_18,tree070_18]
def tree070_47 : CoverTree := CoverTree.split [tree070_16,tree070_29,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_48 : CoverTree := CoverTree.split [tree070_46,tree070_47,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_49 : CoverTree := CoverTree.split [tree070_46,tree070_37,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_50 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_41,tree070_45,tree070_48,tree070_49]
def tree070_51 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_5,tree070_25,tree070_39,tree070_50]
def tree070_52 : CoverTree := CoverTree.reject 85
def tree070_53 : CoverTree := CoverTree.reject 185
def tree070_54 : CoverTree := CoverTree.reject 186
def tree070_55 : CoverTree := CoverTree.reject 187
def tree070_56 : CoverTree := CoverTree.split [tree070_16,tree070_43,tree070_53,tree070_54,tree070_55,tree070_18]
def tree070_57 : CoverTree := CoverTree.reject 151
def tree070_58 : CoverTree := CoverTree.reject 152
def tree070_59 : CoverTree := CoverTree.reject 153
def tree070_60 : CoverTree := CoverTree.split [tree070_20,tree070_57,tree070_58,tree070_59,tree070_18,tree070_18]
def tree070_61 : CoverTree := CoverTree.reject 154
def tree070_62 : CoverTree := CoverTree.split [tree070_22,tree070_61,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_63 : CoverTree := CoverTree.reject 155
def tree070_64 : CoverTree := CoverTree.reject 156
def tree070_65 : CoverTree := CoverTree.split [tree070_63,tree070_64,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_66 : CoverTree := CoverTree.reject 157
def tree070_67 : CoverTree := CoverTree.split [tree070_66,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_68 : CoverTree := CoverTree.split [tree070_42,tree070_56,tree070_60,tree070_62,tree070_65,tree070_67]
def tree070_69 : CoverTree := CoverTree.reject 103
def tree070_70 : CoverTree := CoverTree.reject 119
def tree070_71 : CoverTree := CoverTree.reject 120
def tree070_72 : CoverTree := CoverTree.reject 121
def tree070_73 : CoverTree := CoverTree.split [tree070_16,tree070_29,tree070_70,tree070_71,tree070_72,tree070_18]
def tree070_74 : CoverTree := CoverTree.reject 122
def tree070_75 : CoverTree := CoverTree.reject 123
def tree070_76 : CoverTree := CoverTree.split [tree070_20,tree070_74,tree070_75,tree070_18,tree070_18,tree070_18]
def tree070_77 : CoverTree := CoverTree.reject 124
def tree070_78 : CoverTree := CoverTree.split [tree070_22,tree070_77,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_79 : CoverTree := CoverTree.reject 125
def tree070_80 : CoverTree := CoverTree.split [tree070_79,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_81 : CoverTree := CoverTree.split [tree070_69,tree070_73,tree070_76,tree070_78,tree070_80,tree070_18]
def tree070_82 : CoverTree := CoverTree.reject 104
def tree070_83 : CoverTree := CoverTree.reject 105
def tree070_84 : CoverTree := CoverTree.split [tree070_9,tree070_10,tree070_11,tree070_12,tree070_82,tree070_83]
def tree070_85 : CoverTree := CoverTree.reject 106
def tree070_86 : CoverTree := CoverTree.split [tree070_16,tree070_85,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_87 : CoverTree := CoverTree.split [tree070_84,tree070_86,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_88 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_52,tree070_68,tree070_81,tree070_87]
def tree070_89 : CoverTree := CoverTree.reject 86
def tree070_90 : CoverTree := CoverTree.reject 127
def tree070_91 : CoverTree := CoverTree.reject 128
def tree070_92 : CoverTree := CoverTree.reject 129
def tree070_93 : CoverTree := CoverTree.split [tree070_16,tree070_43,tree070_90,tree070_91,tree070_92,tree070_18]
def tree070_94 : CoverTree := CoverTree.reject 130
def tree070_95 : CoverTree := CoverTree.reject 131
def tree070_96 : CoverTree := CoverTree.split [tree070_20,tree070_94,tree070_95,tree070_18,tree070_18,tree070_18]
def tree070_97 : CoverTree := CoverTree.reject 132
def tree070_98 : CoverTree := CoverTree.split [tree070_22,tree070_97,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_99 : CoverTree := CoverTree.reject 133
def tree070_100 : CoverTree := CoverTree.split [tree070_99,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_101 : CoverTree := CoverTree.split [tree070_42,tree070_93,tree070_96,tree070_98,tree070_100,tree070_18]
def tree070_102 : CoverTree := CoverTree.reject 165
def tree070_103 : CoverTree := CoverTree.reject 166
def tree070_104 : CoverTree := CoverTree.split [tree070_9,tree070_10,tree070_11,tree070_12,tree070_102,tree070_103]
def tree070_105 : CoverTree := CoverTree.reject 107
def tree070_106 : CoverTree := CoverTree.split [tree070_16,tree070_29,tree070_105,tree070_18,tree070_18,tree070_18]
def tree070_107 : CoverTree := CoverTree.reject 108
def tree070_108 : CoverTree := CoverTree.split [tree070_20,tree070_107,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_109 : CoverTree := CoverTree.reject 109
def tree070_110 : CoverTree := CoverTree.split [tree070_109,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_111 : CoverTree := CoverTree.split [tree070_104,tree070_106,tree070_108,tree070_23,tree070_110,tree070_18]
def tree070_112 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_89,tree070_101,tree070_111,tree070_24]
def tree070_113 : CoverTree := CoverTree.reject 14
def tree070_114 : CoverTree := CoverTree.reject 42
def tree070_115 : CoverTree := CoverTree.reject 43
def tree070_116 : CoverTree := CoverTree.reject 169
def tree070_117 : CoverTree := CoverTree.reject 170
def tree070_118 : CoverTree := CoverTree.split [tree070_16,tree070_114,tree070_115,tree070_116,tree070_117,tree070_18]
def tree070_119 : CoverTree := CoverTree.reject 140
def tree070_120 : CoverTree := CoverTree.reject 141
def tree070_121 : CoverTree := CoverTree.split [tree070_20,tree070_119,tree070_120,tree070_18,tree070_18,tree070_18]
def tree070_122 : CoverTree := CoverTree.reject 142
def tree070_123 : CoverTree := CoverTree.split [tree070_22,tree070_122,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_124 : CoverTree := CoverTree.reject 38
def tree070_125 : CoverTree := CoverTree.split [tree070_124,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_126 : CoverTree := CoverTree.split [tree070_113,tree070_118,tree070_121,tree070_123,tree070_125,tree070_18]
def tree070_127 : CoverTree := CoverTree.reject 111
def tree070_128 : CoverTree := CoverTree.reject 112
def tree070_129 : CoverTree := CoverTree.split [tree070_16,tree070_43,tree070_127,tree070_128,tree070_18,tree070_18]
def tree070_130 : CoverTree := CoverTree.reject 113
def tree070_131 : CoverTree := CoverTree.reject 114
def tree070_132 : CoverTree := CoverTree.split [tree070_20,tree070_130,tree070_131,tree070_18,tree070_18,tree070_18]
def tree070_133 : CoverTree := CoverTree.reject 115
def tree070_134 : CoverTree := CoverTree.split [tree070_133,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_135 : CoverTree := CoverTree.split [tree070_42,tree070_129,tree070_132,tree070_23,tree070_134,tree070_18]
def tree070_136 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_126,tree070_135,tree070_34,tree070_38]
def tree070_137 : CoverTree := CoverTree.split [tree070_16,tree070_114,tree070_115,tree070_18,tree070_18,tree070_18]
def tree070_138 : CoverTree := CoverTree.reject 98
def tree070_139 : CoverTree := CoverTree.split [tree070_20,tree070_138,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_140 : CoverTree := CoverTree.split [tree070_113,tree070_137,tree070_139,tree070_23,tree070_125,tree070_18]
def tree070_141 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_140,tree070_45,tree070_48,tree070_49]
def tree070_142 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_88,tree070_112,tree070_136,tree070_141]
def tree070_143 : CoverTree := CoverTree.split [tree070_0,tree070_1,tree070_2,tree070_3,tree070_51,tree070_142]
def tree070_144 : CoverTree := CoverTree.reject 0
def tree070_145 : CoverTree := CoverTree.reject 29
def tree070_146 : CoverTree := CoverTree.reject 67
def tree070_147 : CoverTree := CoverTree.reject 63
def tree070_148 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_145,tree070_146,tree070_147]
def tree070_149 : CoverTree := CoverTree.reject 48
def tree070_150 : CoverTree := CoverTree.reject 68
def tree070_151 : CoverTree := CoverTree.reject 243
def tree070_152 : CoverTree := CoverTree.reject 244
def tree070_153 : CoverTree := CoverTree.split [tree070_16,tree070_17,tree070_151,tree070_152,tree070_18,tree070_18]
def tree070_154 : CoverTree := CoverTree.reject 245
def tree070_155 : CoverTree := CoverTree.reject 246
def tree070_156 : CoverTree := CoverTree.reject 247
def tree070_157 : CoverTree := CoverTree.split [tree070_20,tree070_154,tree070_155,tree070_156,tree070_18,tree070_18]
def tree070_158 : CoverTree := CoverTree.reject 248
def tree070_159 : CoverTree := CoverTree.split [tree070_22,tree070_158,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_160 : CoverTree := CoverTree.split [tree070_15,tree070_153,tree070_157,tree070_159,tree070_18,tree070_18]
def tree070_161 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_149,tree070_150,tree070_160]
def tree070_162 : CoverTree := CoverTree.reject 138
def tree070_163 : CoverTree := CoverTree.reject 249
def tree070_164 : CoverTree := CoverTree.split [tree070_20,tree070_32,tree070_163,tree070_18,tree070_18,tree070_18]
def tree070_165 : CoverTree := CoverTree.split [tree070_28,tree070_162,tree070_164,tree070_23,tree070_18,tree070_18]
def tree070_166 : CoverTree := CoverTree.reject 250
def tree070_167 : CoverTree := CoverTree.split [tree070_16,tree070_18,tree070_166,tree070_18,tree070_18,tree070_18]
def tree070_168 : CoverTree := CoverTree.split [tree070_36,tree070_167,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_169 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_149,tree070_165,tree070_168]
def tree070_170 : CoverTree := CoverTree.reject 7
def tree070_171 : CoverTree := CoverTree.reject 399
def tree070_172 : CoverTree := CoverTree.reject 400
def tree070_173 : CoverTree := CoverTree.reject 391
def tree070_174 : CoverTree := CoverTree.reject 259
def tree070_175 : CoverTree := CoverTree.reject 260
def tree070_176 : CoverTree := CoverTree.split [tree070_124,tree070_174,tree070_175,tree070_18,tree070_18,tree070_18]
def tree070_177 : CoverTree := CoverTree.reject 261
def tree070_178 : CoverTree := CoverTree.split [tree070_18,tree070_177,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_179 : CoverTree := CoverTree.split [tree070_113,tree070_171,tree070_172,tree070_173,tree070_176,tree070_178]
def tree070_180 : CoverTree := CoverTree.reject 374
def tree070_181 : CoverTree := CoverTree.reject 263
def tree070_182 : CoverTree := CoverTree.reject 264
def tree070_183 : CoverTree := CoverTree.reject 265
def tree070_184 : CoverTree := CoverTree.split [tree070_20,tree070_181,tree070_182,tree070_183,tree070_18,tree070_18]
def tree070_185 : CoverTree := CoverTree.reject 266
def tree070_186 : CoverTree := CoverTree.split [tree070_22,tree070_185,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_187 : CoverTree := CoverTree.split [tree070_42,tree070_180,tree070_184,tree070_186,tree070_18,tree070_18]
def tree070_188 : CoverTree := CoverTree.reject 171
def tree070_189 : CoverTree := CoverTree.split [tree070_188,tree070_47,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_190 : CoverTree := CoverTree.reject 293
def tree070_191 : CoverTree := CoverTree.split [tree070_46,tree070_190,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_192 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_179,tree070_187,tree070_189,tree070_191]
def tree070_193 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_148,tree070_161,tree070_169,tree070_192]
def tree070_194 : CoverTree := CoverTree.reject 30
def tree070_195 : CoverTree := CoverTree.reject 69
def tree070_196 : CoverTree := CoverTree.reject 70
def tree070_197 : CoverTree := CoverTree.reject 267
def tree070_198 : CoverTree := CoverTree.reject 268
def tree070_199 : CoverTree := CoverTree.split [tree070_16,tree070_85,tree070_197,tree070_198,tree070_18,tree070_18]
def tree070_200 : CoverTree := CoverTree.reject 269
def tree070_201 : CoverTree := CoverTree.reject 270
def tree070_202 : CoverTree := CoverTree.split [tree070_20,tree070_200,tree070_201,tree070_18,tree070_18,tree070_18]
def tree070_203 : CoverTree := CoverTree.reject 271
def tree070_204 : CoverTree := CoverTree.split [tree070_22,tree070_203,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_205 : CoverTree := CoverTree.split [tree070_84,tree070_199,tree070_202,tree070_204,tree070_18,tree070_18]
def tree070_206 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_194,tree070_195,tree070_196,tree070_205]
def tree070_207 : CoverTree := CoverTree.reject 181
def tree070_208 : CoverTree := CoverTree.reject 71
def tree070_209 : CoverTree := CoverTree.reject 272
def tree070_210 : CoverTree := CoverTree.reject 273
def tree070_211 : CoverTree := CoverTree.split [tree070_16,tree070_29,tree070_105,tree070_209,tree070_210,tree070_18]
def tree070_212 : CoverTree := CoverTree.reject 274
def tree070_213 : CoverTree := CoverTree.reject 275
def tree070_214 : CoverTree := CoverTree.split [tree070_20,tree070_107,tree070_212,tree070_213,tree070_18,tree070_18]
def tree070_215 : CoverTree := CoverTree.split [tree070_104,tree070_211,tree070_214,tree070_23,tree070_110,tree070_18]
def tree070_216 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_207,tree070_208,tree070_215,tree070_24]
def tree070_217 : CoverTree := CoverTree.reject 99
def tree070_218 : CoverTree := CoverTree.reject 72
def tree070_219 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_217,tree070_218,tree070_34,tree070_38]
def tree070_220 : CoverTree := CoverTree.reject 401
def tree070_221 : CoverTree := CoverTree.reject 392
def tree070_222 : CoverTree := CoverTree.reject 345
def tree070_223 : CoverTree := CoverTree.reject 281
def tree070_224 : CoverTree := CoverTree.reject 282
def tree070_225 : CoverTree := CoverTree.split [tree070_124,tree070_223,tree070_224,tree070_18,tree070_18,tree070_18]
def tree070_226 : CoverTree := CoverTree.reject 283
def tree070_227 : CoverTree := CoverTree.split [tree070_18,tree070_226,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_228 : CoverTree := CoverTree.split [tree070_113,tree070_220,tree070_221,tree070_222,tree070_225,tree070_227]
def tree070_229 : CoverTree := CoverTree.reject 393
def tree070_230 : CoverTree := CoverTree.reject 375
def tree070_231 : CoverTree := CoverTree.reject 288
def tree070_232 : CoverTree := CoverTree.split [tree070_22,tree070_231,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_233 : CoverTree := CoverTree.split [tree070_42,tree070_229,tree070_230,tree070_232,tree070_18,tree070_18]
def tree070_234 : CoverTree := CoverTree.reject 289
def tree070_235 : CoverTree := CoverTree.split [tree070_9,tree070_10,tree070_11,tree070_12,tree070_18,tree070_234]
def tree070_236 : CoverTree := CoverTree.split [tree070_235,tree070_47,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_237 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_228,tree070_233,tree070_236,tree070_49]
def tree070_238 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_206,tree070_216,tree070_219,tree070_237]
def tree070_239 : CoverTree := CoverTree.reject 116
def tree070_240 : CoverTree := CoverTree.reject 73
def tree070_241 : CoverTree := CoverTree.reject 66
def tree070_242 : CoverTree := CoverTree.reject 290
def tree070_243 : CoverTree := CoverTree.split [tree070_22,tree070_242,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_244 : CoverTree := CoverTree.split [tree070_84,tree070_86,tree070_21,tree070_243,tree070_18,tree070_18]
def tree070_245 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_239,tree070_240,tree070_241,tree070_244]
def tree070_246 : CoverTree := CoverTree.reject 88
def tree070_247 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_246,tree070_101,tree070_111,tree070_24]
def tree070_248 : CoverTree := CoverTree.reject 89
def tree070_249 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_248,tree070_135,tree070_34,tree070_38]
def tree070_250 : CoverTree := CoverTree.reject 291
def tree070_251 : CoverTree := CoverTree.split [tree070_16,tree070_114,tree070_115,tree070_250,tree070_18,tree070_18]
def tree070_252 : CoverTree := CoverTree.reject 292
def tree070_253 : CoverTree := CoverTree.split [tree070_20,tree070_138,tree070_252,tree070_18,tree070_18,tree070_18]
def tree070_254 : CoverTree := CoverTree.split [tree070_113,tree070_251,tree070_253,tree070_23,tree070_125,tree070_18]
def tree070_255 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_254,tree070_45,tree070_48,tree070_49]
def tree070_256 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_245,tree070_247,tree070_249,tree070_255]
def tree070_257 : CoverTree := CoverTree.reject 90
def tree070_258 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_257,tree070_68,tree070_81,tree070_87]
def tree070_259 : CoverTree := CoverTree.reject 240
def tree070_260 : CoverTree := CoverTree.reject 241
def tree070_261 : CoverTree := CoverTree.split [tree070_16,tree070_114,tree070_115,tree070_259,tree070_260,tree070_18]
def tree070_262 : CoverTree := CoverTree.reject 188
def tree070_263 : CoverTree := CoverTree.reject 189
def tree070_264 : CoverTree := CoverTree.reject 190
def tree070_265 : CoverTree := CoverTree.split [tree070_20,tree070_262,tree070_263,tree070_264,tree070_18,tree070_18]
def tree070_266 : CoverTree := CoverTree.reject 191
def tree070_267 : CoverTree := CoverTree.reject 192
def tree070_268 : CoverTree := CoverTree.split [tree070_22,tree070_266,tree070_267,tree070_18,tree070_18,tree070_18]
def tree070_269 : CoverTree := CoverTree.reject 143
def tree070_270 : CoverTree := CoverTree.split [tree070_124,tree070_269,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_271 : CoverTree := CoverTree.reject 139
def tree070_272 : CoverTree := CoverTree.split [tree070_271,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_273 : CoverTree := CoverTree.split [tree070_113,tree070_261,tree070_265,tree070_268,tree070_270,tree070_272]
def tree070_274 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_273,tree070_101,tree070_111,tree070_24]
def tree070_275 : CoverTree := CoverTree.reject 376
def tree070_276 : CoverTree := CoverTree.reject 346
def tree070_277 : CoverTree := CoverTree.split [tree070_113,tree070_275,tree070_276,tree070_23,tree070_125,tree070_18]
def tree070_278 : CoverTree := CoverTree.split [tree070_40,tree070_40,tree070_277,tree070_45,tree070_48,tree070_49]
def tree070_279 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_258,tree070_274,tree070_136,tree070_278]
def tree070_280 : CoverTree := CoverTree.split [tree070_0,tree070_1,tree070_193,tree070_238,tree070_256,tree070_279]
def tree070_281 : CoverTree := CoverTree.reject 137
def tree070_282 : CoverTree := CoverTree.reject 46
def tree070_283 : CoverTree := CoverTree.reject 172
def tree070_284 : CoverTree := CoverTree.reject 22
def tree070_285 : CoverTree := CoverTree.reject 5
def tree070_286 : CoverTree := CoverTree.reject 320
def tree070_287 : CoverTree := CoverTree.split [tree070_285,tree070_285,tree070_285,tree070_286,tree070_18,tree070_18]
def tree070_288 : CoverTree := CoverTree.split [tree070_285,tree070_285,tree070_285,tree070_18,tree070_18,tree070_18]
def tree070_289 : CoverTree := CoverTree.split [tree070_284,tree070_284,tree070_287,tree070_288,tree070_288,tree070_288]
def tree070_290 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_282,tree070_283,tree070_289]
def tree070_291 : CoverTree := CoverTree.split [tree070_284,tree070_284,tree070_288,tree070_288,tree070_288,tree070_288]
def tree070_292 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_282,tree070_283,tree070_291]
def tree070_293 : CoverTree := CoverTree.reject 44
def tree070_294 : CoverTree := CoverTree.reject 182
def tree070_295 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_293,tree070_294,tree070_291,tree070_291]
def tree070_296 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_281,tree070_290,tree070_292,tree070_295]
def tree070_297 : CoverTree := CoverTree.reject 74
def tree070_298 : CoverTree := CoverTree.reject 134
def tree070_299 : CoverTree := CoverTree.reject 321
def tree070_300 : CoverTree := CoverTree.reject 322
def tree070_301 : CoverTree := CoverTree.split [tree070_20,tree070_299,tree070_300,tree070_18,tree070_18,tree070_18]
def tree070_302 : CoverTree := CoverTree.reject 323
def tree070_303 : CoverTree := CoverTree.split [tree070_22,tree070_302,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_304 : CoverTree := CoverTree.reject 324
def tree070_305 : CoverTree := CoverTree.reject 325
def tree070_306 : CoverTree := CoverTree.split [tree070_18,tree070_304,tree070_305,tree070_18,tree070_18,tree070_18]
def tree070_307 : CoverTree := CoverTree.reject 326
def tree070_308 : CoverTree := CoverTree.split [tree070_18,tree070_307,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_309 : CoverTree := CoverTree.split [tree070_84,tree070_298,tree070_301,tree070_303,tree070_306,tree070_308]
def tree070_310 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_145,tree070_297,tree070_309]
def tree070_311 : CoverTree := CoverTree.reject 75
def tree070_312 : CoverTree := CoverTree.reject 162
def tree070_313 : CoverTree := CoverTree.reject 135
def tree070_314 : CoverTree := CoverTree.reject 327
def tree070_315 : CoverTree := CoverTree.reject 328
def tree070_316 : CoverTree := CoverTree.reject 329
def tree070_317 : CoverTree := CoverTree.split [tree070_22,tree070_314,tree070_315,tree070_316,tree070_18,tree070_18]
def tree070_318 : CoverTree := CoverTree.reject 330
def tree070_319 : CoverTree := CoverTree.split [tree070_109,tree070_318,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_320 : CoverTree := CoverTree.split [tree070_104,tree070_312,tree070_313,tree070_317,tree070_319,tree070_18]
def tree070_321 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_311,tree070_320,tree070_160]
def tree070_322 : CoverTree := CoverTree.reject 200
def tree070_323 : CoverTree := CoverTree.reject 331
def tree070_324 : CoverTree := CoverTree.reject 332
def tree070_325 : CoverTree := CoverTree.split [tree070_20,tree070_130,tree070_131,tree070_323,tree070_324,tree070_18]
def tree070_326 : CoverTree := CoverTree.reject 333
def tree070_327 : CoverTree := CoverTree.reject 334
def tree070_328 : CoverTree := CoverTree.reject 335
def tree070_329 : CoverTree := CoverTree.split [tree070_22,tree070_326,tree070_327,tree070_328,tree070_18,tree070_18]
def tree070_330 : CoverTree := CoverTree.split [tree070_42,tree070_322,tree070_325,tree070_329,tree070_134,tree070_18]
def tree070_331 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_330,tree070_165,tree070_168]
def tree070_332 : CoverTree := CoverTree.reject 402
def tree070_333 : CoverTree := CoverTree.reject 403
def tree070_334 : CoverTree := CoverTree.reject 394
def tree070_335 : CoverTree := CoverTree.split [tree070_113,tree070_332,tree070_333,tree070_334,tree070_176,tree070_178]
def tree070_336 : CoverTree := CoverTree.reject 377
def tree070_337 : CoverTree := CoverTree.split [tree070_42,tree070_336,tree070_184,tree070_186,tree070_18,tree070_18]
def tree070_338 : CoverTree := CoverTree.reject 294
def tree070_339 : CoverTree := CoverTree.split [tree070_46,tree070_338,tree070_21,tree070_23,tree070_18,tree070_18]
def tree070_340 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_335,tree070_337,tree070_189,tree070_339]
def tree070_341 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_310,tree070_321,tree070_331,tree070_340]
def tree070_342 : CoverTree := CoverTree.reject 76
def tree070_343 : CoverTree := CoverTree.reject 318
def tree070_344 : CoverTree := CoverTree.reject 336
def tree070_345 : CoverTree := CoverTree.split [tree070_20,tree070_74,tree070_75,tree070_344,tree070_18,tree070_18]
def tree070_346 : CoverTree := CoverTree.reject 337
def tree070_347 : CoverTree := CoverTree.split [tree070_18,tree070_346,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_348 : CoverTree := CoverTree.split [tree070_69,tree070_343,tree070_345,tree070_78,tree070_80,tree070_347]
def tree070_349 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_194,tree070_342,tree070_348,tree070_205]
def tree070_350 : CoverTree := CoverTree.reject 183
def tree070_351 : CoverTree := CoverTree.reject 77
def tree070_352 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_350,tree070_351,tree070_215,tree070_24]
def tree070_353 : CoverTree := CoverTree.reject 62
def tree070_354 : CoverTree := CoverTree.reject 338
def tree070_355 : CoverTree := CoverTree.split [tree070_22,tree070_122,tree070_354,tree070_18,tree070_18,tree070_18]
def tree070_356 : CoverTree := CoverTree.split [tree070_113,tree070_353,tree070_121,tree070_355,tree070_125,tree070_18]
def tree070_357 : CoverTree := CoverTree.reject 202
def tree070_358 : CoverTree := CoverTree.split [tree070_42,tree070_357,tree070_132,tree070_23,tree070_134,tree070_18]
def tree070_359 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_356,tree070_358,tree070_34,tree070_38]
def tree070_360 : CoverTree := CoverTree.reject 58
def tree070_361 : CoverTree := CoverTree.reject 110
def tree070_362 : CoverTree := CoverTree.reject 276
def tree070_363 : CoverTree := CoverTree.reject 277
def tree070_364 : CoverTree := CoverTree.split [tree070_16,tree070_114,tree070_115,tree070_362,tree070_363,tree070_18]
def tree070_365 : CoverTree := CoverTree.reject 278
def tree070_366 : CoverTree := CoverTree.reject 279
def tree070_367 : CoverTree := CoverTree.split [tree070_20,tree070_138,tree070_365,tree070_366,tree070_18,tree070_18]
def tree070_368 : CoverTree := CoverTree.reject 280
def tree070_369 : CoverTree := CoverTree.split [tree070_22,tree070_18,tree070_368,tree070_18,tree070_18,tree070_18]
def tree070_370 : CoverTree := CoverTree.split [tree070_113,tree070_364,tree070_367,tree070_369,tree070_225,tree070_227]
def tree070_371 : CoverTree := CoverTree.reject 395
def tree070_372 : CoverTree := CoverTree.reject 286
def tree070_373 : CoverTree := CoverTree.reject 287
def tree070_374 : CoverTree := CoverTree.split [tree070_20,tree070_372,tree070_373,tree070_18,tree070_18,tree070_18]
def tree070_375 : CoverTree := CoverTree.split [tree070_42,tree070_371,tree070_374,tree070_232,tree070_18,tree070_18]
def tree070_376 : CoverTree := CoverTree.split [tree070_360,tree070_361,tree070_370,tree070_375,tree070_236,tree070_49]
def tree070_377 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_349,tree070_352,tree070_359,tree070_376]
def tree070_378 : CoverTree := CoverTree.reject 117
def tree070_379 : CoverTree := CoverTree.reject 136
def tree070_380 : CoverTree := CoverTree.split [tree070_42,tree070_379,tree070_60,tree070_62,tree070_65,tree070_67]
def tree070_381 : CoverTree := CoverTree.reject 319
def tree070_382 : CoverTree := CoverTree.split [tree070_69,tree070_381,tree070_76,tree070_78,tree070_80,tree070_18]
def tree070_383 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_378,tree070_380,tree070_382,tree070_244]
def tree070_384 : CoverTree := CoverTree.reject 91
def tree070_385 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_384,tree070_101,tree070_111,tree070_24]
def tree070_386 : CoverTree := CoverTree.reject 339
def tree070_387 : CoverTree := CoverTree.split [tree070_22,tree070_122,tree070_386,tree070_18,tree070_18,tree070_18]
def tree070_388 : CoverTree := CoverTree.split [tree070_113,tree070_118,tree070_121,tree070_387,tree070_125,tree070_18]
def tree070_389 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_388,tree070_135,tree070_34,tree070_38]
def tree070_390 : CoverTree := CoverTree.reject 4
def tree070_391 : CoverTree := CoverTree.reject 24
def tree070_392 : CoverTree := CoverTree.reject 21
def tree070_393 : CoverTree := CoverTree.reject 145
def tree070_394 : CoverTree := CoverTree.reject 146
def tree070_395 : CoverTree := CoverTree.reject 147
def tree070_396 : CoverTree := CoverTree.reject 194
def tree070_397 : CoverTree := CoverTree.reject 195
def tree070_398 : CoverTree := CoverTree.split [tree070_393,tree070_394,tree070_395,tree070_396,tree070_397,tree070_18]
def tree070_399 : CoverTree := CoverTree.reject 184
def tree070_400 : CoverTree := CoverTree.reject 196
def tree070_401 : CoverTree := CoverTree.reject 197
def tree070_402 : CoverTree := CoverTree.reject 198
def tree070_403 : CoverTree := CoverTree.reject 199
def tree070_404 : CoverTree := CoverTree.split [tree070_399,tree070_400,tree070_401,tree070_402,tree070_403,tree070_18]
def tree070_405 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_391,tree070_392,tree070_398,tree070_404]
def tree070_406 : CoverTree := CoverTree.reject 64
def tree070_407 : CoverTree := CoverTree.reject 340
def tree070_408 : CoverTree := CoverTree.reject 341
def tree070_409 : CoverTree := CoverTree.reject 342
def tree070_410 : CoverTree := CoverTree.split [tree070_20,tree070_406,tree070_407,tree070_408,tree070_409,tree070_18]
def tree070_411 : CoverTree := CoverTree.reject 167
def tree070_412 : CoverTree := CoverTree.reject 343
def tree070_413 : CoverTree := CoverTree.reject 344
def tree070_414 : CoverTree := CoverTree.split [tree070_22,tree070_411,tree070_412,tree070_413,tree070_18,tree070_18]
def tree070_415 : CoverTree := CoverTree.reject 60
def tree070_416 : CoverTree := CoverTree.reject 406
def tree070_417 : CoverTree := CoverTree.reject 407
def tree070_418 : CoverTree := CoverTree.split [tree070_415,tree070_416,tree070_417,tree070_18,tree070_18,tree070_18]
def tree070_419 : CoverTree := CoverTree.reject 168
def tree070_420 : CoverTree := CoverTree.split [tree070_419,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_421 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_410,tree070_414,tree070_418,tree070_420]
def tree070_422 : CoverTree := CoverTree.split [tree070_405,tree070_421,tree070_254,tree070_45,tree070_48,tree070_49]
def tree070_423 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_383,tree070_385,tree070_389,tree070_422]
def tree070_424 : CoverTree := CoverTree.reject 40
def tree070_425 : CoverTree := CoverTree.reject 102
def tree070_426 : CoverTree := CoverTree.reject 296
def tree070_427 : CoverTree := CoverTree.reject 297
def tree070_428 : CoverTree := CoverTree.reject 298
def tree070_429 : CoverTree := CoverTree.reject 299
def tree070_430 : CoverTree := CoverTree.split [tree070_22,tree070_426,tree070_427,tree070_428,tree070_429,tree070_18]
def tree070_431 : CoverTree := CoverTree.reject 300
def tree070_432 : CoverTree := CoverTree.reject 301
def tree070_433 : CoverTree := CoverTree.reject 302
def tree070_434 : CoverTree := CoverTree.reject 303
def tree070_435 : CoverTree := CoverTree.split [tree070_415,tree070_431,tree070_432,tree070_433,tree070_434,tree070_18]
def tree070_436 : CoverTree := CoverTree.reject 304
def tree070_437 : CoverTree := CoverTree.split [tree070_436,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_438 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_425,tree070_430,tree070_435,tree070_437]
def tree070_439 : CoverTree := CoverTree.reject 164
def tree070_440 : CoverTree := CoverTree.reject 305
def tree070_441 : CoverTree := CoverTree.reject 306
def tree070_442 : CoverTree := CoverTree.reject 307
def tree070_443 : CoverTree := CoverTree.reject 308
def tree070_444 : CoverTree := CoverTree.split [tree070_20,tree070_440,tree070_441,tree070_442,tree070_443,tree070_18]
def tree070_445 : CoverTree := CoverTree.reject 217
def tree070_446 : CoverTree := CoverTree.reject 218
def tree070_447 : CoverTree := CoverTree.reject 219
def tree070_448 : CoverTree := CoverTree.reject 220
def tree070_449 : CoverTree := CoverTree.split [tree070_22,tree070_445,tree070_446,tree070_447,tree070_448,tree070_18]
def tree070_450 : CoverTree := CoverTree.reject 221
def tree070_451 : CoverTree := CoverTree.reject 222
def tree070_452 : CoverTree := CoverTree.split [tree070_124,tree070_450,tree070_451,tree070_18,tree070_18,tree070_18]
def tree070_453 : CoverTree := CoverTree.reject 203
def tree070_454 : CoverTree := CoverTree.split [tree070_453,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_455 : CoverTree := CoverTree.split [tree070_113,tree070_439,tree070_444,tree070_449,tree070_452,tree070_454]
def tree070_456 : CoverTree := CoverTree.split [tree070_424,tree070_438,tree070_455,tree070_68,tree070_81,tree070_87]
def tree070_457 : CoverTree := CoverTree.reject 41
def tree070_458 : CoverTree := CoverTree.reject 309
def tree070_459 : CoverTree := CoverTree.reject 310
def tree070_460 : CoverTree := CoverTree.reject 311
def tree070_461 : CoverTree := CoverTree.split [tree070_20,tree070_406,tree070_458,tree070_459,tree070_460,tree070_18]
def tree070_462 : CoverTree := CoverTree.reject 233
def tree070_463 : CoverTree := CoverTree.reject 234
def tree070_464 : CoverTree := CoverTree.reject 235
def tree070_465 : CoverTree := CoverTree.reject 236
def tree070_466 : CoverTree := CoverTree.split [tree070_22,tree070_462,tree070_463,tree070_464,tree070_465,tree070_18]
def tree070_467 : CoverTree := CoverTree.reject 237
def tree070_468 : CoverTree := CoverTree.reject 238
def tree070_469 : CoverTree := CoverTree.split [tree070_415,tree070_467,tree070_468,tree070_18,tree070_18,tree070_18]
def tree070_470 : CoverTree := CoverTree.reject 239
def tree070_471 : CoverTree := CoverTree.split [tree070_470,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_472 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_461,tree070_466,tree070_469,tree070_471]
def tree070_473 : CoverTree := CoverTree.split [tree070_457,tree070_472,tree070_273,tree070_101,tree070_111,tree070_24]
def tree070_474 : CoverTree := CoverTree.reject 397
def tree070_475 : CoverTree := CoverTree.reject 314
def tree070_476 : CoverTree := CoverTree.reject 315
def tree070_477 : CoverTree := CoverTree.reject 316
def tree070_478 : CoverTree := CoverTree.split [tree070_20,tree070_406,tree070_475,tree070_476,tree070_477,tree070_18]
def tree070_479 : CoverTree := CoverTree.reject 223
def tree070_480 : CoverTree := CoverTree.reject 224
def tree070_481 : CoverTree := CoverTree.reject 225
def tree070_482 : CoverTree := CoverTree.split [tree070_22,tree070_479,tree070_480,tree070_481,tree070_18,tree070_18]
def tree070_483 : CoverTree := CoverTree.reject 226
def tree070_484 : CoverTree := CoverTree.reject 227
def tree070_485 : CoverTree := CoverTree.split [tree070_415,tree070_483,tree070_484,tree070_18,tree070_18,tree070_18]
def tree070_486 : CoverTree := CoverTree.reject 193
def tree070_487 : CoverTree := CoverTree.split [tree070_486,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_488 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_478,tree070_482,tree070_485,tree070_487]
def tree070_489 : CoverTree := CoverTree.split [tree070_474,tree070_488,tree070_126,tree070_135,tree070_34,tree070_38]
def tree070_490 : CoverTree := CoverTree.split [tree070_20,tree070_406,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_491 : CoverTree := CoverTree.split [tree070_22,tree070_411,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_492 : CoverTree := CoverTree.split [tree070_415,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_493 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_490,tree070_491,tree070_492,tree070_420]
def tree070_494 : CoverTree := CoverTree.split [tree070_405,tree070_493,tree070_140,tree070_45,tree070_48,tree070_49]
def tree070_495 : CoverTree := CoverTree.split [tree070_4,tree070_4,tree070_456,tree070_473,tree070_489,tree070_494]
def tree070_496 : CoverTree := CoverTree.split [tree070_0,tree070_296,tree070_341,tree070_377,tree070_423,tree070_495]
def tree070_497 : CoverTree := CoverTree.reject 35
def tree070_498 : CoverTree := CoverTree.reject 173
def tree070_499 : CoverTree := CoverTree.reject 360
def tree070_500 : CoverTree := CoverTree.split [tree070_285,tree070_285,tree070_285,tree070_499,tree070_18,tree070_18]
def tree070_501 : CoverTree := CoverTree.split [tree070_284,tree070_284,tree070_500,tree070_288,tree070_288,tree070_288]
def tree070_502 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_282,tree070_498,tree070_501]
def tree070_503 : CoverTree := CoverTree.reject 359
def tree070_504 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_282,tree070_503,tree070_289]
def tree070_505 : CoverTree := CoverTree.reject 61
def tree070_506 : CoverTree := CoverTree.split [tree070_284,tree070_284,tree070_505,tree070_505,tree070_288,tree070_288]
def tree070_507 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_282,tree070_506,tree070_291]
def tree070_508 : CoverTree := CoverTree.reject 160
def tree070_509 : CoverTree := CoverTree.split [tree070_42,tree070_284,tree070_508,tree070_288,tree070_288,tree070_288]
def tree070_510 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_293,tree070_509,tree070_291,tree070_291]
def tree070_511 : CoverTree := CoverTree.split [tree070_497,tree070_497,tree070_502,tree070_504,tree070_507,tree070_510]
def tree070_512 : CoverTree := CoverTree.reject 23
def tree070_513 : CoverTree := CoverTree.reject 49
def tree070_514 : CoverTree := CoverTree.reject 50
def tree070_515 : CoverTree := CoverTree.reject 1
def tree070_516 : CoverTree := CoverTree.reject 347
def tree070_517 : CoverTree := CoverTree.reject 150
def tree070_518 : CoverTree := CoverTree.reject 361
def tree070_519 : CoverTree := CoverTree.split [tree070_517,tree070_518,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_520 : CoverTree := CoverTree.reject 362
def tree070_521 : CoverTree := CoverTree.split [tree070_18,tree070_520,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_522 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_516,tree070_519,tree070_521]
def tree070_523 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_513,tree070_514,tree070_522]
def tree070_524 : CoverTree := CoverTree.reject 357
def tree070_525 : CoverTree := CoverTree.reject 178
def tree070_526 : CoverTree := CoverTree.reject 161
def tree070_527 : CoverTree := CoverTree.reject 363
def tree070_528 : CoverTree := CoverTree.split [tree070_18,tree070_527,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_529 : CoverTree := CoverTree.split [tree070_69,tree070_524,tree070_525,tree070_526,tree070_80,tree070_528]
def tree070_530 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_145,tree070_529,tree070_309]
def tree070_531 : CoverTree := CoverTree.reject 78
def tree070_532 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_531,tree070_320,tree070_160]
def tree070_533 : CoverTree := CoverTree.reject 404
def tree070_534 : CoverTree := CoverTree.reject 405
def tree070_535 : CoverTree := CoverTree.reject 256
def tree070_536 : CoverTree := CoverTree.reject 257
def tree070_537 : CoverTree := CoverTree.reject 258
def tree070_538 : CoverTree := CoverTree.split [tree070_22,tree070_535,tree070_536,tree070_537,tree070_18,tree070_18]
def tree070_539 : CoverTree := CoverTree.split [tree070_113,tree070_533,tree070_534,tree070_538,tree070_176,tree070_178]
def tree070_540 : CoverTree := CoverTree.reject 378
def tree070_541 : CoverTree := CoverTree.split [tree070_42,tree070_540,tree070_184,tree070_186,tree070_18,tree070_18]
def tree070_542 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_539,tree070_541,tree070_189,tree070_49]
def tree070_543 : CoverTree := CoverTree.split [tree070_512,tree070_523,tree070_530,tree070_532,tree070_331,tree070_542]
def tree070_544 : CoverTree := CoverTree.reject 20
def tree070_545 : CoverTree := CoverTree.reject 57
def tree070_546 : CoverTree := CoverTree.reject 51
def tree070_547 : CoverTree := CoverTree.reject 174
def tree070_548 : CoverTree := CoverTree.reject 175
def tree070_549 : CoverTree := CoverTree.reject 364
def tree070_550 : CoverTree := CoverTree.reject 365
def tree070_551 : CoverTree := CoverTree.split [tree070_22,tree070_547,tree070_548,tree070_549,tree070_550,tree070_18]
def tree070_552 : CoverTree := CoverTree.reject 176
def tree070_553 : CoverTree := CoverTree.reject 177
def tree070_554 : CoverTree := CoverTree.reject 366
def tree070_555 : CoverTree := CoverTree.split [tree070_552,tree070_553,tree070_554,tree070_18,tree070_18,tree070_18]
def tree070_556 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_551,tree070_555,tree070_18]
def tree070_557 : CoverTree := CoverTree.reject 149
def tree070_558 : CoverTree := CoverTree.split [tree070_22,tree070_557,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_559 : CoverTree := CoverTree.reject 367
def tree070_560 : CoverTree := CoverTree.split [tree070_517,tree070_559,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_561 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_558,tree070_560,tree070_18]
def tree070_562 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_545,tree070_546,tree070_556,tree070_561]
def tree070_563 : CoverTree := CoverTree.reject 79
def tree070_564 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_194,tree070_563,tree070_348,tree070_205]
def tree070_565 : CoverTree := CoverTree.reject 80
def tree070_566 : CoverTree := CoverTree.reject 81
def tree070_567 : CoverTree := CoverTree.reject 368
def tree070_568 : CoverTree := CoverTree.split [tree070_124,tree070_269,tree070_567,tree070_18,tree070_18,tree070_18]
def tree070_569 : CoverTree := CoverTree.reject 369
def tree070_570 : CoverTree := CoverTree.split [tree070_271,tree070_569,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_571 : CoverTree := CoverTree.split [tree070_113,tree070_353,tree070_565,tree070_566,tree070_568,tree070_570]
def tree070_572 : CoverTree := CoverTree.reject 358
def tree070_573 : CoverTree := CoverTree.reject 179
def tree070_574 : CoverTree := CoverTree.split [tree070_42,tree070_572,tree070_573,tree070_98,tree070_100,tree070_18]
def tree070_575 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_571,tree070_574,tree070_215,tree070_24]
def tree070_576 : CoverTree := CoverTree.reject 163
def tree070_577 : CoverTree := CoverTree.reject 370
def tree070_578 : CoverTree := CoverTree.reject 371
def tree070_579 : CoverTree := CoverTree.split [tree070_22,tree070_411,tree070_577,tree070_578,tree070_18,tree070_18]
def tree070_580 : CoverTree := CoverTree.reject 372
def tree070_581 : CoverTree := CoverTree.reject 373
def tree070_582 : CoverTree := CoverTree.split [tree070_415,tree070_580,tree070_581,tree070_18,tree070_18,tree070_18]
def tree070_583 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_576,tree070_579,tree070_582,tree070_420]
def tree070_584 : CoverTree := CoverTree.reject 284
def tree070_585 : CoverTree := CoverTree.reject 285
def tree070_586 : CoverTree := CoverTree.split [tree070_16,tree070_43,tree070_584,tree070_585,tree070_18,tree070_18]
def tree070_587 : CoverTree := CoverTree.split [tree070_42,tree070_586,tree070_374,tree070_232,tree070_18,tree070_18]
def tree070_588 : CoverTree := CoverTree.split [tree070_360,tree070_583,tree070_370,tree070_587,tree070_236,tree070_49]
def tree070_589 : CoverTree := CoverTree.split [tree070_544,tree070_562,tree070_564,tree070_575,tree070_359,tree070_588]
def tree070_590 : CoverTree := CoverTree.reject 33
def tree070_591 : CoverTree := CoverTree.reject 31
def tree070_592 : CoverTree := CoverTree.reject 52
def tree070_593 : CoverTree := CoverTree.reject 53
def tree070_594 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_590,tree070_591,tree070_592,tree070_593]
def tree070_595 : CoverTree := CoverTree.reject 59
def tree070_596 : CoverTree := CoverTree.reject 209
def tree070_597 : CoverTree := CoverTree.reject 210
def tree070_598 : CoverTree := CoverTree.reject 211
def tree070_599 : CoverTree := CoverTree.split [tree070_22,tree070_596,tree070_597,tree070_598,tree070_18,tree070_18]
def tree070_600 : CoverTree := CoverTree.reject 212
def tree070_601 : CoverTree := CoverTree.reject 213
def tree070_602 : CoverTree := CoverTree.reject 214
def tree070_603 : CoverTree := CoverTree.split [tree070_600,tree070_601,tree070_602,tree070_18,tree070_18,tree070_18]
def tree070_604 : CoverTree := CoverTree.reject 215
def tree070_605 : CoverTree := CoverTree.reject 216
def tree070_606 : CoverTree := CoverTree.split [tree070_604,tree070_605,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_607 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_599,tree070_603,tree070_606]
def tree070_608 : CoverTree := CoverTree.split [tree070_22,tree070_547,tree070_548,tree070_18,tree070_18,tree070_18]
def tree070_609 : CoverTree := CoverTree.split [tree070_552,tree070_553,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_610 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_608,tree070_609,tree070_18]
def tree070_611 : CoverTree := CoverTree.split [tree070_517,tree070_18,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_612 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_558,tree070_611,tree070_18]
def tree070_613 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_595,tree070_607,tree070_610,tree070_612]
def tree070_614 : CoverTree := CoverTree.reject 118
def tree070_615 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_614,tree070_380,tree070_382,tree070_244]
def tree070_616 : CoverTree := CoverTree.reject 180
def tree070_617 : CoverTree := CoverTree.split [tree070_113,tree070_616,tree070_265,tree070_268,tree070_270,tree070_272]
def tree070_618 : CoverTree := CoverTree.split [tree070_6,tree070_6,tree070_617,tree070_101,tree070_111,tree070_24]
def tree070_619 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_410,tree070_414,tree070_492,tree070_420]
def tree070_620 : CoverTree := CoverTree.split [tree070_405,tree070_619,tree070_254,tree070_45,tree070_48,tree070_49]
def tree070_621 : CoverTree := CoverTree.split [tree070_594,tree070_613,tree070_615,tree070_618,tree070_389,tree070_620]
def tree070_622 : CoverTree := CoverTree.reject 56
def tree070_623 : CoverTree := CoverTree.reject 39
def tree070_624 : CoverTree := CoverTree.reject 54
def tree070_625 : CoverTree := CoverTree.reject 55
def tree070_626 : CoverTree := CoverTree.split [tree070_622,tree070_623,tree070_590,tree070_591,tree070_624,tree070_625]
def tree070_627 : CoverTree := CoverTree.reject 47
def tree070_628 : CoverTree := CoverTree.reject 230
def tree070_629 : CoverTree := CoverTree.reject 295
def tree070_630 : CoverTree := CoverTree.reject 350
def tree070_631 : CoverTree := CoverTree.reject 351
def tree070_632 : CoverTree := CoverTree.reject 352
def tree070_633 : CoverTree := CoverTree.reject 353
def tree070_634 : CoverTree := CoverTree.split [tree070_124,tree070_630,tree070_631,tree070_632,tree070_633,tree070_18]
def tree070_635 : CoverTree := CoverTree.reject 354
def tree070_636 : CoverTree := CoverTree.reject 355
def tree070_637 : CoverTree := CoverTree.split [tree070_635,tree070_636,tree070_18,tree070_18,tree070_18,tree070_18]
def tree070_638 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_629,tree070_634,tree070_637]
def tree070_639 : CoverTree := CoverTree.split [tree070_627,tree070_628,tree070_638,tree070_607,tree070_610,tree070_612]
def tree070_640 : CoverTree := CoverTree.reject 312
def tree070_641 : CoverTree := CoverTree.reject 313
def tree070_642 : CoverTree := CoverTree.split [tree070_393,tree070_394,tree070_395,tree070_640,tree070_641,tree070_18]
def tree070_643 : CoverTree := CoverTree.reject 87
def tree070_644 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_391,tree070_392,tree070_642,tree070_643]
def tree070_645 : CoverTree := CoverTree.split [tree070_644,tree070_488,tree070_126,tree070_135,tree070_34,tree070_38]
def tree070_646 : CoverTree := CoverTree.split [tree070_626,tree070_639,tree070_456,tree070_473,tree070_645,tree070_494]
def tree070_647 : CoverTree := CoverTree.split [tree070_0,tree070_511,tree070_543,tree070_589,tree070_621,tree070_646]
def tree070_648 : CoverTree := CoverTree.reject 17
def tree070_649 : CoverTree := CoverTree.split [tree070_648,tree070_648,tree070_648,tree070_648,tree070_648,tree070_288]
def tree070_650 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_282,tree070_649,tree070_289]
def tree070_651 : CoverTree := CoverTree.split [tree070_497,tree070_497,tree070_502,tree070_650,tree070_507,tree070_510]
def tree070_652 : CoverTree := CoverTree.reject 389
def tree070_653 : CoverTree := CoverTree.split [tree070_22,tree070_557,tree070_652,tree070_18,tree070_18,tree070_18]
def tree070_654 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_653,tree070_519,tree070_521]
def tree070_655 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_513,tree070_514,tree070_654]
def tree070_656 : CoverTree := CoverTree.reject 387
def tree070_657 : CoverTree := CoverTree.reject 228
def tree070_658 : CoverTree := CoverTree.split [tree070_42,tree070_656,tree070_657,tree070_98,tree070_100,tree070_18]
def tree070_659 : CoverTree := CoverTree.split [tree070_144,tree070_144,tree070_144,tree070_658,tree070_320,tree070_160]
def tree070_660 : CoverTree := CoverTree.reject 251
def tree070_661 : CoverTree := CoverTree.reject 252
def tree070_662 : CoverTree := CoverTree.split [tree070_16,tree070_114,tree070_115,tree070_660,tree070_661,tree070_18]
def tree070_663 : CoverTree := CoverTree.reject 253
def tree070_664 : CoverTree := CoverTree.reject 254
def tree070_665 : CoverTree := CoverTree.reject 255
def tree070_666 : CoverTree := CoverTree.split [tree070_20,tree070_138,tree070_663,tree070_664,tree070_665,tree070_18]
def tree070_667 : CoverTree := CoverTree.split [tree070_113,tree070_662,tree070_666,tree070_538,tree070_176,tree070_178]
def tree070_668 : CoverTree := CoverTree.reject 262
def tree070_669 : CoverTree := CoverTree.split [tree070_16,tree070_43,tree070_18,tree070_668,tree070_18,tree070_18]
def tree070_670 : CoverTree := CoverTree.split [tree070_42,tree070_669,tree070_184,tree070_186,tree070_18,tree070_18]
def tree070_671 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_667,tree070_670,tree070_189,tree070_49]
def tree070_672 : CoverTree := CoverTree.split [tree070_512,tree070_655,tree070_530,tree070_659,tree070_331,tree070_671]
def tree070_673 : CoverTree := CoverTree.reject 16
def tree070_674 : CoverTree := CoverTree.split [tree070_673,tree070_673,tree070_545,tree070_546,tree070_556,tree070_561]
def tree070_675 : CoverTree := CoverTree.reject 388
def tree070_676 : CoverTree := CoverTree.reject 317
def tree070_677 : CoverTree := CoverTree.reject 201
def tree070_678 : CoverTree := CoverTree.reject 390
def tree070_679 : CoverTree := CoverTree.split [tree070_63,tree070_64,tree070_678,tree070_18,tree070_18,tree070_18]
def tree070_680 : CoverTree := CoverTree.split [tree070_42,tree070_675,tree070_676,tree070_677,tree070_679,tree070_67]
def tree070_681 : CoverTree := CoverTree.split [tree070_673,tree070_673,tree070_194,tree070_680,tree070_348,tree070_205]
def tree070_682 : CoverTree := CoverTree.split [tree070_673,tree070_673,tree070_571,tree070_574,tree070_215,tree070_24]
def tree070_683 : CoverTree := CoverTree.reject 148
def tree070_684 : CoverTree := CoverTree.reject 242
def tree070_685 : CoverTree := CoverTree.split [tree070_683,tree070_684,tree070_356,tree070_358,tree070_34,tree070_38]
def tree070_686 : CoverTree := CoverTree.split [tree070_544,tree070_674,tree070_681,tree070_682,tree070_685,tree070_588]
def tree070_687 : CoverTree := CoverTree.split [tree070_673,tree070_673,tree070_590,tree070_591,tree070_592,tree070_593]
def tree070_688 : CoverTree := CoverTree.split [tree070_673,tree070_673,tree070_595,tree070_607,tree070_610,tree070_612]
def tree070_689 : CoverTree := CoverTree.reject 229
def tree070_690 : CoverTree := CoverTree.reject 82
def tree070_691 : CoverTree := CoverTree.split [tree070_113,tree070_689,tree070_690,tree070_449,tree070_452,tree070_454]
def tree070_692 : CoverTree := CoverTree.split [tree070_673,tree070_673,tree070_691,tree070_380,tree070_382,tree070_244]
def tree070_693 : CoverTree := CoverTree.split [tree070_673,tree070_673,tree070_617,tree070_101,tree070_111,tree070_24]
def tree070_694 : CoverTree := CoverTree.reject 83
def tree070_695 : CoverTree := CoverTree.reject 144
def tree070_696 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_695,tree070_482,tree070_485,tree070_487]
def tree070_697 : CoverTree := CoverTree.split [tree070_694,tree070_696,tree070_388,tree070_135,tree070_34,tree070_38]
def tree070_698 : CoverTree := CoverTree.split [tree070_687,tree070_688,tree070_692,tree070_693,tree070_697,tree070_620]
def tree070_699 : CoverTree := CoverTree.reject 100
def tree070_700 : CoverTree := CoverTree.reject 101
def tree070_701 : CoverTree := CoverTree.reject 379
def tree070_702 : CoverTree := CoverTree.reject 380
def tree070_703 : CoverTree := CoverTree.reject 381
def tree070_704 : CoverTree := CoverTree.reject 382
def tree070_705 : CoverTree := CoverTree.split [tree070_701,tree070_702,tree070_703,tree070_704,tree070_18,tree070_18]
def tree070_706 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_699,tree070_700,tree070_705]
def tree070_707 : CoverTree := CoverTree.reject 383
def tree070_708 : CoverTree := CoverTree.reject 384
def tree070_709 : CoverTree := CoverTree.reject 385
def tree070_710 : CoverTree := CoverTree.reject 386
def tree070_711 : CoverTree := CoverTree.split [tree070_22,tree070_707,tree070_708,tree070_709,tree070_710,tree070_18]
def tree070_712 : CoverTree := CoverTree.split [tree070_515,tree070_515,tree070_515,tree070_711,tree070_634,tree070_637]
def tree070_713 : CoverTree := CoverTree.split [tree070_627,tree070_706,tree070_712,tree070_607,tree070_610,tree070_612]
def tree070_714 : CoverTree := CoverTree.split [tree070_626,tree070_713,tree070_456,tree070_473,tree070_645,tree070_494]
def tree070_715 : CoverTree := CoverTree.split [tree070_0,tree070_651,tree070_672,tree070_686,tree070_698,tree070_714]
def tree070_716 : CoverTree := CoverTree.reject 348
def tree070_717 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_293,tree070_716,tree070_498,tree070_501]
def tree070_718 : CoverTree := CoverTree.reject 349
def tree070_719 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_293,tree070_718,tree070_649,tree070_289]
def tree070_720 : CoverTree := CoverTree.reject 356
def tree070_721 : CoverTree := CoverTree.split [tree070_42,tree070_284,tree070_505,tree070_505,tree070_720,tree070_288]
def tree070_722 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_293,tree070_721,tree070_506,tree070_291]
def tree070_723 : CoverTree := CoverTree.split [tree070_497,tree070_497,tree070_717,tree070_719,tree070_722,tree070_510]
def tree070_724 : CoverTree := CoverTree.reject 204
def tree070_725 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_724,tree070_513,tree070_514,tree070_654]
def tree070_726 : CoverTree := CoverTree.reject 231
def tree070_727 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_726,tree070_145,tree070_529,tree070_309]
def tree070_728 : CoverTree := CoverTree.reject 232
def tree070_729 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_728,tree070_658,tree070_320,tree070_160]
def tree070_730 : CoverTree := CoverTree.reject 36
def tree070_731 : CoverTree := CoverTree.split [tree070_113,tree070_730,tree070_730,tree070_730,tree070_730,tree070_18]
def tree070_732 : CoverTree := CoverTree.split [tree070_170,tree070_170,tree070_731,tree070_330,tree070_165,tree070_168]
def tree070_733 : CoverTree := CoverTree.split [tree070_512,tree070_725,tree070_727,tree070_729,tree070_732,tree070_671]
def tree070_734 : CoverTree := CoverTree.reject 205
def tree070_735 : CoverTree := CoverTree.split [tree070_627,tree070_734,tree070_545,tree070_546,tree070_556,tree070_561]
def tree070_736 : CoverTree := CoverTree.reject 206
def tree070_737 : CoverTree := CoverTree.split [tree070_424,tree070_736,tree070_194,tree070_680,tree070_348,tree070_205]
def tree070_738 : CoverTree := CoverTree.reject 207
def tree070_739 : CoverTree := CoverTree.split [tree070_457,tree070_738,tree070_571,tree070_574,tree070_215,tree070_24]
def tree070_740 : CoverTree := CoverTree.reject 32
def tree070_741 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_740,tree070_740,tree070_740,tree070_487]
def tree070_742 : CoverTree := CoverTree.split [tree070_683,tree070_741,tree070_356,tree070_358,tree070_34,tree070_38]
def tree070_743 : CoverTree := CoverTree.split [tree070_544,tree070_735,tree070_737,tree070_739,tree070_742,tree070_588]
def tree070_744 : CoverTree := CoverTree.split [tree070_622,tree070_623,tree070_590,tree070_591,tree070_592,tree070_593]
def tree070_745 : CoverTree := CoverTree.reject 208
def tree070_746 : CoverTree := CoverTree.split [tree070_627,tree070_745,tree070_595,tree070_607,tree070_610,tree070_612]
def tree070_747 : CoverTree := CoverTree.reject 126
def tree070_748 : CoverTree := CoverTree.split [tree070_424,tree070_747,tree070_691,tree070_380,tree070_382,tree070_244]
def tree070_749 : CoverTree := CoverTree.reject 396
def tree070_750 : CoverTree := CoverTree.reject 398
def tree070_751 : CoverTree := CoverTree.split [tree070_415,tree070_467,tree070_468,tree070_750,tree070_18,tree070_18]
def tree070_752 : CoverTree := CoverTree.split [tree070_390,tree070_390,tree070_695,tree070_749,tree070_751,tree070_471]
def tree070_753 : CoverTree := CoverTree.split [tree070_457,tree070_752,tree070_617,tree070_101,tree070_111,tree070_24]
def tree070_754 : CoverTree := CoverTree.split [tree070_744,tree070_746,tree070_748,tree070_753,tree070_697,tree070_620]
def tree070_755 : CoverTree := CoverTree.split [tree070_0,tree070_723,tree070_733,tree070_743,tree070_754,tree070_714]
def tree070_756 : CoverTree := CoverTree.split [tree070_143,tree070_280,tree070_496,tree070_647,tree070_715,tree070_755]
def tree070 : CoverTree := tree070_756

end Snake9.Shared89
