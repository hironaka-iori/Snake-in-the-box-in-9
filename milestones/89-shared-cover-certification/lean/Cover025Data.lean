import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes025 : List Box := [
[(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,6),(1,3)],
[(1,3),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,2),(1,6)],
[(1,2),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,2),(1,5),(1,5),(1,4),(1,6)],
[(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,2),(1,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,2),(1,5),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,2),(1,4),(1,5),(1,5),(1,6)],
[(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,3),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,4),(1,5),(1,5),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,3),(1,5),(1,3),(1,5),(1,6)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
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
[(1,6),(2,2),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(5,5),(1,1)],
[(1,6),(1,4),(1,5),(1,3),(1,2),(1,6)],
[(2,2),(3,3),(3,3),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(2,2)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(5,5),(1,6),(1,6)],
[(1,6),(1,1),(2,2),(1,6),(1,6),(1,6)],
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
[(1,6),(1,1),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(6,6),(4,4),(1,6),(1,6)],
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
[(1,6),(1,1),(5,5),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(2,2)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(3,3)],
[(1,6),(4,4),(5,5),(1,1),(1,6),(1,6)],
[(4,4),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(5,5),(2,2),(2,2),(1,6),(1,6),(1,6)],
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
[(6,6),(1,1),(5,5),(6,6),(1,6),(1,6)],
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
[(1,6),(1,1),(5,5),(4,4),(1,6),(1,6)],
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
[(1,6),(2,2),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,1),(5,5),(6,6),(3,3),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(4,4)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(5,5)],
[(1,6),(1,6),(2,2),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(2,2),(3,3),(6,6),(2,2)],
[(1,6),(2,2),(2,2),(6,6),(4,4),(1,6)],
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
[(1,6),(2,2),(2,2),(6,6),(5,5),(4,4)],
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

def root025 : Nat := 2620

def tree025_0 : CoverTree := CoverTree.reject 9
def tree025_1 : CoverTree := CoverTree.reject 14
def tree025_2 : CoverTree := CoverTree.reject 12
def tree025_3 : CoverTree := CoverTree.reject 3
def tree025_4 : CoverTree := CoverTree.reject 47
def tree025_5 : CoverTree := CoverTree.reject 5
def tree025_6 : CoverTree := CoverTree.reject 23
def tree025_7 : CoverTree := CoverTree.reject 68
def tree025_8 : CoverTree := CoverTree.reject 25
def tree025_9 : CoverTree := CoverTree.reject 26
def tree025_10 : CoverTree := CoverTree.reject 27
def tree025_11 : CoverTree := CoverTree.reject 28
def tree025_12 : CoverTree := CoverTree.reject 98
def tree025_13 : CoverTree := CoverTree.reject 99
def tree025_14 : CoverTree := CoverTree.split [tree025_8,tree025_9,tree025_10,tree025_11,tree025_12,tree025_13]
def tree025_15 : CoverTree := CoverTree.reject 16
def tree025_16 : CoverTree := CoverTree.reject 100
def tree025_17 : CoverTree := CoverTree.accept
def tree025_18 : CoverTree := CoverTree.split [tree025_15,tree025_16,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_19 : CoverTree := CoverTree.reject 15
def tree025_20 : CoverTree := CoverTree.split [tree025_19,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_21 : CoverTree := CoverTree.reject 11
def tree025_22 : CoverTree := CoverTree.split [tree025_21,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_23 : CoverTree := CoverTree.split [tree025_14,tree025_18,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_24 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_6,tree025_6,tree025_7,tree025_23]
def tree025_25 : CoverTree := CoverTree.reject 167
def tree025_26 : CoverTree := CoverTree.reject 168
def tree025_27 : CoverTree := CoverTree.split [tree025_8,tree025_9,tree025_10,tree025_11,tree025_25,tree025_26]
def tree025_28 : CoverTree := CoverTree.reject 37
def tree025_29 : CoverTree := CoverTree.reject 101
def tree025_30 : CoverTree := CoverTree.split [tree025_15,tree025_28,tree025_29,tree025_17,tree025_17,tree025_17]
def tree025_31 : CoverTree := CoverTree.reject 102
def tree025_32 : CoverTree := CoverTree.split [tree025_19,tree025_31,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_33 : CoverTree := CoverTree.split [tree025_27,tree025_30,tree025_32,tree025_22,tree025_17,tree025_17]
def tree025_34 : CoverTree := CoverTree.reject 103
def tree025_35 : CoverTree := CoverTree.split [tree025_8,tree025_9,tree025_10,tree025_11,tree025_17,tree025_34]
def tree025_36 : CoverTree := CoverTree.split [tree025_15,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_37 : CoverTree := CoverTree.split [tree025_35,tree025_36,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_38 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_6,tree025_6,tree025_33,tree025_37]
def tree025_39 : CoverTree := CoverTree.reject 90
def tree025_40 : CoverTree := CoverTree.reject 10
def tree025_41 : CoverTree := CoverTree.reject 38
def tree025_42 : CoverTree := CoverTree.split [tree025_15,tree025_41,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_43 : CoverTree := CoverTree.split [tree025_40,tree025_42,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_44 : CoverTree := CoverTree.split [tree025_8,tree025_9,tree025_10,tree025_11,tree025_17,tree025_17]
def tree025_45 : CoverTree := CoverTree.split [tree025_15,tree025_28,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_46 : CoverTree := CoverTree.split [tree025_44,tree025_45,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_47 : CoverTree := CoverTree.split [tree025_44,tree025_36,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_48 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_39,tree025_43,tree025_46,tree025_47]
def tree025_49 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_4,tree025_24,tree025_38,tree025_48]
def tree025_50 : CoverTree := CoverTree.reject 91
def tree025_51 : CoverTree := CoverTree.reject 195
def tree025_52 : CoverTree := CoverTree.reject 196
def tree025_53 : CoverTree := CoverTree.reject 197
def tree025_54 : CoverTree := CoverTree.split [tree025_15,tree025_41,tree025_51,tree025_52,tree025_53,tree025_17]
def tree025_55 : CoverTree := CoverTree.reject 160
def tree025_56 : CoverTree := CoverTree.reject 161
def tree025_57 : CoverTree := CoverTree.reject 162
def tree025_58 : CoverTree := CoverTree.split [tree025_19,tree025_55,tree025_56,tree025_57,tree025_17,tree025_17]
def tree025_59 : CoverTree := CoverTree.reject 163
def tree025_60 : CoverTree := CoverTree.split [tree025_21,tree025_59,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_61 : CoverTree := CoverTree.reject 164
def tree025_62 : CoverTree := CoverTree.reject 165
def tree025_63 : CoverTree := CoverTree.split [tree025_61,tree025_62,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_64 : CoverTree := CoverTree.reject 166
def tree025_65 : CoverTree := CoverTree.split [tree025_64,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_66 : CoverTree := CoverTree.split [tree025_40,tree025_54,tree025_58,tree025_60,tree025_63,tree025_65]
def tree025_67 : CoverTree := CoverTree.reject 109
def tree025_68 : CoverTree := CoverTree.reject 125
def tree025_69 : CoverTree := CoverTree.reject 126
def tree025_70 : CoverTree := CoverTree.reject 127
def tree025_71 : CoverTree := CoverTree.split [tree025_15,tree025_28,tree025_68,tree025_69,tree025_70,tree025_17]
def tree025_72 : CoverTree := CoverTree.reject 128
def tree025_73 : CoverTree := CoverTree.reject 129
def tree025_74 : CoverTree := CoverTree.split [tree025_19,tree025_72,tree025_73,tree025_17,tree025_17,tree025_17]
def tree025_75 : CoverTree := CoverTree.reject 130
def tree025_76 : CoverTree := CoverTree.split [tree025_21,tree025_75,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_77 : CoverTree := CoverTree.reject 131
def tree025_78 : CoverTree := CoverTree.split [tree025_77,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_79 : CoverTree := CoverTree.split [tree025_67,tree025_71,tree025_74,tree025_76,tree025_78,tree025_17]
def tree025_80 : CoverTree := CoverTree.reject 110
def tree025_81 : CoverTree := CoverTree.reject 111
def tree025_82 : CoverTree := CoverTree.split [tree025_8,tree025_9,tree025_10,tree025_11,tree025_80,tree025_81]
def tree025_83 : CoverTree := CoverTree.reject 112
def tree025_84 : CoverTree := CoverTree.split [tree025_15,tree025_83,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_85 : CoverTree := CoverTree.split [tree025_82,tree025_84,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_86 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_50,tree025_66,tree025_79,tree025_85]
def tree025_87 : CoverTree := CoverTree.reject 92
def tree025_88 : CoverTree := CoverTree.reject 133
def tree025_89 : CoverTree := CoverTree.reject 134
def tree025_90 : CoverTree := CoverTree.reject 135
def tree025_91 : CoverTree := CoverTree.split [tree025_15,tree025_41,tree025_88,tree025_89,tree025_90,tree025_17]
def tree025_92 : CoverTree := CoverTree.reject 136
def tree025_93 : CoverTree := CoverTree.reject 137
def tree025_94 : CoverTree := CoverTree.split [tree025_19,tree025_92,tree025_93,tree025_17,tree025_17,tree025_17]
def tree025_95 : CoverTree := CoverTree.reject 138
def tree025_96 : CoverTree := CoverTree.split [tree025_21,tree025_95,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_97 : CoverTree := CoverTree.reject 139
def tree025_98 : CoverTree := CoverTree.split [tree025_97,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_99 : CoverTree := CoverTree.split [tree025_40,tree025_91,tree025_94,tree025_96,tree025_98,tree025_17]
def tree025_100 : CoverTree := CoverTree.reject 175
def tree025_101 : CoverTree := CoverTree.reject 176
def tree025_102 : CoverTree := CoverTree.split [tree025_8,tree025_9,tree025_10,tree025_11,tree025_100,tree025_101]
def tree025_103 : CoverTree := CoverTree.reject 113
def tree025_104 : CoverTree := CoverTree.split [tree025_15,tree025_28,tree025_103,tree025_17,tree025_17,tree025_17]
def tree025_105 : CoverTree := CoverTree.reject 114
def tree025_106 : CoverTree := CoverTree.split [tree025_19,tree025_105,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_107 : CoverTree := CoverTree.reject 115
def tree025_108 : CoverTree := CoverTree.split [tree025_107,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_109 : CoverTree := CoverTree.split [tree025_102,tree025_104,tree025_106,tree025_22,tree025_108,tree025_17]
def tree025_110 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_87,tree025_99,tree025_109,tree025_23]
def tree025_111 : CoverTree := CoverTree.reject 13
def tree025_112 : CoverTree := CoverTree.reject 44
def tree025_113 : CoverTree := CoverTree.reject 45
def tree025_114 : CoverTree := CoverTree.reject 179
def tree025_115 : CoverTree := CoverTree.reject 180
def tree025_116 : CoverTree := CoverTree.split [tree025_15,tree025_112,tree025_113,tree025_114,tree025_115,tree025_17]
def tree025_117 : CoverTree := CoverTree.reject 146
def tree025_118 : CoverTree := CoverTree.reject 147
def tree025_119 : CoverTree := CoverTree.split [tree025_19,tree025_117,tree025_118,tree025_17,tree025_17,tree025_17]
def tree025_120 : CoverTree := CoverTree.reject 148
def tree025_121 : CoverTree := CoverTree.split [tree025_21,tree025_120,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_122 : CoverTree := CoverTree.reject 39
def tree025_123 : CoverTree := CoverTree.split [tree025_122,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_124 : CoverTree := CoverTree.split [tree025_111,tree025_116,tree025_119,tree025_121,tree025_123,tree025_17]
def tree025_125 : CoverTree := CoverTree.reject 117
def tree025_126 : CoverTree := CoverTree.reject 118
def tree025_127 : CoverTree := CoverTree.split [tree025_15,tree025_41,tree025_125,tree025_126,tree025_17,tree025_17]
def tree025_128 : CoverTree := CoverTree.reject 119
def tree025_129 : CoverTree := CoverTree.reject 120
def tree025_130 : CoverTree := CoverTree.split [tree025_19,tree025_128,tree025_129,tree025_17,tree025_17,tree025_17]
def tree025_131 : CoverTree := CoverTree.reject 121
def tree025_132 : CoverTree := CoverTree.split [tree025_131,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_133 : CoverTree := CoverTree.split [tree025_40,tree025_127,tree025_130,tree025_22,tree025_132,tree025_17]
def tree025_134 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_124,tree025_133,tree025_33,tree025_37]
def tree025_135 : CoverTree := CoverTree.split [tree025_15,tree025_112,tree025_113,tree025_17,tree025_17,tree025_17]
def tree025_136 : CoverTree := CoverTree.reject 104
def tree025_137 : CoverTree := CoverTree.split [tree025_19,tree025_136,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_138 : CoverTree := CoverTree.split [tree025_111,tree025_135,tree025_137,tree025_22,tree025_123,tree025_17]
def tree025_139 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_138,tree025_43,tree025_46,tree025_47]
def tree025_140 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_86,tree025_110,tree025_134,tree025_139]
def tree025_141 : CoverTree := CoverTree.split [tree025_0,tree025_0,tree025_1,tree025_2,tree025_49,tree025_140]
def tree025_142 : CoverTree := CoverTree.reject 0
def tree025_143 : CoverTree := CoverTree.reject 30
def tree025_144 : CoverTree := CoverTree.reject 71
def tree025_145 : CoverTree := CoverTree.reject 66
def tree025_146 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_143,tree025_144,tree025_145]
def tree025_147 : CoverTree := CoverTree.reject 49
def tree025_148 : CoverTree := CoverTree.reject 72
def tree025_149 : CoverTree := CoverTree.reject 254
def tree025_150 : CoverTree := CoverTree.reject 255
def tree025_151 : CoverTree := CoverTree.split [tree025_15,tree025_16,tree025_149,tree025_150,tree025_17,tree025_17]
def tree025_152 : CoverTree := CoverTree.reject 256
def tree025_153 : CoverTree := CoverTree.reject 257
def tree025_154 : CoverTree := CoverTree.reject 258
def tree025_155 : CoverTree := CoverTree.split [tree025_19,tree025_152,tree025_153,tree025_154,tree025_17,tree025_17]
def tree025_156 : CoverTree := CoverTree.reject 259
def tree025_157 : CoverTree := CoverTree.split [tree025_21,tree025_156,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_158 : CoverTree := CoverTree.split [tree025_14,tree025_151,tree025_155,tree025_157,tree025_17,tree025_17]
def tree025_159 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_147,tree025_148,tree025_158]
def tree025_160 : CoverTree := CoverTree.reject 144
def tree025_161 : CoverTree := CoverTree.reject 260
def tree025_162 : CoverTree := CoverTree.split [tree025_19,tree025_31,tree025_161,tree025_17,tree025_17,tree025_17]
def tree025_163 : CoverTree := CoverTree.split [tree025_27,tree025_160,tree025_162,tree025_22,tree025_17,tree025_17]
def tree025_164 : CoverTree := CoverTree.reject 261
def tree025_165 : CoverTree := CoverTree.split [tree025_15,tree025_17,tree025_164,tree025_17,tree025_17,tree025_17]
def tree025_166 : CoverTree := CoverTree.split [tree025_35,tree025_165,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_167 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_147,tree025_163,tree025_166]
def tree025_168 : CoverTree := CoverTree.reject 415
def tree025_169 : CoverTree := CoverTree.reject 416
def tree025_170 : CoverTree := CoverTree.reject 406
def tree025_171 : CoverTree := CoverTree.reject 270
def tree025_172 : CoverTree := CoverTree.reject 271
def tree025_173 : CoverTree := CoverTree.split [tree025_122,tree025_171,tree025_172,tree025_17,tree025_17,tree025_17]
def tree025_174 : CoverTree := CoverTree.reject 272
def tree025_175 : CoverTree := CoverTree.split [tree025_17,tree025_174,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_176 : CoverTree := CoverTree.split [tree025_111,tree025_168,tree025_169,tree025_170,tree025_173,tree025_175]
def tree025_177 : CoverTree := CoverTree.reject 389
def tree025_178 : CoverTree := CoverTree.reject 274
def tree025_179 : CoverTree := CoverTree.reject 275
def tree025_180 : CoverTree := CoverTree.reject 276
def tree025_181 : CoverTree := CoverTree.split [tree025_19,tree025_178,tree025_179,tree025_180,tree025_17,tree025_17]
def tree025_182 : CoverTree := CoverTree.reject 277
def tree025_183 : CoverTree := CoverTree.split [tree025_21,tree025_182,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_184 : CoverTree := CoverTree.split [tree025_40,tree025_177,tree025_181,tree025_183,tree025_17,tree025_17]
def tree025_185 : CoverTree := CoverTree.reject 181
def tree025_186 : CoverTree := CoverTree.split [tree025_185,tree025_45,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_187 : CoverTree := CoverTree.reject 304
def tree025_188 : CoverTree := CoverTree.split [tree025_44,tree025_187,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_189 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_176,tree025_184,tree025_186,tree025_188]
def tree025_190 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_146,tree025_159,tree025_167,tree025_189]
def tree025_191 : CoverTree := CoverTree.reject 31
def tree025_192 : CoverTree := CoverTree.reject 73
def tree025_193 : CoverTree := CoverTree.reject 74
def tree025_194 : CoverTree := CoverTree.reject 278
def tree025_195 : CoverTree := CoverTree.reject 279
def tree025_196 : CoverTree := CoverTree.split [tree025_15,tree025_83,tree025_194,tree025_195,tree025_17,tree025_17]
def tree025_197 : CoverTree := CoverTree.reject 280
def tree025_198 : CoverTree := CoverTree.reject 281
def tree025_199 : CoverTree := CoverTree.split [tree025_19,tree025_197,tree025_198,tree025_17,tree025_17,tree025_17]
def tree025_200 : CoverTree := CoverTree.reject 282
def tree025_201 : CoverTree := CoverTree.split [tree025_21,tree025_200,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_202 : CoverTree := CoverTree.split [tree025_82,tree025_196,tree025_199,tree025_201,tree025_17,tree025_17]
def tree025_203 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_191,tree025_192,tree025_193,tree025_202]
def tree025_204 : CoverTree := CoverTree.reject 191
def tree025_205 : CoverTree := CoverTree.reject 75
def tree025_206 : CoverTree := CoverTree.reject 283
def tree025_207 : CoverTree := CoverTree.reject 284
def tree025_208 : CoverTree := CoverTree.split [tree025_15,tree025_28,tree025_103,tree025_206,tree025_207,tree025_17]
def tree025_209 : CoverTree := CoverTree.reject 285
def tree025_210 : CoverTree := CoverTree.reject 286
def tree025_211 : CoverTree := CoverTree.split [tree025_19,tree025_105,tree025_209,tree025_210,tree025_17,tree025_17]
def tree025_212 : CoverTree := CoverTree.split [tree025_102,tree025_208,tree025_211,tree025_22,tree025_108,tree025_17]
def tree025_213 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_204,tree025_205,tree025_212,tree025_23]
def tree025_214 : CoverTree := CoverTree.reject 105
def tree025_215 : CoverTree := CoverTree.reject 76
def tree025_216 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_214,tree025_215,tree025_33,tree025_37]
def tree025_217 : CoverTree := CoverTree.reject 417
def tree025_218 : CoverTree := CoverTree.reject 407
def tree025_219 : CoverTree := CoverTree.reject 356
def tree025_220 : CoverTree := CoverTree.reject 292
def tree025_221 : CoverTree := CoverTree.reject 293
def tree025_222 : CoverTree := CoverTree.split [tree025_122,tree025_220,tree025_221,tree025_17,tree025_17,tree025_17]
def tree025_223 : CoverTree := CoverTree.reject 294
def tree025_224 : CoverTree := CoverTree.split [tree025_17,tree025_223,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_225 : CoverTree := CoverTree.split [tree025_111,tree025_217,tree025_218,tree025_219,tree025_222,tree025_224]
def tree025_226 : CoverTree := CoverTree.reject 408
def tree025_227 : CoverTree := CoverTree.reject 390
def tree025_228 : CoverTree := CoverTree.reject 299
def tree025_229 : CoverTree := CoverTree.split [tree025_21,tree025_228,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_230 : CoverTree := CoverTree.split [tree025_40,tree025_226,tree025_227,tree025_229,tree025_17,tree025_17]
def tree025_231 : CoverTree := CoverTree.reject 300
def tree025_232 : CoverTree := CoverTree.split [tree025_8,tree025_9,tree025_10,tree025_11,tree025_17,tree025_231]
def tree025_233 : CoverTree := CoverTree.split [tree025_232,tree025_45,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_234 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_225,tree025_230,tree025_233,tree025_47]
def tree025_235 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_203,tree025_213,tree025_216,tree025_234]
def tree025_236 : CoverTree := CoverTree.reject 122
def tree025_237 : CoverTree := CoverTree.reject 77
def tree025_238 : CoverTree := CoverTree.reject 69
def tree025_239 : CoverTree := CoverTree.reject 301
def tree025_240 : CoverTree := CoverTree.split [tree025_21,tree025_239,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_241 : CoverTree := CoverTree.split [tree025_82,tree025_84,tree025_20,tree025_240,tree025_17,tree025_17]
def tree025_242 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_236,tree025_237,tree025_238,tree025_241]
def tree025_243 : CoverTree := CoverTree.reject 94
def tree025_244 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_243,tree025_99,tree025_109,tree025_23]
def tree025_245 : CoverTree := CoverTree.reject 95
def tree025_246 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_245,tree025_133,tree025_33,tree025_37]
def tree025_247 : CoverTree := CoverTree.reject 302
def tree025_248 : CoverTree := CoverTree.split [tree025_15,tree025_112,tree025_113,tree025_247,tree025_17,tree025_17]
def tree025_249 : CoverTree := CoverTree.reject 303
def tree025_250 : CoverTree := CoverTree.split [tree025_19,tree025_136,tree025_249,tree025_17,tree025_17,tree025_17]
def tree025_251 : CoverTree := CoverTree.split [tree025_111,tree025_248,tree025_250,tree025_22,tree025_123,tree025_17]
def tree025_252 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_251,tree025_43,tree025_46,tree025_47]
def tree025_253 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_242,tree025_244,tree025_246,tree025_252]
def tree025_254 : CoverTree := CoverTree.reject 96
def tree025_255 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_254,tree025_66,tree025_79,tree025_85]
def tree025_256 : CoverTree := CoverTree.reject 251
def tree025_257 : CoverTree := CoverTree.reject 252
def tree025_258 : CoverTree := CoverTree.split [tree025_15,tree025_112,tree025_113,tree025_256,tree025_257,tree025_17]
def tree025_259 : CoverTree := CoverTree.reject 198
def tree025_260 : CoverTree := CoverTree.reject 199
def tree025_261 : CoverTree := CoverTree.reject 200
def tree025_262 : CoverTree := CoverTree.split [tree025_19,tree025_259,tree025_260,tree025_261,tree025_17,tree025_17]
def tree025_263 : CoverTree := CoverTree.reject 201
def tree025_264 : CoverTree := CoverTree.reject 202
def tree025_265 : CoverTree := CoverTree.split [tree025_21,tree025_263,tree025_264,tree025_17,tree025_17,tree025_17]
def tree025_266 : CoverTree := CoverTree.reject 149
def tree025_267 : CoverTree := CoverTree.split [tree025_122,tree025_266,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_268 : CoverTree := CoverTree.reject 145
def tree025_269 : CoverTree := CoverTree.split [tree025_268,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_270 : CoverTree := CoverTree.split [tree025_111,tree025_258,tree025_262,tree025_265,tree025_267,tree025_269]
def tree025_271 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_270,tree025_99,tree025_109,tree025_23]
def tree025_272 : CoverTree := CoverTree.reject 391
def tree025_273 : CoverTree := CoverTree.reject 357
def tree025_274 : CoverTree := CoverTree.split [tree025_111,tree025_272,tree025_273,tree025_22,tree025_123,tree025_17]
def tree025_275 : CoverTree := CoverTree.split [tree025_5,tree025_5,tree025_274,tree025_43,tree025_46,tree025_47]
def tree025_276 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_255,tree025_271,tree025_134,tree025_275]
def tree025_277 : CoverTree := CoverTree.split [tree025_0,tree025_0,tree025_190,tree025_235,tree025_253,tree025_276]
def tree025_278 : CoverTree := CoverTree.reject 35
def tree025_279 : CoverTree := CoverTree.reject 143
def tree025_280 : CoverTree := CoverTree.reject 46
def tree025_281 : CoverTree := CoverTree.reject 182
def tree025_282 : CoverTree := CoverTree.reject 17
def tree025_283 : CoverTree := CoverTree.reject 2
def tree025_284 : CoverTree := CoverTree.reject 331
def tree025_285 : CoverTree := CoverTree.split [tree025_283,tree025_283,tree025_283,tree025_284,tree025_17,tree025_17]
def tree025_286 : CoverTree := CoverTree.split [tree025_283,tree025_283,tree025_283,tree025_17,tree025_17,tree025_17]
def tree025_287 : CoverTree := CoverTree.split [tree025_282,tree025_282,tree025_285,tree025_286,tree025_286,tree025_286]
def tree025_288 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_280,tree025_281,tree025_287]
def tree025_289 : CoverTree := CoverTree.split [tree025_282,tree025_282,tree025_286,tree025_286,tree025_286,tree025_286]
def tree025_290 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_280,tree025_281,tree025_289]
def tree025_291 : CoverTree := CoverTree.reject 8
def tree025_292 : CoverTree := CoverTree.reject 32
def tree025_293 : CoverTree := CoverTree.reject 192
def tree025_294 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_292,tree025_293,tree025_289,tree025_289]
def tree025_295 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_279,tree025_288,tree025_290,tree025_294]
def tree025_296 : CoverTree := CoverTree.reject 78
def tree025_297 : CoverTree := CoverTree.reject 140
def tree025_298 : CoverTree := CoverTree.reject 332
def tree025_299 : CoverTree := CoverTree.reject 333
def tree025_300 : CoverTree := CoverTree.split [tree025_19,tree025_298,tree025_299,tree025_17,tree025_17,tree025_17]
def tree025_301 : CoverTree := CoverTree.reject 334
def tree025_302 : CoverTree := CoverTree.split [tree025_21,tree025_301,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_303 : CoverTree := CoverTree.reject 335
def tree025_304 : CoverTree := CoverTree.reject 336
def tree025_305 : CoverTree := CoverTree.split [tree025_17,tree025_303,tree025_304,tree025_17,tree025_17,tree025_17]
def tree025_306 : CoverTree := CoverTree.reject 337
def tree025_307 : CoverTree := CoverTree.split [tree025_17,tree025_306,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_308 : CoverTree := CoverTree.split [tree025_82,tree025_297,tree025_300,tree025_302,tree025_305,tree025_307]
def tree025_309 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_143,tree025_296,tree025_308]
def tree025_310 : CoverTree := CoverTree.reject 79
def tree025_311 : CoverTree := CoverTree.reject 171
def tree025_312 : CoverTree := CoverTree.reject 141
def tree025_313 : CoverTree := CoverTree.reject 338
def tree025_314 : CoverTree := CoverTree.reject 339
def tree025_315 : CoverTree := CoverTree.reject 340
def tree025_316 : CoverTree := CoverTree.split [tree025_21,tree025_313,tree025_314,tree025_315,tree025_17,tree025_17]
def tree025_317 : CoverTree := CoverTree.reject 341
def tree025_318 : CoverTree := CoverTree.split [tree025_107,tree025_317,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_319 : CoverTree := CoverTree.split [tree025_102,tree025_311,tree025_312,tree025_316,tree025_318,tree025_17]
def tree025_320 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_310,tree025_319,tree025_158]
def tree025_321 : CoverTree := CoverTree.reject 210
def tree025_322 : CoverTree := CoverTree.reject 342
def tree025_323 : CoverTree := CoverTree.reject 343
def tree025_324 : CoverTree := CoverTree.split [tree025_19,tree025_128,tree025_129,tree025_322,tree025_323,tree025_17]
def tree025_325 : CoverTree := CoverTree.reject 344
def tree025_326 : CoverTree := CoverTree.reject 345
def tree025_327 : CoverTree := CoverTree.reject 346
def tree025_328 : CoverTree := CoverTree.split [tree025_21,tree025_325,tree025_326,tree025_327,tree025_17,tree025_17]
def tree025_329 : CoverTree := CoverTree.split [tree025_40,tree025_321,tree025_324,tree025_328,tree025_132,tree025_17]
def tree025_330 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_329,tree025_163,tree025_166]
def tree025_331 : CoverTree := CoverTree.reject 418
def tree025_332 : CoverTree := CoverTree.reject 419
def tree025_333 : CoverTree := CoverTree.reject 409
def tree025_334 : CoverTree := CoverTree.split [tree025_111,tree025_331,tree025_332,tree025_333,tree025_173,tree025_175]
def tree025_335 : CoverTree := CoverTree.reject 392
def tree025_336 : CoverTree := CoverTree.split [tree025_40,tree025_335,tree025_181,tree025_183,tree025_17,tree025_17]
def tree025_337 : CoverTree := CoverTree.reject 305
def tree025_338 : CoverTree := CoverTree.split [tree025_44,tree025_337,tree025_20,tree025_22,tree025_17,tree025_17]
def tree025_339 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_334,tree025_336,tree025_186,tree025_338]
def tree025_340 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_309,tree025_320,tree025_330,tree025_339]
def tree025_341 : CoverTree := CoverTree.reject 7
def tree025_342 : CoverTree := CoverTree.reject 80
def tree025_343 : CoverTree := CoverTree.reject 329
def tree025_344 : CoverTree := CoverTree.reject 347
def tree025_345 : CoverTree := CoverTree.split [tree025_19,tree025_72,tree025_73,tree025_344,tree025_17,tree025_17]
def tree025_346 : CoverTree := CoverTree.reject 348
def tree025_347 : CoverTree := CoverTree.split [tree025_17,tree025_346,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_348 : CoverTree := CoverTree.split [tree025_67,tree025_343,tree025_345,tree025_76,tree025_78,tree025_347]
def tree025_349 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_191,tree025_342,tree025_348,tree025_202]
def tree025_350 : CoverTree := CoverTree.reject 193
def tree025_351 : CoverTree := CoverTree.reject 81
def tree025_352 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_350,tree025_351,tree025_212,tree025_23]
def tree025_353 : CoverTree := CoverTree.reject 36
def tree025_354 : CoverTree := CoverTree.reject 65
def tree025_355 : CoverTree := CoverTree.reject 349
def tree025_356 : CoverTree := CoverTree.split [tree025_21,tree025_120,tree025_355,tree025_17,tree025_17,tree025_17]
def tree025_357 : CoverTree := CoverTree.split [tree025_111,tree025_354,tree025_119,tree025_356,tree025_123,tree025_17]
def tree025_358 : CoverTree := CoverTree.reject 212
def tree025_359 : CoverTree := CoverTree.split [tree025_40,tree025_358,tree025_130,tree025_22,tree025_132,tree025_17]
def tree025_360 : CoverTree := CoverTree.split [tree025_353,tree025_353,tree025_357,tree025_359,tree025_33,tree025_37]
def tree025_361 : CoverTree := CoverTree.reject 59
def tree025_362 : CoverTree := CoverTree.reject 116
def tree025_363 : CoverTree := CoverTree.reject 287
def tree025_364 : CoverTree := CoverTree.reject 288
def tree025_365 : CoverTree := CoverTree.split [tree025_15,tree025_112,tree025_113,tree025_363,tree025_364,tree025_17]
def tree025_366 : CoverTree := CoverTree.reject 289
def tree025_367 : CoverTree := CoverTree.reject 290
def tree025_368 : CoverTree := CoverTree.split [tree025_19,tree025_136,tree025_366,tree025_367,tree025_17,tree025_17]
def tree025_369 : CoverTree := CoverTree.reject 291
def tree025_370 : CoverTree := CoverTree.split [tree025_21,tree025_17,tree025_369,tree025_17,tree025_17,tree025_17]
def tree025_371 : CoverTree := CoverTree.split [tree025_111,tree025_365,tree025_368,tree025_370,tree025_222,tree025_224]
def tree025_372 : CoverTree := CoverTree.reject 410
def tree025_373 : CoverTree := CoverTree.reject 297
def tree025_374 : CoverTree := CoverTree.reject 298
def tree025_375 : CoverTree := CoverTree.split [tree025_19,tree025_373,tree025_374,tree025_17,tree025_17,tree025_17]
def tree025_376 : CoverTree := CoverTree.split [tree025_40,tree025_372,tree025_375,tree025_229,tree025_17,tree025_17]
def tree025_377 : CoverTree := CoverTree.split [tree025_361,tree025_362,tree025_371,tree025_376,tree025_233,tree025_47]
def tree025_378 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_349,tree025_352,tree025_360,tree025_377]
def tree025_379 : CoverTree := CoverTree.reject 123
def tree025_380 : CoverTree := CoverTree.reject 142
def tree025_381 : CoverTree := CoverTree.split [tree025_40,tree025_380,tree025_58,tree025_60,tree025_63,tree025_65]
def tree025_382 : CoverTree := CoverTree.reject 330
def tree025_383 : CoverTree := CoverTree.split [tree025_67,tree025_382,tree025_74,tree025_76,tree025_78,tree025_17]
def tree025_384 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_379,tree025_381,tree025_383,tree025_241]
def tree025_385 : CoverTree := CoverTree.reject 97
def tree025_386 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_385,tree025_99,tree025_109,tree025_23]
def tree025_387 : CoverTree := CoverTree.reject 350
def tree025_388 : CoverTree := CoverTree.split [tree025_21,tree025_120,tree025_387,tree025_17,tree025_17,tree025_17]
def tree025_389 : CoverTree := CoverTree.split [tree025_111,tree025_116,tree025_119,tree025_388,tree025_123,tree025_17]
def tree025_390 : CoverTree := CoverTree.split [tree025_353,tree025_353,tree025_389,tree025_133,tree025_33,tree025_37]
def tree025_391 : CoverTree := CoverTree.reject 4
def tree025_392 : CoverTree := CoverTree.reject 24
def tree025_393 : CoverTree := CoverTree.reject 20
def tree025_394 : CoverTree := CoverTree.reject 152
def tree025_395 : CoverTree := CoverTree.reject 153
def tree025_396 : CoverTree := CoverTree.reject 154
def tree025_397 : CoverTree := CoverTree.reject 204
def tree025_398 : CoverTree := CoverTree.reject 205
def tree025_399 : CoverTree := CoverTree.split [tree025_394,tree025_395,tree025_396,tree025_397,tree025_398,tree025_17]
def tree025_400 : CoverTree := CoverTree.reject 194
def tree025_401 : CoverTree := CoverTree.reject 206
def tree025_402 : CoverTree := CoverTree.reject 207
def tree025_403 : CoverTree := CoverTree.reject 208
def tree025_404 : CoverTree := CoverTree.reject 209
def tree025_405 : CoverTree := CoverTree.split [tree025_400,tree025_401,tree025_402,tree025_403,tree025_404,tree025_17]
def tree025_406 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_392,tree025_393,tree025_399,tree025_405]
def tree025_407 : CoverTree := CoverTree.reject 67
def tree025_408 : CoverTree := CoverTree.reject 351
def tree025_409 : CoverTree := CoverTree.reject 352
def tree025_410 : CoverTree := CoverTree.reject 353
def tree025_411 : CoverTree := CoverTree.split [tree025_19,tree025_407,tree025_408,tree025_409,tree025_410,tree025_17]
def tree025_412 : CoverTree := CoverTree.reject 177
def tree025_413 : CoverTree := CoverTree.reject 354
def tree025_414 : CoverTree := CoverTree.reject 355
def tree025_415 : CoverTree := CoverTree.split [tree025_21,tree025_412,tree025_413,tree025_414,tree025_17,tree025_17]
def tree025_416 : CoverTree := CoverTree.reject 64
def tree025_417 : CoverTree := CoverTree.reject 422
def tree025_418 : CoverTree := CoverTree.reject 423
def tree025_419 : CoverTree := CoverTree.split [tree025_416,tree025_417,tree025_418,tree025_17,tree025_17,tree025_17]
def tree025_420 : CoverTree := CoverTree.reject 178
def tree025_421 : CoverTree := CoverTree.split [tree025_420,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_422 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_411,tree025_415,tree025_419,tree025_421]
def tree025_423 : CoverTree := CoverTree.split [tree025_406,tree025_422,tree025_251,tree025_43,tree025_46,tree025_47]
def tree025_424 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_384,tree025_386,tree025_390,tree025_423]
def tree025_425 : CoverTree := CoverTree.reject 42
def tree025_426 : CoverTree := CoverTree.reject 108
def tree025_427 : CoverTree := CoverTree.reject 307
def tree025_428 : CoverTree := CoverTree.reject 308
def tree025_429 : CoverTree := CoverTree.reject 309
def tree025_430 : CoverTree := CoverTree.reject 310
def tree025_431 : CoverTree := CoverTree.split [tree025_21,tree025_427,tree025_428,tree025_429,tree025_430,tree025_17]
def tree025_432 : CoverTree := CoverTree.reject 311
def tree025_433 : CoverTree := CoverTree.reject 312
def tree025_434 : CoverTree := CoverTree.reject 313
def tree025_435 : CoverTree := CoverTree.reject 314
def tree025_436 : CoverTree := CoverTree.split [tree025_416,tree025_432,tree025_433,tree025_434,tree025_435,tree025_17]
def tree025_437 : CoverTree := CoverTree.reject 315
def tree025_438 : CoverTree := CoverTree.split [tree025_437,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_439 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_426,tree025_431,tree025_436,tree025_438]
def tree025_440 : CoverTree := CoverTree.reject 173
def tree025_441 : CoverTree := CoverTree.reject 316
def tree025_442 : CoverTree := CoverTree.reject 317
def tree025_443 : CoverTree := CoverTree.reject 318
def tree025_444 : CoverTree := CoverTree.reject 319
def tree025_445 : CoverTree := CoverTree.split [tree025_19,tree025_441,tree025_442,tree025_443,tree025_444,tree025_17]
def tree025_446 : CoverTree := CoverTree.reject 228
def tree025_447 : CoverTree := CoverTree.reject 229
def tree025_448 : CoverTree := CoverTree.reject 230
def tree025_449 : CoverTree := CoverTree.reject 231
def tree025_450 : CoverTree := CoverTree.split [tree025_21,tree025_446,tree025_447,tree025_448,tree025_449,tree025_17]
def tree025_451 : CoverTree := CoverTree.reject 232
def tree025_452 : CoverTree := CoverTree.reject 233
def tree025_453 : CoverTree := CoverTree.split [tree025_122,tree025_451,tree025_452,tree025_17,tree025_17,tree025_17]
def tree025_454 : CoverTree := CoverTree.reject 213
def tree025_455 : CoverTree := CoverTree.split [tree025_454,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_456 : CoverTree := CoverTree.split [tree025_111,tree025_440,tree025_445,tree025_450,tree025_453,tree025_455]
def tree025_457 : CoverTree := CoverTree.split [tree025_425,tree025_439,tree025_456,tree025_66,tree025_79,tree025_85]
def tree025_458 : CoverTree := CoverTree.reject 43
def tree025_459 : CoverTree := CoverTree.reject 320
def tree025_460 : CoverTree := CoverTree.reject 321
def tree025_461 : CoverTree := CoverTree.reject 322
def tree025_462 : CoverTree := CoverTree.split [tree025_19,tree025_407,tree025_459,tree025_460,tree025_461,tree025_17]
def tree025_463 : CoverTree := CoverTree.reject 244
def tree025_464 : CoverTree := CoverTree.reject 245
def tree025_465 : CoverTree := CoverTree.reject 246
def tree025_466 : CoverTree := CoverTree.reject 247
def tree025_467 : CoverTree := CoverTree.split [tree025_21,tree025_463,tree025_464,tree025_465,tree025_466,tree025_17]
def tree025_468 : CoverTree := CoverTree.reject 248
def tree025_469 : CoverTree := CoverTree.reject 249
def tree025_470 : CoverTree := CoverTree.split [tree025_416,tree025_468,tree025_469,tree025_17,tree025_17,tree025_17]
def tree025_471 : CoverTree := CoverTree.reject 250
def tree025_472 : CoverTree := CoverTree.split [tree025_471,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_473 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_462,tree025_467,tree025_470,tree025_472]
def tree025_474 : CoverTree := CoverTree.split [tree025_458,tree025_473,tree025_270,tree025_99,tree025_109,tree025_23]
def tree025_475 : CoverTree := CoverTree.reject 412
def tree025_476 : CoverTree := CoverTree.reject 325
def tree025_477 : CoverTree := CoverTree.reject 326
def tree025_478 : CoverTree := CoverTree.reject 327
def tree025_479 : CoverTree := CoverTree.split [tree025_19,tree025_407,tree025_476,tree025_477,tree025_478,tree025_17]
def tree025_480 : CoverTree := CoverTree.reject 234
def tree025_481 : CoverTree := CoverTree.reject 235
def tree025_482 : CoverTree := CoverTree.reject 236
def tree025_483 : CoverTree := CoverTree.split [tree025_21,tree025_480,tree025_481,tree025_482,tree025_17,tree025_17]
def tree025_484 : CoverTree := CoverTree.reject 237
def tree025_485 : CoverTree := CoverTree.reject 238
def tree025_486 : CoverTree := CoverTree.split [tree025_416,tree025_484,tree025_485,tree025_17,tree025_17,tree025_17]
def tree025_487 : CoverTree := CoverTree.reject 203
def tree025_488 : CoverTree := CoverTree.split [tree025_487,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_489 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_479,tree025_483,tree025_486,tree025_488]
def tree025_490 : CoverTree := CoverTree.split [tree025_475,tree025_489,tree025_124,tree025_133,tree025_33,tree025_37]
def tree025_491 : CoverTree := CoverTree.split [tree025_19,tree025_407,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_492 : CoverTree := CoverTree.split [tree025_21,tree025_412,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_493 : CoverTree := CoverTree.split [tree025_416,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_494 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_491,tree025_492,tree025_493,tree025_421]
def tree025_495 : CoverTree := CoverTree.split [tree025_406,tree025_494,tree025_138,tree025_43,tree025_46,tree025_47]
def tree025_496 : CoverTree := CoverTree.split [tree025_3,tree025_3,tree025_457,tree025_474,tree025_490,tree025_495]
def tree025_497 : CoverTree := CoverTree.split [tree025_278,tree025_295,tree025_340,tree025_378,tree025_424,tree025_496]
def tree025_498 : CoverTree := CoverTree.reject 29
def tree025_499 : CoverTree := CoverTree.reject 61
def tree025_500 : CoverTree := CoverTree.reject 156
def tree025_501 : CoverTree := CoverTree.reject 183
def tree025_502 : CoverTree := CoverTree.reject 375
def tree025_503 : CoverTree := CoverTree.split [tree025_283,tree025_283,tree025_283,tree025_502,tree025_17,tree025_17]
def tree025_504 : CoverTree := CoverTree.split [tree025_282,tree025_282,tree025_503,tree025_286,tree025_286,tree025_286]
def tree025_505 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_280,tree025_501,tree025_504]
def tree025_506 : CoverTree := CoverTree.reject 374
def tree025_507 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_280,tree025_506,tree025_287]
def tree025_508 : CoverTree := CoverTree.reject 6
def tree025_509 : CoverTree := CoverTree.split [tree025_508,tree025_508,tree025_508,tree025_508,tree025_286,tree025_286]
def tree025_510 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_280,tree025_509,tree025_289]
def tree025_511 : CoverTree := CoverTree.reject 169
def tree025_512 : CoverTree := CoverTree.split [tree025_40,tree025_282,tree025_511,tree025_286,tree025_286,tree025_286]
def tree025_513 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_292,tree025_512,tree025_289,tree025_289]
def tree025_514 : CoverTree := CoverTree.split [tree025_499,tree025_500,tree025_505,tree025_507,tree025_510,tree025_513]
def tree025_515 : CoverTree := CoverTree.reject 34
def tree025_516 : CoverTree := CoverTree.reject 50
def tree025_517 : CoverTree := CoverTree.reject 51
def tree025_518 : CoverTree := CoverTree.reject 1
def tree025_519 : CoverTree := CoverTree.reject 358
def tree025_520 : CoverTree := CoverTree.reject 159
def tree025_521 : CoverTree := CoverTree.reject 376
def tree025_522 : CoverTree := CoverTree.split [tree025_520,tree025_521,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_523 : CoverTree := CoverTree.reject 377
def tree025_524 : CoverTree := CoverTree.split [tree025_17,tree025_523,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_525 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_519,tree025_522,tree025_524]
def tree025_526 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_516,tree025_517,tree025_525]
def tree025_527 : CoverTree := CoverTree.reject 372
def tree025_528 : CoverTree := CoverTree.reject 188
def tree025_529 : CoverTree := CoverTree.reject 170
def tree025_530 : CoverTree := CoverTree.reject 378
def tree025_531 : CoverTree := CoverTree.split [tree025_17,tree025_530,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_532 : CoverTree := CoverTree.split [tree025_67,tree025_527,tree025_528,tree025_529,tree025_78,tree025_531]
def tree025_533 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_143,tree025_532,tree025_308]
def tree025_534 : CoverTree := CoverTree.reject 82
def tree025_535 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_534,tree025_319,tree025_158]
def tree025_536 : CoverTree := CoverTree.reject 420
def tree025_537 : CoverTree := CoverTree.reject 421
def tree025_538 : CoverTree := CoverTree.reject 267
def tree025_539 : CoverTree := CoverTree.reject 268
def tree025_540 : CoverTree := CoverTree.reject 269
def tree025_541 : CoverTree := CoverTree.split [tree025_21,tree025_538,tree025_539,tree025_540,tree025_17,tree025_17]
def tree025_542 : CoverTree := CoverTree.split [tree025_111,tree025_536,tree025_537,tree025_541,tree025_173,tree025_175]
def tree025_543 : CoverTree := CoverTree.reject 393
def tree025_544 : CoverTree := CoverTree.split [tree025_40,tree025_543,tree025_181,tree025_183,tree025_17,tree025_17]
def tree025_545 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_542,tree025_544,tree025_186,tree025_47]
def tree025_546 : CoverTree := CoverTree.split [tree025_515,tree025_526,tree025_533,tree025_535,tree025_330,tree025_545]
def tree025_547 : CoverTree := CoverTree.reject 33
def tree025_548 : CoverTree := CoverTree.reject 58
def tree025_549 : CoverTree := CoverTree.reject 52
def tree025_550 : CoverTree := CoverTree.reject 184
def tree025_551 : CoverTree := CoverTree.reject 185
def tree025_552 : CoverTree := CoverTree.reject 379
def tree025_553 : CoverTree := CoverTree.reject 380
def tree025_554 : CoverTree := CoverTree.split [tree025_21,tree025_550,tree025_551,tree025_552,tree025_553,tree025_17]
def tree025_555 : CoverTree := CoverTree.reject 186
def tree025_556 : CoverTree := CoverTree.reject 187
def tree025_557 : CoverTree := CoverTree.reject 381
def tree025_558 : CoverTree := CoverTree.split [tree025_555,tree025_556,tree025_557,tree025_17,tree025_17,tree025_17]
def tree025_559 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_554,tree025_558,tree025_17]
def tree025_560 : CoverTree := CoverTree.reject 158
def tree025_561 : CoverTree := CoverTree.split [tree025_21,tree025_560,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_562 : CoverTree := CoverTree.reject 382
def tree025_563 : CoverTree := CoverTree.split [tree025_520,tree025_562,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_564 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_561,tree025_563,tree025_17]
def tree025_565 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_548,tree025_549,tree025_559,tree025_564]
def tree025_566 : CoverTree := CoverTree.reject 83
def tree025_567 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_191,tree025_566,tree025_348,tree025_202]
def tree025_568 : CoverTree := CoverTree.reject 84
def tree025_569 : CoverTree := CoverTree.reject 85
def tree025_570 : CoverTree := CoverTree.reject 383
def tree025_571 : CoverTree := CoverTree.split [tree025_122,tree025_266,tree025_570,tree025_17,tree025_17,tree025_17]
def tree025_572 : CoverTree := CoverTree.reject 384
def tree025_573 : CoverTree := CoverTree.split [tree025_268,tree025_572,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_574 : CoverTree := CoverTree.split [tree025_111,tree025_354,tree025_568,tree025_569,tree025_571,tree025_573]
def tree025_575 : CoverTree := CoverTree.reject 373
def tree025_576 : CoverTree := CoverTree.reject 189
def tree025_577 : CoverTree := CoverTree.split [tree025_40,tree025_575,tree025_576,tree025_96,tree025_98,tree025_17]
def tree025_578 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_574,tree025_577,tree025_212,tree025_23]
def tree025_579 : CoverTree := CoverTree.reject 172
def tree025_580 : CoverTree := CoverTree.reject 385
def tree025_581 : CoverTree := CoverTree.reject 386
def tree025_582 : CoverTree := CoverTree.split [tree025_21,tree025_412,tree025_580,tree025_581,tree025_17,tree025_17]
def tree025_583 : CoverTree := CoverTree.reject 387
def tree025_584 : CoverTree := CoverTree.reject 388
def tree025_585 : CoverTree := CoverTree.split [tree025_416,tree025_583,tree025_584,tree025_17,tree025_17,tree025_17]
def tree025_586 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_579,tree025_582,tree025_585,tree025_421]
def tree025_587 : CoverTree := CoverTree.reject 295
def tree025_588 : CoverTree := CoverTree.reject 296
def tree025_589 : CoverTree := CoverTree.split [tree025_15,tree025_41,tree025_587,tree025_588,tree025_17,tree025_17]
def tree025_590 : CoverTree := CoverTree.split [tree025_40,tree025_589,tree025_375,tree025_229,tree025_17,tree025_17]
def tree025_591 : CoverTree := CoverTree.split [tree025_361,tree025_586,tree025_371,tree025_590,tree025_233,tree025_47]
def tree025_592 : CoverTree := CoverTree.split [tree025_547,tree025_565,tree025_567,tree025_578,tree025_360,tree025_591]
def tree025_593 : CoverTree := CoverTree.reject 21
def tree025_594 : CoverTree := CoverTree.reject 18
def tree025_595 : CoverTree := CoverTree.reject 53
def tree025_596 : CoverTree := CoverTree.reject 54
def tree025_597 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_593,tree025_594,tree025_595,tree025_596]
def tree025_598 : CoverTree := CoverTree.reject 60
def tree025_599 : CoverTree := CoverTree.reject 220
def tree025_600 : CoverTree := CoverTree.reject 221
def tree025_601 : CoverTree := CoverTree.reject 222
def tree025_602 : CoverTree := CoverTree.split [tree025_21,tree025_599,tree025_600,tree025_601,tree025_17,tree025_17]
def tree025_603 : CoverTree := CoverTree.reject 223
def tree025_604 : CoverTree := CoverTree.reject 224
def tree025_605 : CoverTree := CoverTree.reject 225
def tree025_606 : CoverTree := CoverTree.split [tree025_603,tree025_604,tree025_605,tree025_17,tree025_17,tree025_17]
def tree025_607 : CoverTree := CoverTree.reject 226
def tree025_608 : CoverTree := CoverTree.reject 227
def tree025_609 : CoverTree := CoverTree.split [tree025_607,tree025_608,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_610 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_602,tree025_606,tree025_609]
def tree025_611 : CoverTree := CoverTree.split [tree025_21,tree025_550,tree025_551,tree025_17,tree025_17,tree025_17]
def tree025_612 : CoverTree := CoverTree.split [tree025_555,tree025_556,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_613 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_611,tree025_612,tree025_17]
def tree025_614 : CoverTree := CoverTree.split [tree025_520,tree025_17,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_615 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_561,tree025_614,tree025_17]
def tree025_616 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_598,tree025_610,tree025_613,tree025_615]
def tree025_617 : CoverTree := CoverTree.reject 124
def tree025_618 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_617,tree025_381,tree025_383,tree025_241]
def tree025_619 : CoverTree := CoverTree.reject 190
def tree025_620 : CoverTree := CoverTree.split [tree025_111,tree025_619,tree025_262,tree025_265,tree025_267,tree025_269]
def tree025_621 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_620,tree025_99,tree025_109,tree025_23]
def tree025_622 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_411,tree025_415,tree025_493,tree025_421]
def tree025_623 : CoverTree := CoverTree.split [tree025_406,tree025_622,tree025_251,tree025_43,tree025_46,tree025_47]
def tree025_624 : CoverTree := CoverTree.split [tree025_597,tree025_616,tree025_618,tree025_621,tree025_390,tree025_623]
def tree025_625 : CoverTree := CoverTree.reject 57
def tree025_626 : CoverTree := CoverTree.reject 41
def tree025_627 : CoverTree := CoverTree.reject 55
def tree025_628 : CoverTree := CoverTree.reject 56
def tree025_629 : CoverTree := CoverTree.split [tree025_625,tree025_626,tree025_593,tree025_594,tree025_627,tree025_628]
def tree025_630 : CoverTree := CoverTree.reject 48
def tree025_631 : CoverTree := CoverTree.reject 241
def tree025_632 : CoverTree := CoverTree.reject 306
def tree025_633 : CoverTree := CoverTree.reject 364
def tree025_634 : CoverTree := CoverTree.reject 365
def tree025_635 : CoverTree := CoverTree.reject 366
def tree025_636 : CoverTree := CoverTree.reject 367
def tree025_637 : CoverTree := CoverTree.split [tree025_122,tree025_633,tree025_634,tree025_635,tree025_636,tree025_17]
def tree025_638 : CoverTree := CoverTree.reject 368
def tree025_639 : CoverTree := CoverTree.reject 369
def tree025_640 : CoverTree := CoverTree.split [tree025_638,tree025_639,tree025_17,tree025_17,tree025_17,tree025_17]
def tree025_641 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_632,tree025_637,tree025_640]
def tree025_642 : CoverTree := CoverTree.split [tree025_630,tree025_631,tree025_641,tree025_610,tree025_613,tree025_615]
def tree025_643 : CoverTree := CoverTree.reject 323
def tree025_644 : CoverTree := CoverTree.reject 324
def tree025_645 : CoverTree := CoverTree.split [tree025_394,tree025_395,tree025_396,tree025_643,tree025_644,tree025_17]
def tree025_646 : CoverTree := CoverTree.reject 93
def tree025_647 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_392,tree025_393,tree025_645,tree025_646]
def tree025_648 : CoverTree := CoverTree.split [tree025_647,tree025_489,tree025_124,tree025_133,tree025_33,tree025_37]
def tree025_649 : CoverTree := CoverTree.split [tree025_629,tree025_642,tree025_457,tree025_474,tree025_648,tree025_495]
def tree025_650 : CoverTree := CoverTree.split [tree025_498,tree025_514,tree025_546,tree025_592,tree025_624,tree025_649]
def tree025_651 : CoverTree := CoverTree.reject 87
def tree025_652 : CoverTree := CoverTree.reject 70
def tree025_653 : CoverTree := CoverTree.reject 62
def tree025_654 : CoverTree := CoverTree.reject 63
def tree025_655 : CoverTree := CoverTree.reject 151
def tree025_656 : CoverTree := CoverTree.reject 363
def tree025_657 : CoverTree := CoverTree.split [tree025_282,tree025_282,tree025_656,tree025_286,tree025_286,tree025_286]
def tree025_658 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_280,tree025_655,tree025_657]
def tree025_659 : CoverTree := CoverTree.reject 88
def tree025_660 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_292,tree025_659,tree025_289,tree025_289]
def tree025_661 : CoverTree := CoverTree.split [tree025_651,tree025_652,tree025_653,tree025_654,tree025_658,tree025_660]
def tree025_662 : CoverTree := CoverTree.reject 157
def tree025_663 : CoverTree := CoverTree.reject 22
def tree025_664 : CoverTree := CoverTree.split [tree025_508,tree025_508,tree025_508,tree025_508,tree025_663,tree025_286]
def tree025_665 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_280,tree025_664,tree025_287]
def tree025_666 : CoverTree := CoverTree.split [tree025_499,tree025_662,tree025_505,tree025_665,tree025_510,tree025_513]
def tree025_667 : CoverTree := CoverTree.reject 404
def tree025_668 : CoverTree := CoverTree.split [tree025_21,tree025_560,tree025_667,tree025_17,tree025_17,tree025_17]
def tree025_669 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_668,tree025_522,tree025_524]
def tree025_670 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_516,tree025_517,tree025_669]
def tree025_671 : CoverTree := CoverTree.reject 402
def tree025_672 : CoverTree := CoverTree.reject 239
def tree025_673 : CoverTree := CoverTree.split [tree025_40,tree025_671,tree025_672,tree025_96,tree025_98,tree025_17]
def tree025_674 : CoverTree := CoverTree.split [tree025_142,tree025_142,tree025_142,tree025_673,tree025_319,tree025_158]
def tree025_675 : CoverTree := CoverTree.reject 262
def tree025_676 : CoverTree := CoverTree.reject 263
def tree025_677 : CoverTree := CoverTree.split [tree025_15,tree025_112,tree025_113,tree025_675,tree025_676,tree025_17]
def tree025_678 : CoverTree := CoverTree.reject 264
def tree025_679 : CoverTree := CoverTree.reject 265
def tree025_680 : CoverTree := CoverTree.reject 266
def tree025_681 : CoverTree := CoverTree.split [tree025_19,tree025_136,tree025_678,tree025_679,tree025_680,tree025_17]
def tree025_682 : CoverTree := CoverTree.split [tree025_111,tree025_677,tree025_681,tree025_541,tree025_173,tree025_175]
def tree025_683 : CoverTree := CoverTree.reject 273
def tree025_684 : CoverTree := CoverTree.split [tree025_15,tree025_41,tree025_17,tree025_683,tree025_17,tree025_17]
def tree025_685 : CoverTree := CoverTree.split [tree025_40,tree025_684,tree025_181,tree025_183,tree025_17,tree025_17]
def tree025_686 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_682,tree025_685,tree025_186,tree025_47]
def tree025_687 : CoverTree := CoverTree.split [tree025_515,tree025_670,tree025_533,tree025_674,tree025_330,tree025_686]
def tree025_688 : CoverTree := CoverTree.reject 403
def tree025_689 : CoverTree := CoverTree.reject 328
def tree025_690 : CoverTree := CoverTree.reject 211
def tree025_691 : CoverTree := CoverTree.reject 405
def tree025_692 : CoverTree := CoverTree.split [tree025_61,tree025_62,tree025_691,tree025_17,tree025_17,tree025_17]
def tree025_693 : CoverTree := CoverTree.split [tree025_40,tree025_688,tree025_689,tree025_690,tree025_692,tree025_65]
def tree025_694 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_191,tree025_693,tree025_348,tree025_202]
def tree025_695 : CoverTree := CoverTree.reject 155
def tree025_696 : CoverTree := CoverTree.reject 253
def tree025_697 : CoverTree := CoverTree.split [tree025_695,tree025_696,tree025_357,tree025_359,tree025_33,tree025_37]
def tree025_698 : CoverTree := CoverTree.split [tree025_547,tree025_565,tree025_694,tree025_578,tree025_697,tree025_591]
def tree025_699 : CoverTree := CoverTree.reject 240
def tree025_700 : CoverTree := CoverTree.reject 86
def tree025_701 : CoverTree := CoverTree.split [tree025_111,tree025_699,tree025_700,tree025_450,tree025_453,tree025_455]
def tree025_702 : CoverTree := CoverTree.split [tree025_341,tree025_341,tree025_701,tree025_381,tree025_383,tree025_241]
def tree025_703 : CoverTree := CoverTree.reject 89
def tree025_704 : CoverTree := CoverTree.reject 150
def tree025_705 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_704,tree025_483,tree025_486,tree025_488]
def tree025_706 : CoverTree := CoverTree.split [tree025_703,tree025_705,tree025_389,tree025_133,tree025_33,tree025_37]
def tree025_707 : CoverTree := CoverTree.split [tree025_597,tree025_616,tree025_702,tree025_621,tree025_706,tree025_623]
def tree025_708 : CoverTree := CoverTree.reject 106
def tree025_709 : CoverTree := CoverTree.reject 107
def tree025_710 : CoverTree := CoverTree.reject 394
def tree025_711 : CoverTree := CoverTree.reject 395
def tree025_712 : CoverTree := CoverTree.reject 396
def tree025_713 : CoverTree := CoverTree.reject 397
def tree025_714 : CoverTree := CoverTree.split [tree025_710,tree025_711,tree025_712,tree025_713,tree025_17,tree025_17]
def tree025_715 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_708,tree025_709,tree025_714]
def tree025_716 : CoverTree := CoverTree.reject 398
def tree025_717 : CoverTree := CoverTree.reject 399
def tree025_718 : CoverTree := CoverTree.reject 400
def tree025_719 : CoverTree := CoverTree.reject 401
def tree025_720 : CoverTree := CoverTree.split [tree025_21,tree025_716,tree025_717,tree025_718,tree025_719,tree025_17]
def tree025_721 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_720,tree025_637,tree025_640]
def tree025_722 : CoverTree := CoverTree.split [tree025_630,tree025_715,tree025_721,tree025_610,tree025_613,tree025_615]
def tree025_723 : CoverTree := CoverTree.split [tree025_629,tree025_722,tree025_457,tree025_474,tree025_648,tree025_495]
def tree025_724 : CoverTree := CoverTree.split [tree025_661,tree025_666,tree025_687,tree025_698,tree025_707,tree025_723]
def tree025_725 : CoverTree := CoverTree.reject 214
def tree025_726 : CoverTree := CoverTree.reject 174
def tree025_727 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_292,tree025_725,tree025_655,tree025_726]
def tree025_728 : CoverTree := CoverTree.split [tree025_651,tree025_652,tree025_653,tree025_654,tree025_727,tree025_660]
def tree025_729 : CoverTree := CoverTree.reject 359
def tree025_730 : CoverTree := CoverTree.reject 360
def tree025_731 : CoverTree := CoverTree.reject 370
def tree025_732 : CoverTree := CoverTree.reject 413
def tree025_733 : CoverTree := CoverTree.split [tree025_283,tree025_283,tree025_283,tree025_732,tree025_17,tree025_17]
def tree025_734 : CoverTree := CoverTree.split [tree025_518,tree025_518,tree025_518,tree025_731,tree025_733,tree025_286]
def tree025_735 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_292,tree025_729,tree025_730,tree025_734]
def tree025_736 : CoverTree := CoverTree.reject 361
def tree025_737 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_292,tree025_736,tree025_501,tree025_504]
def tree025_738 : CoverTree := CoverTree.reject 362
def tree025_739 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_292,tree025_738,tree025_664,tree025_287]
def tree025_740 : CoverTree := CoverTree.reject 371
def tree025_741 : CoverTree := CoverTree.split [tree025_508,tree025_508,tree025_508,tree025_508,tree025_740,tree025_286]
def tree025_742 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_292,tree025_741,tree025_509,tree025_289]
def tree025_743 : CoverTree := CoverTree.split [tree025_499,tree025_735,tree025_737,tree025_739,tree025_742,tree025_513]
def tree025_744 : CoverTree := CoverTree.reject 215
def tree025_745 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_744,tree025_516,tree025_517,tree025_669]
def tree025_746 : CoverTree := CoverTree.reject 242
def tree025_747 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_746,tree025_143,tree025_532,tree025_308]
def tree025_748 : CoverTree := CoverTree.reject 243
def tree025_749 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_748,tree025_673,tree025_319,tree025_158]
def tree025_750 : CoverTree := CoverTree.reject 40
def tree025_751 : CoverTree := CoverTree.split [tree025_111,tree025_750,tree025_750,tree025_750,tree025_750,tree025_17]
def tree025_752 : CoverTree := CoverTree.split [tree025_291,tree025_291,tree025_751,tree025_329,tree025_163,tree025_166]
def tree025_753 : CoverTree := CoverTree.split [tree025_515,tree025_745,tree025_747,tree025_749,tree025_752,tree025_686]
def tree025_754 : CoverTree := CoverTree.reject 216
def tree025_755 : CoverTree := CoverTree.split [tree025_630,tree025_754,tree025_548,tree025_549,tree025_559,tree025_564]
def tree025_756 : CoverTree := CoverTree.reject 217
def tree025_757 : CoverTree := CoverTree.split [tree025_425,tree025_756,tree025_191,tree025_693,tree025_348,tree025_202]
def tree025_758 : CoverTree := CoverTree.reject 218
def tree025_759 : CoverTree := CoverTree.split [tree025_458,tree025_758,tree025_574,tree025_577,tree025_212,tree025_23]
def tree025_760 : CoverTree := CoverTree.reject 19
def tree025_761 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_760,tree025_760,tree025_760,tree025_488]
def tree025_762 : CoverTree := CoverTree.split [tree025_695,tree025_761,tree025_357,tree025_359,tree025_33,tree025_37]
def tree025_763 : CoverTree := CoverTree.split [tree025_547,tree025_755,tree025_757,tree025_759,tree025_762,tree025_591]
def tree025_764 : CoverTree := CoverTree.split [tree025_625,tree025_626,tree025_593,tree025_594,tree025_595,tree025_596]
def tree025_765 : CoverTree := CoverTree.reject 219
def tree025_766 : CoverTree := CoverTree.split [tree025_630,tree025_765,tree025_598,tree025_610,tree025_613,tree025_615]
def tree025_767 : CoverTree := CoverTree.reject 132
def tree025_768 : CoverTree := CoverTree.split [tree025_425,tree025_767,tree025_701,tree025_381,tree025_383,tree025_241]
def tree025_769 : CoverTree := CoverTree.reject 411
def tree025_770 : CoverTree := CoverTree.reject 414
def tree025_771 : CoverTree := CoverTree.split [tree025_416,tree025_468,tree025_469,tree025_770,tree025_17,tree025_17]
def tree025_772 : CoverTree := CoverTree.split [tree025_391,tree025_391,tree025_704,tree025_769,tree025_771,tree025_472]
def tree025_773 : CoverTree := CoverTree.split [tree025_458,tree025_772,tree025_620,tree025_99,tree025_109,tree025_23]
def tree025_774 : CoverTree := CoverTree.split [tree025_764,tree025_766,tree025_768,tree025_773,tree025_706,tree025_623]
def tree025_775 : CoverTree := CoverTree.split [tree025_728,tree025_743,tree025_753,tree025_763,tree025_774,tree025_723]
def tree025_776 : CoverTree := CoverTree.split [tree025_141,tree025_277,tree025_497,tree025_650,tree025_724,tree025_775]
def tree025 : CoverTree := tree025_776

end Snake9.Shared89
