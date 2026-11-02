import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes045 : List Box := [
[(1,6),(1,3),(1,6),(1,3),(1,6),(1,6)],
[(1,3),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,5),(1,3),(1,5)],
[(1,6),(1,3),(1,6),(1,6),(1,2),(1,6)],
[(1,2),(1,6),(1,6),(1,3),(1,6),(1,6)],
[(1,2),(1,4),(1,5),(1,5),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,5),(1,5),(1,4)],
[(1,6),(1,5),(1,5),(1,4),(1,2),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,6),(1,5),(1,5),(1,2),(1,3)],
[(1,3),(1,5),(1,3),(1,5),(1,6),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,4),(1,5),(1,2),(1,5),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,2),(1,5)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,2),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,4),(1,5),(1,5)],
[(1,1),(6,6),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(6,6),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(1,6)],
[(1,6),(2,2),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(2,2),(1,6),(1,6),(1,6)],
[(1,5),(1,5),(1,2),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,3),(1,2)],
[(1,1),(6,6),(3,3),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(5,5),(1,1),(5,5),(1,6),(1,6),(1,6)],
[(5,5),(1,1),(6,6),(1,6),(1,6),(1,6)],
[(6,6),(1,1),(5,5),(1,6),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(1,6),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,1),(5,5),(5,5),(1,6),(1,6),(1,6)],
[(4,4),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(1,6),(1,6),(1,6)],
[(5,5),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(1,6)],
[(4,4),(6,6),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(1,5),(1,3),(1,5),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(5,5),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(5,5),(3,3),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(6,6),(1,1),(1,6)],
[(1,6),(1,6),(4,4),(6,6),(1,1),(1,6)],
[(1,6),(1,6),(5,5),(5,5),(1,1),(1,6)],
[(1,6),(1,5),(1,2),(1,5),(1,4),(1,6)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(6,6),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(2,2),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(3,3),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,5),(1,2),(1,6)],
[(5,5),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(1,1)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)],
[(4,4),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(5,5),(4,4),(2,2)],
[(2,2),(6,6),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)],
[(4,4),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(4,4),(3,3),(2,2),(1,6),(1,6),(1,6)],
[(4,4),(4,4),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(3,3)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(4,4)],
[(1,6),(1,6),(4,4),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(6,6),(5,5),(1,1),(6,6)],
[(3,3),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(5,5),(2,2),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(6,6),(5,5),(1,1)],
[(1,6),(2,2),(5,5),(5,5),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(1,6),(4,4),(5,5),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(2,2)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(3,3)],
[(1,4),(1,5),(1,3),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,6),(5,5),(3,3),(2,2),(1,6)],
[(4,4),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(4,4),(2,2),(5,5),(2,2)],
[(1,6),(1,6),(4,4),(2,2),(5,5),(3,3)],
[(1,6),(1,6),(4,4),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(4,4),(2,2),(6,6),(2,2)],
[(1,6),(1,6),(4,4),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(6,6),(2,2),(3,3),(3,3)],
[(1,6),(1,6),(6,6),(3,3),(3,3),(2,2)],
[(1,6),(2,2),(5,5),(4,4),(3,3),(1,6)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(1,6)],
[(1,6),(6,6),(1,1),(5,5),(6,6),(1,6)],
[(6,6),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(5,5),(2,2)],
[(4,4),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(4,4),(2,2)],
[(1,6),(1,6),(2,2),(6,6),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(6,6),(5,5),(1,1)],
[(1,6),(1,6),(2,2),(6,6),(5,5),(2,2)],
[(1,6),(1,6),(5,5),(2,2),(4,4),(2,2)],
[(1,6),(1,6),(5,5),(2,2),(4,4),(3,3)],
[(1,6),(1,6),(5,5),(2,2),(5,5),(2,2)],
[(1,6),(1,6),(5,5),(2,2),(5,5),(3,3)],
[(1,6),(1,6),(5,5),(2,2),(6,6),(1,1)],
[(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(5,5),(1,1),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(2,2),(4,4),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(4,4)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(3,3)],
[(1,6),(2,2),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(3,3)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(3,3)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(4,4)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(3,3)],
[(1,6),(2,2),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(4,4),(1,6)],
[(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(4,4),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(1,2),(1,3),(1,5),(1,4),(1,6)],
[(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(4,4),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(4,4),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(5,5),(1,6)],
[(1,6),(1,6),(5,5),(4,4),(2,2),(4,4)],
[(1,6),(2,2),(4,4),(4,4),(4,4),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(4,4),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(5,5),(6,6),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(5,5),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(1,6),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(2,2),(2,2),(4,4),(1,6),(1,6)],
[(5,5),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(6,6),(5,5),(3,3),(4,4)],
[(1,6),(2,2),(6,6),(5,5),(4,4),(2,2)],
[(1,6),(2,2),(6,6),(6,6),(3,3),(2,2)],
[(1,6),(2,2),(6,6),(6,6),(3,3),(3,3)],
[(1,6),(3,3),(6,6),(4,4),(3,3),(2,2)],
[(1,6),(3,3),(6,6),(4,4),(3,3),(3,3)],
[(1,6),(3,3),(6,6),(4,4),(3,3),(4,4)],
[(1,6),(3,3),(6,6),(4,4),(4,4),(2,2)],
[(1,6),(4,4),(6,6),(4,4),(2,2),(3,3)],
[(1,6),(4,4),(6,6),(4,4),(2,2),(4,4)],
[(1,6),(4,4),(6,6),(4,4),(3,3),(2,2)],
[(1,6),(4,4),(6,6),(4,4),(4,4),(2,2)],
[(2,2),(4,4),(6,6),(6,6),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(5,5),(3,3),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(2,2),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(2,2),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(2,2),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(2,2),(3,3),(6,6),(2,2)],
[(1,6),(2,2),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(1,6),(2,2),(6,6),(4,4),(3,3),(2,2)],
[(1,6),(2,2),(6,6),(4,4),(3,3),(3,3)],
[(1,6),(2,2),(6,6),(4,4),(3,3),(4,4)],
[(1,6),(2,2),(6,6),(4,4),(4,4),(2,2)],
[(1,6),(2,2),(6,6),(4,4),(4,4),(3,3)],
[(1,6),(2,2),(6,6),(4,4),(5,5),(1,1)],
[(1,6),(2,2),(6,6),(4,4),(5,5),(2,2)],
[(1,6),(3,3),(5,5),(5,5),(4,4),(2,2)],
[(1,6),(4,4),(5,5),(4,4),(3,3),(3,3)],
[(1,6),(4,4),(6,6),(2,2),(3,3),(4,4)],
[(1,6),(4,4),(6,6),(2,2),(3,3),(5,5)],
[(1,6),(4,4),(6,6),(2,2),(4,4),(2,2)],
[(1,6),(4,4),(6,6),(2,2),(4,4),(3,3)],
[(1,6),(4,4),(6,6),(2,2),(4,4),(4,4)],
[(1,6),(4,4),(6,6),(2,2),(5,5),(2,2)],
[(1,6),(4,4),(6,6),(2,2),(6,6),(2,2)],
[(1,6),(4,4),(6,6),(3,3),(2,2),(5,5)],
[(1,6),(4,4),(6,6),(3,3),(3,3),(3,3)],
[(1,6),(4,4),(6,6),(3,3),(4,4),(2,2)],
[(1,6),(4,4),(6,6),(3,3),(5,5),(2,2)],
[(1,6),(5,5),(4,4),(3,3),(5,5),(3,3)],
[(1,6),(5,5),(4,4),(3,3),(6,6),(2,2)],
[(1,6),(5,5),(5,5),(3,3),(3,3),(4,4)],
[(1,6),(5,5),(5,5),(3,3),(4,4),(3,3)],
[(1,6),(5,5),(5,5),(4,4),(3,3),(3,3)],
[(1,6),(5,5),(6,6),(2,2),(3,3),(4,4)],
[(1,6),(5,5),(6,6),(2,2),(5,5),(2,2)],
[(2,2),(2,2),(6,6),(5,5),(3,3),(1,6)],
[(2,2),(6,6),(6,6),(4,4),(2,2),(1,6)],
[(3,3),(5,5),(6,6),(3,3),(3,3),(1,6)],
[(4,4),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(1,3),(1,2),(1,5),(1,5),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(5,5)],
[(1,6),(2,2),(2,2),(6,6),(4,4),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(5,5),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(5,5),(4,4),(4,4),(2,2)],
[(1,6),(2,2),(5,5),(4,4),(4,4),(3,3)],
[(1,6),(2,2),(5,5),(4,4),(5,5),(2,2)],
[(1,6),(2,2),(5,5),(4,4),(5,5),(3,3)],
[(1,6),(2,2),(5,5),(4,4),(6,6),(2,2)],
[(1,6),(2,2),(5,5),(5,5),(4,4),(2,2)],
[(1,6),(3,3),(5,5),(4,4),(4,4),(2,2)],
[(1,6),(3,3),(5,5),(4,4),(4,4),(3,3)],
[(1,6),(3,3),(5,5),(4,4),(5,5),(2,2)],
[(1,6),(4,4),(3,3),(5,5),(6,6),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(4,4),(5,5),(2,2),(4,4),(4,4)],
[(1,6),(4,4),(5,5),(2,2),(4,4),(5,5)],
[(1,6),(4,4),(5,5),(2,2),(5,5),(4,4)],
[(1,6),(4,4),(5,5),(2,2),(5,5),(5,5)],
[(1,6),(4,4),(5,5),(2,2),(6,6),(2,2)],
[(1,6),(4,4),(5,5),(2,2),(6,6),(3,3)],
[(1,6),(4,4),(5,5),(3,3),(4,4),(3,3)],
[(1,6),(4,4),(5,5),(3,3),(5,5),(3,3)],
[(1,6),(5,5),(2,2),(6,6),(6,6),(2,2)],
[(1,6),(5,5),(3,3),(3,3),(6,6),(3,3)],
[(1,6),(5,5),(5,5),(2,2),(4,4),(4,4)],
[(1,6),(5,5),(5,5),(2,2),(4,4),(5,5)],
[(1,6),(5,5),(5,5),(2,2),(5,5),(4,4)],
[(1,6),(5,5),(5,5),(2,2),(6,6),(2,2)],
[(1,6),(6,6),(2,2),(5,5),(6,6),(2,2)],
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(2,2)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(3,3)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(4,4)],
[(1,6),(2,2),(4,4),(4,4),(5,5),(2,2)],
[(1,6),(2,2),(4,4),(4,4),(5,5),(3,3)],
[(1,6),(2,2),(4,4),(4,4),(6,6),(2,2)],
[(1,6),(2,2),(4,4),(4,4),(6,6),(3,3)],
[(1,6),(2,2),(4,4),(4,4),(6,6),(4,4)],
[(1,6),(2,2),(4,4),(5,5),(5,5),(2,2)],
[(1,6),(2,2),(4,4),(5,5),(5,5),(3,3)],
[(1,6),(2,2),(4,4),(5,5),(6,6),(2,2)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(2,2)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(3,3)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(4,4)],
[(1,6),(2,2),(4,4),(6,6),(4,4),(2,2)],
[(1,6),(3,3),(3,3),(4,4),(5,5),(4,4)],
[(1,6),(3,3),(3,3),(4,4),(5,5),(5,5)],
[(1,6),(3,3),(3,3),(4,4),(6,6),(2,2)],
[(1,6),(3,3),(3,3),(4,4),(6,6),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(6,6),(2,2)],
[(1,6),(3,3),(4,4),(4,4),(5,5),(2,2)],
[(1,6),(3,3),(4,4),(4,4),(5,5),(3,3)],
[(1,6),(3,3),(4,4),(4,4),(6,6),(2,2)],
[(1,6),(4,4),(2,2),(5,5),(6,6),(2,2)],
[(1,6),(4,4),(2,2),(6,6),(6,6),(2,2)],
[(1,6),(4,4),(3,3),(3,3),(5,5),(5,5)],
[(1,6),(4,4),(3,3),(3,3),(6,6),(3,3)],
[(1,6),(4,4),(3,3),(4,4),(6,6),(2,2)],
[(1,6),(4,4),(3,3),(4,4),(6,6),(3,3)],
[(1,6),(4,4),(4,4),(2,2),(5,5),(4,4)],
[(1,6),(4,4),(4,4),(2,2),(5,5),(5,5)],
[(1,6),(4,4),(4,4),(2,2),(6,6),(3,3)],
[(1,6),(4,4),(4,4),(2,2),(6,6),(4,4)],
[(1,6),(4,4),(4,4),(3,3),(5,5),(3,3)],
[(1,6),(4,4),(4,4),(3,3),(6,6),(2,2)],
[(1,6),(4,4),(4,4),(3,3),(6,6),(3,3)],
[(1,6),(5,5),(2,2),(4,4),(6,6),(3,3)],
[(1,6),(5,5),(3,3),(2,2),(6,6),(4,4)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(4,4)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(5,5)],
[(1,6),(6,6),(1,1),(6,6),(5,5),(1,1)],
[(1,6),(6,6),(1,1),(6,6),(5,5),(2,2)],
[(1,6),(6,6),(1,1),(6,6),(5,5),(3,3)],
[(1,6),(6,6),(1,1),(6,6),(6,6),(2,2)],
[(3,3),(5,5),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(6,6),(2,2)],
[(1,6),(1,6),(1,1),(5,5),(6,6),(3,3)],
[(1,6),(4,4),(2,2),(4,4),(5,5),(1,6)],
[(1,6),(2,2),(2,2),(6,6),(5,5),(3,3)],
[(1,6),(2,2),(2,2),(6,6),(6,6),(2,2)],
[(1,6),(2,2),(3,3),(4,4),(6,6),(2,2)],
[(1,6),(2,2),(3,3),(4,4),(6,6),(3,3)],
[(1,6),(2,2),(3,3),(4,4),(6,6),(4,4)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(4,4)],
[(1,6),(2,2),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(2,2),(3,3),(6,6),(6,6),(2,2)],
[(1,6),(3,3),(2,2),(4,4),(6,6),(3,3)],
[(1,6),(3,3),(2,2),(4,4),(6,6),(4,4)],
[(1,6),(3,3),(2,2),(4,4),(6,6),(5,5)],
[(1,6),(3,3),(2,2),(5,5),(6,6),(2,2)],
[(1,6),(3,3),(2,2),(6,6),(5,5),(3,3)],
[(1,6),(3,3),(2,2),(6,6),(6,6),(2,2)],
[(1,6),(4,4),(2,2),(3,3),(6,6),(3,3)],
[(1,6),(4,4),(2,2),(4,4),(6,6),(3,3)],
[(1,6),(4,4),(2,2),(4,4),(6,6),(4,4)],
[(1,6),(4,4),(3,3),(2,2),(6,6),(4,4)],
[(1,6),(4,4),(3,3),(2,2),(6,6),(5,5)],
[(1,6),(5,5),(2,2),(3,3),(6,6),(3,3)],
[(1,6),(5,5),(2,2),(3,3),(6,6),(4,4)],
[(3,3),(5,5),(6,6),(2,2),(2,2),(1,6)]
]

def root045 : Nat := 3369

def tree045_0 : CoverTree := CoverTree.reject 34
def tree045_1 : CoverTree := CoverTree.reject 27
def tree045_2 : CoverTree := CoverTree.reject 28
def tree045_3 : CoverTree := CoverTree.reject 18
def tree045_4 : CoverTree := CoverTree.reject 1
def tree045_5 : CoverTree := CoverTree.reject 84
def tree045_6 : CoverTree := CoverTree.reject 66
def tree045_7 : CoverTree := CoverTree.reject 61
def tree045_8 : CoverTree := CoverTree.reject 4
def tree045_9 : CoverTree := CoverTree.reject 60
def tree045_10 : CoverTree := CoverTree.reject 26
def tree045_11 : CoverTree := CoverTree.reject 116
def tree045_12 : CoverTree := CoverTree.reject 214
def tree045_13 : CoverTree := CoverTree.accept
def tree045_14 : CoverTree := CoverTree.split [tree045_10,tree045_11,tree045_12,tree045_13,tree045_13,tree045_13]
def tree045_15 : CoverTree := CoverTree.reject 10
def tree045_16 : CoverTree := CoverTree.split [tree045_15,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_17 : CoverTree := CoverTree.reject 9
def tree045_18 : CoverTree := CoverTree.split [tree045_17,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_19 : CoverTree := CoverTree.split [tree045_9,tree045_14,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_20 : CoverTree := CoverTree.reject 23
def tree045_21 : CoverTree := CoverTree.reject 24
def tree045_22 : CoverTree := CoverTree.reject 25
def tree045_23 : CoverTree := CoverTree.reject 17
def tree045_24 : CoverTree := CoverTree.reject 125
def tree045_25 : CoverTree := CoverTree.split [tree045_20,tree045_21,tree045_22,tree045_23,tree045_13,tree045_24]
def tree045_26 : CoverTree := CoverTree.reject 117
def tree045_27 : CoverTree := CoverTree.split [tree045_10,tree045_26,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_28 : CoverTree := CoverTree.split [tree045_25,tree045_27,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_29 : CoverTree := CoverTree.split [tree045_20,tree045_21,tree045_22,tree045_23,tree045_13,tree045_13]
def tree045_30 : CoverTree := CoverTree.split [tree045_10,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_31 : CoverTree := CoverTree.split [tree045_29,tree045_30,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_32 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_19,tree045_28,tree045_31]
def tree045_33 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_5,tree045_6,tree045_7,tree045_32]
def tree045_34 : CoverTree := CoverTree.reject 49
def tree045_35 : CoverTree := CoverTree.reject 38
def tree045_36 : CoverTree := CoverTree.reject 11
def tree045_37 : CoverTree := CoverTree.reject 209
def tree045_38 : CoverTree := CoverTree.split [tree045_36,tree045_36,tree045_36,tree045_37,tree045_13,tree045_13]
def tree045_39 : CoverTree := CoverTree.reject 109
def tree045_40 : CoverTree := CoverTree.split [tree045_15,tree045_39,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_41 : CoverTree := CoverTree.reject 110
def tree045_42 : CoverTree := CoverTree.split [tree045_41,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_43 : CoverTree := CoverTree.split [tree045_9,tree045_38,tree045_40,tree045_18,tree045_42,tree045_13]
def tree045_44 : CoverTree := CoverTree.reject 82
def tree045_45 : CoverTree := CoverTree.split [tree045_36,tree045_36,tree045_36,tree045_13,tree045_13,tree045_13]
def tree045_46 : CoverTree := CoverTree.split [tree045_44,tree045_45,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_47 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_43,tree045_46,tree045_31]
def tree045_48 : CoverTree := CoverTree.split [tree045_10,tree045_11,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_49 : CoverTree := CoverTree.split [tree045_9,tree045_48,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_50 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_49,tree045_28,tree045_31]
def tree045_51 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_34,tree045_35,tree045_47,tree045_50]
def tree045_52 : CoverTree := CoverTree.split [tree045_0,tree045_1,tree045_2,tree045_3,tree045_33,tree045_51]
def tree045_53 : CoverTree := CoverTree.reject 35
def tree045_54 : CoverTree := CoverTree.reject 94
def tree045_55 : CoverTree := CoverTree.reject 95
def tree045_56 : CoverTree := CoverTree.reject 96
def tree045_57 : CoverTree := CoverTree.reject 0
def tree045_58 : CoverTree := CoverTree.reject 102
def tree045_59 : CoverTree := CoverTree.reject 3
def tree045_60 : CoverTree := CoverTree.reject 277
def tree045_61 : CoverTree := CoverTree.reject 221
def tree045_62 : CoverTree := CoverTree.split [tree045_17,tree045_61,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_63 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_60,tree045_62,tree045_13,tree045_13]
def tree045_64 : CoverTree := CoverTree.reject 222
def tree045_65 : CoverTree := CoverTree.reject 223
def tree045_66 : CoverTree := CoverTree.split [tree045_15,tree045_64,tree045_65,tree045_13,tree045_13,tree045_13]
def tree045_67 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_66,tree045_18,tree045_13,tree045_13]
def tree045_68 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_58,tree045_63,tree045_67]
def tree045_69 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_54,tree045_55,tree045_56,tree045_68]
def tree045_70 : CoverTree := CoverTree.reject 97
def tree045_71 : CoverTree := CoverTree.reject 98
def tree045_72 : CoverTree := CoverTree.reject 99
def tree045_73 : CoverTree := CoverTree.reject 224
def tree045_74 : CoverTree := CoverTree.reject 225
def tree045_75 : CoverTree := CoverTree.reject 226
def tree045_76 : CoverTree := CoverTree.split [tree045_15,tree045_73,tree045_74,tree045_75,tree045_13,tree045_13]
def tree045_77 : CoverTree := CoverTree.reject 227
def tree045_78 : CoverTree := CoverTree.split [tree045_17,tree045_77,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_79 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_76,tree045_78,tree045_13,tree045_13]
def tree045_80 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_81 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_79,tree045_80,tree045_80]
def tree045_82 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_70,tree045_71,tree045_72,tree045_81]
def tree045_83 : CoverTree := CoverTree.reject 85
def tree045_84 : CoverTree := CoverTree.reject 86
def tree045_85 : CoverTree := CoverTree.reject 5
def tree045_86 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_85,tree045_85,tree045_31]
def tree045_87 : CoverTree := CoverTree.reject 228
def tree045_88 : CoverTree := CoverTree.reject 229
def tree045_89 : CoverTree := CoverTree.split [tree045_10,tree045_11,tree045_87,tree045_88,tree045_13,tree045_13]
def tree045_90 : CoverTree := CoverTree.reject 230
def tree045_91 : CoverTree := CoverTree.split [tree045_15,tree045_90,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_92 : CoverTree := CoverTree.reject 231
def tree045_93 : CoverTree := CoverTree.split [tree045_17,tree045_92,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_94 : CoverTree := CoverTree.split [tree045_9,tree045_89,tree045_91,tree045_93,tree045_13,tree045_13]
def tree045_95 : CoverTree := CoverTree.reject 232
def tree045_96 : CoverTree := CoverTree.split [tree045_29,tree045_95,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_97 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_94,tree045_28,tree045_96]
def tree045_98 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_83,tree045_84,tree045_86,tree045_97]
def tree045_99 : CoverTree := CoverTree.reject 87
def tree045_100 : CoverTree := CoverTree.reject 36
def tree045_101 : CoverTree := CoverTree.reject 103
def tree045_102 : CoverTree := CoverTree.reject 81
def tree045_103 : CoverTree := CoverTree.reject 135
def tree045_104 : CoverTree := CoverTree.reject 136
def tree045_105 : CoverTree := CoverTree.split [tree045_10,tree045_103,tree045_104,tree045_13,tree045_13,tree045_13]
def tree045_106 : CoverTree := CoverTree.split [tree045_102,tree045_105,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_107 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_100,tree045_101,tree045_106]
def tree045_108 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_100,tree045_46,tree045_31]
def tree045_109 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_99,tree045_107,tree045_108,tree045_32]
def tree045_110 : CoverTree := CoverTree.reject 115
def tree045_111 : CoverTree := CoverTree.reject 215
def tree045_112 : CoverTree := CoverTree.reject 216
def tree045_113 : CoverTree := CoverTree.reject 2
def tree045_114 : CoverTree := CoverTree.split [tree045_113,tree045_113,tree045_113,tree045_113,tree045_113,tree045_13]
def tree045_115 : CoverTree := CoverTree.reject 133
def tree045_116 : CoverTree := CoverTree.split [tree045_17,tree045_115,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_117 : CoverTree := CoverTree.reject 22
def tree045_118 : CoverTree := CoverTree.reject 134
def tree045_119 : CoverTree := CoverTree.split [tree045_117,tree045_118,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_120 : CoverTree := CoverTree.split [tree045_111,tree045_112,tree045_114,tree045_116,tree045_119,tree045_13]
def tree045_121 : CoverTree := CoverTree.reject 80
def tree045_122 : CoverTree := CoverTree.reject 183
def tree045_123 : CoverTree := CoverTree.reject 184
def tree045_124 : CoverTree := CoverTree.reject 185
def tree045_125 : CoverTree := CoverTree.split [tree045_10,tree045_122,tree045_123,tree045_124,tree045_13,tree045_13]
def tree045_126 : CoverTree := CoverTree.reject 129
def tree045_127 : CoverTree := CoverTree.split [tree045_126,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_128 : CoverTree := CoverTree.split [tree045_121,tree045_125,tree045_16,tree045_18,tree045_127,tree045_13]
def tree045_129 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_110,tree045_120,tree045_128]
def tree045_130 : CoverTree := CoverTree.reject 217
def tree045_131 : CoverTree := CoverTree.reject 48
def tree045_132 : CoverTree := CoverTree.reject 121
def tree045_133 : CoverTree := CoverTree.reject 122
def tree045_134 : CoverTree := CoverTree.split [tree045_15,tree045_131,tree045_132,tree045_133,tree045_13,tree045_13]
def tree045_135 : CoverTree := CoverTree.reject 123
def tree045_136 : CoverTree := CoverTree.reject 124
def tree045_137 : CoverTree := CoverTree.split [tree045_17,tree045_135,tree045_136,tree045_13,tree045_13,tree045_13]
def tree045_138 : CoverTree := CoverTree.split [tree045_117,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_139 : CoverTree := CoverTree.split [tree045_9,tree045_130,tree045_134,tree045_137,tree045_138,tree045_13]
def tree045_140 : CoverTree := CoverTree.reject 175
def tree045_141 : CoverTree := CoverTree.reject 33
def tree045_142 : CoverTree := CoverTree.split [tree045_36,tree045_36,tree045_36,tree045_141,tree045_141,tree045_13]
def tree045_143 : CoverTree := CoverTree.split [tree045_15,tree045_131,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_144 : CoverTree := CoverTree.reject 114
def tree045_145 : CoverTree := CoverTree.split [tree045_17,tree045_144,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_146 : CoverTree := CoverTree.split [tree045_140,tree045_142,tree045_143,tree045_145,tree045_138,tree045_13]
def tree045_147 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_139,tree045_146,tree045_106]
def tree045_148 : CoverTree := CoverTree.reject 278
def tree045_149 : CoverTree := CoverTree.split [tree045_9,tree045_148,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_150 : CoverTree := CoverTree.split [tree045_8,tree045_8,tree045_8,tree045_149,tree045_28,tree045_31]
def tree045_151 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_129,tree045_147,tree045_47,tree045_150]
def tree045_152 : CoverTree := CoverTree.split [tree045_53,tree045_69,tree045_82,tree045_98,tree045_109,tree045_151]
def tree045_153 : CoverTree := CoverTree.reject 29
def tree045_154 : CoverTree := CoverTree.reject 100
def tree045_155 : CoverTree := CoverTree.reject 55
def tree045_156 : CoverTree := CoverTree.reject 50
def tree045_157 : CoverTree := CoverTree.reject 250
def tree045_158 : CoverTree := CoverTree.reject 251
def tree045_159 : CoverTree := CoverTree.reject 252
def tree045_160 : CoverTree := CoverTree.split [tree045_15,tree045_157,tree045_158,tree045_159,tree045_13,tree045_13]
def tree045_161 : CoverTree := CoverTree.reject 253
def tree045_162 : CoverTree := CoverTree.reject 254
def tree045_163 : CoverTree := CoverTree.split [tree045_17,tree045_161,tree045_162,tree045_13,tree045_13,tree045_13]
def tree045_164 : CoverTree := CoverTree.reject 255
def tree045_165 : CoverTree := CoverTree.reject 256
def tree045_166 : CoverTree := CoverTree.split [tree045_164,tree045_165,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_167 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_160,tree045_163,tree045_166,tree045_13]
def tree045_168 : CoverTree := CoverTree.reject 220
def tree045_169 : CoverTree := CoverTree.split [tree045_15,tree045_13,tree045_13,tree045_168,tree045_13,tree045_13]
def tree045_170 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_169,tree045_62,tree045_13,tree045_13]
def tree045_171 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_167,tree045_170,tree045_67]
def tree045_172 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_154,tree045_155,tree045_156,tree045_171]
def tree045_173 : CoverTree := CoverTree.reject 101
def tree045_174 : CoverTree := CoverTree.reject 56
def tree045_175 : CoverTree := CoverTree.reject 104
def tree045_176 : CoverTree := CoverTree.reject 257
def tree045_177 : CoverTree := CoverTree.split [tree045_17,tree045_176,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_178 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_16,tree045_177,tree045_13,tree045_13]
def tree045_179 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_175,tree045_178,tree045_80]
def tree045_180 : CoverTree := CoverTree.reject 233
def tree045_181 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_180,tree045_18,tree045_13,tree045_13]
def tree045_182 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_79,tree045_181,tree045_80]
def tree045_183 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_173,tree045_174,tree045_179,tree045_182]
def tree045_184 : CoverTree := CoverTree.reject 88
def tree045_185 : CoverTree := CoverTree.reject 14
def tree045_186 : CoverTree := CoverTree.reject 204
def tree045_187 : CoverTree := CoverTree.reject 173
def tree045_188 : CoverTree := CoverTree.reject 7
def tree045_189 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_134,tree045_137,tree045_138,tree045_13]
def tree045_190 : CoverTree := CoverTree.reject 107
def tree045_191 : CoverTree := CoverTree.split [tree045_190,tree045_190,tree045_143,tree045_145,tree045_138,tree045_13]
def tree045_192 : CoverTree := CoverTree.split [tree045_185,tree045_186,tree045_187,tree045_189,tree045_191,tree045_106]
def tree045_193 : CoverTree := CoverTree.reject 30
def tree045_194 : CoverTree := CoverTree.reject 19
def tree045_195 : CoverTree := CoverTree.reject 40
def tree045_196 : CoverTree := CoverTree.reject 41
def tree045_197 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_193,tree045_194,tree045_195,tree045_196]
def tree045_198 : CoverTree := CoverTree.reject 126
def tree045_199 : CoverTree := CoverTree.reject 106
def tree045_200 : CoverTree := CoverTree.reject 258
def tree045_201 : CoverTree := CoverTree.split [tree045_15,tree045_39,tree045_200,tree045_13,tree045_13,tree045_13]
def tree045_202 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_201,tree045_18,tree045_42,tree045_13]
def tree045_203 : CoverTree := CoverTree.split [tree045_44,tree045_190,tree045_16,tree045_18,tree045_13,tree045_13]
def tree045_204 : CoverTree := CoverTree.split [tree045_197,tree045_198,tree045_199,tree045_202,tree045_203,tree045_31]
def tree045_205 : CoverTree := CoverTree.reject 79
def tree045_206 : CoverTree := CoverTree.reject 39
def tree045_207 : CoverTree := CoverTree.reject 42
def tree045_208 : CoverTree := CoverTree.reject 43
def tree045_209 : CoverTree := CoverTree.split [tree045_205,tree045_206,tree045_193,tree045_194,tree045_207,tree045_208]
def tree045_210 : CoverTree := CoverTree.reject 74
def tree045_211 : CoverTree := CoverTree.reject 112
def tree045_212 : CoverTree := CoverTree.reject 140
def tree045_213 : CoverTree := CoverTree.reject 155
def tree045_214 : CoverTree := CoverTree.reject 259
def tree045_215 : CoverTree := CoverTree.reject 260
def tree045_216 : CoverTree := CoverTree.split [tree045_15,tree045_212,tree045_213,tree045_214,tree045_215,tree045_13]
def tree045_217 : CoverTree := CoverTree.reject 261
def tree045_218 : CoverTree := CoverTree.reject 262
def tree045_219 : CoverTree := CoverTree.reject 263
def tree045_220 : CoverTree := CoverTree.split [tree045_17,tree045_217,tree045_218,tree045_219,tree045_13,tree045_13]
def tree045_221 : CoverTree := CoverTree.reject 90
def tree045_222 : CoverTree := CoverTree.reject 264
def tree045_223 : CoverTree := CoverTree.split [tree045_221,tree045_222,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_224 : CoverTree := CoverTree.reject 265
def tree045_225 : CoverTree := CoverTree.split [tree045_13,tree045_224,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_226 : CoverTree := CoverTree.split [tree045_210,tree045_211,tree045_216,tree045_220,tree045_223,tree045_225]
def tree045_227 : CoverTree := CoverTree.reject 75
def tree045_228 : CoverTree := CoverTree.reject 141
def tree045_229 : CoverTree := CoverTree.reject 142
def tree045_230 : CoverTree := CoverTree.reject 266
def tree045_231 : CoverTree := CoverTree.split [tree045_10,tree045_228,tree045_229,tree045_13,tree045_230,tree045_13]
def tree045_232 : CoverTree := CoverTree.reject 156
def tree045_233 : CoverTree := CoverTree.reject 267
def tree045_234 : CoverTree := CoverTree.split [tree045_15,tree045_232,tree045_233,tree045_13,tree045_13,tree045_13]
def tree045_235 : CoverTree := CoverTree.reject 268
def tree045_236 : CoverTree := CoverTree.split [tree045_17,tree045_235,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_237 : CoverTree := CoverTree.reject 91
def tree045_238 : CoverTree := CoverTree.reject 269
def tree045_239 : CoverTree := CoverTree.split [tree045_237,tree045_238,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_240 : CoverTree := CoverTree.split [tree045_227,tree045_231,tree045_234,tree045_236,tree045_239,tree045_13]
def tree045_241 : CoverTree := CoverTree.split [tree045_209,tree045_226,tree045_240,tree045_94,tree045_28,tree045_31]
def tree045_242 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_184,tree045_192,tree045_204,tree045_241]
def tree045_243 : CoverTree := CoverTree.reject 12
def tree045_244 : CoverTree := CoverTree.split [tree045_243,tree045_243,tree045_243,tree045_243,tree045_243,tree045_128]
def tree045_245 : CoverTree := CoverTree.reject 205
def tree045_246 : CoverTree := CoverTree.reject 72
def tree045_247 : CoverTree := CoverTree.reject 366
def tree045_248 : CoverTree := CoverTree.reject 154
def tree045_249 : CoverTree := CoverTree.reject 270
def tree045_250 : CoverTree := CoverTree.split [tree045_117,tree045_248,tree045_249,tree045_13,tree045_13,tree045_13]
def tree045_251 : CoverTree := CoverTree.reject 271
def tree045_252 : CoverTree := CoverTree.split [tree045_13,tree045_251,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_253 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_246,tree045_247,tree045_250,tree045_252]
def tree045_254 : CoverTree := CoverTree.reject 249
def tree045_255 : CoverTree := CoverTree.split [tree045_140,tree045_254,tree045_143,tree045_145,tree045_138,tree045_13]
def tree045_256 : CoverTree := CoverTree.split [tree045_185,tree045_245,tree045_253,tree045_189,tree045_255,tree045_106]
def tree045_257 : CoverTree := CoverTree.reject 127
def tree045_258 : CoverTree := CoverTree.reject 195
def tree045_259 : CoverTree := CoverTree.reject 196
def tree045_260 : CoverTree := CoverTree.reject 272
def tree045_261 : CoverTree := CoverTree.split [tree045_15,tree045_258,tree045_259,tree045_260,tree045_13,tree045_13]
def tree045_262 : CoverTree := CoverTree.reject 161
def tree045_263 : CoverTree := CoverTree.reject 273
def tree045_264 : CoverTree := CoverTree.split [tree045_17,tree045_262,tree045_263,tree045_13,tree045_13,tree045_13]
def tree045_265 : CoverTree := CoverTree.reject 162
def tree045_266 : CoverTree := CoverTree.split [tree045_237,tree045_265,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_267 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_261,tree045_264,tree045_266,tree045_13]
def tree045_268 : CoverTree := CoverTree.reject 274
def tree045_269 : CoverTree := CoverTree.split [tree045_15,tree045_39,tree045_268,tree045_13,tree045_13,tree045_13]
def tree045_270 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_269,tree045_18,tree045_42,tree045_13]
def tree045_271 : CoverTree := CoverTree.split [tree045_197,tree045_257,tree045_267,tree045_270,tree045_46,tree045_31]
def tree045_272 : CoverTree := CoverTree.reject 393
def tree045_273 : CoverTree := CoverTree.reject 275
def tree045_274 : CoverTree := CoverTree.split [tree045_15,tree045_212,tree045_213,tree045_273,tree045_13,tree045_13]
def tree045_275 : CoverTree := CoverTree.reject 276
def tree045_276 : CoverTree := CoverTree.split [tree045_221,tree045_275,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_277 : CoverTree := CoverTree.split [tree045_210,tree045_272,tree045_274,tree045_18,tree045_276,tree045_13]
def tree045_278 : CoverTree := CoverTree.split [tree045_10,tree045_228,tree045_229,tree045_13,tree045_13,tree045_13]
def tree045_279 : CoverTree := CoverTree.reject 279
def tree045_280 : CoverTree := CoverTree.split [tree045_237,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_281 : CoverTree := CoverTree.split [tree045_227,tree045_278,tree045_279,tree045_18,tree045_280,tree045_13]
def tree045_282 : CoverTree := CoverTree.split [tree045_209,tree045_277,tree045_281,tree045_19,tree045_28,tree045_31]
def tree045_283 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_244,tree045_256,tree045_271,tree045_282]
def tree045_284 : CoverTree := CoverTree.reject 31
def tree045_285 : CoverTree := CoverTree.reject 236
def tree045_286 : CoverTree := CoverTree.reject 237
def tree045_287 : CoverTree := CoverTree.reject 67
def tree045_288 : CoverTree := CoverTree.reject 68
def tree045_289 : CoverTree := CoverTree.reject 189
def tree045_290 : CoverTree := CoverTree.reject 190
def tree045_291 : CoverTree := CoverTree.reject 191
def tree045_292 : CoverTree := CoverTree.split [tree045_289,tree045_290,tree045_291,tree045_13,tree045_13,tree045_13]
def tree045_293 : CoverTree := CoverTree.split [tree045_210,tree045_285,tree045_286,tree045_287,tree045_288,tree045_292]
def tree045_294 : CoverTree := CoverTree.reject 238
def tree045_295 : CoverTree := CoverTree.reject 239
def tree045_296 : CoverTree := CoverTree.reject 69
def tree045_297 : CoverTree := CoverTree.reject 178
def tree045_298 : CoverTree := CoverTree.reject 179
def tree045_299 : CoverTree := CoverTree.reject 180
def tree045_300 : CoverTree := CoverTree.split [tree045_117,tree045_297,tree045_298,tree045_299,tree045_13,tree045_13]
def tree045_301 : CoverTree := CoverTree.reject 181
def tree045_302 : CoverTree := CoverTree.reject 182
def tree045_303 : CoverTree := CoverTree.split [tree045_301,tree045_302,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_304 : CoverTree := CoverTree.split [tree045_227,tree045_294,tree045_295,tree045_296,tree045_300,tree045_303]
def tree045_305 : CoverTree := CoverTree.reject 240
def tree045_306 : CoverTree := CoverTree.reject 241
def tree045_307 : CoverTree := CoverTree.reject 145
def tree045_308 : CoverTree := CoverTree.reject 146
def tree045_309 : CoverTree := CoverTree.split [tree045_17,tree045_307,tree045_308,tree045_13,tree045_13,tree045_13]
def tree045_310 : CoverTree := CoverTree.reject 147
def tree045_311 : CoverTree := CoverTree.reject 148
def tree045_312 : CoverTree := CoverTree.split [tree045_117,tree045_310,tree045_311,tree045_13,tree045_13,tree045_13]
def tree045_313 : CoverTree := CoverTree.reject 149
def tree045_314 : CoverTree := CoverTree.split [tree045_313,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_315 : CoverTree := CoverTree.split [tree045_9,tree045_305,tree045_306,tree045_309,tree045_312,tree045_314]
def tree045_316 : CoverTree := CoverTree.split [tree045_284,tree045_293,tree045_304,tree045_315,tree045_120,tree045_128]
def tree045_317 : CoverTree := CoverTree.reject 242
def tree045_318 : CoverTree := CoverTree.reject 71
def tree045_319 : CoverTree := CoverTree.reject 58
def tree045_320 : CoverTree := CoverTree.reject 150
def tree045_321 : CoverTree := CoverTree.reject 151
def tree045_322 : CoverTree := CoverTree.split [tree045_117,tree045_320,tree045_321,tree045_13,tree045_13,tree045_13]
def tree045_323 : CoverTree := CoverTree.reject 152
def tree045_324 : CoverTree := CoverTree.reject 153
def tree045_325 : CoverTree := CoverTree.split [tree045_323,tree045_324,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_326 : CoverTree := CoverTree.split [tree045_210,tree045_317,tree045_318,tree045_319,tree045_322,tree045_325]
def tree045_327 : CoverTree := CoverTree.reject 243
def tree045_328 : CoverTree := CoverTree.reject 192
def tree045_329 : CoverTree := CoverTree.reject 193
def tree045_330 : CoverTree := CoverTree.reject 194
def tree045_331 : CoverTree := CoverTree.split [tree045_17,tree045_328,tree045_329,tree045_330,tree045_13,tree045_13]
def tree045_332 : CoverTree := CoverTree.split [tree045_117,tree045_248,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_333 : CoverTree := CoverTree.split [tree045_227,tree045_327,tree045_246,tree045_331,tree045_332,tree045_13]
def tree045_334 : CoverTree := CoverTree.split [tree045_185,tree045_326,tree045_333,tree045_139,tree045_146,tree045_106]
def tree045_335 : CoverTree := CoverTree.split [tree045_205,tree045_206,tree045_193,tree045_194,tree045_195,tree045_196]
def tree045_336 : CoverTree := CoverTree.reject 244
def tree045_337 : CoverTree := CoverTree.reject 59
def tree045_338 : CoverTree := CoverTree.reject 168
def tree045_339 : CoverTree := CoverTree.reject 169
def tree045_340 : CoverTree := CoverTree.split [tree045_17,tree045_338,tree045_339,tree045_13,tree045_13,tree045_13]
def tree045_341 : CoverTree := CoverTree.reject 170
def tree045_342 : CoverTree := CoverTree.reject 171
def tree045_343 : CoverTree := CoverTree.split [tree045_221,tree045_341,tree045_342,tree045_13,tree045_13,tree045_13]
def tree045_344 : CoverTree := CoverTree.reject 172
def tree045_345 : CoverTree := CoverTree.split [tree045_344,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_346 : CoverTree := CoverTree.split [tree045_210,tree045_336,tree045_337,tree045_340,tree045_343,tree045_345]
def tree045_347 : CoverTree := CoverTree.reject 143
def tree045_348 : CoverTree := CoverTree.split [tree045_15,tree045_258,tree045_259,tree045_13,tree045_13,tree045_13]
def tree045_349 : CoverTree := CoverTree.split [tree045_17,tree045_262,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_350 : CoverTree := CoverTree.split [tree045_227,tree045_347,tree045_348,tree045_349,tree045_266,tree045_13]
def tree045_351 : CoverTree := CoverTree.split [tree045_335,tree045_346,tree045_350,tree045_43,tree045_46,tree045_31]
def tree045_352 : CoverTree := CoverTree.reject 186
def tree045_353 : CoverTree := CoverTree.reject 187
def tree045_354 : CoverTree := CoverTree.reject 138
def tree045_355 : CoverTree := CoverTree.reject 139
def tree045_356 : CoverTree := CoverTree.split [tree045_10,tree045_352,tree045_353,tree045_354,tree045_355,tree045_13]
def tree045_357 : CoverTree := CoverTree.split [tree045_15,tree045_212,tree045_213,tree045_13,tree045_13,tree045_13]
def tree045_358 : CoverTree := CoverTree.split [tree045_221,tree045_13,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_359 : CoverTree := CoverTree.split [tree045_210,tree045_356,tree045_357,tree045_18,tree045_358,tree045_13]
def tree045_360 : CoverTree := CoverTree.split [tree045_15,tree045_232,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_361 : CoverTree := CoverTree.split [tree045_227,tree045_278,tree045_360,tree045_18,tree045_280,tree045_13]
def tree045_362 : CoverTree := CoverTree.split [tree045_209,tree045_359,tree045_361,tree045_49,tree045_28,tree045_31]
def tree045_363 : CoverTree := CoverTree.split [tree045_4,tree045_4,tree045_316,tree045_334,tree045_351,tree045_362]
def tree045_364 : CoverTree := CoverTree.split [tree045_153,tree045_172,tree045_183,tree045_242,tree045_283,tree045_363]
def tree045_365 : CoverTree := CoverTree.reject 13
def tree045_366 : CoverTree := CoverTree.reject 44
def tree045_367 : CoverTree := CoverTree.reject 118
def tree045_368 : CoverTree := CoverTree.reject 62
def tree045_369 : CoverTree := CoverTree.reject 57
def tree045_370 : CoverTree := CoverTree.reject 157
def tree045_371 : CoverTree := CoverTree.reject 288
def tree045_372 : CoverTree := CoverTree.reject 289
def tree045_373 : CoverTree := CoverTree.split [tree045_17,tree045_371,tree045_372,tree045_13,tree045_13,tree045_13]
def tree045_374 : CoverTree := CoverTree.reject 290
def tree045_375 : CoverTree := CoverTree.reject 291
def tree045_376 : CoverTree := CoverTree.split [tree045_41,tree045_374,tree045_375,tree045_13,tree045_13,tree045_13]
def tree045_377 : CoverTree := CoverTree.reject 292
def tree045_378 : CoverTree := CoverTree.split [tree045_13,tree045_377,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_379 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_370,tree045_373,tree045_376,tree045_378]
def tree045_380 : CoverTree := CoverTree.reject 130
def tree045_381 : CoverTree := CoverTree.reject 293
def tree045_382 : CoverTree := CoverTree.split [tree045_17,tree045_381,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_383 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_380,tree045_382,tree045_13,tree045_13]
def tree045_384 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_379,tree045_383,tree045_80]
def tree045_385 : CoverTree := CoverTree.split [tree045_366,tree045_367,tree045_368,tree045_369,tree045_384,tree045_171]
def tree045_386 : CoverTree := CoverTree.reject 45
def tree045_387 : CoverTree := CoverTree.reject 119
def tree045_388 : CoverTree := CoverTree.reject 63
def tree045_389 : CoverTree := CoverTree.reject 113
def tree045_390 : CoverTree := CoverTree.reject 280
def tree045_391 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_390,tree045_145,tree045_138,tree045_13]
def tree045_392 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_389,tree045_391,tree045_80]
def tree045_393 : CoverTree := CoverTree.reject 158
def tree045_394 : CoverTree := CoverTree.reject 294
def tree045_395 : CoverTree := CoverTree.reject 295
def tree045_396 : CoverTree := CoverTree.split [tree045_17,tree045_394,tree045_395,tree045_13,tree045_13,tree045_13]
def tree045_397 : CoverTree := CoverTree.reject 296
def tree045_398 : CoverTree := CoverTree.split [tree045_41,tree045_397,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_399 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_393,tree045_396,tree045_398,tree045_13]
def tree045_400 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_399,tree045_178,tree045_80]
def tree045_401 : CoverTree := CoverTree.split [tree045_386,tree045_387,tree045_388,tree045_392,tree045_400,tree045_81]
def tree045_402 : CoverTree := CoverTree.reject 21
def tree045_403 : CoverTree := CoverTree.reject 120
def tree045_404 : CoverTree := CoverTree.reject 137
def tree045_405 : CoverTree := CoverTree.reject 163
def tree045_406 : CoverTree := CoverTree.reject 128
def tree045_407 : CoverTree := CoverTree.reject 73
def tree045_408 : CoverTree := CoverTree.reject 297
def tree045_409 : CoverTree := CoverTree.split [tree045_13,tree045_408,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_410 : CoverTree := CoverTree.split [tree045_407,tree045_407,tree045_407,tree045_116,tree045_119,tree045_409]
def tree045_411 : CoverTree := CoverTree.reject 131
def tree045_412 : CoverTree := CoverTree.reject 298
def tree045_413 : CoverTree := CoverTree.split [tree045_15,tree045_412,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_414 : CoverTree := CoverTree.reject 299
def tree045_415 : CoverTree := CoverTree.split [tree045_17,tree045_414,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_416 : CoverTree := CoverTree.split [tree045_121,tree045_411,tree045_413,tree045_415,tree045_127,tree045_13]
def tree045_417 : CoverTree := CoverTree.split [tree045_284,tree045_404,tree045_405,tree045_406,tree045_410,tree045_416]
def tree045_418 : CoverTree := CoverTree.reject 206
def tree045_419 : CoverTree := CoverTree.reject 174
def tree045_420 : CoverTree := CoverTree.split [tree045_185,tree045_418,tree045_419,tree045_189,tree045_191,tree045_106]
def tree045_421 : CoverTree := CoverTree.reject 300
def tree045_422 : CoverTree := CoverTree.reject 301
def tree045_423 : CoverTree := CoverTree.split [tree045_17,tree045_338,tree045_339,tree045_421,tree045_422,tree045_13]
def tree045_424 : CoverTree := CoverTree.reject 302
def tree045_425 : CoverTree := CoverTree.reject 303
def tree045_426 : CoverTree := CoverTree.split [tree045_221,tree045_341,tree045_342,tree045_424,tree045_425,tree045_13]
def tree045_427 : CoverTree := CoverTree.reject 304
def tree045_428 : CoverTree := CoverTree.reject 305
def tree045_429 : CoverTree := CoverTree.split [tree045_344,tree045_427,tree045_428,tree045_13,tree045_13,tree045_13]
def tree045_430 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_337,tree045_423,tree045_426,tree045_429]
def tree045_431 : CoverTree := CoverTree.reject 132
def tree045_432 : CoverTree := CoverTree.reject 306
def tree045_433 : CoverTree := CoverTree.split [tree045_17,tree045_262,tree045_432,tree045_13,tree045_13,tree045_13]
def tree045_434 : CoverTree := CoverTree.reject 307
def tree045_435 : CoverTree := CoverTree.split [tree045_237,tree045_265,tree045_434,tree045_13,tree045_13,tree045_13]
def tree045_436 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_431,tree045_433,tree045_435,tree045_13]
def tree045_437 : CoverTree := CoverTree.split [tree045_197,tree045_430,tree045_436,tree045_202,tree045_203,tree045_31]
def tree045_438 : CoverTree := CoverTree.split [tree045_402,tree045_403,tree045_417,tree045_420,tree045_437,tree045_241]
def tree045_439 : CoverTree := CoverTree.reject 144
def tree045_440 : CoverTree := CoverTree.reject 15
def tree045_441 : CoverTree := CoverTree.reject 8
def tree045_442 : CoverTree := CoverTree.reject 164
def tree045_443 : CoverTree := CoverTree.reject 165
def tree045_444 : CoverTree := CoverTree.split [tree045_17,tree045_442,tree045_443,tree045_13,tree045_13,tree045_13]
def tree045_445 : CoverTree := CoverTree.reject 166
def tree045_446 : CoverTree := CoverTree.reject 167
def tree045_447 : CoverTree := CoverTree.split [tree045_445,tree045_446,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_448 : CoverTree := CoverTree.reject 308
def tree045_449 : CoverTree := CoverTree.split [tree045_13,tree045_448,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_450 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_444,tree045_447,tree045_449]
def tree045_451 : CoverTree := CoverTree.split [tree045_440,tree045_440,tree045_440,tree045_440,tree045_440,tree045_450]
def tree045_452 : CoverTree := CoverTree.reject 309
def tree045_453 : CoverTree := CoverTree.split [tree045_301,tree045_302,tree045_452,tree045_13,tree045_13,tree045_13]
def tree045_454 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_407,tree045_296,tree045_300,tree045_453]
def tree045_455 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_407,tree045_309,tree045_312,tree045_314]
def tree045_456 : CoverTree := CoverTree.split [tree045_407,tree045_407,tree045_407,tree045_116,tree045_119,tree045_13]
def tree045_457 : CoverTree := CoverTree.split [tree045_284,tree045_404,tree045_454,tree045_455,tree045_456,tree045_128]
def tree045_458 : CoverTree := CoverTree.reject 207
def tree045_459 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_246,tree045_331,tree045_250,tree045_252]
def tree045_460 : CoverTree := CoverTree.split [tree045_185,tree045_458,tree045_459,tree045_189,tree045_255,tree045_106]
def tree045_461 : CoverTree := CoverTree.reject 310
def tree045_462 : CoverTree := CoverTree.reject 311
def tree045_463 : CoverTree := CoverTree.split [tree045_17,tree045_338,tree045_339,tree045_461,tree045_462,tree045_13]
def tree045_464 : CoverTree := CoverTree.reject 312
def tree045_465 : CoverTree := CoverTree.split [tree045_221,tree045_341,tree045_342,tree045_464,tree045_13,tree045_13]
def tree045_466 : CoverTree := CoverTree.reject 313
def tree045_467 : CoverTree := CoverTree.split [tree045_344,tree045_466,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_468 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_337,tree045_463,tree045_465,tree045_467]
def tree045_469 : CoverTree := CoverTree.split [tree045_197,tree045_468,tree045_267,tree045_270,tree045_46,tree045_31]
def tree045_470 : CoverTree := CoverTree.split [tree045_210,tree045_356,tree045_274,tree045_18,tree045_276,tree045_13]
def tree045_471 : CoverTree := CoverTree.split [tree045_209,tree045_470,tree045_361,tree045_19,tree045_28,tree045_31]
def tree045_472 : CoverTree := CoverTree.split [tree045_439,tree045_451,tree045_457,tree045_460,tree045_469,tree045_471]
def tree045_473 : CoverTree := CoverTree.reject 70
def tree045_474 : CoverTree := CoverTree.reject 76
def tree045_475 : CoverTree := CoverTree.reject 199
def tree045_476 : CoverTree := CoverTree.reject 200
def tree045_477 : CoverTree := CoverTree.reject 282
def tree045_478 : CoverTree := CoverTree.reject 6
def tree045_479 : CoverTree := CoverTree.reject 37
def tree045_480 : CoverTree := CoverTree.split [tree045_478,tree045_478,tree045_478,tree045_478,tree045_479,tree045_13]
def tree045_481 : CoverTree := CoverTree.reject 176
def tree045_482 : CoverTree := CoverTree.reject 177
def tree045_483 : CoverTree := CoverTree.split [tree045_481,tree045_482,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_484 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_477,tree045_480,tree045_483]
def tree045_485 : CoverTree := CoverTree.reject 283
def tree045_486 : CoverTree := CoverTree.split [tree045_478,tree045_478,tree045_478,tree045_478,tree045_485,tree045_13]
def tree045_487 : CoverTree := CoverTree.split [tree045_478,tree045_478,tree045_478,tree045_478,tree045_13,tree045_13]
def tree045_488 : CoverTree := CoverTree.reject 314
def tree045_489 : CoverTree := CoverTree.split [tree045_13,tree045_488,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_490 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_486,tree045_487,tree045_489]
def tree045_491 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_444,tree045_447,tree045_13]
def tree045_492 : CoverTree := CoverTree.split [tree045_474,tree045_475,tree045_476,tree045_484,tree045_490,tree045_491]
def tree045_493 : CoverTree := CoverTree.split [tree045_473,tree045_492,tree045_316,tree045_334,tree045_351,tree045_362]
def tree045_494 : CoverTree := CoverTree.split [tree045_365,tree045_385,tree045_401,tree045_438,tree045_472,tree045_493]
def tree045_495 : CoverTree := CoverTree.reject 65
def tree045_496 : CoverTree := CoverTree.reject 46
def tree045_497 : CoverTree := CoverTree.reject 20
def tree045_498 : CoverTree := CoverTree.reject 16
def tree045_499 : CoverTree := CoverTree.reject 51
def tree045_500 : CoverTree := CoverTree.reject 52
def tree045_501 : CoverTree := CoverTree.split [tree045_495,tree045_496,tree045_497,tree045_498,tree045_499,tree045_500]
def tree045_502 : CoverTree := CoverTree.reject 77
def tree045_503 : CoverTree := CoverTree.reject 64
def tree045_504 : CoverTree := CoverTree.reject 247
def tree045_505 : CoverTree := CoverTree.reject 210
def tree045_506 : CoverTree := CoverTree.reject 322
def tree045_507 : CoverTree := CoverTree.reject 323
def tree045_508 : CoverTree := CoverTree.split [tree045_117,tree045_506,tree045_507,tree045_13,tree045_13,tree045_13]
def tree045_509 : CoverTree := CoverTree.reject 324
def tree045_510 : CoverTree := CoverTree.reject 325
def tree045_511 : CoverTree := CoverTree.reject 326
def tree045_512 : CoverTree := CoverTree.split [tree045_13,tree045_509,tree045_510,tree045_511,tree045_13,tree045_13]
def tree045_513 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_504,tree045_505,tree045_508,tree045_512]
def tree045_514 : CoverTree := CoverTree.reject 197
def tree045_515 : CoverTree := CoverTree.reject 198
def tree045_516 : CoverTree := CoverTree.reject 327
def tree045_517 : CoverTree := CoverTree.reject 328
def tree045_518 : CoverTree := CoverTree.split [tree045_117,tree045_516,tree045_517,tree045_13,tree045_13,tree045_13]
def tree045_519 : CoverTree := CoverTree.reject 329
def tree045_520 : CoverTree := CoverTree.split [tree045_13,tree045_519,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_521 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_514,tree045_515,tree045_518,tree045_520]
def tree045_522 : CoverTree := CoverTree.reject 330
def tree045_523 : CoverTree := CoverTree.reject 331
def tree045_524 : CoverTree := CoverTree.reject 332
def tree045_525 : CoverTree := CoverTree.split [tree045_15,tree045_522,tree045_523,tree045_524,tree045_13,tree045_13]
def tree045_526 : CoverTree := CoverTree.reject 333
def tree045_527 : CoverTree := CoverTree.split [tree045_17,tree045_526,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_528 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_525,tree045_527,tree045_13,tree045_13]
def tree045_529 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_513,tree045_521,tree045_528]
def tree045_530 : CoverTree := CoverTree.split [tree045_366,tree045_502,tree045_503,tree045_529,tree045_384,tree045_171]
def tree045_531 : CoverTree := CoverTree.reject 78
def tree045_532 : CoverTree := CoverTree.reject 211
def tree045_533 : CoverTree := CoverTree.reject 334
def tree045_534 : CoverTree := CoverTree.reject 335
def tree045_535 : CoverTree := CoverTree.split [tree045_117,tree045_310,tree045_311,tree045_533,tree045_534,tree045_13]
def tree045_536 : CoverTree := CoverTree.reject 336
def tree045_537 : CoverTree := CoverTree.reject 337
def tree045_538 : CoverTree := CoverTree.split [tree045_313,tree045_536,tree045_537,tree045_13,tree045_13,tree045_13]
def tree045_539 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_407,tree045_532,tree045_535,tree045_538]
def tree045_540 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_407,tree045_116,tree045_119,tree045_13]
def tree045_541 : CoverTree := CoverTree.reject 338
def tree045_542 : CoverTree := CoverTree.reject 339
def tree045_543 : CoverTree := CoverTree.split [tree045_15,tree045_541,tree045_542,tree045_13,tree045_13,tree045_13]
def tree045_544 : CoverTree := CoverTree.reject 340
def tree045_545 : CoverTree := CoverTree.split [tree045_17,tree045_544,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_546 : CoverTree := CoverTree.reject 341
def tree045_547 : CoverTree := CoverTree.split [tree045_13,tree045_546,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_548 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_543,tree045_545,tree045_127,tree045_547]
def tree045_549 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_539,tree045_540,tree045_548]
def tree045_550 : CoverTree := CoverTree.reject 248
def tree045_551 : CoverTree := CoverTree.reject 212
def tree045_552 : CoverTree := CoverTree.reject 342
def tree045_553 : CoverTree := CoverTree.reject 343
def tree045_554 : CoverTree := CoverTree.split [tree045_117,tree045_552,tree045_553,tree045_13,tree045_13,tree045_13]
def tree045_555 : CoverTree := CoverTree.reject 344
def tree045_556 : CoverTree := CoverTree.split [tree045_13,tree045_555,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_557 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_550,tree045_551,tree045_554,tree045_556]
def tree045_558 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_143,tree045_145,tree045_138,tree045_13]
def tree045_559 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_557,tree045_558,tree045_80]
def tree045_560 : CoverTree := CoverTree.split [tree045_386,tree045_531,tree045_549,tree045_559,tree045_400,tree045_81]
def tree045_561 : CoverTree := CoverTree.reject 47
def tree045_562 : CoverTree := CoverTree.reject 219
def tree045_563 : CoverTree := CoverTree.reject 83
def tree045_564 : CoverTree := CoverTree.reject 345
def tree045_565 : CoverTree := CoverTree.split [tree045_13,tree045_564,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_566 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_563,tree045_487,tree045_565]
def tree045_567 : CoverTree := CoverTree.reject 346
def tree045_568 : CoverTree := CoverTree.split [tree045_13,tree045_567,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_569 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_444,tree045_447,tree045_568]
def tree045_570 : CoverTree := CoverTree.split [tree045_561,tree045_561,tree045_561,tree045_562,tree045_566,tree045_569]
def tree045_571 : CoverTree := CoverTree.reject 287
def tree045_572 : CoverTree := CoverTree.reject 347
def tree045_573 : CoverTree := CoverTree.split [tree045_117,tree045_297,tree045_298,tree045_299,tree045_572,tree045_13]
def tree045_574 : CoverTree := CoverTree.reject 348
def tree045_575 : CoverTree := CoverTree.split [tree045_301,tree045_302,tree045_574,tree045_13,tree045_13,tree045_13]
def tree045_576 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_407,tree045_296,tree045_573,tree045_575]
def tree045_577 : CoverTree := CoverTree.reject 213
def tree045_578 : CoverTree := CoverTree.reject 349
def tree045_579 : CoverTree := CoverTree.reject 350
def tree045_580 : CoverTree := CoverTree.split [tree045_313,tree045_578,tree045_579,tree045_13,tree045_13,tree045_13]
def tree045_581 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_407,tree045_577,tree045_312,tree045_580]
def tree045_582 : CoverTree := CoverTree.split [tree045_284,tree045_571,tree045_576,tree045_581,tree045_410,tree045_416]
def tree045_583 : CoverTree := CoverTree.reject 351
def tree045_584 : CoverTree := CoverTree.reject 352
def tree045_585 : CoverTree := CoverTree.split [tree045_117,tree045_320,tree045_321,tree045_583,tree045_584,tree045_13]
def tree045_586 : CoverTree := CoverTree.reject 353
def tree045_587 : CoverTree := CoverTree.reject 354
def tree045_588 : CoverTree := CoverTree.split [tree045_323,tree045_324,tree045_586,tree045_587,tree045_13,tree045_13]
def tree045_589 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_318,tree045_319,tree045_585,tree045_588]
def tree045_590 : CoverTree := CoverTree.reject 111
def tree045_591 : CoverTree := CoverTree.reject 355
def tree045_592 : CoverTree := CoverTree.split [tree045_117,tree045_248,tree045_591,tree045_13,tree045_13,tree045_13]
def tree045_593 : CoverTree := CoverTree.reject 356
def tree045_594 : CoverTree := CoverTree.reject 357
def tree045_595 : CoverTree := CoverTree.split [tree045_13,tree045_593,tree045_594,tree045_13,tree045_13,tree045_13]
def tree045_596 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_246,tree045_590,tree045_592,tree045_595]
def tree045_597 : CoverTree := CoverTree.split [tree045_185,tree045_589,tree045_596,tree045_189,tree045_191,tree045_106]
def tree045_598 : CoverTree := CoverTree.split [tree045_402,tree045_570,tree045_582,tree045_597,tree045_437,tree045_241]
def tree045_599 : CoverTree := CoverTree.reject 108
def tree045_600 : CoverTree := CoverTree.reject 358
def tree045_601 : CoverTree := CoverTree.split [tree045_481,tree045_482,tree045_600,tree045_13,tree045_13,tree045_13]
def tree045_602 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_441,tree045_563,tree045_480,tree045_601]
def tree045_603 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_563,tree045_487,tree045_13]
def tree045_604 : CoverTree := CoverTree.split [tree045_561,tree045_561,tree045_561,tree045_602,tree045_603,tree045_450]
def tree045_605 : CoverTree := CoverTree.reject 359
def tree045_606 : CoverTree := CoverTree.split [tree045_289,tree045_290,tree045_291,tree045_605,tree045_13,tree045_13]
def tree045_607 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_407,tree045_287,tree045_288,tree045_606]
def tree045_608 : CoverTree := CoverTree.split [tree045_284,tree045_607,tree045_454,tree045_455,tree045_456,tree045_128]
def tree045_609 : CoverTree := CoverTree.reject 360
def tree045_610 : CoverTree := CoverTree.reject 361
def tree045_611 : CoverTree := CoverTree.split [tree045_117,tree045_320,tree045_321,tree045_609,tree045_610,tree045_13]
def tree045_612 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_318,tree045_319,tree045_611,tree045_325]
def tree045_613 : CoverTree := CoverTree.split [tree045_185,tree045_612,tree045_459,tree045_189,tree045_255,tree045_106]
def tree045_614 : CoverTree := CoverTree.split [tree045_599,tree045_604,tree045_608,tree045_613,tree045_469,tree045_471]
def tree045_615 : CoverTree := CoverTree.reject 105
def tree045_616 : CoverTree := CoverTree.reject 92
def tree045_617 : CoverTree := CoverTree.reject 93
def tree045_618 : CoverTree := CoverTree.reject 32
def tree045_619 : CoverTree := CoverTree.reject 234
def tree045_620 : CoverTree := CoverTree.reject 208
def tree045_621 : CoverTree := CoverTree.reject 159
def tree045_622 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_619,tree045_620,tree045_621]
def tree045_623 : CoverTree := CoverTree.reject 89
def tree045_624 : CoverTree := CoverTree.reject 362
def tree045_625 : CoverTree := CoverTree.reject 363
def tree045_626 : CoverTree := CoverTree.reject 364
def tree045_627 : CoverTree := CoverTree.split [tree045_624,tree045_625,tree045_626,tree045_13,tree045_13,tree045_13]
def tree045_628 : CoverTree := CoverTree.reject 365
def tree045_629 : CoverTree := CoverTree.split [tree045_13,tree045_628,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_630 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_623,tree045_627,tree045_629]
def tree045_631 : CoverTree := CoverTree.split [tree045_615,tree045_616,tree045_617,tree045_618,tree045_622,tree045_630]
def tree045_632 : CoverTree := CoverTree.reject 315
def tree045_633 : CoverTree := CoverTree.reject 316
def tree045_634 : CoverTree := CoverTree.reject 318
def tree045_635 : CoverTree := CoverTree.reject 319
def tree045_636 : CoverTree := CoverTree.reject 320
def tree045_637 : CoverTree := CoverTree.reject 321
def tree045_638 : CoverTree := CoverTree.split [tree045_634,tree045_635,tree045_636,tree045_637,tree045_13,tree045_13]
def tree045_639 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_632,tree045_633,tree045_638]
def tree045_640 : CoverTree := CoverTree.reject 317
def tree045_641 : CoverTree := CoverTree.reject 235
def tree045_642 : CoverTree := CoverTree.reject 245
def tree045_643 : CoverTree := CoverTree.reject 246
def tree045_644 : CoverTree := CoverTree.split [tree045_642,tree045_643,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_645 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_640,tree045_641,tree045_644]
def tree045_646 : CoverTree := CoverTree.split [tree045_474,tree045_639,tree045_645,tree045_484,tree045_490,tree045_491]
def tree045_647 : CoverTree := CoverTree.split [tree045_631,tree045_646,tree045_316,tree045_334,tree045_351,tree045_362]
def tree045_648 : CoverTree := CoverTree.split [tree045_501,tree045_530,tree045_560,tree045_598,tree045_614,tree045_647]
def tree045_649 : CoverTree := CoverTree.reject 53
def tree045_650 : CoverTree := CoverTree.reject 54
def tree045_651 : CoverTree := CoverTree.split [tree045_495,tree045_496,tree045_497,tree045_498,tree045_649,tree045_650]
def tree045_652 : CoverTree := CoverTree.reject 218
def tree045_653 : CoverTree := CoverTree.reject 188
def tree045_654 : CoverTree := CoverTree.reject 284
def tree045_655 : CoverTree := CoverTree.reject 370
def tree045_656 : CoverTree := CoverTree.split [tree045_445,tree045_446,tree045_655,tree045_13,tree045_13,tree045_13]
def tree045_657 : CoverTree := CoverTree.reject 371
def tree045_658 : CoverTree := CoverTree.split [tree045_13,tree045_657,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_659 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_441,tree045_654,tree045_656,tree045_658]
def tree045_660 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_652,tree045_653,tree045_659]
def tree045_661 : CoverTree := CoverTree.reject 201
def tree045_662 : CoverTree := CoverTree.reject 285
def tree045_663 : CoverTree := CoverTree.reject 372
def tree045_664 : CoverTree := CoverTree.reject 373
def tree045_665 : CoverTree := CoverTree.reject 374
def tree045_666 : CoverTree := CoverTree.split [tree045_313,tree045_663,tree045_664,tree045_665,tree045_13,tree045_13]
def tree045_667 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_407,tree045_661,tree045_662,tree045_666]
def tree045_668 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_407,tree045_661,tree045_119,tree045_13]
def tree045_669 : CoverTree := CoverTree.reject 375
def tree045_670 : CoverTree := CoverTree.reject 376
def tree045_671 : CoverTree := CoverTree.reject 377
def tree045_672 : CoverTree := CoverTree.split [tree045_15,tree045_669,tree045_670,tree045_671,tree045_13,tree045_13]
def tree045_673 : CoverTree := CoverTree.reject 378
def tree045_674 : CoverTree := CoverTree.split [tree045_17,tree045_673,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_675 : CoverTree := CoverTree.reject 379
def tree045_676 : CoverTree := CoverTree.split [tree045_13,tree045_675,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_677 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_672,tree045_674,tree045_127,tree045_676]
def tree045_678 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_667,tree045_668,tree045_677]
def tree045_679 : CoverTree := CoverTree.split [tree045_366,tree045_660,tree045_678,tree045_529,tree045_384,tree045_171]
def tree045_680 : CoverTree := CoverTree.reject 281
def tree045_681 : CoverTree := CoverTree.reject 380
def tree045_682 : CoverTree := CoverTree.reject 381
def tree045_683 : CoverTree := CoverTree.reject 382
def tree045_684 : CoverTree := CoverTree.split [tree045_481,tree045_482,tree045_681,tree045_682,tree045_683,tree045_13]
def tree045_685 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_441,tree045_563,tree045_680,tree045_684]
def tree045_686 : CoverTree := CoverTree.reject 383
def tree045_687 : CoverTree := CoverTree.split [tree045_13,tree045_686,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_688 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_441,tree045_563,tree045_680,tree045_687]
def tree045_689 : CoverTree := CoverTree.reject 286
def tree045_690 : CoverTree := CoverTree.reject 384
def tree045_691 : CoverTree := CoverTree.split [tree045_445,tree045_446,tree045_690,tree045_13,tree045_13,tree045_13]
def tree045_692 : CoverTree := CoverTree.reject 385
def tree045_693 : CoverTree := CoverTree.split [tree045_13,tree045_692,tree045_13,tree045_13,tree045_13,tree045_13]
def tree045_694 : CoverTree := CoverTree.split [tree045_59,tree045_59,tree045_441,tree045_689,tree045_691,tree045_693]
def tree045_695 : CoverTree := CoverTree.split [tree045_57,tree045_57,tree045_57,tree045_685,tree045_688,tree045_694]
def tree045_696 : CoverTree := CoverTree.split [tree045_386,tree045_695,tree045_549,tree045_559,tree045_400,tree045_81]
def tree045_697 : CoverTree := CoverTree.reject 202
def tree045_698 : CoverTree := CoverTree.reject 386
def tree045_699 : CoverTree := CoverTree.split [tree045_642,tree045_643,tree045_698,tree045_13,tree045_13,tree045_13]
def tree045_700 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_441,tree045_563,tree045_641,tree045_699]
def tree045_701 : CoverTree := CoverTree.reject 369
def tree045_702 : CoverTree := CoverTree.reject 387
def tree045_703 : CoverTree := CoverTree.reject 388
def tree045_704 : CoverTree := CoverTree.split [tree045_481,tree045_482,tree045_702,tree045_703,tree045_13,tree045_13]
def tree045_705 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_441,tree045_563,tree045_701,tree045_704]
def tree045_706 : CoverTree := CoverTree.split [tree045_474,tree045_697,tree045_700,tree045_705,tree045_566,tree045_569]
def tree045_707 : CoverTree := CoverTree.reject 389
def tree045_708 : CoverTree := CoverTree.reject 390
def tree045_709 : CoverTree := CoverTree.split [tree045_289,tree045_290,tree045_291,tree045_707,tree045_708,tree045_13]
def tree045_710 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_407,tree045_287,tree045_288,tree045_709]
def tree045_711 : CoverTree := CoverTree.split [tree045_284,tree045_710,tree045_576,tree045_581,tree045_410,tree045_416]
def tree045_712 : CoverTree := CoverTree.split [tree045_402,tree045_706,tree045_711,tree045_597,tree045_437,tree045_241]
def tree045_713 : CoverTree := CoverTree.reject 367
def tree045_714 : CoverTree := CoverTree.reject 368
def tree045_715 : CoverTree := CoverTree.split [tree045_13,tree045_713,tree045_714,tree045_13,tree045_13,tree045_13]
def tree045_716 : CoverTree := CoverTree.split [tree045_441,tree045_441,tree045_441,tree045_563,tree045_620,tree045_715]
def tree045_717 : CoverTree := CoverTree.reject 160
def tree045_718 : CoverTree := CoverTree.split [tree045_615,tree045_616,tree045_617,tree045_618,tree045_716,tree045_717]
def tree045_719 : CoverTree := CoverTree.reject 203
def tree045_720 : CoverTree := CoverTree.reject 391
def tree045_721 : CoverTree := CoverTree.reject 392
def tree045_722 : CoverTree := CoverTree.split [tree045_642,tree045_643,tree045_720,tree045_721,tree045_13,tree045_13]
def tree045_723 : CoverTree := CoverTree.split [tree045_188,tree045_188,tree045_441,tree045_563,tree045_641,tree045_722]
def tree045_724 : CoverTree := CoverTree.split [tree045_474,tree045_719,tree045_723,tree045_602,tree045_603,tree045_450]
def tree045_725 : CoverTree := CoverTree.split [tree045_718,tree045_724,tree045_608,tree045_613,tree045_469,tree045_471]
def tree045_726 : CoverTree := CoverTree.split [tree045_651,tree045_679,tree045_696,tree045_712,tree045_725,tree045_647]
def tree045_727 : CoverTree := CoverTree.split [tree045_52,tree045_152,tree045_364,tree045_494,tree045_648,tree045_726]
def tree045 : CoverTree := tree045_727

end Snake9.Shared89
