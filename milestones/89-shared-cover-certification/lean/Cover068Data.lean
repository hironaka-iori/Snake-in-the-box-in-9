import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes068 : List Box := [
[(1,5),(1,3),(1,5),(1,3),(1,6),(1,6)],
[(1,6),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,2),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,6),(1,6),(1,2)],
[(1,4),(1,5),(1,5),(1,2),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,5),(1,1),(1,6)],
[(1,2),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,2),(1,4),(1,5),(1,5),(1,6)],
[(1,6),(1,5),(1,5),(1,2),(1,3),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,2),(1,6),(1,6),(1,6),(1,3)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,2),(1,6),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,5),(1,5),(1,4),(1,2),(1,6),(1,6)],
[(1,1),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,2),(1,5),(1,6)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,1)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(1,3),(1,2),(1,5),(1,5),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(5,5),(1,6),(1,6)],
[(1,6),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)],
[(1,6),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,3),(1,5),(1,3),(1,5),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(6,6),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(1,2),(1,3),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(3,3),(6,6),(1,1),(1,6),(1,6)],
[(1,5),(1,2),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,4),(1,5),(1,3),(1,2),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(2,2),(5,5),(1,1)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(4,4),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(5,5),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(5,5),(3,3),(3,3),(3,3),(1,6)],
[(1,6),(1,2),(1,5),(1,5),(1,4),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(1,6),(5,5),(5,5),(1,1),(1,6),(1,6)],
[(1,1),(5,5),(6,6),(3,3),(1,6),(1,6)],
[(1,1),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(6,6),(5,5),(1,1),(6,6),(1,6)],
[(2,2),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(5,5),(3,3),(1,6),(1,6)],
[(2,2),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(4,4),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(2,2),(3,3),(3,3),(6,6),(1,6),(1,6)],
[(3,3),(3,3),(2,2),(6,6),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(6,6),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(6,6),(1,1),(5,5)],
[(1,6),(3,3),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(3,3),(3,3),(5,5),(3,3),(1,6)],
[(1,6),(3,3),(3,3),(5,5),(4,4),(1,6)],
[(1,6),(3,3),(4,4),(5,5),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(3,3),(5,5),(5,5),(2,2),(1,6)],
[(1,6),(4,4),(2,2),(6,6),(2,2),(1,6)],
[(3,3),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(4,4),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(3,3),(6,6),(2,2),(1,6),(1,6)],
[(4,4),(3,3),(6,6),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(6,6),(2,2),(1,6)],
[(1,6),(3,3),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(4,4),(5,5),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(3,3),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(1,1),(5,5)],
[(1,6),(2,2),(6,6),(4,4),(3,3),(1,6)],
[(1,6),(4,4),(2,2),(5,5),(3,3),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(5,5),(2,2),(4,4),(3,3),(1,6)],
[(1,6),(5,5),(2,2),(5,5),(3,3),(1,6)],
[(1,6),(6,6),(2,2),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(1,1)],
[(1,6),(1,6),(4,4),(4,4),(5,5),(1,1)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(6,6),(2,2),(3,3),(3,3)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(2,2)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(3,3)],
[(1,6),(4,4),(5,5),(1,1),(1,6),(1,6)],
[(2,2),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(1,1)],
[(1,6),(3,3),(2,2),(6,6),(2,2),(1,6)],
[(1,6),(3,3),(2,2),(6,6),(3,3),(1,6)],
[(1,6),(4,4),(2,2),(5,5),(2,2),(1,6)],
[(1,6),(4,4),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(2,2),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(2,2),(5,5),(2,2),(1,6)],
[(1,6),(6,6),(3,3),(3,3),(2,2),(1,6)],
[(2,2),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(5,5),(1,1),(5,5)],
[(2,2),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(3,3),(2,2),(5,5)],
[(1,6),(3,3),(4,4),(6,6),(1,1),(1,6)],
[(1,6),(3,3),(6,6),(5,5),(1,1),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(2,2),(1,6)],
[(1,6),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(3,3),(1,6)],
[(1,6),(5,5),(4,4),(3,3),(2,2),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(3,3),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(2,2)],
[(1,6),(3,3),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(1,6),(3,3),(6,6),(2,2),(4,4),(1,6)],
[(2,2),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(2,2)],
[(1,6),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(5,5),(2,2),(4,4),(2,2)],
[(1,6),(3,3),(6,6),(2,2),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(3,3),(3,3),(2,2),(1,6)],
[(3,3),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(5,5),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(6,6),(3,3),(4,4),(3,3),(2,2)],
[(1,6),(6,6),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(4,4),(3,3),(2,2),(5,5)],
[(1,6),(5,5),(4,4),(5,5),(1,1),(1,6)],
[(1,1),(5,5),(4,4),(6,6),(2,2),(1,6)],
[(1,6),(3,3),(6,6),(4,4),(3,3),(3,3)],
[(1,6),(4,4),(3,3),(6,6),(1,1),(6,6)],
[(1,6),(4,4),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(4,4),(4,4),(5,5),(2,2),(3,3)],
[(1,6),(4,4),(6,6),(3,3),(3,3),(2,2)],
[(1,6),(5,5),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(5,5),(4,4),(4,4),(2,2),(3,3)],
[(2,2),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(4,4),(5,5),(5,5),(3,3),(1,6)],
[(2,2),(4,4),(5,5),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(5,5),(3,3),(6,6),(3,3),(1,6)],
[(2,2),(5,5),(3,3),(6,6),(4,4),(1,6)],
[(2,2),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(5,5),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(6,6),(3,3),(4,4),(4,4),(1,6)],
[(2,2),(6,6),(3,3),(4,4),(5,5),(1,6)],
[(2,2),(6,6),(3,3),(5,5),(3,3),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(6,6),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(6,6),(5,5),(3,3),(4,4),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(4,4),(2,2),(6,6),(3,3),(1,6)],
[(3,3),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(3,3),(4,4),(3,3),(5,5),(3,3),(1,6)],
[(3,3),(4,4),(3,3),(5,5),(4,4),(1,6)],
[(3,3),(4,4),(3,3),(5,5),(5,5),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(3,3),(4,4),(4,4),(6,6),(2,2),(1,6)],
[(3,3),(5,5),(2,2),(6,6),(2,2),(1,6)],
[(3,3),(5,5),(2,2),(6,6),(3,3),(1,6)],
[(3,3),(5,5),(3,3),(4,4),(3,3),(1,6)],
[(3,3),(5,5),(3,3),(4,4),(4,4),(1,6)],
[(3,3),(5,5),(3,3),(4,4),(5,5),(1,6)],
[(3,3),(5,5),(3,3),(5,5),(3,3),(1,6)],
[(3,3),(5,5),(3,3),(5,5),(4,4),(1,6)],
[(3,3),(5,5),(3,3),(6,6),(3,3),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(3,3),(5,5),(6,6),(1,1),(6,6),(1,6)],
[(3,3),(6,6),(2,2),(4,4),(3,3),(1,6)],
[(3,3),(6,6),(2,2),(5,5),(3,3),(1,6)],
[(3,3),(6,6),(2,2),(5,5),(4,4),(1,6)],
[(3,3),(6,6),(2,2),(6,6),(2,2),(1,6)],
[(3,3),(6,6),(3,3),(2,2),(5,5),(1,6)],
[(3,3),(6,6),(3,3),(3,3),(3,3),(1,6)],
[(3,3),(6,6),(3,3),(3,3),(4,4),(1,6)],
[(3,3),(6,6),(3,3),(3,3),(5,5),(1,6)],
[(3,3),(6,6),(3,3),(4,4),(4,4),(1,6)],
[(3,3),(6,6),(3,3),(5,5),(3,3),(1,6)],
[(3,3),(6,6),(4,4),(2,2),(5,5),(1,6)],
[(3,3),(6,6),(4,4),(3,3),(4,4),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(5,5),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(3,3),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(4,4),(4,4),(3,3),(5,5),(3,3),(1,6)],
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
[(5,5),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(5,5),(1,6)],
[(5,5),(4,4),(3,3),(5,5),(3,3),(1,6)],
[(5,5),(5,5),(2,2),(4,4),(5,5),(1,6)],
[(5,5),(5,5),(2,2),(5,5),(4,4),(1,6)],
[(5,5),(5,5),(2,2),(6,6),(2,2),(1,6)],
[(5,5),(5,5),(3,3),(3,3),(4,4),(1,6)],
[(5,5),(5,5),(3,3),(4,4),(3,3),(1,6)],
[(5,5),(6,6),(2,2),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(2,2),(1,6)],
[(1,6),(3,3),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(3,3),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(2,2),(4,4),(2,2),(5,5)],
[(1,6),(1,6),(2,2),(5,5),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(3,3)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(4,4)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(3,3)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(4,4)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(5,5)],
[(1,6),(3,3),(3,3),(6,6),(1,1),(1,6)],
[(1,6),(4,4),(2,2),(6,6),(1,1),(1,6)],
[(1,6),(5,5),(2,2),(6,6),(1,1),(1,6)],
[(1,6),(5,5),(4,4),(2,2),(4,4),(1,6)],
[(1,1),(6,6),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(3,3),(3,3),(6,6),(5,5),(3,3)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(3,3)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(4,4)],
[(1,6),(3,3),(5,5),(4,4),(4,4),(3,3)],
[(1,6),(4,4),(2,2),(6,6),(5,5),(2,2)],
[(1,6),(4,4),(3,3),(5,5),(6,6),(2,2)],
[(1,6),(5,5),(2,2),(6,6),(4,4),(2,2)],
[(1,6),(5,5),(6,6),(2,2),(4,4),(2,2)],
[(1,6),(6,6),(2,2),(6,6),(1,1),(6,6)],
[(1,6),(6,6),(2,2),(6,6),(3,3),(2,2)],
[(2,2),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(2,2),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(3,3),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(3,3),(6,6),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(2,2),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(2,2),(4,4),(3,3),(6,6),(4,4),(1,6)],
[(2,2),(4,4),(5,5),(5,5),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(6,6),(4,4),(2,2),(1,6)],
[(2,2),(5,5),(3,3),(6,6),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(5,5),(5,5),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(3,3),(4,4),(3,3),(1,6)],
[(2,2),(6,6),(3,3),(5,5),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(3,3),(1,6)],
[(2,2),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(6,6),(5,5),(4,4),(2,2),(1,6)],
[(3,3),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(3,3),(3,3),(3,3),(6,6),(4,4),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(4,4),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(5,5),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(3,3),(3,3),(6,6),(6,6),(2,2),(1,6)],
[(3,3),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(3,3),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(3,3),(5,5),(3,3),(6,6),(2,2),(1,6)],
[(3,3),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(3,3),(5,5),(5,5),(4,4),(2,2),(1,6)],
[(3,3),(6,6),(2,2),(4,4),(4,4),(1,6)],
[(3,3),(6,6),(3,3),(4,4),(3,3),(1,6)],
[(3,3),(6,6),(3,3),(5,5),(2,2),(1,6)],
[(3,3),(6,6),(4,4),(2,2),(4,4),(1,6)],
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
[(4,4),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(4,4),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(5,5),(2,2),(4,4),(4,4),(1,6)],
[(4,4),(5,5),(4,4),(3,3),(3,3),(1,6)],
[(4,4),(6,6),(2,2),(4,4),(4,4),(1,6)],
[(4,4),(6,6),(3,3),(5,5),(2,2),(1,6)],
[(4,4),(6,6),(4,4),(2,2),(4,4),(1,6)],
[(4,4),(6,6),(4,4),(4,4),(2,2),(1,6)],
[(5,5),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(5,5),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(5,5),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(5,5),(5,5),(2,2),(4,4),(4,4),(1,6)],
[(5,5),(5,5),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(3,3),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(3,3)],
[(1,6),(2,2),(5,5),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(2,2),(6,6),(1,1),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)],
[(4,4),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(4,4)],
[(1,6),(4,4),(3,3),(5,5),(4,4),(2,2)],
[(1,6),(4,4),(4,4),(3,3),(5,5),(2,2)],
[(1,6),(4,4),(4,4),(3,3),(5,5),(3,3)],
[(1,6),(4,4),(4,4),(3,3),(6,6),(2,2)],
[(1,6),(4,4),(6,6),(2,2),(4,4),(2,2)],
[(1,6),(5,5),(3,3),(4,4),(4,4),(2,2)],
[(1,6),(5,5),(4,4),(3,3),(4,4),(2,2)],
[(1,6),(6,6),(3,3),(2,2),(4,4),(4,4)],
[(1,6),(6,6),(3,3),(2,2),(4,4),(5,5)],
[(1,6),(6,6),(3,3),(2,2),(4,4),(6,6)],
[(2,2),(2,2),(6,6),(5,5),(3,3),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(4,4),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(2,2),(1,6)],
[(2,2),(5,5),(4,4),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(3,3),(4,4),(2,2),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(3,3),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(5,5),(1,6)],
[(3,3),(2,2),(6,6),(5,5),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(2,2),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(2,2),(1,6)],
[(3,3),(5,5),(6,6),(2,2),(3,3),(1,6)],
[(3,3),(6,6),(2,2),(5,5),(2,2),(1,6)],
[(3,3),(6,6),(3,3),(4,4),(2,2),(1,6)],
[(3,3),(6,6),(4,4),(2,2),(3,3),(1,6)],
[(4,4),(2,2),(4,4),(6,6),(3,3),(1,6)],
[(4,4),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(4,4),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(4,4),(6,6),(2,2),(5,5),(2,2),(1,6)],
[(4,4),(6,6),(3,3),(4,4),(2,2),(1,6)],
[(4,4),(6,6),(4,4),(2,2),(3,3),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(5,5),(2,2),(4,4),(6,6),(3,3),(1,6)],
[(5,5),(6,6),(2,2),(5,5),(2,2),(1,6)],
[(5,5),(6,6),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(2,2),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(2,2)],
[(1,6),(3,3),(6,6),(2,2),(2,2),(1,6)],
[(3,3),(6,6),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(6,6),(3,3),(2,2)],
[(1,6),(4,4),(2,2),(6,6),(3,3),(3,3)],
[(1,6),(4,4),(2,2),(6,6),(4,4),(2,2)],
[(1,6),(4,4),(3,3),(4,4),(5,5),(3,3)],
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
[(1,6),(4,4),(2,2),(5,5),(4,4),(2,2)],
[(1,6),(4,4),(2,2),(5,5),(4,4),(3,3)],
[(1,6),(4,4),(3,3),(5,5),(3,3),(2,2)],
[(1,6),(5,5),(2,2),(4,4),(4,4),(4,4)],
[(1,6),(5,5),(2,2),(6,6),(2,2),(2,2)],
[(1,6),(5,5),(3,3),(4,4),(3,3),(2,2)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(2,2)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(3,3)],
[(1,6),(5,5),(4,4),(2,2),(5,5),(4,4)],
[(2,2),(5,5),(3,3),(6,6),(1,1),(1,6)],
[(2,2),(6,6),(4,4),(5,5),(1,1),(1,6)],
[(3,3),(5,5),(6,6),(2,2),(2,2),(1,6)],
[(3,3),(6,6),(2,2),(4,4),(2,2),(1,6)],
[(4,4),(6,6),(2,2),(4,4),(2,2),(1,6)]
]

def root068 : Nat := 3493

def tree068_0 : CoverTree := CoverTree.reject 1
def tree068_1 : CoverTree := CoverTree.reject 53
def tree068_2 : CoverTree := CoverTree.reject 20
def tree068_3 : CoverTree := CoverTree.reject 9
def tree068_4 : CoverTree := CoverTree.reject 2
def tree068_5 : CoverTree := CoverTree.reject 59
def tree068_6 : CoverTree := CoverTree.reject 4
def tree068_7 : CoverTree := CoverTree.reject 27
def tree068_8 : CoverTree := CoverTree.reject 72
def tree068_9 : CoverTree := CoverTree.reject 24
def tree068_10 : CoverTree := CoverTree.reject 25
def tree068_11 : CoverTree := CoverTree.reject 21
def tree068_12 : CoverTree := CoverTree.reject 22
def tree068_13 : CoverTree := CoverTree.accept
def tree068_14 : CoverTree := CoverTree.split [tree068_9,tree068_10,tree068_11,tree068_12,tree068_13,tree068_13]
def tree068_15 : CoverTree := CoverTree.reject 201
def tree068_16 : CoverTree := CoverTree.reject 16
def tree068_17 : CoverTree := CoverTree.split [tree068_16,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_18 : CoverTree := CoverTree.reject 13
def tree068_19 : CoverTree := CoverTree.split [tree068_18,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_20 : CoverTree := CoverTree.split [tree068_14,tree068_15,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_21 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_7,tree068_7,tree068_8,tree068_20]
def tree068_22 : CoverTree := CoverTree.reject 15
def tree068_23 : CoverTree := CoverTree.reject 46
def tree068_24 : CoverTree := CoverTree.split [tree068_22,tree068_23,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_25 : CoverTree := CoverTree.split [tree068_14,tree068_24,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_26 : CoverTree := CoverTree.split [tree068_22,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_27 : CoverTree := CoverTree.split [tree068_14,tree068_26,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_28 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_7,tree068_7,tree068_25,tree068_27]
def tree068_29 : CoverTree := CoverTree.reject 6
def tree068_30 : CoverTree := CoverTree.reject 91
def tree068_31 : CoverTree := CoverTree.reject 12
def tree068_32 : CoverTree := CoverTree.reject 52
def tree068_33 : CoverTree := CoverTree.split [tree068_22,tree068_32,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_34 : CoverTree := CoverTree.split [tree068_31,tree068_33,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_35 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_30,tree068_34,tree068_25,tree068_27]
def tree068_36 : CoverTree := CoverTree.split [tree068_4,tree068_4,tree068_5,tree068_21,tree068_28,tree068_35]
def tree068_37 : CoverTree := CoverTree.reject 92
def tree068_38 : CoverTree := CoverTree.reject 175
def tree068_39 : CoverTree := CoverTree.split [tree068_22,tree068_32,tree068_38,tree068_13,tree068_13,tree068_13]
def tree068_40 : CoverTree := CoverTree.reject 193
def tree068_41 : CoverTree := CoverTree.split [tree068_16,tree068_40,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_42 : CoverTree := CoverTree.reject 151
def tree068_43 : CoverTree := CoverTree.split [tree068_42,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_44 : CoverTree := CoverTree.split [tree068_31,tree068_39,tree068_41,tree068_19,tree068_43,tree068_13]
def tree068_45 : CoverTree := CoverTree.reject 106
def tree068_46 : CoverTree := CoverTree.reject 311
def tree068_47 : CoverTree := CoverTree.reject 139
def tree068_48 : CoverTree := CoverTree.split [tree068_47,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_49 : CoverTree := CoverTree.split [tree068_45,tree068_46,tree068_17,tree068_19,tree068_48,tree068_13]
def tree068_50 : CoverTree := CoverTree.reject 107
def tree068_51 : CoverTree := CoverTree.split [tree068_9,tree068_10,tree068_11,tree068_12,tree068_50,tree068_13]
def tree068_52 : CoverTree := CoverTree.reject 194
def tree068_53 : CoverTree := CoverTree.split [tree068_22,tree068_52,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_54 : CoverTree := CoverTree.split [tree068_51,tree068_53,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_55 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_37,tree068_44,tree068_49,tree068_54]
def tree068_56 : CoverTree := CoverTree.reject 93
def tree068_57 : CoverTree := CoverTree.reject 140
def tree068_58 : CoverTree := CoverTree.split [tree068_57,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_59 : CoverTree := CoverTree.split [tree068_31,tree068_33,tree068_17,tree068_19,tree068_58,tree068_13]
def tree068_60 : CoverTree := CoverTree.reject 160
def tree068_61 : CoverTree := CoverTree.split [tree068_9,tree068_10,tree068_11,tree068_12,tree068_60,tree068_13]
def tree068_62 : CoverTree := CoverTree.split [tree068_61,tree068_24,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_63 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_56,tree068_59,tree068_62,tree068_27]
def tree068_64 : CoverTree := CoverTree.reject 11
def tree068_65 : CoverTree := CoverTree.reject 56
def tree068_66 : CoverTree := CoverTree.reject 51
def tree068_67 : CoverTree := CoverTree.reject 163
def tree068_68 : CoverTree := CoverTree.split [tree068_22,tree068_65,tree068_66,tree068_13,tree068_67,tree068_13]
def tree068_69 : CoverTree := CoverTree.reject 141
def tree068_70 : CoverTree := CoverTree.split [tree068_16,tree068_69,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_71 : CoverTree := CoverTree.reject 58
def tree068_72 : CoverTree := CoverTree.split [tree068_71,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_73 : CoverTree := CoverTree.split [tree068_64,tree068_68,tree068_70,tree068_19,tree068_72,tree068_13]
def tree068_74 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_73,tree068_34,tree068_25,tree068_27]
def tree068_75 : CoverTree := CoverTree.split [tree068_22,tree068_65,tree068_66,tree068_13,tree068_13,tree068_13]
def tree068_76 : CoverTree := CoverTree.split [tree068_64,tree068_75,tree068_17,tree068_19,tree068_72,tree068_13]
def tree068_77 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_76,tree068_34,tree068_25,tree068_27]
def tree068_78 : CoverTree := CoverTree.split [tree068_4,tree068_4,tree068_55,tree068_63,tree068_74,tree068_77]
def tree068_79 : CoverTree := CoverTree.split [tree068_0,tree068_1,tree068_2,tree068_3,tree068_36,tree068_78]
def tree068_80 : CoverTree := CoverTree.reject 147
def tree068_81 : CoverTree := CoverTree.reject 148
def tree068_82 : CoverTree := CoverTree.reject 149
def tree068_83 : CoverTree := CoverTree.reject 23
def tree068_84 : CoverTree := CoverTree.reject 172
def tree068_85 : CoverTree := CoverTree.reject 10
def tree068_86 : CoverTree := CoverTree.reject 405
def tree068_87 : CoverTree := CoverTree.reject 3
def tree068_88 : CoverTree := CoverTree.reject 17
def tree068_89 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_88,tree068_13,tree068_13,tree068_13]
def tree068_90 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_86,tree068_89,tree068_89,tree068_89]
def tree068_91 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_89,tree068_89,tree068_89,tree068_89]
def tree068_92 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_83,tree068_84,tree068_90,tree068_91]
def tree068_93 : CoverTree := CoverTree.split [tree068_4,tree068_4,tree068_80,tree068_81,tree068_82,tree068_92]
def tree068_94 : CoverTree := CoverTree.reject 0
def tree068_95 : CoverTree := CoverTree.reject 37
def tree068_96 : CoverTree := CoverTree.reject 180
def tree068_97 : CoverTree := CoverTree.reject 102
def tree068_98 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_95,tree068_96,tree068_97]
def tree068_99 : CoverTree := CoverTree.reject 62
def tree068_100 : CoverTree := CoverTree.reject 159
def tree068_101 : CoverTree := CoverTree.reject 164
def tree068_102 : CoverTree := CoverTree.reject 322
def tree068_103 : CoverTree := CoverTree.reject 323
def tree068_104 : CoverTree := CoverTree.reject 324
def tree068_105 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_106 : CoverTree := CoverTree.split [tree068_101,tree068_102,tree068_103,tree068_104,tree068_105,tree068_105]
def tree068_107 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_99,tree068_100,tree068_106]
def tree068_108 : CoverTree := CoverTree.reject 5
def tree068_109 : CoverTree := CoverTree.reject 113
def tree068_110 : CoverTree := CoverTree.split [tree068_108,tree068_109,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_111 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_11,tree068_12,tree068_13,tree068_13]
def tree068_112 : CoverTree := CoverTree.split [tree068_111,tree068_105,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_113 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_99,tree068_110,tree068_112]
def tree068_114 : CoverTree := CoverTree.reject 406
def tree068_115 : CoverTree := CoverTree.reject 325
def tree068_116 : CoverTree := CoverTree.reject 326
def tree068_117 : CoverTree := CoverTree.split [tree068_64,tree068_114,tree068_115,tree068_116,tree068_105,tree068_105]
def tree068_118 : CoverTree := CoverTree.reject 327
def tree068_119 : CoverTree := CoverTree.reject 202
def tree068_120 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_119,tree068_13,tree068_13,tree068_13]
def tree068_121 : CoverTree := CoverTree.split [tree068_31,tree068_118,tree068_120,tree068_105,tree068_105,tree068_105]
def tree068_122 : CoverTree := CoverTree.reject 165
def tree068_123 : CoverTree := CoverTree.split [tree068_122,tree068_105,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_124 : CoverTree := CoverTree.reject 328
def tree068_125 : CoverTree := CoverTree.split [tree068_111,tree068_124,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_126 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_117,tree068_121,tree068_123,tree068_125]
def tree068_127 : CoverTree := CoverTree.split [tree068_4,tree068_4,tree068_98,tree068_107,tree068_113,tree068_126]
def tree068_128 : CoverTree := CoverTree.reject 32
def tree068_129 : CoverTree := CoverTree.reject 74
def tree068_130 : CoverTree := CoverTree.reject 75
def tree068_131 : CoverTree := CoverTree.reject 203
def tree068_132 : CoverTree := CoverTree.split [tree068_9,tree068_10,tree068_11,tree068_12,tree068_50,tree068_131]
def tree068_133 : CoverTree := CoverTree.reject 329
def tree068_134 : CoverTree := CoverTree.reject 330
def tree068_135 : CoverTree := CoverTree.reject 331
def tree068_136 : CoverTree := CoverTree.split [tree068_132,tree068_133,tree068_134,tree068_135,tree068_13,tree068_13]
def tree068_137 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_128,tree068_129,tree068_130,tree068_136]
def tree068_138 : CoverTree := CoverTree.reject 161
def tree068_139 : CoverTree := CoverTree.reject 76
def tree068_140 : CoverTree := CoverTree.reject 407
def tree068_141 : CoverTree := CoverTree.reject 211
def tree068_142 : CoverTree := CoverTree.split [tree068_108,tree068_140,tree068_141,tree068_19,tree068_13,tree068_13]
def tree068_143 : CoverTree := CoverTree.reject 212
def tree068_144 : CoverTree := CoverTree.reject 213
def tree068_145 : CoverTree := CoverTree.reject 214
def tree068_146 : CoverTree := CoverTree.split [tree068_14,tree068_143,tree068_144,tree068_145,tree068_13,tree068_13]
def tree068_147 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_138,tree068_139,tree068_142,tree068_146]
def tree068_148 : CoverTree := CoverTree.reject 104
def tree068_149 : CoverTree := CoverTree.reject 77
def tree068_150 : CoverTree := CoverTree.reject 332
def tree068_151 : CoverTree := CoverTree.reject 215
def tree068_152 : CoverTree := CoverTree.split [tree068_108,tree068_150,tree068_151,tree068_19,tree068_13,tree068_13]
def tree068_153 : CoverTree := CoverTree.reject 216
def tree068_154 : CoverTree := CoverTree.split [tree068_14,tree068_153,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_155 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_148,tree068_149,tree068_152,tree068_154]
def tree068_156 : CoverTree := CoverTree.reject 408
def tree068_157 : CoverTree := CoverTree.reject 333
def tree068_158 : CoverTree := CoverTree.reject 217
def tree068_159 : CoverTree := CoverTree.split [tree068_64,tree068_156,tree068_157,tree068_158,tree068_72,tree068_13]
def tree068_160 : CoverTree := CoverTree.reject 334
def tree068_161 : CoverTree := CoverTree.split [tree068_31,tree068_160,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_162 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_159,tree068_161,tree068_25,tree068_27]
def tree068_163 : CoverTree := CoverTree.split [tree068_4,tree068_4,tree068_137,tree068_147,tree068_155,tree068_162]
def tree068_164 : CoverTree := CoverTree.reject 117
def tree068_165 : CoverTree := CoverTree.reject 78
def tree068_166 : CoverTree := CoverTree.reject 73
def tree068_167 : CoverTree := CoverTree.reject 465
def tree068_168 : CoverTree := CoverTree.reject 335
def tree068_169 : CoverTree := CoverTree.reject 218
def tree068_170 : CoverTree := CoverTree.reject 219
def tree068_171 : CoverTree := CoverTree.split [tree068_167,tree068_168,tree068_169,tree068_170,tree068_13,tree068_13]
def tree068_172 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_164,tree068_165,tree068_166,tree068_171]
def tree068_173 : CoverTree := CoverTree.reject 95
def tree068_174 : CoverTree := CoverTree.reject 409
def tree068_175 : CoverTree := CoverTree.reject 220
def tree068_176 : CoverTree := CoverTree.split [tree068_31,tree068_174,tree068_175,tree068_19,tree068_58,tree068_13]
def tree068_177 : CoverTree := CoverTree.reject 200
def tree068_178 : CoverTree := CoverTree.reject 336
def tree068_179 : CoverTree := CoverTree.reject 221
def tree068_180 : CoverTree := CoverTree.split [tree068_177,tree068_178,tree068_179,tree068_19,tree068_13,tree068_13]
def tree068_181 : CoverTree := CoverTree.reject 222
def tree068_182 : CoverTree := CoverTree.split [tree068_14,tree068_181,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_183 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_173,tree068_176,tree068_180,tree068_182]
def tree068_184 : CoverTree := CoverTree.reject 96
def tree068_185 : CoverTree := CoverTree.reject 337
def tree068_186 : CoverTree := CoverTree.split [tree068_31,tree068_185,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_187 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_184,tree068_186,tree068_25,tree068_27]
def tree068_188 : CoverTree := CoverTree.split [tree068_4,tree068_4,tree068_172,tree068_183,tree068_187,tree068_77]
def tree068_189 : CoverTree := CoverTree.reject 97
def tree068_190 : CoverTree := CoverTree.reject 410
def tree068_191 : CoverTree := CoverTree.reject 338
def tree068_192 : CoverTree := CoverTree.reject 223
def tree068_193 : CoverTree := CoverTree.reject 224
def tree068_194 : CoverTree := CoverTree.split [tree068_31,tree068_190,tree068_191,tree068_192,tree068_193,tree068_13]
def tree068_195 : CoverTree := CoverTree.reject 339
def tree068_196 : CoverTree := CoverTree.reject 225
def tree068_197 : CoverTree := CoverTree.split [tree068_45,tree068_195,tree068_196,tree068_19,tree068_48,tree068_13]
def tree068_198 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_189,tree068_194,tree068_197,tree068_54]
def tree068_199 : CoverTree := CoverTree.reject 450
def tree068_200 : CoverTree := CoverTree.reject 340
def tree068_201 : CoverTree := CoverTree.reject 226
def tree068_202 : CoverTree := CoverTree.split [tree068_64,tree068_199,tree068_200,tree068_201,tree068_72,tree068_13]
def tree068_203 : CoverTree := CoverTree.reject 341
def tree068_204 : CoverTree := CoverTree.reject 227
def tree068_205 : CoverTree := CoverTree.split [tree068_31,tree068_203,tree068_204,tree068_19,tree068_58,tree068_13]
def tree068_206 : CoverTree := CoverTree.reject 466
def tree068_207 : CoverTree := CoverTree.reject 342
def tree068_208 : CoverTree := CoverTree.split [tree068_206,tree068_207,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_209 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_202,tree068_205,tree068_208,tree068_27]
def tree068_210 : CoverTree := CoverTree.reject 228
def tree068_211 : CoverTree := CoverTree.split [tree068_64,tree068_68,tree068_70,tree068_210,tree068_72,tree068_13]
def tree068_212 : CoverTree := CoverTree.reject 343
def tree068_213 : CoverTree := CoverTree.split [tree068_31,tree068_212,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_214 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_211,tree068_213,tree068_25,tree068_27]
def tree068_215 : CoverTree := CoverTree.reject 411
def tree068_216 : CoverTree := CoverTree.reject 229
def tree068_217 : CoverTree := CoverTree.split [tree068_64,tree068_215,tree068_216,tree068_19,tree068_72,tree068_13]
def tree068_218 : CoverTree := CoverTree.split [tree068_29,tree068_29,tree068_217,tree068_34,tree068_25,tree068_27]
def tree068_219 : CoverTree := CoverTree.split [tree068_4,tree068_4,tree068_198,tree068_209,tree068_214,tree068_218]
def tree068_220 : CoverTree := CoverTree.split [tree068_0,tree068_93,tree068_127,tree068_163,tree068_188,tree068_219]
def tree068_221 : CoverTree := CoverTree.reject 34
def tree068_222 : CoverTree := CoverTree.reject 150
def tree068_223 : CoverTree := CoverTree.reject 41
def tree068_224 : CoverTree := CoverTree.reject 412
def tree068_225 : CoverTree := CoverTree.reject 413
def tree068_226 : CoverTree := CoverTree.reject 414
def tree068_227 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_224,tree068_225,tree068_226,tree068_89]
def tree068_228 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_223,tree068_223,tree068_227]
def tree068_229 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_223,tree068_223,tree068_91]
def tree068_230 : CoverTree := CoverTree.reject 173
def tree068_231 : CoverTree := CoverTree.reject 415
def tree068_232 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_231,tree068_89,tree068_89,tree068_89]
def tree068_233 : CoverTree := CoverTree.split [tree068_83,tree068_83,tree068_83,tree068_230,tree068_232,tree068_91]
def tree068_234 : CoverTree := CoverTree.split [tree068_221,tree068_221,tree068_222,tree068_228,tree068_229,tree068_233]
def tree068_235 : CoverTree := CoverTree.reject 18
def tree068_236 : CoverTree := CoverTree.reject 47
def tree068_237 : CoverTree := CoverTree.reject 48
def tree068_238 : CoverTree := CoverTree.reject 103
def tree068_239 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_236,tree068_237,tree068_238]
def tree068_240 : CoverTree := CoverTree.reject 181
def tree068_241 : CoverTree := CoverTree.reject 307
def tree068_242 : CoverTree := CoverTree.reject 125
def tree068_243 : CoverTree := CoverTree.reject 344
def tree068_244 : CoverTree := CoverTree.reject 345
def tree068_245 : CoverTree := CoverTree.reject 312
def tree068_246 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_245,tree068_13,tree068_13,tree068_13]
def tree068_247 : CoverTree := CoverTree.split [tree068_241,tree068_242,tree068_243,tree068_244,tree068_246,tree068_105]
def tree068_248 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_95,tree068_240,tree068_247]
def tree068_249 : CoverTree := CoverTree.reject 115
def tree068_250 : CoverTree := CoverTree.reject 111
def tree068_251 : CoverTree := CoverTree.reject 112
def tree068_252 : CoverTree := CoverTree.reject 346
def tree068_253 : CoverTree := CoverTree.reject 347
def tree068_254 : CoverTree := CoverTree.split [tree068_108,tree068_250,tree068_251,tree068_252,tree068_253,tree068_105]
def tree068_255 : CoverTree := CoverTree.reject 348
def tree068_256 : CoverTree := CoverTree.reject 349
def tree068_257 : CoverTree := CoverTree.split [tree068_101,tree068_255,tree068_256,tree068_105,tree068_105,tree068_105]
def tree068_258 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_249,tree068_254,tree068_257]
def tree068_259 : CoverTree := CoverTree.reject 126
def tree068_260 : CoverTree := CoverTree.reject 313
def tree068_261 : CoverTree := CoverTree.reject 314
def tree068_262 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_260,tree068_261,tree068_13,tree068_13]
def tree068_263 : CoverTree := CoverTree.reject 315
def tree068_264 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_263,tree068_13,tree068_13,tree068_13]
def tree068_265 : CoverTree := CoverTree.split [tree068_108,tree068_259,tree068_262,tree068_264,tree068_105,tree068_105]
def tree068_266 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_265,tree068_110,tree068_112]
def tree068_267 : CoverTree := CoverTree.reject 63
def tree068_268 : CoverTree := CoverTree.reject 120
def tree068_269 : CoverTree := CoverTree.reject 416
def tree068_270 : CoverTree := CoverTree.reject 350
def tree068_271 : CoverTree := CoverTree.split [tree068_64,tree068_269,tree068_270,tree068_105,tree068_105,tree068_105]
def tree068_272 : CoverTree := CoverTree.reject 351
def tree068_273 : CoverTree := CoverTree.split [tree068_31,tree068_272,tree068_120,tree068_105,tree068_105,tree068_105]
def tree068_274 : CoverTree := CoverTree.reject 352
def tree068_275 : CoverTree := CoverTree.split [tree068_111,tree068_274,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_276 : CoverTree := CoverTree.split [tree068_267,tree068_268,tree068_271,tree068_273,tree068_123,tree068_275]
def tree068_277 : CoverTree := CoverTree.split [tree068_235,tree068_239,tree068_248,tree068_258,tree068_266,tree068_276]
def tree068_278 : CoverTree := CoverTree.reject 14
def tree068_279 : CoverTree := CoverTree.reject 38
def tree068_280 : CoverTree := CoverTree.reject 39
def tree068_281 : CoverTree := CoverTree.reject 98
def tree068_282 : CoverTree := CoverTree.reject 308
def tree068_283 : CoverTree := CoverTree.reject 114
def tree068_284 : CoverTree := CoverTree.reject 230
def tree068_285 : CoverTree := CoverTree.reject 231
def tree068_286 : CoverTree := CoverTree.reject 35
def tree068_287 : CoverTree := CoverTree.reject 316
def tree068_288 : CoverTree := CoverTree.split [tree068_286,tree068_287,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_289 : CoverTree := CoverTree.split [tree068_286,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_290 : CoverTree := CoverTree.split [tree068_282,tree068_283,tree068_284,tree068_285,tree068_288,tree068_289]
def tree068_291 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_279,tree068_280,tree068_281,tree068_290]
def tree068_292 : CoverTree := CoverTree.reject 79
def tree068_293 : CoverTree := CoverTree.reject 127
def tree068_294 : CoverTree := CoverTree.reject 232
def tree068_295 : CoverTree := CoverTree.reject 233
def tree068_296 : CoverTree := CoverTree.reject 234
def tree068_297 : CoverTree := CoverTree.reject 317
def tree068_298 : CoverTree := CoverTree.split [tree068_13,tree068_297,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_299 : CoverTree := CoverTree.split [tree068_108,tree068_293,tree068_294,tree068_295,tree068_296,tree068_298]
def tree068_300 : CoverTree := CoverTree.reject 353
def tree068_301 : CoverTree := CoverTree.reject 354
def tree068_302 : CoverTree := CoverTree.reject 206
def tree068_303 : CoverTree := CoverTree.split [tree068_18,tree068_302,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_304 : CoverTree := CoverTree.split [tree068_132,tree068_300,tree068_301,tree068_303,tree068_13,tree068_13]
def tree068_305 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_128,tree068_292,tree068_299,tree068_304]
def tree068_306 : CoverTree := CoverTree.reject 162
def tree068_307 : CoverTree := CoverTree.reject 80
def tree068_308 : CoverTree := CoverTree.reject 417
def tree068_309 : CoverTree := CoverTree.reject 235
def tree068_310 : CoverTree := CoverTree.split [tree068_108,tree068_308,tree068_309,tree068_19,tree068_13,tree068_13]
def tree068_311 : CoverTree := CoverTree.reject 236
def tree068_312 : CoverTree := CoverTree.split [tree068_14,tree068_311,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_313 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_306,tree068_307,tree068_310,tree068_312]
def tree068_314 : CoverTree := CoverTree.reject 68
def tree068_315 : CoverTree := CoverTree.split [tree068_108,tree068_314,tree068_70,tree068_19,tree068_72,tree068_13]
def tree068_316 : CoverTree := CoverTree.reject 128
def tree068_317 : CoverTree := CoverTree.split [tree068_108,tree068_316,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_318 : CoverTree := CoverTree.split [tree068_108,tree068_24,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_319 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_315,tree068_317,tree068_318,tree068_27]
def tree068_320 : CoverTree := CoverTree.reject 60
def tree068_321 : CoverTree := CoverTree.reject 105
def tree068_322 : CoverTree := CoverTree.reject 208
def tree068_323 : CoverTree := CoverTree.split [tree068_16,tree068_322,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_324 : CoverTree := CoverTree.split [tree068_64,tree068_75,tree068_323,tree068_19,tree068_72,tree068_13]
def tree068_325 : CoverTree := CoverTree.split [tree068_320,tree068_321,tree068_324,tree068_34,tree068_25,tree068_27]
def tree068_326 : CoverTree := CoverTree.split [tree068_278,tree068_291,tree068_305,tree068_313,tree068_319,tree068_325]
def tree068_327 : CoverTree := CoverTree.reject 31
def tree068_328 : CoverTree := CoverTree.reject 28
def tree068_329 : CoverTree := CoverTree.reject 42
def tree068_330 : CoverTree := CoverTree.reject 43
def tree068_331 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_327,tree068_328,tree068_329,tree068_330]
def tree068_332 : CoverTree := CoverTree.reject 40
def tree068_333 : CoverTree := CoverTree.reject 99
def tree068_334 : CoverTree := CoverTree.reject 81
def tree068_335 : CoverTree := CoverTree.reject 309
def tree068_336 : CoverTree := CoverTree.reject 237
def tree068_337 : CoverTree := CoverTree.reject 238
def tree068_338 : CoverTree := CoverTree.reject 318
def tree068_339 : CoverTree := CoverTree.split [tree068_18,tree068_338,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_340 : CoverTree := CoverTree.split [tree068_335,tree068_336,tree068_337,tree068_339,tree068_289,tree068_289]
def tree068_341 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_332,tree068_333,tree068_334,tree068_340]
def tree068_342 : CoverTree := CoverTree.reject 118
def tree068_343 : CoverTree := CoverTree.reject 129
def tree068_344 : CoverTree := CoverTree.reject 239
def tree068_345 : CoverTree := CoverTree.reject 240
def tree068_346 : CoverTree := CoverTree.reject 241
def tree068_347 : CoverTree := CoverTree.split [tree068_31,tree068_343,tree068_344,tree068_345,tree068_346,tree068_13]
def tree068_348 : CoverTree := CoverTree.reject 130
def tree068_349 : CoverTree := CoverTree.reject 242
def tree068_350 : CoverTree := CoverTree.reject 243
def tree068_351 : CoverTree := CoverTree.split [tree068_45,tree068_348,tree068_349,tree068_350,tree068_48,tree068_13]
def tree068_352 : CoverTree := CoverTree.reject 355
def tree068_353 : CoverTree := CoverTree.reject 244
def tree068_354 : CoverTree := CoverTree.split [tree068_51,tree068_352,tree068_353,tree068_19,tree068_13,tree068_13]
def tree068_355 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_342,tree068_347,tree068_351,tree068_354]
def tree068_356 : CoverTree := CoverTree.reject 100
def tree068_357 : CoverTree := CoverTree.reject 418
def tree068_358 : CoverTree := CoverTree.reject 245
def tree068_359 : CoverTree := CoverTree.split [tree068_31,tree068_357,tree068_358,tree068_19,tree068_58,tree068_13]
def tree068_360 : CoverTree := CoverTree.reject 356
def tree068_361 : CoverTree := CoverTree.split [tree068_177,tree068_360,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_362 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_356,tree068_359,tree068_361,tree068_27]
def tree068_363 : CoverTree := CoverTree.reject 357
def tree068_364 : CoverTree := CoverTree.split [tree068_31,tree068_363,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_365 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_73,tree068_364,tree068_25,tree068_27]
def tree068_366 : CoverTree := CoverTree.reject 89
def tree068_367 : CoverTree := CoverTree.reject 29
def tree068_368 : CoverTree := CoverTree.reject 30
def tree068_369 : CoverTree := CoverTree.reject 19
def tree068_370 : CoverTree := CoverTree.reject 143
def tree068_371 : CoverTree := CoverTree.reject 144
def tree068_372 : CoverTree := CoverTree.reject 145
def tree068_373 : CoverTree := CoverTree.split [tree068_370,tree068_371,tree068_372,tree068_13,tree068_13,tree068_13]
def tree068_374 : CoverTree := CoverTree.reject 246
def tree068_375 : CoverTree := CoverTree.split [tree068_366,tree068_367,tree068_368,tree068_369,tree068_373,tree068_374]
def tree068_376 : CoverTree := CoverTree.reject 55
def tree068_377 : CoverTree := CoverTree.reject 467
def tree068_378 : CoverTree := CoverTree.reject 419
def tree068_379 : CoverTree := CoverTree.reject 319
def tree068_380 : CoverTree := CoverTree.split [tree068_18,tree068_379,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_381 : CoverTree := CoverTree.reject 71
def tree068_382 : CoverTree := CoverTree.split [tree068_381,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_383 : CoverTree := CoverTree.split [tree068_376,tree068_377,tree068_378,tree068_380,tree068_382,tree068_13]
def tree068_384 : CoverTree := CoverTree.split [tree068_375,tree068_383,tree068_76,tree068_34,tree068_25,tree068_27]
def tree068_385 : CoverTree := CoverTree.split [tree068_331,tree068_341,tree068_355,tree068_362,tree068_365,tree068_384]
def tree068_386 : CoverTree := CoverTree.reject 61
def tree068_387 : CoverTree := CoverTree.reject 36
def tree068_388 : CoverTree := CoverTree.reject 44
def tree068_389 : CoverTree := CoverTree.reject 45
def tree068_390 : CoverTree := CoverTree.split [tree068_386,tree068_387,tree068_327,tree068_328,tree068_388,tree068_389]
def tree068_391 : CoverTree := CoverTree.reject 54
def tree068_392 : CoverTree := CoverTree.reject 190
def tree068_393 : CoverTree := CoverTree.reject 101
def tree068_394 : CoverTree := CoverTree.reject 468
def tree068_395 : CoverTree := CoverTree.reject 247
def tree068_396 : CoverTree := CoverTree.reject 358
def tree068_397 : CoverTree := CoverTree.split [tree068_31,tree068_394,tree068_395,tree068_396,tree068_289,tree068_289]
def tree068_398 : CoverTree := CoverTree.reject 138
def tree068_399 : CoverTree := CoverTree.reject 420
def tree068_400 : CoverTree := CoverTree.reject 248
def tree068_401 : CoverTree := CoverTree.reject 249
def tree068_402 : CoverTree := CoverTree.split [tree068_398,tree068_399,tree068_400,tree068_401,tree068_289,tree068_289]
def tree068_403 : CoverTree := CoverTree.reject 131
def tree068_404 : CoverTree := CoverTree.reject 320
def tree068_405 : CoverTree := CoverTree.split [tree068_9,tree068_10,tree068_11,tree068_12,tree068_403,tree068_404]
def tree068_406 : CoverTree := CoverTree.reject 250
def tree068_407 : CoverTree := CoverTree.reject 321
def tree068_408 : CoverTree := CoverTree.split [tree068_16,tree068_407,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_409 : CoverTree := CoverTree.split [tree068_405,tree068_406,tree068_408,tree068_19,tree068_289,tree068_289]
def tree068_410 : CoverTree := CoverTree.split [tree068_391,tree068_392,tree068_393,tree068_397,tree068_402,tree068_409]
def tree068_411 : CoverTree := CoverTree.reject 49
def tree068_412 : CoverTree := CoverTree.reject 286
def tree068_413 : CoverTree := CoverTree.reject 123
def tree068_414 : CoverTree := CoverTree.reject 388
def tree068_415 : CoverTree := CoverTree.reject 389
def tree068_416 : CoverTree := CoverTree.reject 402
def tree068_417 : CoverTree := CoverTree.reject 403
def tree068_418 : CoverTree := CoverTree.reject 404
def tree068_419 : CoverTree := CoverTree.split [tree068_18,tree068_414,tree068_415,tree068_416,tree068_417,tree068_418]
def tree068_420 : CoverTree := CoverTree.reject 251
def tree068_421 : CoverTree := CoverTree.reject 301
def tree068_422 : CoverTree := CoverTree.split [tree068_421,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_423 : CoverTree := CoverTree.split [tree068_376,tree068_412,tree068_413,tree068_419,tree068_420,tree068_422]
def tree068_424 : CoverTree := CoverTree.reject 158
def tree068_425 : CoverTree := CoverTree.reject 252
def tree068_426 : CoverTree := CoverTree.reject 253
def tree068_427 : CoverTree := CoverTree.reject 254
def tree068_428 : CoverTree := CoverTree.reject 185
def tree068_429 : CoverTree := CoverTree.split [tree068_428,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_430 : CoverTree := CoverTree.split [tree068_64,tree068_424,tree068_425,tree068_426,tree068_427,tree068_429]
def tree068_431 : CoverTree := CoverTree.reject 421
def tree068_432 : CoverTree := CoverTree.reject 359
def tree068_433 : CoverTree := CoverTree.reject 255
def tree068_434 : CoverTree := CoverTree.split [tree068_31,tree068_431,tree068_432,tree068_433,tree068_43,tree068_13]
def tree068_435 : CoverTree := CoverTree.reject 360
def tree068_436 : CoverTree := CoverTree.reject 256
def tree068_437 : CoverTree := CoverTree.split [tree068_45,tree068_435,tree068_436,tree068_19,tree068_48,tree068_13]
def tree068_438 : CoverTree := CoverTree.split [tree068_411,tree068_423,tree068_430,tree068_434,tree068_437,tree068_54]
def tree068_439 : CoverTree := CoverTree.reject 50
def tree068_440 : CoverTree := CoverTree.reject 287
def tree068_441 : CoverTree := CoverTree.reject 422
def tree068_442 : CoverTree := CoverTree.reject 361
def tree068_443 : CoverTree := CoverTree.reject 257
def tree068_444 : CoverTree := CoverTree.reject 198
def tree068_445 : CoverTree := CoverTree.split [tree068_444,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_446 : CoverTree := CoverTree.split [tree068_376,tree068_440,tree068_441,tree068_442,tree068_443,tree068_445]
def tree068_447 : CoverTree := CoverTree.reject 451
def tree068_448 : CoverTree := CoverTree.reject 362
def tree068_449 : CoverTree := CoverTree.reject 258
def tree068_450 : CoverTree := CoverTree.split [tree068_64,tree068_447,tree068_448,tree068_449,tree068_72,tree068_13]
def tree068_451 : CoverTree := CoverTree.reject 363
def tree068_452 : CoverTree := CoverTree.split [tree068_31,tree068_451,tree068_17,tree068_19,tree068_58,tree068_13]
def tree068_453 : CoverTree := CoverTree.split [tree068_439,tree068_446,tree068_450,tree068_452,tree068_62,tree068_27]
def tree068_454 : CoverTree := CoverTree.reject 439
def tree068_455 : CoverTree := CoverTree.reject 288
def tree068_456 : CoverTree := CoverTree.reject 70
def tree068_457 : CoverTree := CoverTree.reject 304
def tree068_458 : CoverTree := CoverTree.reject 305
def tree068_459 : CoverTree := CoverTree.reject 306
def tree068_460 : CoverTree := CoverTree.split [tree068_16,tree068_456,tree068_457,tree068_458,tree068_459,tree068_13]
def tree068_461 : CoverTree := CoverTree.reject 186
def tree068_462 : CoverTree := CoverTree.split [tree068_18,tree068_461,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_463 : CoverTree := CoverTree.split [tree068_376,tree068_455,tree068_460,tree068_462,tree068_382,tree068_13]
def tree068_464 : CoverTree := CoverTree.split [tree068_454,tree068_463,tree068_73,tree068_34,tree068_25,tree068_27]
def tree068_465 : CoverTree := CoverTree.reject 174
def tree068_466 : CoverTree := CoverTree.split [tree068_465,tree068_13,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_467 : CoverTree := CoverTree.split [tree068_366,tree068_367,tree068_368,tree068_369,tree068_373,tree068_466]
def tree068_468 : CoverTree := CoverTree.reject 69
def tree068_469 : CoverTree := CoverTree.reject 65
def tree068_470 : CoverTree := CoverTree.reject 66
def tree068_471 : CoverTree := CoverTree.reject 67
def tree068_472 : CoverTree := CoverTree.split [tree068_22,tree068_468,tree068_469,tree068_470,tree068_471,tree068_13]
def tree068_473 : CoverTree := CoverTree.reject 142
def tree068_474 : CoverTree := CoverTree.split [tree068_16,tree068_456,tree068_473,tree068_13,tree068_13,tree068_13]
def tree068_475 : CoverTree := CoverTree.split [tree068_376,tree068_472,tree068_474,tree068_19,tree068_382,tree068_13]
def tree068_476 : CoverTree := CoverTree.split [tree068_467,tree068_475,tree068_76,tree068_34,tree068_25,tree068_27]
def tree068_477 : CoverTree := CoverTree.split [tree068_390,tree068_410,tree068_438,tree068_453,tree068_464,tree068_476]
def tree068_478 : CoverTree := CoverTree.split [tree068_0,tree068_234,tree068_277,tree068_326,tree068_385,tree068_477]
def tree068_479 : CoverTree := CoverTree.reject 64
def tree068_480 : CoverTree := CoverTree.reject 169
def tree068_481 : CoverTree := CoverTree.reject 452
def tree068_482 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_481,tree068_89,tree068_89,tree068_89]
def tree068_483 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_479,tree068_480,tree068_482]
def tree068_484 : CoverTree := CoverTree.reject 393
def tree068_485 : CoverTree := CoverTree.reject 423
def tree068_486 : CoverTree := CoverTree.reject 424
def tree068_487 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_485,tree068_486,tree068_89,tree068_89]
def tree068_488 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_479,tree068_484,tree068_487]
def tree068_489 : CoverTree := CoverTree.reject 88
def tree068_490 : CoverTree := CoverTree.split [tree068_108,tree068_85,tree068_489,tree068_489,tree068_89,tree068_89]
def tree068_491 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_479,tree068_490,tree068_91]
def tree068_492 : CoverTree := CoverTree.reject 132
def tree068_493 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_492,tree068_89,tree068_89,tree068_89]
def tree068_494 : CoverTree := CoverTree.split [tree068_83,tree068_83,tree068_83,tree068_493,tree068_91,tree068_91]
def tree068_495 : CoverTree := CoverTree.split [tree068_221,tree068_221,tree068_483,tree068_488,tree068_491,tree068_494]
def tree068_496 : CoverTree := CoverTree.reject 391
def tree068_497 : CoverTree := CoverTree.reject 152
def tree068_498 : CoverTree := CoverTree.reject 153
def tree068_499 : CoverTree := CoverTree.reject 364
def tree068_500 : CoverTree := CoverTree.reject 365
def tree068_501 : CoverTree := CoverTree.split [tree068_496,tree068_497,tree068_498,tree068_499,tree068_500,tree068_105]
def tree068_502 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_236,tree068_237,tree068_501]
def tree068_503 : CoverTree := CoverTree.reject 108
def tree068_504 : CoverTree := CoverTree.reject 109
def tree068_505 : CoverTree := CoverTree.reject 110
def tree068_506 : CoverTree := CoverTree.reject 366
def tree068_507 : CoverTree := CoverTree.split [tree068_108,tree068_503,tree068_504,tree068_505,tree068_506,tree068_105]
def tree068_508 : CoverTree := CoverTree.reject 367
def tree068_509 : CoverTree := CoverTree.split [tree068_241,tree068_242,tree068_508,tree068_105,tree068_246,tree068_105]
def tree068_510 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_95,tree068_507,tree068_509]
def tree068_511 : CoverTree := CoverTree.reject 116
def tree068_512 : CoverTree := CoverTree.split [tree068_108,tree068_250,tree068_251,tree068_105,tree068_105,tree068_105]
def tree068_513 : CoverTree := CoverTree.reject 368
def tree068_514 : CoverTree := CoverTree.reject 369
def tree068_515 : CoverTree := CoverTree.split [tree068_101,tree068_513,tree068_514,tree068_105,tree068_105,tree068_105]
def tree068_516 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_511,tree068_512,tree068_515]
def tree068_517 : CoverTree := CoverTree.reject 370
def tree068_518 : CoverTree := CoverTree.split [tree068_111,tree068_517,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_519 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_265,tree068_110,tree068_518]
def tree068_520 : CoverTree := CoverTree.reject 121
def tree068_521 : CoverTree := CoverTree.reject 425
def tree068_522 : CoverTree := CoverTree.split [tree068_64,tree068_521,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_523 : CoverTree := CoverTree.reject 371
def tree068_524 : CoverTree := CoverTree.split [tree068_31,tree068_523,tree068_120,tree068_105,tree068_105,tree068_105]
def tree068_525 : CoverTree := CoverTree.split [tree068_267,tree068_520,tree068_522,tree068_524,tree068_123,tree068_112]
def tree068_526 : CoverTree := CoverTree.split [tree068_235,tree068_502,tree068_510,tree068_516,tree068_519,tree068_525]
def tree068_527 : CoverTree := CoverTree.reject 154
def tree068_528 : CoverTree := CoverTree.reject 133
def tree068_529 : CoverTree := CoverTree.reject 259
def tree068_530 : CoverTree := CoverTree.reject 260
def tree068_531 : CoverTree := CoverTree.split [tree068_108,tree068_527,tree068_528,tree068_529,tree068_530,tree068_289]
def tree068_532 : CoverTree := CoverTree.reject 261
def tree068_533 : CoverTree := CoverTree.reject 262
def tree068_534 : CoverTree := CoverTree.split [tree068_282,tree068_283,tree068_532,tree068_533,tree068_288,tree068_289]
def tree068_535 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_279,tree068_280,tree068_531,tree068_534]
def tree068_536 : CoverTree := CoverTree.reject 82
def tree068_537 : CoverTree := CoverTree.reject 263
def tree068_538 : CoverTree := CoverTree.reject 395
def tree068_539 : CoverTree := CoverTree.split [tree068_18,tree068_538,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_540 : CoverTree := CoverTree.split [tree068_108,tree068_293,tree068_537,tree068_539,tree068_48,tree068_298]
def tree068_541 : CoverTree := CoverTree.reject 372
def tree068_542 : CoverTree := CoverTree.reject 373
def tree068_543 : CoverTree := CoverTree.split [tree068_132,tree068_541,tree068_542,tree068_303,tree068_13,tree068_13]
def tree068_544 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_128,tree068_536,tree068_540,tree068_543]
def tree068_545 : CoverTree := CoverTree.reject 85
def tree068_546 : CoverTree := CoverTree.reject 86
def tree068_547 : CoverTree := CoverTree.reject 396
def tree068_548 : CoverTree := CoverTree.reject 397
def tree068_549 : CoverTree := CoverTree.split [tree068_71,tree068_547,tree068_548,tree068_13,tree068_13,tree068_13]
def tree068_550 : CoverTree := CoverTree.reject 398
def tree068_551 : CoverTree := CoverTree.split [tree068_13,tree068_550,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_552 : CoverTree := CoverTree.split [tree068_108,tree068_314,tree068_545,tree068_546,tree068_549,tree068_551]
def tree068_553 : CoverTree := CoverTree.reject 155
def tree068_554 : CoverTree := CoverTree.reject 134
def tree068_555 : CoverTree := CoverTree.split [tree068_108,tree068_553,tree068_554,tree068_19,tree068_58,tree068_13]
def tree068_556 : CoverTree := CoverTree.reject 207
def tree068_557 : CoverTree := CoverTree.split [tree068_22,tree068_23,tree068_556,tree068_13,tree068_13,tree068_13]
def tree068_558 : CoverTree := CoverTree.split [tree068_108,tree068_557,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_559 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_552,tree068_555,tree068_558,tree068_27]
def tree068_560 : CoverTree := CoverTree.reject 392
def tree068_561 : CoverTree := CoverTree.reject 170
def tree068_562 : CoverTree := CoverTree.reject 399
def tree068_563 : CoverTree := CoverTree.split [tree068_18,tree068_562,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_564 : CoverTree := CoverTree.split [tree068_376,tree068_560,tree068_561,tree068_563,tree068_382,tree068_13]
def tree068_565 : CoverTree := CoverTree.split [tree068_320,tree068_564,tree068_324,tree068_34,tree068_25,tree068_27]
def tree068_566 : CoverTree := CoverTree.split [tree068_278,tree068_535,tree068_544,tree068_559,tree068_319,tree068_565]
def tree068_567 : CoverTree := CoverTree.reject 156
def tree068_568 : CoverTree := CoverTree.reject 135
def tree068_569 : CoverTree := CoverTree.reject 374
def tree068_570 : CoverTree := CoverTree.reject 264
def tree068_571 : CoverTree := CoverTree.split [tree068_31,tree068_567,tree068_568,tree068_569,tree068_570,tree068_289]
def tree068_572 : CoverTree := CoverTree.reject 157
def tree068_573 : CoverTree := CoverTree.reject 136
def tree068_574 : CoverTree := CoverTree.reject 265
def tree068_575 : CoverTree := CoverTree.reject 266
def tree068_576 : CoverTree := CoverTree.split [tree068_398,tree068_572,tree068_573,tree068_574,tree068_575,tree068_289]
def tree068_577 : CoverTree := CoverTree.reject 267
def tree068_578 : CoverTree := CoverTree.reject 268
def tree068_579 : CoverTree := CoverTree.split [tree068_335,tree068_577,tree068_578,tree068_339,tree068_289,tree068_289]
def tree068_580 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_332,tree068_571,tree068_576,tree068_579]
def tree068_581 : CoverTree := CoverTree.reject 119
def tree068_582 : CoverTree := CoverTree.reject 269
def tree068_583 : CoverTree := CoverTree.reject 400
def tree068_584 : CoverTree := CoverTree.split [tree068_18,tree068_583,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_585 : CoverTree := CoverTree.split [tree068_31,tree068_343,tree068_582,tree068_584,tree068_43,tree068_13]
def tree068_586 : CoverTree := CoverTree.reject 270
def tree068_587 : CoverTree := CoverTree.split [tree068_45,tree068_348,tree068_586,tree068_19,tree068_48,tree068_13]
def tree068_588 : CoverTree := CoverTree.reject 209
def tree068_589 : CoverTree := CoverTree.split [tree068_22,tree068_588,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_590 : CoverTree := CoverTree.split [tree068_51,tree068_589,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_591 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_581,tree068_585,tree068_587,tree068_590]
def tree068_592 : CoverTree := CoverTree.reject 171
def tree068_593 : CoverTree := CoverTree.reject 375
def tree068_594 : CoverTree := CoverTree.reject 401
def tree068_595 : CoverTree := CoverTree.split [tree068_18,tree068_594,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_596 : CoverTree := CoverTree.split [tree068_64,tree068_592,tree068_593,tree068_595,tree068_72,tree068_13]
def tree068_597 : CoverTree := CoverTree.reject 210
def tree068_598 : CoverTree := CoverTree.split [tree068_22,tree068_32,tree068_597,tree068_13,tree068_13,tree068_13]
def tree068_599 : CoverTree := CoverTree.split [tree068_31,tree068_598,tree068_17,tree068_19,tree068_58,tree068_13]
def tree068_600 : CoverTree := CoverTree.split [tree068_177,tree068_24,tree068_17,tree068_19,tree068_13,tree068_13]
def tree068_601 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_596,tree068_599,tree068_600,tree068_27]
def tree068_602 : CoverTree := CoverTree.split [tree068_6,tree068_6,tree068_73,tree068_34,tree068_25,tree068_27]
def tree068_603 : CoverTree := CoverTree.split [tree068_376,tree068_472,tree068_474,tree068_380,tree068_382,tree068_13]
def tree068_604 : CoverTree := CoverTree.split [tree068_467,tree068_603,tree068_76,tree068_34,tree068_25,tree068_27]
def tree068_605 : CoverTree := CoverTree.split [tree068_331,tree068_580,tree068_591,tree068_601,tree068_602,tree068_604]
def tree068_606 : CoverTree := CoverTree.reject 191
def tree068_607 : CoverTree := CoverTree.reject 168
def tree068_608 : CoverTree := CoverTree.reject 137
def tree068_609 : CoverTree := CoverTree.reject 271
def tree068_610 : CoverTree := CoverTree.reject 272
def tree068_611 : CoverTree := CoverTree.split [tree068_64,tree068_607,tree068_608,tree068_609,tree068_610,tree068_289]
def tree068_612 : CoverTree := CoverTree.reject 469
def tree068_613 : CoverTree := CoverTree.reject 273
def tree068_614 : CoverTree := CoverTree.reject 376
def tree068_615 : CoverTree := CoverTree.split [tree068_31,tree068_612,tree068_613,tree068_614,tree068_289,tree068_289]
def tree068_616 : CoverTree := CoverTree.reject 426
def tree068_617 : CoverTree := CoverTree.reject 387
def tree068_618 : CoverTree := CoverTree.split [tree068_16,tree068_617,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_619 : CoverTree := CoverTree.split [tree068_398,tree068_616,tree068_618,tree068_19,tree068_289,tree068_289]
def tree068_620 : CoverTree := CoverTree.reject 274
def tree068_621 : CoverTree := CoverTree.split [tree068_405,tree068_620,tree068_408,tree068_19,tree068_289,tree068_289]
def tree068_622 : CoverTree := CoverTree.split [tree068_391,tree068_606,tree068_611,tree068_615,tree068_619,tree068_621]
def tree068_623 : CoverTree := CoverTree.reject 275
def tree068_624 : CoverTree := CoverTree.split [tree068_376,tree068_412,tree068_413,tree068_419,tree068_623,tree068_422]
def tree068_625 : CoverTree := CoverTree.reject 276
def tree068_626 : CoverTree := CoverTree.split [tree068_64,tree068_424,tree068_625,tree068_19,tree068_72,tree068_429]
def tree068_627 : CoverTree := CoverTree.reject 427
def tree068_628 : CoverTree := CoverTree.split [tree068_31,tree068_627,tree068_41,tree068_19,tree068_43,tree068_13]
def tree068_629 : CoverTree := CoverTree.reject 377
def tree068_630 : CoverTree := CoverTree.split [tree068_45,tree068_629,tree068_17,tree068_19,tree068_48,tree068_13]
def tree068_631 : CoverTree := CoverTree.split [tree068_411,tree068_624,tree068_626,tree068_628,tree068_630,tree068_54]
def tree068_632 : CoverTree := CoverTree.reject 428
def tree068_633 : CoverTree := CoverTree.reject 378
def tree068_634 : CoverTree := CoverTree.split [tree068_376,tree068_440,tree068_632,tree068_633,tree068_382,tree068_445]
def tree068_635 : CoverTree := CoverTree.reject 453
def tree068_636 : CoverTree := CoverTree.reject 176
def tree068_637 : CoverTree := CoverTree.split [tree068_16,tree068_636,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_638 : CoverTree := CoverTree.split [tree068_64,tree068_635,tree068_637,tree068_19,tree068_72,tree068_13]
def tree068_639 : CoverTree := CoverTree.reject 379
def tree068_640 : CoverTree := CoverTree.split [tree068_31,tree068_639,tree068_17,tree068_19,tree068_58,tree068_13]
def tree068_641 : CoverTree := CoverTree.split [tree068_439,tree068_634,tree068_638,tree068_640,tree068_62,tree068_27]
def tree068_642 : CoverTree := CoverTree.reject 303
def tree068_643 : CoverTree := CoverTree.split [tree068_370,tree068_371,tree068_372,tree068_642,tree068_13,tree068_13]
def tree068_644 : CoverTree := CoverTree.reject 94
def tree068_645 : CoverTree := CoverTree.split [tree068_366,tree068_367,tree068_368,tree068_369,tree068_643,tree068_644]
def tree068_646 : CoverTree := CoverTree.split [tree068_645,tree068_463,tree068_73,tree068_34,tree068_25,tree068_27]
def tree068_647 : CoverTree := CoverTree.split [tree068_390,tree068_622,tree068_631,tree068_641,tree068_646,tree068_476]
def tree068_648 : CoverTree := CoverTree.split [tree068_0,tree068_495,tree068_526,tree068_566,tree068_605,tree068_647]
def tree068_649 : CoverTree := CoverTree.reject 454
def tree068_650 : CoverTree := CoverTree.reject 429
def tree068_651 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_649,tree068_650,tree068_89,tree068_89]
def tree068_652 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_479,tree068_480,tree068_651]
def tree068_653 : CoverTree := CoverTree.reject 7
def tree068_654 : CoverTree := CoverTree.split [tree068_108,tree068_653,tree068_653,tree068_653,tree068_653,tree068_89]
def tree068_655 : CoverTree := CoverTree.reject 430
def tree068_656 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_655,tree068_89,tree068_89,tree068_89]
def tree068_657 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_479,tree068_654,tree068_656]
def tree068_658 : CoverTree := CoverTree.split [tree068_221,tree068_221,tree068_652,tree068_657,tree068_491,tree068_494]
def tree068_659 : CoverTree := CoverTree.reject 380
def tree068_660 : CoverTree := CoverTree.split [tree068_496,tree068_497,tree068_498,tree068_659,tree068_105,tree068_105]
def tree068_661 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_236,tree068_237,tree068_660]
def tree068_662 : CoverTree := CoverTree.split [tree068_108,tree068_503,tree068_504,tree068_505,tree068_105,tree068_105]
def tree068_663 : CoverTree := CoverTree.reject 381
def tree068_664 : CoverTree := CoverTree.split [tree068_241,tree068_242,tree068_663,tree068_105,tree068_246,tree068_105]
def tree068_665 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_95,tree068_662,tree068_664]
def tree068_666 : CoverTree := CoverTree.reject 177
def tree068_667 : CoverTree := CoverTree.reject 178
def tree068_668 : CoverTree := CoverTree.split [tree068_108,tree068_666,tree068_667,tree068_105,tree068_105,tree068_105]
def tree068_669 : CoverTree := CoverTree.split [tree068_101,tree068_105,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_670 : CoverTree := CoverTree.split [tree068_94,tree068_94,tree068_94,tree068_668,tree068_512,tree068_669]
def tree068_671 : CoverTree := CoverTree.reject 438
def tree068_672 : CoverTree := CoverTree.reject 187
def tree068_673 : CoverTree := CoverTree.reject 179
def tree068_674 : CoverTree := CoverTree.split [tree068_376,tree068_671,tree068_672,tree068_673,tree068_105,tree068_105]
def tree068_675 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_66,tree068_13,tree068_13,tree068_13]
def tree068_676 : CoverTree := CoverTree.split [tree068_64,tree068_675,tree068_105,tree068_105,tree068_105,tree068_105]
def tree068_677 : CoverTree := CoverTree.split [tree068_31,tree068_105,tree068_120,tree068_105,tree068_105,tree068_105]
def tree068_678 : CoverTree := CoverTree.split [tree068_267,tree068_674,tree068_676,tree068_677,tree068_123,tree068_112]
def tree068_679 : CoverTree := CoverTree.split [tree068_235,tree068_661,tree068_665,tree068_670,tree068_266,tree068_678]
def tree068_680 : CoverTree := CoverTree.reject 26
def tree068_681 : CoverTree := CoverTree.reject 277
def tree068_682 : CoverTree := CoverTree.reject 278
def tree068_683 : CoverTree := CoverTree.split [tree068_108,tree068_527,tree068_528,tree068_681,tree068_682,tree068_289]
def tree068_684 : CoverTree := CoverTree.reject 440
def tree068_685 : CoverTree := CoverTree.reject 441
def tree068_686 : CoverTree := CoverTree.split [tree068_16,tree068_684,tree068_685,tree068_13,tree068_13,tree068_13]
def tree068_687 : CoverTree := CoverTree.reject 442
def tree068_688 : CoverTree := CoverTree.split [tree068_18,tree068_687,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_689 : CoverTree := CoverTree.split [tree068_282,tree068_283,tree068_686,tree068_688,tree068_288,tree068_289]
def tree068_690 : CoverTree := CoverTree.split [tree068_680,tree068_680,tree068_279,tree068_280,tree068_683,tree068_689]
def tree068_691 : CoverTree := CoverTree.reject 188
def tree068_692 : CoverTree := CoverTree.reject 166
def tree068_693 : CoverTree := CoverTree.reject 167
def tree068_694 : CoverTree := CoverTree.reject 443
def tree068_695 : CoverTree := CoverTree.split [tree068_42,tree068_13,tree068_694,tree068_13,tree068_13,tree068_13]
def tree068_696 : CoverTree := CoverTree.split [tree068_108,tree068_691,tree068_692,tree068_693,tree068_695,tree068_13]
def tree068_697 : CoverTree := CoverTree.reject 279
def tree068_698 : CoverTree := CoverTree.split [tree068_108,tree068_293,tree068_697,tree068_539,tree068_48,tree068_298]
def tree068_699 : CoverTree := CoverTree.reject 382
def tree068_700 : CoverTree := CoverTree.reject 205
def tree068_701 : CoverTree := CoverTree.split [tree068_16,tree068_700,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_702 : CoverTree := CoverTree.split [tree068_132,tree068_699,tree068_701,tree068_303,tree068_13,tree068_13]
def tree068_703 : CoverTree := CoverTree.split [tree068_680,tree068_680,tree068_128,tree068_696,tree068_698,tree068_702]
def tree068_704 : CoverTree := CoverTree.split [tree068_680,tree068_680,tree068_552,tree068_555,tree068_558,tree068_27]
def tree068_705 : CoverTree := CoverTree.reject 146
def tree068_706 : CoverTree := CoverTree.reject 192
def tree068_707 : CoverTree := CoverTree.split [tree068_705,tree068_706,tree068_315,tree068_317,tree068_318,tree068_27]
def tree068_708 : CoverTree := CoverTree.split [tree068_278,tree068_690,tree068_703,tree068_704,tree068_707,tree068_565]
def tree068_709 : CoverTree := CoverTree.split [tree068_680,tree068_680,tree068_327,tree068_328,tree068_329,tree068_330]
def tree068_710 : CoverTree := CoverTree.reject 383
def tree068_711 : CoverTree := CoverTree.reject 280
def tree068_712 : CoverTree := CoverTree.split [tree068_31,tree068_567,tree068_568,tree068_710,tree068_711,tree068_289]
def tree068_713 : CoverTree := CoverTree.reject 281
def tree068_714 : CoverTree := CoverTree.split [tree068_398,tree068_572,tree068_573,tree068_713,tree068_289,tree068_289]
def tree068_715 : CoverTree := CoverTree.reject 282
def tree068_716 : CoverTree := CoverTree.reject 444
def tree068_717 : CoverTree := CoverTree.split [tree068_16,tree068_716,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_718 : CoverTree := CoverTree.split [tree068_335,tree068_715,tree068_717,tree068_339,tree068_289,tree068_289]
def tree068_719 : CoverTree := CoverTree.split [tree068_680,tree068_680,tree068_332,tree068_712,tree068_714,tree068_718]
def tree068_720 : CoverTree := CoverTree.reject 189
def tree068_721 : CoverTree := CoverTree.reject 87
def tree068_722 : CoverTree := CoverTree.reject 283
def tree068_723 : CoverTree := CoverTree.reject 445
def tree068_724 : CoverTree := CoverTree.reject 446
def tree068_725 : CoverTree := CoverTree.split [tree068_71,tree068_723,tree068_724,tree068_13,tree068_13,tree068_13]
def tree068_726 : CoverTree := CoverTree.split [tree068_64,tree068_720,tree068_721,tree068_722,tree068_725,tree068_429]
def tree068_727 : CoverTree := CoverTree.reject 284
def tree068_728 : CoverTree := CoverTree.split [tree068_31,tree068_343,tree068_727,tree068_584,tree068_43,tree068_13]
def tree068_729 : CoverTree := CoverTree.split [tree068_45,tree068_348,tree068_17,tree068_19,tree068_48,tree068_13]
def tree068_730 : CoverTree := CoverTree.split [tree068_680,tree068_680,tree068_726,tree068_728,tree068_729,tree068_590]
def tree068_731 : CoverTree := CoverTree.reject 384
def tree068_732 : CoverTree := CoverTree.split [tree068_64,tree068_592,tree068_731,tree068_595,tree068_72,tree068_13]
def tree068_733 : CoverTree := CoverTree.split [tree068_680,tree068_680,tree068_732,tree068_599,tree068_600,tree068_27]
def tree068_734 : CoverTree := CoverTree.reject 90
def tree068_735 : CoverTree := CoverTree.reject 8
def tree068_736 : CoverTree := CoverTree.split [tree068_735,tree068_735,tree068_735,tree068_462,tree068_382,tree068_13]
def tree068_737 : CoverTree := CoverTree.split [tree068_734,tree068_736,tree068_73,tree068_34,tree068_25,tree068_27]
def tree068_738 : CoverTree := CoverTree.split [tree068_709,tree068_719,tree068_730,tree068_733,tree068_737,tree068_604]
def tree068_739 : CoverTree := CoverTree.reject 433
def tree068_740 : CoverTree := CoverTree.reject 122
def tree068_741 : CoverTree := CoverTree.reject 83
def tree068_742 : CoverTree := CoverTree.reject 84
def tree068_743 : CoverTree := CoverTree.split [tree068_376,tree068_739,tree068_740,tree068_741,tree068_742,tree068_289]
def tree068_744 : CoverTree := CoverTree.reject 285
def tree068_745 : CoverTree := CoverTree.reject 434
def tree068_746 : CoverTree := CoverTree.split [tree068_286,tree068_745,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_747 : CoverTree := CoverTree.split [tree068_64,tree068_607,tree068_608,tree068_744,tree068_746,tree068_289]
def tree068_748 : CoverTree := CoverTree.reject 297
def tree068_749 : CoverTree := CoverTree.reject 298
def tree068_750 : CoverTree := CoverTree.reject 299
def tree068_751 : CoverTree := CoverTree.split [tree068_22,tree068_32,tree068_748,tree068_749,tree068_750,tree068_13]
def tree068_752 : CoverTree := CoverTree.reject 435
def tree068_753 : CoverTree := CoverTree.reject 447
def tree068_754 : CoverTree := CoverTree.split [tree068_16,tree068_752,tree068_753,tree068_13,tree068_13,tree068_13]
def tree068_755 : CoverTree := CoverTree.reject 182
def tree068_756 : CoverTree := CoverTree.split [tree068_18,tree068_755,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_757 : CoverTree := CoverTree.split [tree068_31,tree068_751,tree068_754,tree068_756,tree068_289,tree068_289]
def tree068_758 : CoverTree := CoverTree.reject 431
def tree068_759 : CoverTree := CoverTree.split [tree068_398,tree068_758,tree068_618,tree068_19,tree068_289,tree068_289]
def tree068_760 : CoverTree := CoverTree.reject 448
def tree068_761 : CoverTree := CoverTree.reject 449
def tree068_762 : CoverTree := CoverTree.split [tree068_22,tree068_760,tree068_761,tree068_13,tree068_13,tree068_13]
def tree068_763 : CoverTree := CoverTree.split [tree068_405,tree068_762,tree068_408,tree068_19,tree068_289,tree068_289]
def tree068_764 : CoverTree := CoverTree.split [tree068_391,tree068_743,tree068_747,tree068_757,tree068_759,tree068_763]
def tree068_765 : CoverTree := CoverTree.reject 436
def tree068_766 : CoverTree := CoverTree.split [tree068_381,tree068_765,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_767 : CoverTree := CoverTree.split [tree068_376,tree068_412,tree068_413,tree068_419,tree068_766,tree068_422]
def tree068_768 : CoverTree := CoverTree.reject 437
def tree068_769 : CoverTree := CoverTree.split [tree068_16,tree068_768,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_770 : CoverTree := CoverTree.split [tree068_64,tree068_424,tree068_769,tree068_19,tree068_72,tree068_429]
def tree068_771 : CoverTree := CoverTree.split [tree068_45,tree068_24,tree068_17,tree068_19,tree068_48,tree068_13]
def tree068_772 : CoverTree := CoverTree.split [tree068_411,tree068_767,tree068_770,tree068_44,tree068_771,tree068_54]
def tree068_773 : CoverTree := CoverTree.reject 432
def tree068_774 : CoverTree := CoverTree.reject 197
def tree068_775 : CoverTree := CoverTree.split [tree068_18,tree068_774,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_776 : CoverTree := CoverTree.split [tree068_376,tree068_440,tree068_773,tree068_775,tree068_382,tree068_445]
def tree068_777 : CoverTree := CoverTree.reject 199
def tree068_778 : CoverTree := CoverTree.split [tree068_22,tree068_65,tree068_66,tree068_13,tree068_777,tree068_13]
def tree068_779 : CoverTree := CoverTree.split [tree068_64,tree068_778,tree068_637,tree068_19,tree068_72,tree068_13]
def tree068_780 : CoverTree := CoverTree.split [tree068_439,tree068_776,tree068_779,tree068_59,tree068_62,tree068_27]
def tree068_781 : CoverTree := CoverTree.split [tree068_390,tree068_764,tree068_772,tree068_780,tree068_646,tree068_476]
def tree068_782 : CoverTree := CoverTree.split [tree068_0,tree068_658,tree068_679,tree068_708,tree068_738,tree068_781]
def tree068_783 : CoverTree := CoverTree.reject 385
def tree068_784 : CoverTree := CoverTree.reject 394
def tree068_785 : CoverTree := CoverTree.split [tree068_87,tree068_87,tree068_88,tree068_784,tree068_13,tree068_13]
def tree068_786 : CoverTree := CoverTree.split [tree068_85,tree068_85,tree068_785,tree068_89,tree068_89,tree068_89]
def tree068_787 : CoverTree := CoverTree.split [tree068_83,tree068_83,tree068_83,tree068_783,tree068_480,tree068_786]
def tree068_788 : CoverTree := CoverTree.reject 386
def tree068_789 : CoverTree := CoverTree.split [tree068_83,tree068_83,tree068_83,tree068_788,tree068_654,tree068_91]
def tree068_790 : CoverTree := CoverTree.reject 390
def tree068_791 : CoverTree := CoverTree.split [tree068_108,tree068_85,tree068_489,tree068_489,tree068_790,tree068_89]
def tree068_792 : CoverTree := CoverTree.split [tree068_83,tree068_83,tree068_83,tree068_791,tree068_490,tree068_91]
def tree068_793 : CoverTree := CoverTree.split [tree068_221,tree068_221,tree068_787,tree068_789,tree068_792,tree068_494]
def tree068_794 : CoverTree := CoverTree.reject 289
def tree068_795 : CoverTree := CoverTree.reject 290
def tree068_796 : CoverTree := CoverTree.split [tree068_496,tree068_497,tree068_498,tree068_105,tree068_105,tree068_105]
def tree068_797 : CoverTree := CoverTree.split [tree068_391,tree068_794,tree068_795,tree068_236,tree068_237,tree068_796]
def tree068_798 : CoverTree := CoverTree.reject 291
def tree068_799 : CoverTree := CoverTree.reject 292
def tree068_800 : CoverTree := CoverTree.split [tree068_241,tree068_242,tree068_105,tree068_105,tree068_246,tree068_105]
def tree068_801 : CoverTree := CoverTree.split [tree068_411,tree068_798,tree068_799,tree068_95,tree068_662,tree068_800]
def tree068_802 : CoverTree := CoverTree.reject 293
def tree068_803 : CoverTree := CoverTree.reject 294
def tree068_804 : CoverTree := CoverTree.split [tree068_439,tree068_802,tree068_803,tree068_668,tree068_512,tree068_669]
def tree068_805 : CoverTree := CoverTree.reject 295
def tree068_806 : CoverTree := CoverTree.reject 296
def tree068_807 : CoverTree := CoverTree.reject 57
def tree068_808 : CoverTree := CoverTree.split [tree068_108,tree068_807,tree068_807,tree068_807,tree068_807,tree068_105]
def tree068_809 : CoverTree := CoverTree.split [tree068_805,tree068_806,tree068_808,tree068_265,tree068_110,tree068_112]
def tree068_810 : CoverTree := CoverTree.split [tree068_235,tree068_797,tree068_801,tree068_804,tree068_809,tree068_678]
def tree068_811 : CoverTree := CoverTree.reject 195
def tree068_812 : CoverTree := CoverTree.reject 456
def tree068_813 : CoverTree := CoverTree.reject 457
def tree068_814 : CoverTree := CoverTree.split [tree068_18,tree068_812,tree068_813,tree068_13,tree068_13,tree068_13]
def tree068_815 : CoverTree := CoverTree.split [tree068_108,tree068_527,tree068_528,tree068_814,tree068_289,tree068_289]
def tree068_816 : CoverTree := CoverTree.split [tree068_391,tree068_811,tree068_279,tree068_280,tree068_815,tree068_689]
def tree068_817 : CoverTree := CoverTree.reject 183
def tree068_818 : CoverTree := CoverTree.reject 458
def tree068_819 : CoverTree := CoverTree.split [tree068_16,tree068_818,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_820 : CoverTree := CoverTree.split [tree068_108,tree068_293,tree068_819,tree068_539,tree068_48,tree068_298]
def tree068_821 : CoverTree := CoverTree.reject 204
def tree068_822 : CoverTree := CoverTree.split [tree068_22,tree068_821,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_823 : CoverTree := CoverTree.split [tree068_132,tree068_822,tree068_701,tree068_303,tree068_13,tree068_13]
def tree068_824 : CoverTree := CoverTree.split [tree068_411,tree068_817,tree068_128,tree068_696,tree068_820,tree068_823]
def tree068_825 : CoverTree := CoverTree.reject 184
def tree068_826 : CoverTree := CoverTree.split [tree068_439,tree068_825,tree068_552,tree068_555,tree068_558,tree068_27]
def tree068_827 : CoverTree := CoverTree.reject 33
def tree068_828 : CoverTree := CoverTree.split [tree068_108,tree068_735,tree068_735,tree068_827,tree068_827,tree068_13]
def tree068_829 : CoverTree := CoverTree.split [tree068_705,tree068_828,tree068_315,tree068_317,tree068_318,tree068_27]
def tree068_830 : CoverTree := CoverTree.split [tree068_278,tree068_816,tree068_824,tree068_826,tree068_829,tree068_565]
def tree068_831 : CoverTree := CoverTree.split [tree068_386,tree068_387,tree068_327,tree068_328,tree068_329,tree068_330]
def tree068_832 : CoverTree := CoverTree.reject 196
def tree068_833 : CoverTree := CoverTree.reject 459
def tree068_834 : CoverTree := CoverTree.split [tree068_18,tree068_755,tree068_13,tree068_833,tree068_13,tree068_13]
def tree068_835 : CoverTree := CoverTree.split [tree068_31,tree068_567,tree068_568,tree068_834,tree068_289,tree068_289]
def tree068_836 : CoverTree := CoverTree.split [tree068_398,tree068_572,tree068_573,tree068_19,tree068_289,tree068_289]
def tree068_837 : CoverTree := CoverTree.reject 460
def tree068_838 : CoverTree := CoverTree.split [tree068_22,tree068_837,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_839 : CoverTree := CoverTree.split [tree068_335,tree068_838,tree068_717,tree068_339,tree068_289,tree068_289]
def tree068_840 : CoverTree := CoverTree.split [tree068_391,tree068_832,tree068_332,tree068_835,tree068_836,tree068_839]
def tree068_841 : CoverTree := CoverTree.reject 124
def tree068_842 : CoverTree := CoverTree.split [tree068_64,tree068_720,tree068_721,tree068_19,tree068_725,tree068_429]
def tree068_843 : CoverTree := CoverTree.reject 461
def tree068_844 : CoverTree := CoverTree.split [tree068_16,tree068_843,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_845 : CoverTree := CoverTree.split [tree068_31,tree068_343,tree068_844,tree068_584,tree068_43,tree068_13]
def tree068_846 : CoverTree := CoverTree.split [tree068_411,tree068_841,tree068_842,tree068_845,tree068_729,tree068_590]
def tree068_847 : CoverTree := CoverTree.reject 310
def tree068_848 : CoverTree := CoverTree.reject 462
def tree068_849 : CoverTree := CoverTree.reject 463
def tree068_850 : CoverTree := CoverTree.reject 464
def tree068_851 : CoverTree := CoverTree.split [tree068_381,tree068_848,tree068_849,tree068_850,tree068_13,tree068_13]
def tree068_852 : CoverTree := CoverTree.split [tree068_735,tree068_735,tree068_735,tree068_847,tree068_851,tree068_445]
def tree068_853 : CoverTree := CoverTree.split [tree068_64,tree068_592,tree068_637,tree068_595,tree068_72,tree068_13]
def tree068_854 : CoverTree := CoverTree.split [tree068_439,tree068_852,tree068_853,tree068_599,tree068_600,tree068_27]
def tree068_855 : CoverTree := CoverTree.split [tree068_831,tree068_840,tree068_846,tree068_854,tree068_737,tree068_604]
def tree068_856 : CoverTree := CoverTree.reject 455
def tree068_857 : CoverTree := CoverTree.split [tree068_18,tree068_856,tree068_13,tree068_13,tree068_13,tree068_13]
def tree068_858 : CoverTree := CoverTree.split [tree068_64,tree068_607,tree068_608,tree068_857,tree068_746,tree068_289]
def tree068_859 : CoverTree := CoverTree.reject 300
def tree068_860 : CoverTree := CoverTree.split [tree068_22,tree068_23,tree068_859,tree068_13,tree068_13,tree068_13]
def tree068_861 : CoverTree := CoverTree.split [tree068_398,tree068_860,tree068_618,tree068_19,tree068_289,tree068_289]
def tree068_862 : CoverTree := CoverTree.split [tree068_391,tree068_743,tree068_858,tree068_757,tree068_861,tree068_763]
def tree068_863 : CoverTree := CoverTree.reject 302
def tree068_864 : CoverTree := CoverTree.split [tree068_16,tree068_456,tree068_863,tree068_13,tree068_13,tree068_13]
def tree068_865 : CoverTree := CoverTree.split [tree068_376,tree068_440,tree068_864,tree068_775,tree068_382,tree068_445]
def tree068_866 : CoverTree := CoverTree.split [tree068_439,tree068_865,tree068_779,tree068_59,tree068_62,tree068_27]
def tree068_867 : CoverTree := CoverTree.split [tree068_390,tree068_862,tree068_772,tree068_866,tree068_646,tree068_476]
def tree068_868 : CoverTree := CoverTree.split [tree068_0,tree068_793,tree068_810,tree068_830,tree068_855,tree068_867]
def tree068_869 : CoverTree := CoverTree.split [tree068_79,tree068_220,tree068_478,tree068_648,tree068_782,tree068_868]
def tree068 : CoverTree := tree068_869

end Snake9.Shared89
