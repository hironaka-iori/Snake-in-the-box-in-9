import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes053 : List Box := [
[(1,6),(1,5),(1,3),(1,5),(1,3),(1,6)],
[(1,6),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)],
[(1,3),(1,6),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,2),(1,4),(1,5),(1,5)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,2)],
[(1,6),(1,6),(1,6),(1,6),(1,2),(1,2)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,5),(1,5),(1,4),(1,2),(1,6)],
[(1,6),(2,2),(1,6),(1,6),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,5),(1,2),(1,5),(1,4),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,1)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(3,3),(1,6),(1,6),(2,2),(1,6)],
[(1,6),(1,6),(1,2),(1,5),(1,5),(1,4)],
[(1,6),(1,6),(1,3),(1,5),(1,3),(1,5)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,2),(1,5)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,6),(1,6),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(6,6),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(1,6)],
[(1,6),(1,6),(1,1),(6,6),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(1,6)],
[(1,6),(3,3),(1,6),(1,6),(1,1),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,3),(1,2)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,2),(1,3),(1,5),(1,4),(1,6)],
[(1,1),(5,5),(2,2),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(3,3)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(4,4)],
[(1,6),(1,6),(4,4),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(4,4),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(4,4),(5,5),(4,4),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(1,1)],
[(1,6),(3,3),(3,3),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(3,3),(5,5),(3,3),(3,3),(1,6)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(4,4),(5,5),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(5,5),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(5,5),(1,1)],
[(1,6),(6,6),(1,1),(5,5),(6,6),(1,6)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(3,3)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(4,4)],
[(1,6),(1,6),(6,6),(3,3),(3,3),(2,2)],
[(2,2),(3,3),(5,5),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,1),(5,5),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(2,2)],
[(2,2),(3,3),(3,3),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(4,4),(3,3)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(1,1),(5,5),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(4,4)],
[(2,2),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(3,3),(2,2),(5,5),(5,5),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(4,4),(3,3),(2,2)],
[(1,6),(2,2),(4,4),(3,3),(5,5),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(4,4),(1,6)],
[(1,6),(2,2),(5,5),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(5,5),(3,3),(5,5),(1,6)],
[(2,2),(2,2),(6,6),(3,3),(1,6),(1,6)],
[(2,2),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(2,2),(5,5),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,4),(1,5),(1,5),(1,2),(1,6)],
[(1,1),(6,6),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(3,3),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(5,5),(3,3),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(5,5),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,3),(1,2),(1,5),(1,5),(1,6)],
[(1,6),(1,6),(1,5),(1,5),(1,2),(1,3)],
[(1,1),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,6),(4,4),(6,6),(1,1),(1,6)],
[(1,6),(1,6),(5,5),(5,5),(1,1),(1,6)],
[(2,2),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(3,3),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(1,1),(5,5),(6,6),(2,2),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(3,3),(6,6),(1,6)],
[(1,6),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(2,2),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(6,6),(2,2),(1,6),(1,6)],
[(2,2),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(1,1),(6,6),(2,2),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(3,3)],
[(2,2),(4,4),(2,2),(6,6),(1,6),(1,6)],
[(3,3),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(4,4),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(5,5),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,6),(5,5),(3,3),(2,2),(1,6)],
[(1,1),(5,5),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(3,3)],
[(1,6),(2,2),(3,3),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(4,4),(1,6)],
[(2,2),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(2,2),(5,5),(5,5),(2,2),(1,6),(1,6)],
[(3,3),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(1,1),(6,6),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(6,6),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(4,4),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(4,4),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(5,5),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(5,5),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(1,1),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(5,5),(1,1),(1,6)],
[(1,1),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(6,6),(5,5),(1,1),(6,6)],
[(1,6),(2,2),(3,3),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(4,4),(2,2),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(2,2),(5,5),(2,2),(5,5),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(2,2),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(2,2),(6,6),(4,4),(2,2),(1,6),(1,6)],
[(3,3),(2,2),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(5,5),(2,2),(4,4),(3,3),(1,6),(1,6)],
[(5,5),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(5,5),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(3,3),(1,6)],
[(1,1),(6,6),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(5,5)],
[(1,6),(4,4),(2,2),(4,4),(5,5),(1,6)],
[(2,2),(5,5),(2,2),(4,4),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(4,4),(1,6),(1,6)],
[(4,4),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(5,5),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(6,6),(4,4),(2,2)],
[(1,6),(4,4),(3,3),(2,2),(6,6),(4,4)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(4,4),(3,3),(6,6),(4,4),(2,2)],
[(2,2),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(4,4),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(5,5),(1,6)],
[(2,2),(4,4),(6,6),(4,4),(3,3),(1,6)],
[(2,2),(5,5),(3,3),(6,6),(3,3),(1,6)],
[(2,2),(5,5),(3,3),(6,6),(4,4),(1,6)],
[(2,2),(6,6),(3,3),(6,6),(3,3),(1,6)],
[(2,2),(6,6),(3,3),(6,6),(4,4),(1,6)],
[(3,3),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(3,3),(2,2),(6,6),(3,3),(4,4),(1,6)],
[(3,3),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(3,3),(3,3),(3,3),(6,6),(4,4),(1,6)],
[(3,3),(3,3),(3,3),(6,6),(5,5),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(3,3),(3,3),(5,5),(4,4),(4,4),(1,6)],
[(3,3),(3,3),(5,5),(5,5),(3,3),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(3,3),(3,3),(6,6),(4,4),(3,3),(1,6)],
[(3,3),(5,5),(3,3),(6,6),(3,3),(1,6)],
[(3,3),(5,5),(3,3),(6,6),(4,4),(1,6)],
[(4,4),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(4,4),(2,2),(3,3),(6,6),(5,5),(1,6)],
[(4,4),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(4,4),(2,2),(5,5),(4,4),(4,4),(1,6)],
[(4,4),(2,2),(6,6),(3,3),(4,4),(1,6)],
[(4,4),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(3,3),(3,3),(6,6),(4,4),(1,6)],
[(4,4),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(4,4),(3,3),(5,5),(4,4),(4,4),(1,6)],
[(4,4),(3,3),(6,6),(4,4),(3,3),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(5,5),(2,2),(5,5),(4,4),(4,4),(1,6)],
[(5,5),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(1,1),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(2,2),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(3,3),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(4,4),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(4,4),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(4,4),(5,5),(1,1),(5,5),(1,6),(1,6)],
[(4,4),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(5,5),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(5,5),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(5,5),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(5,5),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(5,5),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(5,5),(5,5),(1,1),(5,5),(1,6),(1,6)],
[(5,5),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(3,3),(6,6),(6,6),(2,2)],
[(1,6),(4,4),(6,6),(2,2),(3,3),(4,4)],
[(2,2),(3,3),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(2,2),(4,4),(5,5),(4,4),(3,3),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(5,5),(5,5),(4,4),(3,3),(1,6)],
[(2,2),(5,5),(6,6),(3,3),(3,3),(1,6)],
[(2,2),(6,6),(5,5),(3,3),(4,4),(1,6)],
[(2,2),(6,6),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(3,3),(2,2),(6,6),(5,5),(1,6)],
[(3,3),(3,3),(4,4),(6,6),(4,4),(1,6)],
[(3,3),(3,3),(6,6),(3,3),(3,3),(1,6)],
[(3,3),(4,4),(2,2),(6,6),(5,5),(1,6)],
[(3,3),(4,4),(3,3),(5,5),(4,4),(1,6)],
[(3,3),(4,4),(3,3),(5,5),(5,5),(1,6)],
[(3,3),(4,4),(3,3),(6,6),(4,4),(1,6)],
[(3,3),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(3,3),(4,4),(5,5),(4,4),(3,3),(1,6)],
[(3,3),(5,5),(6,6),(3,3),(3,3),(1,6)],
[(4,4),(3,3),(2,2),(6,6),(5,5),(1,6)],
[(4,4),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(4,4),(3,3),(5,5),(3,3),(4,4),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(5,5),(1,6)],
[(4,4),(4,4),(4,4),(5,5),(3,3),(1,6)],
[(4,4),(4,4),(5,5),(4,4),(3,3),(1,6)],
[(5,5),(3,3),(2,2),(6,6),(5,5),(1,6)],
[(5,5),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(2,2),(1,6)],
[(1,6),(1,6),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(2,2),(1,6)],
[(1,1),(6,6),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(4,4),(2,2),(4,4)],
[(1,6),(2,2),(4,4),(4,4),(4,4),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)],
[(1,6),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(2,2),(6,6),(3,3),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(4,4),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(5,5),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(6,6),(6,6),(2,2)],
[(2,2),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(2,2),(5,5),(2,2),(6,6),(4,4),(1,6)],
[(2,2),(5,5),(6,6),(2,2),(3,3),(1,6)],
[(2,2),(5,5),(6,6),(2,2),(4,4),(1,6)],
[(2,2),(6,6),(3,3),(4,4),(4,4),(1,6)],
[(2,2),(6,6),(5,5),(3,3),(3,3),(1,6)],
[(2,2),(6,6),(6,6),(2,2),(3,3),(1,6)],
[(3,3),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(3,3),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(3,3),(5,5),(2,2),(6,6),(4,4),(1,6)],
[(3,3),(5,5),(3,3),(4,4),(4,4),(1,6)],
[(3,3),(5,5),(5,5),(2,2),(4,4),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(4,4),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(4,4),(5,5),(2,2),(4,4),(1,6)],
[(5,5),(4,4),(5,5),(2,2),(4,4),(1,6)],
[(2,2),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(5,5),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(6,6),(4,4),(2,2)],
[(1,6),(2,2),(4,4),(6,6),(4,4),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(4,4),(2,2)],
[(3,3),(4,4),(6,6),(2,2),(3,3),(1,6)],
[(3,3),(5,5),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(6,6),(3,3)],
[(1,6),(2,2),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(4,4)],
[(4,4),(5,5),(2,2),(4,4),(5,5),(1,6)],
[(4,4),(5,5),(6,6),(2,2),(2,2),(1,6)],
[(2,2),(5,5),(2,2),(6,6),(5,5),(3,3)],
[(3,3),(5,5),(2,2),(6,6),(5,5),(3,3)]
]

def root053 : Nat := 3444

def tree053_0 : CoverTree := CoverTree.reject 1
def tree053_1 : CoverTree := CoverTree.reject 17
def tree053_2 : CoverTree := CoverTree.reject 14
def tree053_3 : CoverTree := CoverTree.reject 9
def tree053_4 : CoverTree := CoverTree.reject 135
def tree053_5 : CoverTree := CoverTree.reject 59
def tree053_6 : CoverTree := CoverTree.reject 35
def tree053_7 : CoverTree := CoverTree.reject 19
def tree053_8 : CoverTree := CoverTree.reject 193
def tree053_9 : CoverTree := CoverTree.reject 143
def tree053_10 : CoverTree := CoverTree.reject 109
def tree053_11 : CoverTree := CoverTree.reject 98
def tree053_12 : CoverTree := CoverTree.reject 3
def tree053_13 : CoverTree := CoverTree.reject 16
def tree053_14 : CoverTree := CoverTree.accept
def tree053_15 : CoverTree := CoverTree.split [tree053_13,tree053_14,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_16 : CoverTree := CoverTree.reject 12
def tree053_17 : CoverTree := CoverTree.split [tree053_16,tree053_14,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_18 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_19 : CoverTree := CoverTree.split [tree053_7,tree053_8,tree053_9,tree053_10,tree053_11,tree053_18]
def tree053_20 : CoverTree := CoverTree.reject 30
def tree053_21 : CoverTree := CoverTree.reject 31
def tree053_22 : CoverTree := CoverTree.reject 47
def tree053_23 : CoverTree := CoverTree.reject 48
def tree053_24 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_20,tree053_21,tree053_22,tree053_23]
def tree053_25 : CoverTree := CoverTree.reject 164
def tree053_26 : CoverTree := CoverTree.reject 99
def tree053_27 : CoverTree := CoverTree.reject 93
def tree053_28 : CoverTree := CoverTree.split [tree053_24,tree053_25,tree053_26,tree053_27,tree053_18,tree053_18]
def tree053_29 : CoverTree := CoverTree.reject 50
def tree053_30 : CoverTree := CoverTree.reject 51
def tree053_31 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_20,tree053_21,tree053_29,tree053_30]
def tree053_32 : CoverTree := CoverTree.reject 144
def tree053_33 : CoverTree := CoverTree.reject 88
def tree053_34 : CoverTree := CoverTree.split [tree053_13,tree053_33,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_35 : CoverTree := CoverTree.reject 44
def tree053_36 : CoverTree := CoverTree.split [tree053_35,tree053_14,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_37 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_34,tree053_17,tree053_36,tree053_14]
def tree053_38 : CoverTree := CoverTree.split [tree053_31,tree053_32,tree053_37,tree053_18,tree053_18,tree053_18]
def tree053_39 : CoverTree := CoverTree.split [tree053_4,tree053_5,tree053_6,tree053_19,tree053_28,tree053_38]
def tree053_40 : CoverTree := CoverTree.reject 173
def tree053_41 : CoverTree := CoverTree.reject 15
def tree053_42 : CoverTree := CoverTree.reject 272
def tree053_43 : CoverTree := CoverTree.reject 223
def tree053_44 : CoverTree := CoverTree.reject 174
def tree053_45 : CoverTree := CoverTree.reject 154
def tree053_46 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_42,tree053_43,tree053_44,tree053_45]
def tree053_47 : CoverTree := CoverTree.reject 22
def tree053_48 : CoverTree := CoverTree.reject 331
def tree053_49 : CoverTree := CoverTree.reject 188
def tree053_50 : CoverTree := CoverTree.reject 122
def tree053_51 : CoverTree := CoverTree.reject 34
def tree053_52 : CoverTree := CoverTree.split [tree053_13,tree053_51,tree053_51,tree053_51,tree053_51,tree053_14]
def tree053_53 : CoverTree := CoverTree.reject 94
def tree053_54 : CoverTree := CoverTree.split [tree053_16,tree053_53,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_55 : CoverTree := CoverTree.reject 23
def tree053_56 : CoverTree := CoverTree.reject 83
def tree053_57 : CoverTree := CoverTree.split [tree053_55,tree053_56,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_58 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_52,tree053_54,tree053_57,tree053_14]
def tree053_59 : CoverTree := CoverTree.reject 84
def tree053_60 : CoverTree := CoverTree.split [tree053_59,tree053_14,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_61 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_15,tree053_17,tree053_60,tree053_14]
def tree053_62 : CoverTree := CoverTree.split [tree053_47,tree053_48,tree053_49,tree053_50,tree053_58,tree053_61]
def tree053_63 : CoverTree := CoverTree.reject 194
def tree053_64 : CoverTree := CoverTree.reject 145
def tree053_65 : CoverTree := CoverTree.reject 56
def tree053_66 : CoverTree := CoverTree.reject 86
def tree053_67 : CoverTree := CoverTree.reject 87
def tree053_68 : CoverTree := CoverTree.split [tree053_13,tree053_65,tree053_66,tree053_67,tree053_14,tree053_14]
def tree053_69 : CoverTree := CoverTree.reject 65
def tree053_70 : CoverTree := CoverTree.reject 66
def tree053_71 : CoverTree := CoverTree.split [tree053_16,tree053_69,tree053_70,tree053_14,tree053_14,tree053_14]
def tree053_72 : CoverTree := CoverTree.split [tree053_55,tree053_14,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_73 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_68,tree053_71,tree053_72,tree053_14]
def tree053_74 : CoverTree := CoverTree.split [tree053_13,tree053_65,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_75 : CoverTree := CoverTree.reject 67
def tree053_76 : CoverTree := CoverTree.split [tree053_16,tree053_75,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_77 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_74,tree053_76,tree053_72,tree053_14]
def tree053_78 : CoverTree := CoverTree.split [tree053_7,tree053_63,tree053_64,tree053_73,tree053_77,tree053_18]
def tree053_79 : CoverTree := CoverTree.reject 49
def tree053_80 : CoverTree := CoverTree.reject 2
def tree053_81 : CoverTree := CoverTree.split [tree053_80,tree053_80,tree053_80,tree053_14,tree053_14,tree053_14]
def tree053_82 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_79,tree053_81,tree053_81,tree053_81]
def tree053_83 : CoverTree := CoverTree.reject 155
def tree053_84 : CoverTree := CoverTree.reject 156
def tree053_85 : CoverTree := CoverTree.split [tree053_13,tree053_83,tree053_84,tree053_14,tree053_14,tree053_14]
def tree053_86 : CoverTree := CoverTree.reject 68
def tree053_87 : CoverTree := CoverTree.split [tree053_16,tree053_86,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_88 : CoverTree := CoverTree.reject 69
def tree053_89 : CoverTree := CoverTree.split [tree053_35,tree053_88,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_90 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_85,tree053_87,tree053_89,tree053_14]
def tree053_91 : CoverTree := CoverTree.reject 110
def tree053_92 : CoverTree := CoverTree.split [tree053_13,tree053_91,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_93 : CoverTree := CoverTree.reject 70
def tree053_94 : CoverTree := CoverTree.split [tree053_93,tree053_14,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_95 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_92,tree053_17,tree053_94,tree053_14]
def tree053_96 : CoverTree := CoverTree.split [tree053_24,tree053_82,tree053_90,tree053_95,tree053_18,tree053_18]
def tree053_97 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_81,tree053_81,tree053_81,tree053_81]
def tree053_98 : CoverTree := CoverTree.split [tree053_31,tree053_97,tree053_37,tree053_18,tree053_18,tree053_18]
def tree053_99 : CoverTree := CoverTree.split [tree053_40,tree053_46,tree053_62,tree053_78,tree053_96,tree053_98]
def tree053_100 : CoverTree := CoverTree.split [tree053_0,tree053_1,tree053_2,tree053_3,tree053_39,tree053_99]
def tree053_101 : CoverTree := CoverTree.reject 13
def tree053_102 : CoverTree := CoverTree.reject 41
def tree053_103 : CoverTree := CoverTree.reject 40
def tree053_104 : CoverTree := CoverTree.reject 37
def tree053_105 : CoverTree := CoverTree.reject 5
def tree053_106 : CoverTree := CoverTree.reject 115
def tree053_107 : CoverTree := CoverTree.reject 106
def tree053_108 : CoverTree := CoverTree.reject 11
def tree053_109 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_108,tree053_17,tree053_14,tree053_14]
def tree053_110 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_106,tree053_107,tree053_109,tree053_109]
def tree053_111 : CoverTree := CoverTree.split [tree053_101,tree053_101,tree053_102,tree053_103,tree053_104,tree053_110]
def tree053_112 : CoverTree := CoverTree.reject 24
def tree053_113 : CoverTree := CoverTree.reject 60
def tree053_114 : CoverTree := CoverTree.reject 274
def tree053_115 : CoverTree := CoverTree.reject 177
def tree053_116 : CoverTree := CoverTree.reject 123
def tree053_117 : CoverTree := CoverTree.reject 95
def tree053_118 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_114,tree053_115,tree053_116,tree053_117]
def tree053_119 : CoverTree := CoverTree.reject 148
def tree053_120 : CoverTree := CoverTree.reject 116
def tree053_121 : CoverTree := CoverTree.reject 103
def tree053_122 : CoverTree := CoverTree.reject 235
def tree053_123 : CoverTree := CoverTree.reject 300
def tree053_124 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_122,tree053_123,tree053_14,tree053_14]
def tree053_125 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_119,tree053_120,tree053_121,tree053_124]
def tree053_126 : CoverTree := CoverTree.reject 124
def tree053_127 : CoverTree := CoverTree.reject 117
def tree053_128 : CoverTree := CoverTree.reject 89
def tree053_129 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_126,tree053_127,tree053_128,tree053_18]
def tree053_130 : CoverTree := CoverTree.reject 301
def tree053_131 : CoverTree := CoverTree.reject 236
def tree053_132 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_130,tree053_131,tree053_36,tree053_14]
def tree053_133 : CoverTree := CoverTree.reject 237
def tree053_134 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_133,tree053_17,tree053_14,tree053_14]
def tree053_135 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_132,tree053_134,tree053_18,tree053_18]
def tree053_136 : CoverTree := CoverTree.split [tree053_112,tree053_113,tree053_118,tree053_125,tree053_129,tree053_135]
def tree053_137 : CoverTree := CoverTree.reject 25
def tree053_138 : CoverTree := CoverTree.reject 275
def tree053_139 : CoverTree := CoverTree.reject 276
def tree053_140 : CoverTree := CoverTree.reject 198
def tree053_141 : CoverTree := CoverTree.reject 157
def tree053_142 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_138,tree053_139,tree053_140,tree053_141]
def tree053_143 : CoverTree := CoverTree.reject 358
def tree053_144 : CoverTree := CoverTree.reject 199
def tree053_145 : CoverTree := CoverTree.reject 178
def tree053_146 : CoverTree := CoverTree.reject 125
def tree053_147 : CoverTree := CoverTree.reject 342
def tree053_148 : CoverTree := CoverTree.reject 234
def tree053_149 : CoverTree := CoverTree.split [tree053_16,tree053_148,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_150 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_147,tree053_149,tree053_60,tree053_14]
def tree053_151 : CoverTree := CoverTree.split [tree053_47,tree053_143,tree053_144,tree053_145,tree053_146,tree053_150]
def tree053_152 : CoverTree := CoverTree.reject 200
def tree053_153 : CoverTree := CoverTree.reject 149
def tree053_154 : CoverTree := CoverTree.reject 118
def tree053_155 : CoverTree := CoverTree.reject 302
def tree053_156 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_155,tree053_76,tree053_72,tree053_14]
def tree053_157 : CoverTree := CoverTree.reject 238
def tree053_158 : CoverTree := CoverTree.reject 239
def tree053_159 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_157,tree053_158,tree053_14,tree053_14]
def tree053_160 : CoverTree := CoverTree.split [tree053_7,tree053_152,tree053_153,tree053_154,tree053_156,tree053_159]
def tree053_161 : CoverTree := CoverTree.reject 170
def tree053_162 : CoverTree := CoverTree.reject 126
def tree053_163 : CoverTree := CoverTree.reject 303
def tree053_164 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_163,tree053_17,tree053_94,tree053_14]
def tree053_165 : CoverTree := CoverTree.split [tree053_24,tree053_161,tree053_162,tree053_164,tree053_18,tree053_18]
def tree053_166 : CoverTree := CoverTree.reject 150
def tree053_167 : CoverTree := CoverTree.reject 304
def tree053_168 : CoverTree := CoverTree.reject 240
def tree053_169 : CoverTree := CoverTree.reject 241
def tree053_170 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_167,tree053_168,tree053_169,tree053_14]
def tree053_171 : CoverTree := CoverTree.reject 242
def tree053_172 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_171,tree053_17,tree053_14,tree053_14]
def tree053_173 : CoverTree := CoverTree.split [tree053_31,tree053_166,tree053_170,tree053_172,tree053_18,tree053_18]
def tree053_174 : CoverTree := CoverTree.split [tree053_137,tree053_142,tree053_151,tree053_160,tree053_165,tree053_173]
def tree053_175 : CoverTree := CoverTree.reject 141
def tree053_176 : CoverTree := CoverTree.reject 277
def tree053_177 : CoverTree := CoverTree.reject 226
def tree053_178 : CoverTree := CoverTree.reject 201
def tree053_179 : CoverTree := CoverTree.reject 8
def tree053_180 : CoverTree := CoverTree.reject 343
def tree053_181 : CoverTree := CoverTree.reject 6
def tree053_182 : CoverTree := CoverTree.reject 374
def tree053_183 : CoverTree := CoverTree.split [tree053_181,tree053_181,tree053_182,tree053_14,tree053_14,tree053_14]
def tree053_184 : CoverTree := CoverTree.split [tree053_181,tree053_181,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_185 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_180,tree053_183,tree053_184]
def tree053_186 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_176,tree053_177,tree053_178,tree053_185]
def tree053_187 : CoverTree := CoverTree.reject 336
def tree053_188 : CoverTree := CoverTree.reject 202
def tree053_189 : CoverTree := CoverTree.reject 132
def tree053_190 : CoverTree := CoverTree.reject 0
def tree053_191 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_54,tree053_57,tree053_14]
def tree053_192 : CoverTree := CoverTree.reject 243
def tree053_193 : CoverTree := CoverTree.reject 244
def tree053_194 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_192,tree053_193,tree053_60,tree053_14]
def tree053_195 : CoverTree := CoverTree.split [tree053_47,tree053_187,tree053_188,tree053_189,tree053_191,tree053_194]
def tree053_196 : CoverTree := CoverTree.reject 203
def tree053_197 : CoverTree := CoverTree.reject 151
def tree053_198 : CoverTree := CoverTree.split [tree053_7,tree053_196,tree053_197,tree053_73,tree053_77,tree053_18]
def tree053_199 : CoverTree := CoverTree.reject 171
def tree053_200 : CoverTree := CoverTree.reject 305
def tree053_201 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_200,tree053_17,tree053_94,tree053_14]
def tree053_202 : CoverTree := CoverTree.split [tree053_24,tree053_199,tree053_90,tree053_201,tree053_18,tree053_18]
def tree053_203 : CoverTree := CoverTree.reject 344
def tree053_204 : CoverTree := CoverTree.reject 345
def tree053_205 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_203,tree053_204,tree053_81,tree053_81]
def tree053_206 : CoverTree := CoverTree.reject 306
def tree053_207 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_206,tree053_17,tree053_36,tree053_14]
def tree053_208 : CoverTree := CoverTree.split [tree053_31,tree053_205,tree053_207,tree053_18,tree053_18,tree053_18]
def tree053_209 : CoverTree := CoverTree.split [tree053_175,tree053_186,tree053_195,tree053_198,tree053_202,tree053_208]
def tree053_210 : CoverTree := CoverTree.reject 38
def tree053_211 : CoverTree := CoverTree.reject 39
def tree053_212 : CoverTree := CoverTree.reject 136
def tree053_213 : CoverTree := CoverTree.reject 77
def tree053_214 : CoverTree := CoverTree.reject 85
def tree053_215 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_212,tree053_213,tree053_214]
def tree053_216 : CoverTree := CoverTree.reject 179
def tree053_217 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_210,tree053_211,tree053_215,tree053_216]
def tree053_218 : CoverTree := CoverTree.reject 189
def tree053_219 : CoverTree := CoverTree.reject 96
def tree053_220 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_218,tree053_219,tree053_184]
def tree053_221 : CoverTree := CoverTree.reject 190
def tree053_222 : CoverTree := CoverTree.reject 4
def tree053_223 : CoverTree := CoverTree.split [tree053_222,tree053_222,tree053_222,tree053_222,tree053_222,tree053_14]
def tree053_224 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_221,tree053_223,tree053_184]
def tree053_225 : CoverTree := CoverTree.reject 33
def tree053_226 : CoverTree := CoverTree.reject 224
def tree053_227 : CoverTree := CoverTree.split [tree053_181,tree053_181,tree053_225,tree053_225,tree053_226,tree053_14]
def tree053_228 : CoverTree := CoverTree.split [tree053_181,tree053_181,tree053_225,tree053_225,tree053_14,tree053_14]
def tree053_229 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_227,tree053_228,tree053_184]
def tree053_230 : CoverTree := CoverTree.reject 97
def tree053_231 : CoverTree := CoverTree.split [tree053_181,tree053_181,tree053_230,tree053_14,tree053_14,tree053_14]
def tree053_232 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_231,tree053_184,tree053_184]
def tree053_233 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_220,tree053_224,tree053_229,tree053_232]
def tree053_234 : CoverTree := CoverTree.reject 337
def tree053_235 : CoverTree := CoverTree.reject 221
def tree053_236 : CoverTree := CoverTree.reject 27
def tree053_237 : CoverTree := CoverTree.reject 100
def tree053_238 : CoverTree := CoverTree.reject 101
def tree053_239 : CoverTree := CoverTree.reject 102
def tree053_240 : CoverTree := CoverTree.split [tree053_55,tree053_237,tree053_238,tree053_239,tree053_14,tree053_14]
def tree053_241 : CoverTree := CoverTree.reject 78
def tree053_242 : CoverTree := CoverTree.reject 79
def tree053_243 : CoverTree := CoverTree.split [tree053_241,tree053_242,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_244 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_235,tree053_236,tree053_240,tree053_243]
def tree053_245 : CoverTree := CoverTree.reject 222
def tree053_246 : CoverTree := CoverTree.reject 346
def tree053_247 : CoverTree := CoverTree.reject 80
def tree053_248 : CoverTree := CoverTree.reject 81
def tree053_249 : CoverTree := CoverTree.split [tree053_55,tree053_247,tree053_248,tree053_14,tree053_14,tree053_14]
def tree053_250 : CoverTree := CoverTree.reject 82
def tree053_251 : CoverTree := CoverTree.split [tree053_250,tree053_14,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_252 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_245,tree053_246,tree053_249,tree053_251]
def tree053_253 : CoverTree := CoverTree.reject 245
def tree053_254 : CoverTree := CoverTree.reject 246
def tree053_255 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_253,tree053_254,tree053_60,tree053_14]
def tree053_256 : CoverTree := CoverTree.split [tree053_47,tree053_234,tree053_244,tree053_252,tree053_58,tree053_255]
def tree053_257 : CoverTree := CoverTree.reject 204
def tree053_258 : CoverTree := CoverTree.reject 28
def tree053_259 : CoverTree := CoverTree.reject 61
def tree053_260 : CoverTree := CoverTree.reject 62
def tree053_261 : CoverTree := CoverTree.reject 63
def tree053_262 : CoverTree := CoverTree.split [tree053_16,tree053_259,tree053_260,tree053_261,tree053_14,tree053_14]
def tree053_263 : CoverTree := CoverTree.reject 64
def tree053_264 : CoverTree := CoverTree.split [tree053_55,tree053_263,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_265 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_258,tree053_262,tree053_264,tree053_14]
def tree053_266 : CoverTree := CoverTree.split [tree053_7,tree053_257,tree053_265,tree053_73,tree053_77,tree053_18]
def tree053_267 : CoverTree := CoverTree.reject 347
def tree053_268 : CoverTree := CoverTree.reject 307
def tree053_269 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_267,tree053_268,tree053_89,tree053_14]
def tree053_270 : CoverTree := CoverTree.split [tree053_24,tree053_82,tree053_269,tree053_95,tree053_18,tree053_18]
def tree053_271 : CoverTree := CoverTree.reject 348
def tree053_272 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_271,tree053_81,tree053_81,tree053_81]
def tree053_273 : CoverTree := CoverTree.reject 308
def tree053_274 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_273,tree053_17,tree053_36,tree053_14]
def tree053_275 : CoverTree := CoverTree.split [tree053_31,tree053_272,tree053_274,tree053_18,tree053_18,tree053_18]
def tree053_276 : CoverTree := CoverTree.split [tree053_217,tree053_233,tree053_256,tree053_266,tree053_270,tree053_275]
def tree053_277 : CoverTree := CoverTree.split [tree053_0,tree053_111,tree053_136,tree053_174,tree053_209,tree053_276]
def tree053_278 : CoverTree := CoverTree.reject 42
def tree053_279 : CoverTree := CoverTree.reject 205
def tree053_280 : CoverTree := CoverTree.reject 127
def tree053_281 : CoverTree := CoverTree.reject 158
def tree053_282 : CoverTree := CoverTree.reject 247
def tree053_283 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_108,tree053_282,tree053_14,tree053_14]
def tree053_284 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_279,tree053_280,tree053_281,tree053_283]
def tree053_285 : CoverTree := CoverTree.reject 206
def tree053_286 : CoverTree := CoverTree.reject 119
def tree053_287 : CoverTree := CoverTree.reject 107
def tree053_288 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_285,tree053_286,tree053_287,tree053_109]
def tree053_289 : CoverTree := CoverTree.reject 248
def tree053_290 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_108,tree053_289,tree053_36,tree053_14]
def tree053_291 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_290,tree053_109,tree053_109,tree053_109]
def tree053_292 : CoverTree := CoverTree.split [tree053_101,tree053_101,tree053_278,tree053_284,tree053_288,tree053_291]
def tree053_293 : CoverTree := CoverTree.reject 108
def tree053_294 : CoverTree := CoverTree.reject 278
def tree053_295 : CoverTree := CoverTree.reject 279
def tree053_296 : CoverTree := CoverTree.reject 147
def tree053_297 : CoverTree := CoverTree.reject 309
def tree053_298 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_296,tree053_297,tree053_184]
def tree053_299 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_293,tree053_294,tree053_295,tree053_298]
def tree053_300 : CoverTree := CoverTree.reject 280
def tree053_301 : CoverTree := CoverTree.reject 180
def tree053_302 : CoverTree := CoverTree.reject 128
def tree053_303 : CoverTree := CoverTree.reject 249
def tree053_304 : CoverTree := CoverTree.reject 250
def tree053_305 : CoverTree := CoverTree.reject 251
def tree053_306 : CoverTree := CoverTree.reject 298
def tree053_307 : CoverTree := CoverTree.split [tree053_14,tree053_306,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_308 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_303,tree053_304,tree053_305,tree053_307]
def tree053_309 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_300,tree053_301,tree053_302,tree053_308]
def tree053_310 : CoverTree := CoverTree.reject 152
def tree053_311 : CoverTree := CoverTree.reject 120
def tree053_312 : CoverTree := CoverTree.reject 104
def tree053_313 : CoverTree := CoverTree.reject 252
def tree053_314 : CoverTree := CoverTree.reject 310
def tree053_315 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_313,tree053_314,tree053_14,tree053_14]
def tree053_316 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_310,tree053_311,tree053_312,tree053_315]
def tree053_317 : CoverTree := CoverTree.reject 129
def tree053_318 : CoverTree := CoverTree.reject 74
def tree053_319 : CoverTree := CoverTree.reject 253
def tree053_320 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_318,tree053_319,tree053_94,tree053_14]
def tree053_321 : CoverTree := CoverTree.reject 254
def tree053_322 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_321,tree053_17,tree053_14,tree053_14]
def tree053_323 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_317,tree053_320,tree053_322,tree053_18]
def tree053_324 : CoverTree := CoverTree.reject 311
def tree053_325 : CoverTree := CoverTree.reject 255
def tree053_326 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_324,tree053_325,tree053_36,tree053_14]
def tree053_327 : CoverTree := CoverTree.reject 256
def tree053_328 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_327,tree053_17,tree053_14,tree053_14]
def tree053_329 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_326,tree053_328,tree053_18,tree053_18]
def tree053_330 : CoverTree := CoverTree.split [tree053_112,tree053_299,tree053_309,tree053_316,tree053_323,tree053_329]
def tree053_331 : CoverTree := CoverTree.reject 281
def tree053_332 : CoverTree := CoverTree.reject 282
def tree053_333 : CoverTree := CoverTree.reject 207
def tree053_334 : CoverTree := CoverTree.reject 349
def tree053_335 : CoverTree := CoverTree.reject 312
def tree053_336 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_334,tree053_335,tree053_184]
def tree053_337 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_331,tree053_332,tree053_333,tree053_336]
def tree053_338 : CoverTree := CoverTree.reject 359
def tree053_339 : CoverTree := CoverTree.reject 208
def tree053_340 : CoverTree := CoverTree.reject 181
def tree053_341 : CoverTree := CoverTree.reject 313
def tree053_342 : CoverTree := CoverTree.reject 314
def tree053_343 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_341,tree053_342,tree053_14]
def tree053_344 : CoverTree := CoverTree.reject 350
def tree053_345 : CoverTree := CoverTree.reject 315
def tree053_346 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_344,tree053_345,tree053_60,tree053_14]
def tree053_347 : CoverTree := CoverTree.split [tree053_47,tree053_338,tree053_339,tree053_340,tree053_343,tree053_346]
def tree053_348 : CoverTree := CoverTree.reject 209
def tree053_349 : CoverTree := CoverTree.reject 176
def tree053_350 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_258,tree053_349,tree053_264,tree053_14]
def tree053_351 : CoverTree := CoverTree.reject 316
def tree053_352 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_351,tree053_76,tree053_72,tree053_14]
def tree053_353 : CoverTree := CoverTree.split [tree053_7,tree053_348,tree053_350,tree053_73,tree053_352,tree053_18]
def tree053_354 : CoverTree := CoverTree.reject 172
def tree053_355 : CoverTree := CoverTree.reject 76
def tree053_356 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_355,tree053_87,tree053_89,tree053_14]
def tree053_357 : CoverTree := CoverTree.reject 317
def tree053_358 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_357,tree053_17,tree053_94,tree053_14]
def tree053_359 : CoverTree := CoverTree.split [tree053_24,tree053_354,tree053_356,tree053_358,tree053_18,tree053_18]
def tree053_360 : CoverTree := CoverTree.reject 365
def tree053_361 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_360,tree053_81,tree053_81,tree053_81]
def tree053_362 : CoverTree := CoverTree.split [tree053_31,tree053_361,tree053_37,tree053_18,tree053_18,tree053_18]
def tree053_363 : CoverTree := CoverTree.split [tree053_137,tree053_337,tree053_347,tree053_353,tree053_359,tree053_362]
def tree053_364 : CoverTree := CoverTree.reject 142
def tree053_365 : CoverTree := CoverTree.reject 283
def tree053_366 : CoverTree := CoverTree.reject 227
def tree053_367 : CoverTree := CoverTree.reject 210
def tree053_368 : CoverTree := CoverTree.reject 351
def tree053_369 : CoverTree := CoverTree.reject 375
def tree053_370 : CoverTree := CoverTree.split [tree053_181,tree053_181,tree053_369,tree053_14,tree053_14,tree053_14]
def tree053_371 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_179,tree053_368,tree053_370,tree053_184]
def tree053_372 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_365,tree053_366,tree053_367,tree053_371]
def tree053_373 : CoverTree := CoverTree.reject 338
def tree053_374 : CoverTree := CoverTree.reject 211
def tree053_375 : CoverTree := CoverTree.reject 352
def tree053_376 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_375,tree053_249,tree053_251]
def tree053_377 : CoverTree := CoverTree.reject 257
def tree053_378 : CoverTree := CoverTree.reject 258
def tree053_379 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_377,tree053_378,tree053_60,tree053_14]
def tree053_380 : CoverTree := CoverTree.split [tree053_47,tree053_373,tree053_374,tree053_376,tree053_191,tree053_379]
def tree053_381 : CoverTree := CoverTree.reject 212
def tree053_382 : CoverTree := CoverTree.reject 366
def tree053_383 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_258,tree053_382,tree053_264,tree053_14]
def tree053_384 : CoverTree := CoverTree.split [tree053_7,tree053_381,tree053_383,tree053_73,tree053_77,tree053_18]
def tree053_385 : CoverTree := CoverTree.reject 353
def tree053_386 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_79,tree053_385,tree053_81,tree053_81]
def tree053_387 : CoverTree := CoverTree.split [tree053_24,tree053_386,tree053_90,tree053_95,tree053_18,tree053_18]
def tree053_388 : CoverTree := CoverTree.reject 318
def tree053_389 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_388,tree053_17,tree053_36,tree053_14]
def tree053_390 : CoverTree := CoverTree.split [tree053_31,tree053_97,tree053_389,tree053_18,tree053_18,tree053_18]
def tree053_391 : CoverTree := CoverTree.split [tree053_364,tree053_372,tree053_380,tree053_384,tree053_387,tree053_390]
def tree053_392 : CoverTree := CoverTree.reject 182
def tree053_393 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_210,tree053_211,tree053_215,tree053_392]
def tree053_394 : CoverTree := CoverTree.reject 191
def tree053_395 : CoverTree := CoverTree.reject 53
def tree053_396 : CoverTree := CoverTree.reject 54
def tree053_397 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_394,tree053_395,tree053_396,tree053_81]
def tree053_398 : CoverTree := CoverTree.reject 165
def tree053_399 : CoverTree := CoverTree.reject 166
def tree053_400 : CoverTree := CoverTree.split [tree053_16,tree053_398,tree053_399,tree053_14,tree053_14,tree053_14]
def tree053_401 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_245,tree053_400,tree053_249,tree053_251]
def tree053_402 : CoverTree := CoverTree.split [tree053_47,tree053_397,tree053_244,tree053_401,tree053_58,tree053_61]
def tree053_403 : CoverTree := CoverTree.reject 45
def tree053_404 : CoverTree := CoverTree.reject 46
def tree053_405 : CoverTree := CoverTree.split [tree053_12,tree053_12,tree053_403,tree053_404,tree053_81,tree053_81]
def tree053_406 : CoverTree := CoverTree.split [tree053_7,tree053_405,tree053_265,tree053_73,tree053_77,tree053_18]
def tree053_407 : CoverTree := CoverTree.split [tree053_393,tree053_233,tree053_402,tree053_406,tree053_96,tree053_98]
def tree053_408 : CoverTree := CoverTree.split [tree053_0,tree053_292,tree053_330,tree053_363,tree053_391,tree053_407]
def tree053_409 : CoverTree := CoverTree.reject 196
def tree053_410 : CoverTree := CoverTree.reject 146
def tree053_411 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_236,tree053_409,tree053_410]
def tree053_412 : CoverTree := CoverTree.reject 228
def tree053_413 : CoverTree := CoverTree.reject 160
def tree053_414 : CoverTree := CoverTree.reject 18
def tree053_415 : CoverTree := CoverTree.reject 259
def tree053_416 : CoverTree := CoverTree.reject 260
def tree053_417 : CoverTree := CoverTree.reject 341
def tree053_418 : CoverTree := CoverTree.split [tree053_14,tree053_417,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_419 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_108,tree053_415,tree053_416,tree053_418]
def tree053_420 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_411,tree053_412,tree053_413,tree053_419]
def tree053_421 : CoverTree := CoverTree.reject 213
def tree053_422 : CoverTree := CoverTree.reject 130
def tree053_423 : CoverTree := CoverTree.reject 159
def tree053_424 : CoverTree := CoverTree.reject 21
def tree053_425 : CoverTree := CoverTree.reject 261
def tree053_426 : CoverTree := CoverTree.split [tree053_424,tree053_424,tree053_108,tree053_425,tree053_14,tree053_14]
def tree053_427 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_421,tree053_422,tree053_423,tree053_426]
def tree053_428 : CoverTree := CoverTree.reject 214
def tree053_429 : CoverTree := CoverTree.reject 10
def tree053_430 : CoverTree := CoverTree.reject 262
def tree053_431 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_108,tree053_430,tree053_94,tree053_14]
def tree053_432 : CoverTree := CoverTree.split [tree053_424,tree053_424,tree053_108,tree053_17,tree053_14,tree053_14]
def tree053_433 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_428,tree053_431,tree053_432,tree053_432]
def tree053_434 : CoverTree := CoverTree.reject 263
def tree053_435 : CoverTree := CoverTree.split [tree053_424,tree053_424,tree053_108,tree053_434,tree053_36,tree053_14]
def tree053_436 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_435,tree053_432,tree053_432,tree053_432]
def tree053_437 : CoverTree := CoverTree.split [tree053_101,tree053_101,tree053_420,tree053_427,tree053_433,tree053_436]
def tree053_438 : CoverTree := CoverTree.reject 284
def tree053_439 : CoverTree := CoverTree.reject 285
def tree053_440 : CoverTree := CoverTree.reject 319
def tree053_441 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_296,tree053_440,tree053_184]
def tree053_442 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_293,tree053_438,tree053_439,tree053_441]
def tree053_443 : CoverTree := CoverTree.reject 286
def tree053_444 : CoverTree := CoverTree.reject 183
def tree053_445 : CoverTree := CoverTree.reject 264
def tree053_446 : CoverTree := CoverTree.reject 265
def tree053_447 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_445,tree053_446,tree053_60,tree053_307]
def tree053_448 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_443,tree053_444,tree053_191,tree053_447]
def tree053_449 : CoverTree := CoverTree.reject 153
def tree053_450 : CoverTree := CoverTree.reject 197
def tree053_451 : CoverTree := CoverTree.reject 169
def tree053_452 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_450,tree053_451,tree053_72,tree053_14]
def tree053_453 : CoverTree := CoverTree.reject 55
def tree053_454 : CoverTree := CoverTree.reject 32
def tree053_455 : CoverTree := CoverTree.reject 320
def tree053_456 : CoverTree := CoverTree.split [tree053_453,tree053_454,tree053_455,tree053_76,tree053_72,tree053_14]
def tree053_457 : CoverTree := CoverTree.reject 266
def tree053_458 : CoverTree := CoverTree.reject 230
def tree053_459 : CoverTree := CoverTree.split [tree053_16,tree053_458,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_460 : CoverTree := CoverTree.split [tree053_453,tree053_454,tree053_457,tree053_459,tree053_14,tree053_14]
def tree053_461 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_449,tree053_452,tree053_456,tree053_460]
def tree053_462 : CoverTree := CoverTree.reject 73
def tree053_463 : CoverTree := CoverTree.reject 321
def tree053_464 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_462,tree053_463,tree053_89,tree053_14]
def tree053_465 : CoverTree := CoverTree.reject 267
def tree053_466 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_318,tree053_465,tree053_94,tree053_14]
def tree053_467 : CoverTree := CoverTree.split [tree053_453,tree053_454,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_468 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_464,tree053_466,tree053_467,tree053_467]
def tree053_469 : CoverTree := CoverTree.split [tree053_453,tree053_454,tree053_34,tree053_17,tree053_36,tree053_14]
def tree053_470 : CoverTree := CoverTree.reject 268
def tree053_471 : CoverTree := CoverTree.split [tree053_453,tree053_454,tree053_470,tree053_17,tree053_14,tree053_14]
def tree053_472 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_469,tree053_471,tree053_467,tree053_467]
def tree053_473 : CoverTree := CoverTree.split [tree053_112,tree053_442,tree053_448,tree053_461,tree053_468,tree053_472]
def tree053_474 : CoverTree := CoverTree.reject 287
def tree053_475 : CoverTree := CoverTree.reject 288
def tree053_476 : CoverTree := CoverTree.reject 215
def tree053_477 : CoverTree := CoverTree.reject 354
def tree053_478 : CoverTree := CoverTree.reject 322
def tree053_479 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_477,tree053_478,tree053_184]
def tree053_480 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_474,tree053_475,tree053_476,tree053_479]
def tree053_481 : CoverTree := CoverTree.reject 360
def tree053_482 : CoverTree := CoverTree.reject 216
def tree053_483 : CoverTree := CoverTree.reject 75
def tree053_484 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_483,tree053_249,tree053_251]
def tree053_485 : CoverTree := CoverTree.reject 355
def tree053_486 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_485,tree053_149,tree053_60,tree053_14]
def tree053_487 : CoverTree := CoverTree.split [tree053_47,tree053_481,tree053_482,tree053_484,tree053_191,tree053_486]
def tree053_488 : CoverTree := CoverTree.reject 217
def tree053_489 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_258,tree053_349,tree053_264,tree053_14]
def tree053_490 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_68,tree053_71,tree053_72,tree053_14]
def tree053_491 : CoverTree := CoverTree.reject 43
def tree053_492 : CoverTree := CoverTree.reject 121
def tree053_493 : CoverTree := CoverTree.reject 323
def tree053_494 : CoverTree := CoverTree.split [tree053_491,tree053_492,tree053_493,tree053_76,tree053_72,tree053_14]
def tree053_495 : CoverTree := CoverTree.reject 7
def tree053_496 : CoverTree := CoverTree.reject 167
def tree053_497 : CoverTree := CoverTree.split [tree053_495,tree053_495,tree053_496,tree053_14,tree053_14,tree053_14]
def tree053_498 : CoverTree := CoverTree.split [tree053_491,tree053_497,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_499 : CoverTree := CoverTree.split [tree053_7,tree053_488,tree053_489,tree053_490,tree053_494,tree053_498]
def tree053_500 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_20,tree053_21,tree053_22,tree053_23]
def tree053_501 : CoverTree := CoverTree.reject 356
def tree053_502 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_79,tree053_501,tree053_81,tree053_81]
def tree053_503 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_355,tree053_87,tree053_89,tree053_14]
def tree053_504 : CoverTree := CoverTree.reject 324
def tree053_505 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_504,tree053_17,tree053_94,tree053_14]
def tree053_506 : CoverTree := CoverTree.split [tree053_491,tree053_492,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_507 : CoverTree := CoverTree.split [tree053_495,tree053_495,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_508 : CoverTree := CoverTree.split [tree053_491,tree053_507,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_509 : CoverTree := CoverTree.split [tree053_500,tree053_502,tree053_503,tree053_505,tree053_506,tree053_508]
def tree053_510 : CoverTree := CoverTree.reject 57
def tree053_511 : CoverTree := CoverTree.split [tree053_491,tree053_510,tree053_20,tree053_21,tree053_29,tree053_30]
def tree053_512 : CoverTree := CoverTree.reject 334
def tree053_513 : CoverTree := CoverTree.reject 299
def tree053_514 : CoverTree := CoverTree.split [tree053_80,tree053_80,tree053_80,tree053_513,tree053_14,tree053_14]
def tree053_515 : CoverTree := CoverTree.split [tree053_491,tree053_512,tree053_514,tree053_81,tree053_81,tree053_81]
def tree053_516 : CoverTree := CoverTree.reject 162
def tree053_517 : CoverTree := CoverTree.split [tree053_495,tree053_495,tree053_516,tree053_14,tree053_14,tree053_14]
def tree053_518 : CoverTree := CoverTree.split [tree053_491,tree053_517,tree053_34,tree053_17,tree053_36,tree053_14]
def tree053_519 : CoverTree := CoverTree.split [tree053_511,tree053_515,tree053_518,tree053_508,tree053_508,tree053_508]
def tree053_520 : CoverTree := CoverTree.split [tree053_137,tree053_480,tree053_487,tree053_499,tree053_509,tree053_519]
def tree053_521 : CoverTree := CoverTree.reject 289
def tree053_522 : CoverTree := CoverTree.reject 184
def tree053_523 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_210,tree053_211,tree053_521,tree053_522]
def tree053_524 : CoverTree := CoverTree.reject 290
def tree053_525 : CoverTree := CoverTree.reject 20
def tree053_526 : CoverTree := CoverTree.reject 372
def tree053_527 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_525,tree053_526,tree053_184]
def tree053_528 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_525,tree053_228,tree053_184]
def tree053_529 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_231,tree053_184,tree053_184]
def tree053_530 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_524,tree053_527,tree053_528,tree053_529]
def tree053_531 : CoverTree := CoverTree.reject 339
def tree053_532 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_236,tree053_240,tree053_243]
def tree053_533 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_400,tree053_249,tree053_251]
def tree053_534 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_15,tree053_17,tree053_60,tree053_14]
def tree053_535 : CoverTree := CoverTree.split [tree053_47,tree053_531,tree053_532,tree053_533,tree053_191,tree053_534]
def tree053_536 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_403,tree053_404,tree053_81,tree053_81]
def tree053_537 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_258,tree053_262,tree053_264,tree053_14]
def tree053_538 : CoverTree := CoverTree.reject 192
def tree053_539 : CoverTree := CoverTree.reject 335
def tree053_540 : CoverTree := CoverTree.split [tree053_538,tree053_539,tree053_74,tree053_76,tree053_72,tree053_14]
def tree053_541 : CoverTree := CoverTree.reject 139
def tree053_542 : CoverTree := CoverTree.split [tree053_541,tree053_497,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_543 : CoverTree := CoverTree.split [tree053_7,tree053_536,tree053_537,tree053_490,tree053_540,tree053_542]
def tree053_544 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_79,tree053_81,tree053_81,tree053_81]
def tree053_545 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_85,tree053_87,tree053_89,tree053_14]
def tree053_546 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_92,tree053_17,tree053_94,tree053_14]
def tree053_547 : CoverTree := CoverTree.reject 140
def tree053_548 : CoverTree := CoverTree.reject 134
def tree053_549 : CoverTree := CoverTree.split [tree053_495,tree053_495,tree053_548,tree053_14,tree053_14,tree053_14]
def tree053_550 : CoverTree := CoverTree.split [tree053_547,tree053_549,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_551 : CoverTree := CoverTree.reject 29
def tree053_552 : CoverTree := CoverTree.reject 26
def tree053_553 : CoverTree := CoverTree.split [tree053_495,tree053_495,tree053_551,tree053_552,tree053_14,tree053_14]
def tree053_554 : CoverTree := CoverTree.split [tree053_553,tree053_507,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_555 : CoverTree := CoverTree.split [tree053_500,tree053_544,tree053_545,tree053_546,tree053_550,tree053_554]
def tree053_556 : CoverTree := CoverTree.reject 105
def tree053_557 : CoverTree := CoverTree.split [tree053_556,tree053_510,tree053_20,tree053_21,tree053_29,tree053_30]
def tree053_558 : CoverTree := CoverTree.reject 90
def tree053_559 : CoverTree := CoverTree.reject 373
def tree053_560 : CoverTree := CoverTree.split [tree053_558,tree053_559,tree053_81,tree053_81,tree053_81,tree053_81]
def tree053_561 : CoverTree := CoverTree.reject 91
def tree053_562 : CoverTree := CoverTree.split [tree053_561,tree053_517,tree053_34,tree053_17,tree053_36,tree053_14]
def tree053_563 : CoverTree := CoverTree.reject 92
def tree053_564 : CoverTree := CoverTree.split [tree053_563,tree053_507,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_565 : CoverTree := CoverTree.reject 195
def tree053_566 : CoverTree := CoverTree.split [tree053_495,tree053_495,tree053_551,tree053_552,tree053_14,tree053_565]
def tree053_567 : CoverTree := CoverTree.split [tree053_566,tree053_507,tree053_15,tree053_17,tree053_14,tree053_14]
def tree053_568 : CoverTree := CoverTree.split [tree053_557,tree053_560,tree053_562,tree053_564,tree053_567,tree053_554]
def tree053_569 : CoverTree := CoverTree.split [tree053_523,tree053_530,tree053_535,tree053_543,tree053_555,tree053_568]
def tree053_570 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_212,tree053_213,tree053_214]
def tree053_571 : CoverTree := CoverTree.reject 185
def tree053_572 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_210,tree053_211,tree053_570,tree053_571]
def tree053_573 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_218,tree053_219,tree053_184]
def tree053_574 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_221,tree053_223,tree053_184]
def tree053_575 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_227,tree053_228,tree053_184]
def tree053_576 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_573,tree053_574,tree053_575,tree053_529]
def tree053_577 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_394,tree053_395,tree053_396,tree053_81]
def tree053_578 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_235,tree053_236,tree053_240,tree053_243]
def tree053_579 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_245,tree053_400,tree053_249,tree053_251]
def tree053_580 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_52,tree053_54,tree053_57,tree053_14]
def tree053_581 : CoverTree := CoverTree.split [tree053_47,tree053_577,tree053_578,tree053_579,tree053_580,tree053_534]
def tree053_582 : CoverTree := CoverTree.reject 327
def tree053_583 : CoverTree := CoverTree.split [tree053_558,tree053_582,tree053_403,tree053_404,tree053_81,tree053_81]
def tree053_584 : CoverTree := CoverTree.reject 328
def tree053_585 : CoverTree := CoverTree.split [tree053_561,tree053_584,tree053_258,tree053_262,tree053_264,tree053_14]
def tree053_586 : CoverTree := CoverTree.reject 329
def tree053_587 : CoverTree := CoverTree.split [tree053_563,tree053_586,tree053_68,tree053_71,tree053_72,tree053_14]
def tree053_588 : CoverTree := CoverTree.reject 36
def tree053_589 : CoverTree := CoverTree.split [tree053_495,tree053_495,tree053_588,tree053_588,tree053_588,tree053_14]
def tree053_590 : CoverTree := CoverTree.split [tree053_538,tree053_589,tree053_74,tree053_76,tree053_72,tree053_14]
def tree053_591 : CoverTree := CoverTree.split [tree053_7,tree053_583,tree053_585,tree053_587,tree053_590,tree053_542]
def tree053_592 : CoverTree := CoverTree.split [tree053_556,tree053_510,tree053_20,tree053_21,tree053_22,tree053_23]
def tree053_593 : CoverTree := CoverTree.reject 330
def tree053_594 : CoverTree := CoverTree.split [tree053_558,tree053_593,tree053_79,tree053_81,tree053_81,tree053_81]
def tree053_595 : CoverTree := CoverTree.reject 163
def tree053_596 : CoverTree := CoverTree.split [tree053_561,tree053_595,tree053_85,tree053_87,tree053_89,tree053_14]
def tree053_597 : CoverTree := CoverTree.reject 332
def tree053_598 : CoverTree := CoverTree.split [tree053_495,tree053_495,tree053_548,tree053_597,tree053_14,tree053_14]
def tree053_599 : CoverTree := CoverTree.split [tree053_563,tree053_598,tree053_92,tree053_17,tree053_94,tree053_14]
def tree053_600 : CoverTree := CoverTree.split [tree053_592,tree053_594,tree053_596,tree053_599,tree053_550,tree053_554]
def tree053_601 : CoverTree := CoverTree.reject 137
def tree053_602 : CoverTree := CoverTree.reject 138
def tree053_603 : CoverTree := CoverTree.split [tree053_80,tree053_80,tree053_80,tree053_601,tree053_602,tree053_14]
def tree053_604 : CoverTree := CoverTree.split [tree053_558,tree053_603,tree053_81,tree053_81,tree053_81,tree053_81]
def tree053_605 : CoverTree := CoverTree.split [tree053_557,tree053_604,tree053_562,tree053_564,tree053_567,tree053_554]
def tree053_606 : CoverTree := CoverTree.split [tree053_572,tree053_576,tree053_581,tree053_591,tree053_600,tree053_605]
def tree053_607 : CoverTree := CoverTree.split [tree053_0,tree053_437,tree053_473,tree053_520,tree053_569,tree053_606]
def tree053_608 : CoverTree := CoverTree.reject 229
def tree053_609 : CoverTree := CoverTree.reject 161
def tree053_610 : CoverTree := CoverTree.reject 269
def tree053_611 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_108,tree053_610,tree053_60,tree053_418]
def tree053_612 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_411,tree053_608,tree053_609,tree053_611]
def tree053_613 : CoverTree := CoverTree.reject 218
def tree053_614 : CoverTree := CoverTree.reject 131
def tree053_615 : CoverTree := CoverTree.reject 112
def tree053_616 : CoverTree := CoverTree.split [tree053_424,tree053_424,tree053_108,tree053_615,tree053_72,tree053_14]
def tree053_617 : CoverTree := CoverTree.reject 362
def tree053_618 : CoverTree := CoverTree.reject 363
def tree053_619 : CoverTree := CoverTree.split [tree053_16,tree053_617,tree053_618,tree053_14,tree053_14,tree053_14]
def tree053_620 : CoverTree := CoverTree.split [tree053_424,tree053_424,tree053_108,tree053_619,tree053_14,tree053_14]
def tree053_621 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_613,tree053_614,tree053_616,tree053_620]
def tree053_622 : CoverTree := CoverTree.reject 219
def tree053_623 : CoverTree := CoverTree.reject 270
def tree053_624 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_108,tree053_623,tree053_94,tree053_14]
def tree053_625 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_622,tree053_624,tree053_432,tree053_432]
def tree053_626 : CoverTree := CoverTree.split [tree053_424,tree053_424,tree053_108,tree053_17,tree053_36,tree053_14]
def tree053_627 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_626,tree053_432,tree053_432,tree053_432]
def tree053_628 : CoverTree := CoverTree.split [tree053_101,tree053_101,tree053_612,tree053_621,tree053_625,tree053_627]
def tree053_629 : CoverTree := CoverTree.reject 291
def tree053_630 : CoverTree := CoverTree.reject 292
def tree053_631 : CoverTree := CoverTree.reject 325
def tree053_632 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_296,tree053_631,tree053_184]
def tree053_633 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_293,tree053_629,tree053_630,tree053_632]
def tree053_634 : CoverTree := CoverTree.reject 293
def tree053_635 : CoverTree := CoverTree.reject 72
def tree053_636 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_635,tree053_249,tree053_251]
def tree053_637 : CoverTree := CoverTree.reject 271
def tree053_638 : CoverTree := CoverTree.reject 364
def tree053_639 : CoverTree := CoverTree.split [tree053_16,tree053_638,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_640 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_637,tree053_639,tree053_60,tree053_307]
def tree053_641 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_634,tree053_636,tree053_191,tree053_640]
def tree053_642 : CoverTree := CoverTree.reject 273
def tree053_643 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_258,tree053_642,tree053_264,tree053_14]
def tree053_644 : CoverTree := CoverTree.reject 326
def tree053_645 : CoverTree := CoverTree.split [tree053_453,tree053_454,tree053_644,tree053_76,tree053_72,tree053_14]
def tree053_646 : CoverTree := CoverTree.split [tree053_453,tree053_454,tree053_15,tree053_459,tree053_14,tree053_14]
def tree053_647 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_643,tree053_452,tree053_645,tree053_646]
def tree053_648 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_462,tree053_87,tree053_89,tree053_14]
def tree053_649 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_318,tree053_17,tree053_94,tree053_14]
def tree053_650 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_648,tree053_649,tree053_467,tree053_467]
def tree053_651 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_469,tree053_467,tree053_467,tree053_467]
def tree053_652 : CoverTree := CoverTree.split [tree053_112,tree053_633,tree053_641,tree053_647,tree053_650,tree053_651]
def tree053_653 : CoverTree := CoverTree.reject 294
def tree053_654 : CoverTree := CoverTree.reject 295
def tree053_655 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_653,tree053_654,tree053_528,tree053_529]
def tree053_656 : CoverTree := CoverTree.reject 361
def tree053_657 : CoverTree := CoverTree.reject 220
def tree053_658 : CoverTree := CoverTree.reject 232
def tree053_659 : CoverTree := CoverTree.reject 233
def tree053_660 : CoverTree := CoverTree.split [tree053_13,tree053_658,tree053_659,tree053_14,tree053_14,tree053_14]
def tree053_661 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_660,tree053_149,tree053_60,tree053_14]
def tree053_662 : CoverTree := CoverTree.split [tree053_47,tree053_656,tree053_657,tree053_484,tree053_191,tree053_661]
def tree053_663 : CoverTree := CoverTree.split [tree053_491,tree053_492,tree053_74,tree053_76,tree053_72,tree053_14]
def tree053_664 : CoverTree := CoverTree.split [tree053_7,tree053_536,tree053_489,tree053_490,tree053_663,tree053_498]
def tree053_665 : CoverTree := CoverTree.reject 357
def tree053_666 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_79,tree053_665,tree053_81,tree053_81]
def tree053_667 : CoverTree := CoverTree.split [tree053_500,tree053_666,tree053_503,tree053_546,tree053_506,tree053_508]
def tree053_668 : CoverTree := CoverTree.split [tree053_137,tree053_655,tree053_662,tree053_664,tree053_667,tree053_519]
def tree053_669 : CoverTree := CoverTree.reject 296
def tree053_670 : CoverTree := CoverTree.reject 186
def tree053_671 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_210,tree053_211,tree053_669,tree053_670]
def tree053_672 : CoverTree := CoverTree.reject 297
def tree053_673 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_525,tree053_223,tree053_184]
def tree053_674 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_672,tree053_673,tree053_528,tree053_529]
def tree053_675 : CoverTree := CoverTree.reject 340
def tree053_676 : CoverTree := CoverTree.split [tree053_47,tree053_675,tree053_532,tree053_533,tree053_191,tree053_534]
def tree053_677 : CoverTree := CoverTree.split [tree053_671,tree053_674,tree053_676,tree053_543,tree053_555,tree053_605]
def tree053_678 : CoverTree := CoverTree.reject 187
def tree053_679 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_210,tree053_211,tree053_570,tree053_678]
def tree053_680 : CoverTree := CoverTree.split [tree053_679,tree053_576,tree053_581,tree053_591,tree053_600,tree053_605]
def tree053_681 : CoverTree := CoverTree.split [tree053_0,tree053_628,tree053_652,tree053_668,tree053_677,tree053_680]
def tree053_682 : CoverTree := CoverTree.reject 58
def tree053_683 : CoverTree := CoverTree.reject 168
def tree053_684 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_682,tree053_683,tree053_251]
def tree053_685 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_682,tree053_57,tree053_14]
def tree053_686 : CoverTree := CoverTree.reject 368
def tree053_687 : CoverTree := CoverTree.split [tree053_16,tree053_686,tree053_14,tree053_14,tree053_14,tree053_14]
def tree053_688 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_108,tree053_687,tree053_60,tree053_418]
def tree053_689 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_411,tree053_684,tree053_685,tree053_688]
def tree053_690 : CoverTree := CoverTree.reject 175
def tree053_691 : CoverTree := CoverTree.reject 111
def tree053_692 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_108,tree053_690,tree053_691,tree053_14]
def tree053_693 : CoverTree := CoverTree.reject 333
def tree053_694 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_108,tree053_693,tree053_72,tree053_14]
def tree053_695 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_692,tree053_694,tree053_616,tree053_620]
def tree053_696 : CoverTree := CoverTree.reject 113
def tree053_697 : CoverTree := CoverTree.reject 114
def tree053_698 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_108,tree053_696,tree053_697,tree053_14]
def tree053_699 : CoverTree := CoverTree.split [tree053_429,tree053_429,tree053_108,tree053_17,tree053_94,tree053_14]
def tree053_700 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_698,tree053_699,tree053_432,tree053_432]
def tree053_701 : CoverTree := CoverTree.split [tree053_101,tree053_101,tree053_689,tree053_695,tree053_700,tree053_627]
def tree053_702 : CoverTree := CoverTree.reject 133
def tree053_703 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_525,tree053_702,tree053_184]
def tree053_704 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_296,tree053_184,tree053_184]
def tree053_705 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_293,tree053_703,tree053_703,tree053_704]
def tree053_706 : CoverTree := CoverTree.reject 71
def tree053_707 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_236,tree053_706,tree053_243]
def tree053_708 : CoverTree := CoverTree.reject 369
def tree053_709 : CoverTree := CoverTree.reject 370
def tree053_710 : CoverTree := CoverTree.reject 371
def tree053_711 : CoverTree := CoverTree.split [tree053_13,tree053_708,tree053_709,tree053_710,tree053_14,tree053_14]
def tree053_712 : CoverTree := CoverTree.split [tree053_414,tree053_414,tree053_711,tree053_639,tree053_60,tree053_307]
def tree053_713 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_707,tree053_636,tree053_191,tree053_712]
def tree053_714 : CoverTree := CoverTree.split [tree053_453,tree053_454,tree053_74,tree053_76,tree053_72,tree053_14]
def tree053_715 : CoverTree := CoverTree.split [tree053_105,tree053_105,tree053_643,tree053_452,tree053_714,tree053_646]
def tree053_716 : CoverTree := CoverTree.split [tree053_112,tree053_705,tree053_713,tree053_715,tree053_650,tree053_651]
def tree053_717 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_525,tree053_219,tree053_184]
def tree053_718 : CoverTree := CoverTree.reject 225
def tree053_719 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_525,tree053_718,tree053_184]
def tree053_720 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_717,tree053_719,tree053_528,tree053_529]
def tree053_721 : CoverTree := CoverTree.reject 231
def tree053_722 : CoverTree := CoverTree.split [tree053_80,tree053_80,tree053_80,tree053_721,tree053_14,tree053_14]
def tree053_723 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_395,tree053_396,tree053_722]
def tree053_724 : CoverTree := CoverTree.split [tree053_47,tree053_723,tree053_532,tree053_484,tree053_191,tree053_661]
def tree053_725 : CoverTree := CoverTree.split [tree053_500,tree053_544,tree053_503,tree053_546,tree053_506,tree053_508]
def tree053_726 : CoverTree := CoverTree.split [tree053_137,tree053_720,tree053_724,tree053_664,tree053_725,tree053_519]
def tree053_727 : CoverTree := CoverTree.reject 367
def tree053_728 : CoverTree := CoverTree.split [tree053_181,tree053_181,tree053_727,tree053_14,tree053_14,tree053_14]
def tree053_729 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_525,tree053_213,tree053_728]
def tree053_730 : CoverTree := CoverTree.reject 52
def tree053_731 : CoverTree := CoverTree.split [tree053_179,tree053_179,tree053_179,tree053_730,tree053_184,tree053_184]
def tree053_732 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_210,tree053_211,tree053_729,tree053_731]
def tree053_733 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_717,tree053_673,tree053_528,tree053_529]
def tree053_734 : CoverTree := CoverTree.split [tree053_190,tree053_190,tree053_190,tree053_395,tree053_396,tree053_81]
def tree053_735 : CoverTree := CoverTree.split [tree053_47,tree053_734,tree053_532,tree053_533,tree053_191,tree053_534]
def tree053_736 : CoverTree := CoverTree.split [tree053_732,tree053_733,tree053_735,tree053_543,tree053_555,tree053_605]
def tree053_737 : CoverTree := CoverTree.split [tree053_41,tree053_41,tree053_210,tree053_211,tree053_570,tree053_731]
def tree053_738 : CoverTree := CoverTree.split [tree053_737,tree053_576,tree053_581,tree053_591,tree053_600,tree053_605]
def tree053_739 : CoverTree := CoverTree.split [tree053_0,tree053_701,tree053_716,tree053_726,tree053_736,tree053_738]
def tree053_740 : CoverTree := CoverTree.split [tree053_100,tree053_277,tree053_408,tree053_607,tree053_681,tree053_739]
def tree053 : CoverTree := tree053_740

end Snake9.Shared89
