import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes073 : List Box := [
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
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,6),(1,2),(1,2),(1,6),(1,6)],
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
[(1,6),(1,6),(1,2),(1,5),(1,5),(1,4)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,5),(1,3),(1,5)],
[(1,6),(1,6),(1,4),(1,5),(1,2),(1,5)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(2,2),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,4),(1,5),(1,3),(1,2)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(6,6),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(1,6)],
[(1,6),(1,4),(1,5),(1,5),(1,2),(1,6)],
[(1,6),(1,6),(1,1),(6,6),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,2),(1,3),(1,5),(1,4),(1,6)],
[(1,1),(5,5),(2,2),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
[(1,6),(1,6),(6,6),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(3,3)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(4,4)],
[(1,6),(1,6),(4,4),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(3,3)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(4,4)],
[(1,6),(1,6),(4,4),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(4,4),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(4,4),(5,5),(4,4),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(3,3),(3,3)],
[(1,6),(1,6),(5,5),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(5,5),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(1,1)],
[(1,6),(3,3),(3,3),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(5,5),(1,6)],
[(1,6),(1,6),(4,4),(6,6),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(5,5),(1,1)],
[(1,6),(6,6),(1,1),(5,5),(6,6),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(5,5),(1,6),(1,6)],
[(3,3),(2,2),(5,5),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(2,2)],
[(2,2),(3,3),(3,3),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(1,6)],
[(1,1),(5,5),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(4,4),(3,3)],
[(1,6),(2,2),(6,6),(3,3),(3,3),(1,6)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(1,6)],
[(3,3),(2,2),(5,5),(4,4),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(4,4)],
[(2,2),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(3,3),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(5,5),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(5,5),(1,6),(1,6)],
[(1,1),(5,5),(5,5),(3,3),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(3,3),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(3,3),(3,3),(5,5),(3,3),(1,6),(1,6)],
[(4,4),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(5,5),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(3,3),(5,5),(1,6)],
[(2,2),(2,2),(6,6),(3,3),(1,6),(1,6)],
[(2,2),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(5,5),(2,2),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(2,2),(5,5),(5,5),(3,3),(1,6)],
[(1,1),(6,6),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(5,5),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,3),(1,2),(1,5),(1,5),(1,6)],
[(1,1),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,6),(5,5),(5,5),(1,1),(1,6)],
[(2,2),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(3,3),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(1,1),(5,5),(6,6),(2,2),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(3,3)],
[(1,6),(1,6),(6,6),(5,5),(1,1),(6,6)],
[(1,6),(2,2),(3,3),(3,3),(6,6),(1,6)],
[(1,6),(2,2),(5,5),(4,4),(3,3),(1,6)],
[(1,6),(3,3),(2,2),(6,6),(4,4),(1,6)],
[(1,6),(4,4),(5,5),(3,3),(3,3),(1,6)],
[(2,2),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(6,6),(2,2),(1,6),(1,6)],
[(2,2),(5,5),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(1,1),(6,6),(2,2),(6,6),(1,6),(1,6)],
[(2,2),(4,4),(2,2),(6,6),(1,6),(1,6)],
[(4,4),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(5,5),(2,2),(3,3),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(1,5),(1,5),(1,2),(1,3)],
[(1,6),(1,6),(5,5),(3,3),(2,2),(1,6)],
[(1,1),(5,5),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)],
[(1,6),(2,2),(3,3),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(4,4),(1,6)],
[(1,6),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(1,6),(3,3),(5,5),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(2,2),(5,5),(5,5),(2,2),(1,6),(1,6)],
[(3,3),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(1,1),(6,6),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(6,6),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(4,4),(1,6)],
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
[(3,3),(4,4),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(5,5),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(2,2),(5,5),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(5,5),(2,2),(4,4),(3,3),(1,6),(1,6)],
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
[(1,6),(2,2),(6,6),(6,6),(3,3),(2,2)],
[(1,6),(2,2),(6,6),(6,6),(3,3),(3,3)],
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
[(3,3),(2,2),(6,6),(4,4),(3,3),(1,6)],
[(3,3),(2,2),(6,6),(5,5),(3,3),(1,6)],
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
[(4,4),(2,2),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(4,4),(2,2),(3,3),(6,6),(5,5),(1,6)],
[(4,4),(2,2),(4,4),(6,6),(3,3),(1,6)],
[(4,4),(2,2),(4,4),(6,6),(4,4),(1,6)],
[(4,4),(2,2),(5,5),(4,4),(4,4),(1,6)],
[(4,4),(2,2),(6,6),(3,3),(4,4),(1,6)],
[(4,4),(2,2),(6,6),(4,4),(3,3),(1,6)],
[(4,4),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(3,3),(3,3),(6,6),(4,4),(1,6)],
[(4,4),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(4,4),(3,3),(5,5),(4,4),(4,4),(1,6)],
[(4,4),(3,3),(6,6),(4,4),(3,3),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(3,3),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(5,5),(2,2),(5,5),(4,4),(4,4),(1,6)],
[(5,5),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(1,1),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(2,2),(5,5),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(5,5),(3,3),(5,5),(1,6)],
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
[(4,4),(3,3),(6,6),(4,4),(2,2),(1,6)],
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
[(1,6),(2,2),(5,5),(3,3),(3,3),(1,6)],
[(1,6),(3,3),(6,6),(5,5),(1,1),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)],
[(1,6),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(2,2),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(2,2),(6,6),(3,3),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(4,4),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(5,5),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(6,6),(6,6),(2,2)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(2,2)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(3,3)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(4,4)],
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
[(4,4),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(4,4),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(4,4),(4,4),(5,5),(2,2),(4,4),(1,6)],
[(5,5),(4,4),(5,5),(2,2),(4,4),(1,6)],
[(1,6),(2,2),(4,4),(4,4),(3,3),(1,6)],
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
[(1,6),(2,2),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(4,4)],
[(1,6),(2,2),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(4,4)],
[(4,4),(5,5),(2,2),(4,4),(5,5),(1,6)],
[(4,4),(5,5),(6,6),(2,2),(2,2),(1,6)],
[(2,2),(5,5),(2,2),(6,6),(5,5),(3,3)],
[(3,3),(5,5),(2,2),(6,6),(5,5),(3,3)]
]

def root073 : Nat := 3511

def tree073_0 : CoverTree := CoverTree.reject 1
def tree073_1 : CoverTree := CoverTree.reject 16
def tree073_2 : CoverTree := CoverTree.reject 13
def tree073_3 : CoverTree := CoverTree.reject 9
def tree073_4 : CoverTree := CoverTree.reject 136
def tree073_5 : CoverTree := CoverTree.reject 58
def tree073_6 : CoverTree := CoverTree.reject 36
def tree073_7 : CoverTree := CoverTree.reject 18
def tree073_8 : CoverTree := CoverTree.reject 196
def tree073_9 : CoverTree := CoverTree.reject 143
def tree073_10 : CoverTree := CoverTree.reject 118
def tree073_11 : CoverTree := CoverTree.reject 102
def tree073_12 : CoverTree := CoverTree.reject 3
def tree073_13 : CoverTree := CoverTree.reject 14
def tree073_14 : CoverTree := CoverTree.accept
def tree073_15 : CoverTree := CoverTree.split [tree073_13,tree073_14,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_16 : CoverTree := CoverTree.reject 11
def tree073_17 : CoverTree := CoverTree.split [tree073_16,tree073_14,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_18 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_19 : CoverTree := CoverTree.split [tree073_7,tree073_8,tree073_9,tree073_10,tree073_11,tree073_18]
def tree073_20 : CoverTree := CoverTree.reject 29
def tree073_21 : CoverTree := CoverTree.reject 30
def tree073_22 : CoverTree := CoverTree.reject 45
def tree073_23 : CoverTree := CoverTree.reject 46
def tree073_24 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_20,tree073_21,tree073_22,tree073_23]
def tree073_25 : CoverTree := CoverTree.reject 164
def tree073_26 : CoverTree := CoverTree.reject 110
def tree073_27 : CoverTree := CoverTree.reject 97
def tree073_28 : CoverTree := CoverTree.split [tree073_24,tree073_25,tree073_26,tree073_27,tree073_18,tree073_18]
def tree073_29 : CoverTree := CoverTree.reject 48
def tree073_30 : CoverTree := CoverTree.reject 49
def tree073_31 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_20,tree073_21,tree073_29,tree073_30]
def tree073_32 : CoverTree := CoverTree.reject 144
def tree073_33 : CoverTree := CoverTree.reject 61
def tree073_34 : CoverTree := CoverTree.split [tree073_13,tree073_33,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_35 : CoverTree := CoverTree.reject 41
def tree073_36 : CoverTree := CoverTree.split [tree073_35,tree073_14,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_37 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_34,tree073_17,tree073_36,tree073_14]
def tree073_38 : CoverTree := CoverTree.split [tree073_31,tree073_32,tree073_37,tree073_18,tree073_18,tree073_18]
def tree073_39 : CoverTree := CoverTree.split [tree073_4,tree073_5,tree073_6,tree073_19,tree073_28,tree073_38]
def tree073_40 : CoverTree := CoverTree.reject 174
def tree073_41 : CoverTree := CoverTree.reject 15
def tree073_42 : CoverTree := CoverTree.reject 279
def tree073_43 : CoverTree := CoverTree.reject 222
def tree073_44 : CoverTree := CoverTree.reject 175
def tree073_45 : CoverTree := CoverTree.reject 158
def tree073_46 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_42,tree073_43,tree073_44,tree073_45]
def tree073_47 : CoverTree := CoverTree.reject 21
def tree073_48 : CoverTree := CoverTree.reject 341
def tree073_49 : CoverTree := CoverTree.reject 191
def tree073_50 : CoverTree := CoverTree.reject 130
def tree073_51 : CoverTree := CoverTree.reject 33
def tree073_52 : CoverTree := CoverTree.split [tree073_13,tree073_51,tree073_51,tree073_51,tree073_51,tree073_14]
def tree073_53 : CoverTree := CoverTree.reject 94
def tree073_54 : CoverTree := CoverTree.split [tree073_16,tree073_53,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_55 : CoverTree := CoverTree.reject 22
def tree073_56 : CoverTree := CoverTree.reject 88
def tree073_57 : CoverTree := CoverTree.split [tree073_55,tree073_56,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_58 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_52,tree073_54,tree073_57,tree073_14]
def tree073_59 : CoverTree := CoverTree.reject 89
def tree073_60 : CoverTree := CoverTree.split [tree073_59,tree073_14,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_61 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_15,tree073_17,tree073_60,tree073_14]
def tree073_62 : CoverTree := CoverTree.split [tree073_47,tree073_48,tree073_49,tree073_50,tree073_58,tree073_61]
def tree073_63 : CoverTree := CoverTree.reject 197
def tree073_64 : CoverTree := CoverTree.reject 145
def tree073_65 : CoverTree := CoverTree.reject 42
def tree073_66 : CoverTree := CoverTree.reject 66
def tree073_67 : CoverTree := CoverTree.reject 67
def tree073_68 : CoverTree := CoverTree.split [tree073_13,tree073_65,tree073_66,tree073_67,tree073_14,tree073_14]
def tree073_69 : CoverTree := CoverTree.reject 68
def tree073_70 : CoverTree := CoverTree.reject 69
def tree073_71 : CoverTree := CoverTree.split [tree073_16,tree073_69,tree073_70,tree073_14,tree073_14,tree073_14]
def tree073_72 : CoverTree := CoverTree.split [tree073_55,tree073_14,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_73 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_68,tree073_71,tree073_72,tree073_14]
def tree073_74 : CoverTree := CoverTree.split [tree073_13,tree073_65,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_75 : CoverTree := CoverTree.reject 70
def tree073_76 : CoverTree := CoverTree.split [tree073_16,tree073_75,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_77 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_74,tree073_76,tree073_72,tree073_14]
def tree073_78 : CoverTree := CoverTree.split [tree073_7,tree073_63,tree073_64,tree073_73,tree073_77,tree073_18]
def tree073_79 : CoverTree := CoverTree.reject 47
def tree073_80 : CoverTree := CoverTree.reject 2
def tree073_81 : CoverTree := CoverTree.split [tree073_80,tree073_80,tree073_80,tree073_14,tree073_14,tree073_14]
def tree073_82 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_79,tree073_81,tree073_81,tree073_81]
def tree073_83 : CoverTree := CoverTree.reject 71
def tree073_84 : CoverTree := CoverTree.reject 72
def tree073_85 : CoverTree := CoverTree.split [tree073_13,tree073_83,tree073_84,tree073_14,tree073_14,tree073_14]
def tree073_86 : CoverTree := CoverTree.reject 73
def tree073_87 : CoverTree := CoverTree.split [tree073_16,tree073_86,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_88 : CoverTree := CoverTree.reject 74
def tree073_89 : CoverTree := CoverTree.split [tree073_35,tree073_88,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_90 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_85,tree073_87,tree073_89,tree073_14]
def tree073_91 : CoverTree := CoverTree.reject 75
def tree073_92 : CoverTree := CoverTree.split [tree073_13,tree073_91,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_93 : CoverTree := CoverTree.reject 76
def tree073_94 : CoverTree := CoverTree.split [tree073_93,tree073_14,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_95 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_92,tree073_17,tree073_94,tree073_14]
def tree073_96 : CoverTree := CoverTree.split [tree073_24,tree073_82,tree073_90,tree073_95,tree073_18,tree073_18]
def tree073_97 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_81,tree073_81,tree073_81,tree073_81]
def tree073_98 : CoverTree := CoverTree.split [tree073_31,tree073_97,tree073_37,tree073_18,tree073_18,tree073_18]
def tree073_99 : CoverTree := CoverTree.split [tree073_40,tree073_46,tree073_62,tree073_78,tree073_96,tree073_98]
def tree073_100 : CoverTree := CoverTree.split [tree073_0,tree073_1,tree073_2,tree073_3,tree073_39,tree073_99]
def tree073_101 : CoverTree := CoverTree.reject 12
def tree073_102 : CoverTree := CoverTree.reject 39
def tree073_103 : CoverTree := CoverTree.reject 35
def tree073_104 : CoverTree := CoverTree.reject 32
def tree073_105 : CoverTree := CoverTree.reject 5
def tree073_106 : CoverTree := CoverTree.reject 120
def tree073_107 : CoverTree := CoverTree.reject 91
def tree073_108 : CoverTree := CoverTree.reject 229
def tree073_109 : CoverTree := CoverTree.reject 230
def tree073_110 : CoverTree := CoverTree.split [tree073_13,tree073_108,tree073_109,tree073_14,tree073_14,tree073_14]
def tree073_111 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_110,tree073_17,tree073_14,tree073_14]
def tree073_112 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_106,tree073_107,tree073_18,tree073_111]
def tree073_113 : CoverTree := CoverTree.split [tree073_101,tree073_101,tree073_102,tree073_103,tree073_104,tree073_112]
def tree073_114 : CoverTree := CoverTree.reject 23
def tree073_115 : CoverTree := CoverTree.reject 59
def tree073_116 : CoverTree := CoverTree.reject 283
def tree073_117 : CoverTree := CoverTree.reject 180
def tree073_118 : CoverTree := CoverTree.reject 131
def tree073_119 : CoverTree := CoverTree.reject 95
def tree073_120 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_116,tree073_117,tree073_118,tree073_119]
def tree073_121 : CoverTree := CoverTree.reject 152
def tree073_122 : CoverTree := CoverTree.reject 121
def tree073_123 : CoverTree := CoverTree.reject 106
def tree073_124 : CoverTree := CoverTree.reject 236
def tree073_125 : CoverTree := CoverTree.reject 309
def tree073_126 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_124,tree073_125,tree073_14,tree073_14]
def tree073_127 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_121,tree073_122,tree073_123,tree073_126]
def tree073_128 : CoverTree := CoverTree.reject 111
def tree073_129 : CoverTree := CoverTree.reject 122
def tree073_130 : CoverTree := CoverTree.reject 92
def tree073_131 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_128,tree073_129,tree073_130,tree073_18]
def tree073_132 : CoverTree := CoverTree.reject 310
def tree073_133 : CoverTree := CoverTree.reject 237
def tree073_134 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_132,tree073_133,tree073_36,tree073_14]
def tree073_135 : CoverTree := CoverTree.reject 238
def tree073_136 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_135,tree073_17,tree073_14,tree073_14]
def tree073_137 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_134,tree073_136,tree073_18,tree073_18]
def tree073_138 : CoverTree := CoverTree.split [tree073_114,tree073_115,tree073_120,tree073_127,tree073_131,tree073_137]
def tree073_139 : CoverTree := CoverTree.reject 24
def tree073_140 : CoverTree := CoverTree.reject 284
def tree073_141 : CoverTree := CoverTree.reject 285
def tree073_142 : CoverTree := CoverTree.reject 200
def tree073_143 : CoverTree := CoverTree.reject 159
def tree073_144 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_140,tree073_141,tree073_142,tree073_143]
def tree073_145 : CoverTree := CoverTree.reject 375
def tree073_146 : CoverTree := CoverTree.reject 201
def tree073_147 : CoverTree := CoverTree.reject 181
def tree073_148 : CoverTree := CoverTree.reject 132
def tree073_149 : CoverTree := CoverTree.reject 357
def tree073_150 : CoverTree := CoverTree.reject 235
def tree073_151 : CoverTree := CoverTree.split [tree073_16,tree073_150,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_152 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_149,tree073_151,tree073_60,tree073_14]
def tree073_153 : CoverTree := CoverTree.split [tree073_47,tree073_145,tree073_146,tree073_147,tree073_148,tree073_152]
def tree073_154 : CoverTree := CoverTree.reject 202
def tree073_155 : CoverTree := CoverTree.reject 153
def tree073_156 : CoverTree := CoverTree.reject 123
def tree073_157 : CoverTree := CoverTree.reject 311
def tree073_158 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_157,tree073_76,tree073_72,tree073_14]
def tree073_159 : CoverTree := CoverTree.reject 239
def tree073_160 : CoverTree := CoverTree.reject 240
def tree073_161 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_159,tree073_160,tree073_14,tree073_14]
def tree073_162 : CoverTree := CoverTree.split [tree073_7,tree073_154,tree073_155,tree073_156,tree073_158,tree073_161]
def tree073_163 : CoverTree := CoverTree.reject 171
def tree073_164 : CoverTree := CoverTree.reject 112
def tree073_165 : CoverTree := CoverTree.reject 312
def tree073_166 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_165,tree073_17,tree073_94,tree073_14]
def tree073_167 : CoverTree := CoverTree.split [tree073_24,tree073_163,tree073_164,tree073_166,tree073_18,tree073_18]
def tree073_168 : CoverTree := CoverTree.reject 154
def tree073_169 : CoverTree := CoverTree.reject 313
def tree073_170 : CoverTree := CoverTree.reject 241
def tree073_171 : CoverTree := CoverTree.reject 242
def tree073_172 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_169,tree073_170,tree073_171,tree073_14]
def tree073_173 : CoverTree := CoverTree.reject 243
def tree073_174 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_173,tree073_17,tree073_14,tree073_14]
def tree073_175 : CoverTree := CoverTree.split [tree073_31,tree073_168,tree073_172,tree073_174,tree073_18,tree073_18]
def tree073_176 : CoverTree := CoverTree.split [tree073_139,tree073_144,tree073_153,tree073_162,tree073_167,tree073_175]
def tree073_177 : CoverTree := CoverTree.reject 141
def tree073_178 : CoverTree := CoverTree.reject 286
def tree073_179 : CoverTree := CoverTree.reject 225
def tree073_180 : CoverTree := CoverTree.reject 203
def tree073_181 : CoverTree := CoverTree.reject 8
def tree073_182 : CoverTree := CoverTree.reject 358
def tree073_183 : CoverTree := CoverTree.reject 6
def tree073_184 : CoverTree := CoverTree.reject 394
def tree073_185 : CoverTree := CoverTree.split [tree073_183,tree073_183,tree073_184,tree073_14,tree073_14,tree073_14]
def tree073_186 : CoverTree := CoverTree.split [tree073_183,tree073_183,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_187 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_182,tree073_185,tree073_186]
def tree073_188 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_178,tree073_179,tree073_180,tree073_187]
def tree073_189 : CoverTree := CoverTree.reject 348
def tree073_190 : CoverTree := CoverTree.reject 204
def tree073_191 : CoverTree := CoverTree.reject 134
def tree073_192 : CoverTree := CoverTree.reject 0
def tree073_193 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_54,tree073_57,tree073_14]
def tree073_194 : CoverTree := CoverTree.reject 244
def tree073_195 : CoverTree := CoverTree.reject 245
def tree073_196 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_194,tree073_195,tree073_60,tree073_14]
def tree073_197 : CoverTree := CoverTree.split [tree073_47,tree073_189,tree073_190,tree073_191,tree073_193,tree073_196]
def tree073_198 : CoverTree := CoverTree.reject 205
def tree073_199 : CoverTree := CoverTree.reject 155
def tree073_200 : CoverTree := CoverTree.split [tree073_7,tree073_198,tree073_199,tree073_73,tree073_77,tree073_18]
def tree073_201 : CoverTree := CoverTree.reject 172
def tree073_202 : CoverTree := CoverTree.reject 314
def tree073_203 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_202,tree073_17,tree073_94,tree073_14]
def tree073_204 : CoverTree := CoverTree.split [tree073_24,tree073_201,tree073_90,tree073_203,tree073_18,tree073_18]
def tree073_205 : CoverTree := CoverTree.reject 359
def tree073_206 : CoverTree := CoverTree.reject 360
def tree073_207 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_205,tree073_206,tree073_81,tree073_81]
def tree073_208 : CoverTree := CoverTree.reject 315
def tree073_209 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_208,tree073_17,tree073_36,tree073_14]
def tree073_210 : CoverTree := CoverTree.split [tree073_31,tree073_207,tree073_209,tree073_18,tree073_18,tree073_18]
def tree073_211 : CoverTree := CoverTree.split [tree073_177,tree073_188,tree073_197,tree073_200,tree073_204,tree073_210]
def tree073_212 : CoverTree := CoverTree.reject 37
def tree073_213 : CoverTree := CoverTree.reject 38
def tree073_214 : CoverTree := CoverTree.reject 137
def tree073_215 : CoverTree := CoverTree.reject 81
def tree073_216 : CoverTree := CoverTree.reject 90
def tree073_217 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_214,tree073_215,tree073_216]
def tree073_218 : CoverTree := CoverTree.reject 182
def tree073_219 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_212,tree073_213,tree073_217,tree073_218]
def tree073_220 : CoverTree := CoverTree.reject 192
def tree073_221 : CoverTree := CoverTree.reject 96
def tree073_222 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_220,tree073_221,tree073_186]
def tree073_223 : CoverTree := CoverTree.reject 193
def tree073_224 : CoverTree := CoverTree.reject 4
def tree073_225 : CoverTree := CoverTree.split [tree073_224,tree073_224,tree073_224,tree073_224,tree073_224,tree073_14]
def tree073_226 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_223,tree073_225,tree073_186]
def tree073_227 : CoverTree := CoverTree.reject 31
def tree073_228 : CoverTree := CoverTree.reject 223
def tree073_229 : CoverTree := CoverTree.split [tree073_183,tree073_183,tree073_227,tree073_227,tree073_228,tree073_14]
def tree073_230 : CoverTree := CoverTree.split [tree073_183,tree073_183,tree073_227,tree073_227,tree073_14,tree073_14]
def tree073_231 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_229,tree073_230,tree073_186]
def tree073_232 : CoverTree := CoverTree.reject 98
def tree073_233 : CoverTree := CoverTree.split [tree073_183,tree073_183,tree073_232,tree073_14,tree073_14,tree073_14]
def tree073_234 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_233,tree073_186,tree073_186]
def tree073_235 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_222,tree073_226,tree073_231,tree073_234]
def tree073_236 : CoverTree := CoverTree.reject 349
def tree073_237 : CoverTree := CoverTree.reject 220
def tree073_238 : CoverTree := CoverTree.reject 26
def tree073_239 : CoverTree := CoverTree.reject 103
def tree073_240 : CoverTree := CoverTree.reject 104
def tree073_241 : CoverTree := CoverTree.reject 105
def tree073_242 : CoverTree := CoverTree.split [tree073_55,tree073_239,tree073_240,tree073_241,tree073_14,tree073_14]
def tree073_243 : CoverTree := CoverTree.reject 83
def tree073_244 : CoverTree := CoverTree.reject 84
def tree073_245 : CoverTree := CoverTree.split [tree073_243,tree073_244,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_246 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_237,tree073_238,tree073_242,tree073_245]
def tree073_247 : CoverTree := CoverTree.reject 221
def tree073_248 : CoverTree := CoverTree.reject 361
def tree073_249 : CoverTree := CoverTree.reject 85
def tree073_250 : CoverTree := CoverTree.reject 86
def tree073_251 : CoverTree := CoverTree.split [tree073_55,tree073_249,tree073_250,tree073_14,tree073_14,tree073_14]
def tree073_252 : CoverTree := CoverTree.reject 87
def tree073_253 : CoverTree := CoverTree.split [tree073_252,tree073_14,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_254 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_247,tree073_248,tree073_251,tree073_253]
def tree073_255 : CoverTree := CoverTree.reject 246
def tree073_256 : CoverTree := CoverTree.reject 247
def tree073_257 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_255,tree073_256,tree073_60,tree073_14]
def tree073_258 : CoverTree := CoverTree.split [tree073_47,tree073_236,tree073_246,tree073_254,tree073_58,tree073_257]
def tree073_259 : CoverTree := CoverTree.reject 206
def tree073_260 : CoverTree := CoverTree.reject 27
def tree073_261 : CoverTree := CoverTree.reject 62
def tree073_262 : CoverTree := CoverTree.reject 63
def tree073_263 : CoverTree := CoverTree.reject 64
def tree073_264 : CoverTree := CoverTree.split [tree073_16,tree073_261,tree073_262,tree073_263,tree073_14,tree073_14]
def tree073_265 : CoverTree := CoverTree.reject 65
def tree073_266 : CoverTree := CoverTree.split [tree073_55,tree073_265,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_267 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_260,tree073_264,tree073_266,tree073_14]
def tree073_268 : CoverTree := CoverTree.split [tree073_7,tree073_259,tree073_267,tree073_73,tree073_77,tree073_18]
def tree073_269 : CoverTree := CoverTree.reject 362
def tree073_270 : CoverTree := CoverTree.reject 316
def tree073_271 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_269,tree073_270,tree073_89,tree073_14]
def tree073_272 : CoverTree := CoverTree.split [tree073_24,tree073_82,tree073_271,tree073_95,tree073_18,tree073_18]
def tree073_273 : CoverTree := CoverTree.reject 363
def tree073_274 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_273,tree073_81,tree073_81,tree073_81]
def tree073_275 : CoverTree := CoverTree.reject 317
def tree073_276 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_275,tree073_17,tree073_36,tree073_14]
def tree073_277 : CoverTree := CoverTree.split [tree073_31,tree073_274,tree073_276,tree073_18,tree073_18,tree073_18]
def tree073_278 : CoverTree := CoverTree.split [tree073_219,tree073_235,tree073_258,tree073_268,tree073_272,tree073_277]
def tree073_279 : CoverTree := CoverTree.split [tree073_0,tree073_113,tree073_138,tree073_176,tree073_211,tree073_278]
def tree073_280 : CoverTree := CoverTree.reject 40
def tree073_281 : CoverTree := CoverTree.reject 207
def tree073_282 : CoverTree := CoverTree.reject 124
def tree073_283 : CoverTree := CoverTree.reject 107
def tree073_284 : CoverTree := CoverTree.reject 354
def tree073_285 : CoverTree := CoverTree.reject 355
def tree073_286 : CoverTree := CoverTree.reject 356
def tree073_287 : CoverTree := CoverTree.split [tree073_13,tree073_284,tree073_285,tree073_286,tree073_14,tree073_14]
def tree073_288 : CoverTree := CoverTree.reject 248
def tree073_289 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_287,tree073_288,tree073_14,tree073_14]
def tree073_290 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_281,tree073_282,tree073_283,tree073_289]
def tree073_291 : CoverTree := CoverTree.reject 113
def tree073_292 : CoverTree := CoverTree.reject 101
def tree073_293 : CoverTree := CoverTree.reject 93
def tree073_294 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_291,tree073_292,tree073_293,tree073_18]
def tree073_295 : CoverTree := CoverTree.reject 99
def tree073_296 : CoverTree := CoverTree.reject 249
def tree073_297 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_295,tree073_296,tree073_36,tree073_14]
def tree073_298 : CoverTree := CoverTree.reject 250
def tree073_299 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_298,tree073_17,tree073_14,tree073_14]
def tree073_300 : CoverTree := CoverTree.reject 251
def tree073_301 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_300,tree073_17,tree073_14,tree073_14]
def tree073_302 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_297,tree073_299,tree073_301,tree073_111]
def tree073_303 : CoverTree := CoverTree.split [tree073_101,tree073_101,tree073_280,tree073_290,tree073_294,tree073_302]
def tree073_304 : CoverTree := CoverTree.reject 117
def tree073_305 : CoverTree := CoverTree.reject 287
def tree073_306 : CoverTree := CoverTree.reject 288
def tree073_307 : CoverTree := CoverTree.reject 150
def tree073_308 : CoverTree := CoverTree.reject 318
def tree073_309 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_307,tree073_308,tree073_186]
def tree073_310 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_304,tree073_305,tree073_306,tree073_309]
def tree073_311 : CoverTree := CoverTree.reject 289
def tree073_312 : CoverTree := CoverTree.reject 183
def tree073_313 : CoverTree := CoverTree.reject 133
def tree073_314 : CoverTree := CoverTree.reject 252
def tree073_315 : CoverTree := CoverTree.reject 253
def tree073_316 : CoverTree := CoverTree.reject 254
def tree073_317 : CoverTree := CoverTree.reject 307
def tree073_318 : CoverTree := CoverTree.split [tree073_14,tree073_317,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_319 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_314,tree073_315,tree073_316,tree073_318]
def tree073_320 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_311,tree073_312,tree073_313,tree073_319]
def tree073_321 : CoverTree := CoverTree.reject 156
def tree073_322 : CoverTree := CoverTree.reject 125
def tree073_323 : CoverTree := CoverTree.reject 108
def tree073_324 : CoverTree := CoverTree.reject 255
def tree073_325 : CoverTree := CoverTree.reject 319
def tree073_326 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_324,tree073_325,tree073_14,tree073_14]
def tree073_327 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_321,tree073_322,tree073_323,tree073_326]
def tree073_328 : CoverTree := CoverTree.reject 114
def tree073_329 : CoverTree := CoverTree.reject 100
def tree073_330 : CoverTree := CoverTree.reject 256
def tree073_331 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_329,tree073_330,tree073_94,tree073_14]
def tree073_332 : CoverTree := CoverTree.reject 257
def tree073_333 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_332,tree073_17,tree073_14,tree073_14]
def tree073_334 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_328,tree073_331,tree073_333,tree073_18]
def tree073_335 : CoverTree := CoverTree.reject 320
def tree073_336 : CoverTree := CoverTree.reject 258
def tree073_337 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_335,tree073_336,tree073_36,tree073_14]
def tree073_338 : CoverTree := CoverTree.reject 259
def tree073_339 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_338,tree073_17,tree073_14,tree073_14]
def tree073_340 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_337,tree073_339,tree073_18,tree073_18]
def tree073_341 : CoverTree := CoverTree.split [tree073_114,tree073_310,tree073_320,tree073_327,tree073_334,tree073_340]
def tree073_342 : CoverTree := CoverTree.reject 290
def tree073_343 : CoverTree := CoverTree.reject 291
def tree073_344 : CoverTree := CoverTree.reject 208
def tree073_345 : CoverTree := CoverTree.reject 364
def tree073_346 : CoverTree := CoverTree.reject 321
def tree073_347 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_345,tree073_346,tree073_186]
def tree073_348 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_342,tree073_343,tree073_344,tree073_347]
def tree073_349 : CoverTree := CoverTree.reject 376
def tree073_350 : CoverTree := CoverTree.reject 209
def tree073_351 : CoverTree := CoverTree.reject 184
def tree073_352 : CoverTree := CoverTree.reject 322
def tree073_353 : CoverTree := CoverTree.reject 323
def tree073_354 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_352,tree073_353,tree073_14]
def tree073_355 : CoverTree := CoverTree.reject 365
def tree073_356 : CoverTree := CoverTree.reject 324
def tree073_357 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_355,tree073_356,tree073_60,tree073_14]
def tree073_358 : CoverTree := CoverTree.split [tree073_47,tree073_349,tree073_350,tree073_351,tree073_354,tree073_357]
def tree073_359 : CoverTree := CoverTree.reject 210
def tree073_360 : CoverTree := CoverTree.reject 179
def tree073_361 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_260,tree073_360,tree073_266,tree073_14]
def tree073_362 : CoverTree := CoverTree.reject 325
def tree073_363 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_362,tree073_76,tree073_72,tree073_14]
def tree073_364 : CoverTree := CoverTree.split [tree073_7,tree073_359,tree073_361,tree073_73,tree073_363,tree073_18]
def tree073_365 : CoverTree := CoverTree.reject 173
def tree073_366 : CoverTree := CoverTree.reject 151
def tree073_367 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_366,tree073_87,tree073_89,tree073_14]
def tree073_368 : CoverTree := CoverTree.reject 326
def tree073_369 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_368,tree073_17,tree073_94,tree073_14]
def tree073_370 : CoverTree := CoverTree.split [tree073_24,tree073_365,tree073_367,tree073_369,tree073_18,tree073_18]
def tree073_371 : CoverTree := CoverTree.reject 382
def tree073_372 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_371,tree073_81,tree073_81,tree073_81]
def tree073_373 : CoverTree := CoverTree.split [tree073_31,tree073_372,tree073_37,tree073_18,tree073_18,tree073_18]
def tree073_374 : CoverTree := CoverTree.split [tree073_139,tree073_348,tree073_358,tree073_364,tree073_370,tree073_373]
def tree073_375 : CoverTree := CoverTree.reject 142
def tree073_376 : CoverTree := CoverTree.reject 292
def tree073_377 : CoverTree := CoverTree.reject 226
def tree073_378 : CoverTree := CoverTree.reject 211
def tree073_379 : CoverTree := CoverTree.reject 366
def tree073_380 : CoverTree := CoverTree.reject 395
def tree073_381 : CoverTree := CoverTree.split [tree073_183,tree073_183,tree073_380,tree073_14,tree073_14,tree073_14]
def tree073_382 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_181,tree073_379,tree073_381,tree073_186]
def tree073_383 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_376,tree073_377,tree073_378,tree073_382]
def tree073_384 : CoverTree := CoverTree.reject 350
def tree073_385 : CoverTree := CoverTree.reject 212
def tree073_386 : CoverTree := CoverTree.reject 367
def tree073_387 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_386,tree073_251,tree073_253]
def tree073_388 : CoverTree := CoverTree.reject 260
def tree073_389 : CoverTree := CoverTree.reject 261
def tree073_390 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_388,tree073_389,tree073_60,tree073_14]
def tree073_391 : CoverTree := CoverTree.split [tree073_47,tree073_384,tree073_385,tree073_387,tree073_193,tree073_390]
def tree073_392 : CoverTree := CoverTree.reject 213
def tree073_393 : CoverTree := CoverTree.reject 383
def tree073_394 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_260,tree073_393,tree073_266,tree073_14]
def tree073_395 : CoverTree := CoverTree.split [tree073_7,tree073_392,tree073_394,tree073_73,tree073_77,tree073_18]
def tree073_396 : CoverTree := CoverTree.reject 368
def tree073_397 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_79,tree073_396,tree073_81,tree073_81]
def tree073_398 : CoverTree := CoverTree.split [tree073_24,tree073_397,tree073_90,tree073_95,tree073_18,tree073_18]
def tree073_399 : CoverTree := CoverTree.reject 327
def tree073_400 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_399,tree073_17,tree073_36,tree073_14]
def tree073_401 : CoverTree := CoverTree.split [tree073_31,tree073_97,tree073_400,tree073_18,tree073_18,tree073_18]
def tree073_402 : CoverTree := CoverTree.split [tree073_375,tree073_383,tree073_391,tree073_395,tree073_398,tree073_401]
def tree073_403 : CoverTree := CoverTree.reject 185
def tree073_404 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_212,tree073_213,tree073_217,tree073_403]
def tree073_405 : CoverTree := CoverTree.reject 194
def tree073_406 : CoverTree := CoverTree.reject 52
def tree073_407 : CoverTree := CoverTree.reject 53
def tree073_408 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_405,tree073_406,tree073_407,tree073_81]
def tree073_409 : CoverTree := CoverTree.reject 165
def tree073_410 : CoverTree := CoverTree.reject 166
def tree073_411 : CoverTree := CoverTree.split [tree073_16,tree073_409,tree073_410,tree073_14,tree073_14,tree073_14]
def tree073_412 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_247,tree073_411,tree073_251,tree073_253]
def tree073_413 : CoverTree := CoverTree.split [tree073_47,tree073_408,tree073_246,tree073_412,tree073_58,tree073_61]
def tree073_414 : CoverTree := CoverTree.reject 43
def tree073_415 : CoverTree := CoverTree.reject 44
def tree073_416 : CoverTree := CoverTree.split [tree073_12,tree073_12,tree073_414,tree073_415,tree073_81,tree073_81]
def tree073_417 : CoverTree := CoverTree.split [tree073_7,tree073_416,tree073_267,tree073_73,tree073_77,tree073_18]
def tree073_418 : CoverTree := CoverTree.split [tree073_404,tree073_235,tree073_413,tree073_417,tree073_96,tree073_98]
def tree073_419 : CoverTree := CoverTree.split [tree073_0,tree073_303,tree073_341,tree073_374,tree073_402,tree073_418]
def tree073_420 : CoverTree := CoverTree.reject 198
def tree073_421 : CoverTree := CoverTree.reject 148
def tree073_422 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_238,tree073_420,tree073_421]
def tree073_423 : CoverTree := CoverTree.reject 227
def tree073_424 : CoverTree := CoverTree.reject 160
def tree073_425 : CoverTree := CoverTree.reject 17
def tree073_426 : CoverTree := CoverTree.reject 262
def tree073_427 : CoverTree := CoverTree.reject 263
def tree073_428 : CoverTree := CoverTree.reject 264
def tree073_429 : CoverTree := CoverTree.reject 353
def tree073_430 : CoverTree := CoverTree.split [tree073_14,tree073_429,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_431 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_426,tree073_427,tree073_428,tree073_430]
def tree073_432 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_422,tree073_423,tree073_424,tree073_431]
def tree073_433 : CoverTree := CoverTree.reject 214
def tree073_434 : CoverTree := CoverTree.reject 126
def tree073_435 : CoverTree := CoverTree.reject 109
def tree073_436 : CoverTree := CoverTree.reject 20
def tree073_437 : CoverTree := CoverTree.reject 265
def tree073_438 : CoverTree := CoverTree.reject 266
def tree073_439 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_437,tree073_438,tree073_14,tree073_14]
def tree073_440 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_433,tree073_434,tree073_435,tree073_439]
def tree073_441 : CoverTree := CoverTree.reject 115
def tree073_442 : CoverTree := CoverTree.reject 10
def tree073_443 : CoverTree := CoverTree.reject 149
def tree073_444 : CoverTree := CoverTree.reject 267
def tree073_445 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_443,tree073_444,tree073_94,tree073_14]
def tree073_446 : CoverTree := CoverTree.reject 129
def tree073_447 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_446,tree073_17,tree073_14,tree073_14]
def tree073_448 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_449 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_441,tree073_445,tree073_447,tree073_448]
def tree073_450 : CoverTree := CoverTree.reject 268
def tree073_451 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_295,tree073_450,tree073_36,tree073_14]
def tree073_452 : CoverTree := CoverTree.reject 269
def tree073_453 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_452,tree073_17,tree073_14,tree073_14]
def tree073_454 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_110,tree073_17,tree073_14,tree073_14]
def tree073_455 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_451,tree073_453,tree073_448,tree073_454]
def tree073_456 : CoverTree := CoverTree.split [tree073_101,tree073_101,tree073_432,tree073_440,tree073_449,tree073_455]
def tree073_457 : CoverTree := CoverTree.reject 293
def tree073_458 : CoverTree := CoverTree.reject 294
def tree073_459 : CoverTree := CoverTree.reject 328
def tree073_460 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_307,tree073_459,tree073_186]
def tree073_461 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_304,tree073_457,tree073_458,tree073_460]
def tree073_462 : CoverTree := CoverTree.reject 295
def tree073_463 : CoverTree := CoverTree.reject 186
def tree073_464 : CoverTree := CoverTree.reject 270
def tree073_465 : CoverTree := CoverTree.reject 271
def tree073_466 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_464,tree073_465,tree073_60,tree073_318]
def tree073_467 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_462,tree073_463,tree073_193,tree073_466]
def tree073_468 : CoverTree := CoverTree.reject 157
def tree073_469 : CoverTree := CoverTree.reject 199
def tree073_470 : CoverTree := CoverTree.reject 168
def tree073_471 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_469,tree073_470,tree073_72,tree073_14]
def tree073_472 : CoverTree := CoverTree.reject 50
def tree073_473 : CoverTree := CoverTree.reject 329
def tree073_474 : CoverTree := CoverTree.split [tree073_472,tree073_472,tree073_473,tree073_76,tree073_72,tree073_14]
def tree073_475 : CoverTree := CoverTree.reject 82
def tree073_476 : CoverTree := CoverTree.reject 169
def tree073_477 : CoverTree := CoverTree.reject 272
def tree073_478 : CoverTree := CoverTree.reject 231
def tree073_479 : CoverTree := CoverTree.split [tree073_16,tree073_478,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_480 : CoverTree := CoverTree.split [tree073_475,tree073_476,tree073_477,tree073_479,tree073_14,tree073_14]
def tree073_481 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_468,tree073_471,tree073_474,tree073_480]
def tree073_482 : CoverTree := CoverTree.reject 170
def tree073_483 : CoverTree := CoverTree.reject 330
def tree073_484 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_482,tree073_483,tree073_89,tree073_14]
def tree073_485 : CoverTree := CoverTree.reject 273
def tree073_486 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_329,tree073_485,tree073_94,tree073_14]
def tree073_487 : CoverTree := CoverTree.split [tree073_472,tree073_472,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_488 : CoverTree := CoverTree.reject 7
def tree073_489 : CoverTree := CoverTree.reject 28
def tree073_490 : CoverTree := CoverTree.reject 25
def tree073_491 : CoverTree := CoverTree.split [tree073_488,tree073_488,tree073_489,tree073_490,tree073_14,tree073_14]
def tree073_492 : CoverTree := CoverTree.split [tree073_488,tree073_488,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_493 : CoverTree := CoverTree.split [tree073_491,tree073_492,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_494 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_484,tree073_486,tree073_487,tree073_493]
def tree073_495 : CoverTree := CoverTree.reject 55
def tree073_496 : CoverTree := CoverTree.reject 369
def tree073_497 : CoverTree := CoverTree.split [tree073_495,tree073_496,tree073_34,tree073_17,tree073_36,tree073_14]
def tree073_498 : CoverTree := CoverTree.reject 56
def tree073_499 : CoverTree := CoverTree.reject 331
def tree073_500 : CoverTree := CoverTree.reject 274
def tree073_501 : CoverTree := CoverTree.split [tree073_498,tree073_499,tree073_500,tree073_17,tree073_14,tree073_14]
def tree073_502 : CoverTree := CoverTree.reject 345
def tree073_503 : CoverTree := CoverTree.split [tree073_502,tree073_492,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_504 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_497,tree073_501,tree073_503,tree073_493]
def tree073_505 : CoverTree := CoverTree.split [tree073_114,tree073_461,tree073_467,tree073_481,tree073_494,tree073_504]
def tree073_506 : CoverTree := CoverTree.reject 296
def tree073_507 : CoverTree := CoverTree.reject 297
def tree073_508 : CoverTree := CoverTree.reject 215
def tree073_509 : CoverTree := CoverTree.reject 370
def tree073_510 : CoverTree := CoverTree.reject 332
def tree073_511 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_509,tree073_510,tree073_186]
def tree073_512 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_506,tree073_507,tree073_508,tree073_511]
def tree073_513 : CoverTree := CoverTree.reject 377
def tree073_514 : CoverTree := CoverTree.reject 216
def tree073_515 : CoverTree := CoverTree.reject 79
def tree073_516 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_515,tree073_251,tree073_253]
def tree073_517 : CoverTree := CoverTree.reject 371
def tree073_518 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_517,tree073_151,tree073_60,tree073_14]
def tree073_519 : CoverTree := CoverTree.split [tree073_47,tree073_513,tree073_514,tree073_516,tree073_193,tree073_518]
def tree073_520 : CoverTree := CoverTree.reject 217
def tree073_521 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_260,tree073_360,tree073_266,tree073_14]
def tree073_522 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_68,tree073_71,tree073_72,tree073_14]
def tree073_523 : CoverTree := CoverTree.reject 333
def tree073_524 : CoverTree := CoverTree.split [tree073_472,tree073_472,tree073_523,tree073_76,tree073_72,tree073_14]
def tree073_525 : CoverTree := CoverTree.reject 146
def tree073_526 : CoverTree := CoverTree.split [tree073_488,tree073_488,tree073_525,tree073_14,tree073_14,tree073_14]
def tree073_527 : CoverTree := CoverTree.split [tree073_475,tree073_526,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_528 : CoverTree := CoverTree.split [tree073_7,tree073_520,tree073_521,tree073_522,tree073_524,tree073_527]
def tree073_529 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_20,tree073_21,tree073_22,tree073_23]
def tree073_530 : CoverTree := CoverTree.reject 372
def tree073_531 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_79,tree073_530,tree073_81,tree073_81]
def tree073_532 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_366,tree073_87,tree073_89,tree073_14]
def tree073_533 : CoverTree := CoverTree.reject 334
def tree073_534 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_533,tree073_17,tree073_94,tree073_14]
def tree073_535 : CoverTree := CoverTree.split [tree073_529,tree073_531,tree073_532,tree073_534,tree073_487,tree073_493]
def tree073_536 : CoverTree := CoverTree.reject 80
def tree073_537 : CoverTree := CoverTree.reject 54
def tree073_538 : CoverTree := CoverTree.split [tree073_536,tree073_537,tree073_20,tree073_21,tree073_29,tree073_30]
def tree073_539 : CoverTree := CoverTree.reject 60
def tree073_540 : CoverTree := CoverTree.reject 346
def tree073_541 : CoverTree := CoverTree.reject 308
def tree073_542 : CoverTree := CoverTree.split [tree073_80,tree073_80,tree073_80,tree073_541,tree073_14,tree073_14]
def tree073_543 : CoverTree := CoverTree.split [tree073_539,tree073_540,tree073_542,tree073_81,tree073_81,tree073_81]
def tree073_544 : CoverTree := CoverTree.reject 128
def tree073_545 : CoverTree := CoverTree.split [tree073_488,tree073_488,tree073_544,tree073_14,tree073_14,tree073_14]
def tree073_546 : CoverTree := CoverTree.split [tree073_495,tree073_545,tree073_34,tree073_17,tree073_36,tree073_14]
def tree073_547 : CoverTree := CoverTree.split [tree073_498,tree073_492,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_548 : CoverTree := CoverTree.reject 147
def tree073_549 : CoverTree := CoverTree.split [tree073_488,tree073_488,tree073_489,tree073_490,tree073_14,tree073_548]
def tree073_550 : CoverTree := CoverTree.split [tree073_549,tree073_492,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_551 : CoverTree := CoverTree.split [tree073_538,tree073_543,tree073_546,tree073_547,tree073_550,tree073_493]
def tree073_552 : CoverTree := CoverTree.split [tree073_139,tree073_512,tree073_519,tree073_528,tree073_535,tree073_551]
def tree073_553 : CoverTree := CoverTree.reject 298
def tree073_554 : CoverTree := CoverTree.reject 187
def tree073_555 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_212,tree073_213,tree073_553,tree073_554]
def tree073_556 : CoverTree := CoverTree.reject 299
def tree073_557 : CoverTree := CoverTree.reject 19
def tree073_558 : CoverTree := CoverTree.reject 392
def tree073_559 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_557,tree073_558,tree073_186]
def tree073_560 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_557,tree073_230,tree073_186]
def tree073_561 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_233,tree073_186,tree073_186]
def tree073_562 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_556,tree073_559,tree073_560,tree073_561]
def tree073_563 : CoverTree := CoverTree.reject 351
def tree073_564 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_238,tree073_242,tree073_245]
def tree073_565 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_411,tree073_251,tree073_253]
def tree073_566 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_15,tree073_17,tree073_60,tree073_14]
def tree073_567 : CoverTree := CoverTree.split [tree073_47,tree073_563,tree073_564,tree073_565,tree073_193,tree073_566]
def tree073_568 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_414,tree073_415,tree073_81,tree073_81]
def tree073_569 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_260,tree073_264,tree073_266,tree073_14]
def tree073_570 : CoverTree := CoverTree.reject 195
def tree073_571 : CoverTree := CoverTree.reject 347
def tree073_572 : CoverTree := CoverTree.split [tree073_570,tree073_571,tree073_74,tree073_76,tree073_72,tree073_14]
def tree073_573 : CoverTree := CoverTree.split [tree073_7,tree073_568,tree073_569,tree073_522,tree073_572,tree073_527]
def tree073_574 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_79,tree073_81,tree073_81,tree073_81]
def tree073_575 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_85,tree073_87,tree073_89,tree073_14]
def tree073_576 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_92,tree073_17,tree073_94,tree073_14]
def tree073_577 : CoverTree := CoverTree.reject 140
def tree073_578 : CoverTree := CoverTree.reject 162
def tree073_579 : CoverTree := CoverTree.split [tree073_488,tree073_488,tree073_578,tree073_14,tree073_14,tree073_14]
def tree073_580 : CoverTree := CoverTree.split [tree073_577,tree073_579,tree073_15,tree073_17,tree073_14,tree073_14]
def tree073_581 : CoverTree := CoverTree.split [tree073_529,tree073_574,tree073_575,tree073_576,tree073_580,tree073_493]
def tree073_582 : CoverTree := CoverTree.reject 393
def tree073_583 : CoverTree := CoverTree.split [tree073_539,tree073_582,tree073_81,tree073_81,tree073_81,tree073_81]
def tree073_584 : CoverTree := CoverTree.split [tree073_538,tree073_583,tree073_546,tree073_547,tree073_550,tree073_493]
def tree073_585 : CoverTree := CoverTree.split [tree073_555,tree073_562,tree073_567,tree073_573,tree073_581,tree073_584]
def tree073_586 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_214,tree073_215,tree073_216]
def tree073_587 : CoverTree := CoverTree.reject 188
def tree073_588 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_212,tree073_213,tree073_586,tree073_587]
def tree073_589 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_220,tree073_221,tree073_186]
def tree073_590 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_223,tree073_225,tree073_186]
def tree073_591 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_229,tree073_230,tree073_186]
def tree073_592 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_589,tree073_590,tree073_591,tree073_561]
def tree073_593 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_405,tree073_406,tree073_407,tree073_81]
def tree073_594 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_237,tree073_238,tree073_242,tree073_245]
def tree073_595 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_247,tree073_411,tree073_251,tree073_253]
def tree073_596 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_52,tree073_54,tree073_57,tree073_14]
def tree073_597 : CoverTree := CoverTree.split [tree073_47,tree073_593,tree073_594,tree073_595,tree073_596,tree073_566]
def tree073_598 : CoverTree := CoverTree.reject 337
def tree073_599 : CoverTree := CoverTree.split [tree073_539,tree073_598,tree073_414,tree073_415,tree073_81,tree073_81]
def tree073_600 : CoverTree := CoverTree.reject 338
def tree073_601 : CoverTree := CoverTree.split [tree073_495,tree073_600,tree073_260,tree073_264,tree073_266,tree073_14]
def tree073_602 : CoverTree := CoverTree.reject 339
def tree073_603 : CoverTree := CoverTree.split [tree073_498,tree073_602,tree073_68,tree073_71,tree073_72,tree073_14]
def tree073_604 : CoverTree := CoverTree.reject 34
def tree073_605 : CoverTree := CoverTree.split [tree073_488,tree073_488,tree073_604,tree073_604,tree073_604,tree073_14]
def tree073_606 : CoverTree := CoverTree.split [tree073_570,tree073_605,tree073_74,tree073_76,tree073_72,tree073_14]
def tree073_607 : CoverTree := CoverTree.split [tree073_7,tree073_599,tree073_601,tree073_603,tree073_606,tree073_527]
def tree073_608 : CoverTree := CoverTree.split [tree073_536,tree073_537,tree073_20,tree073_21,tree073_22,tree073_23]
def tree073_609 : CoverTree := CoverTree.reject 340
def tree073_610 : CoverTree := CoverTree.split [tree073_539,tree073_609,tree073_79,tree073_81,tree073_81,tree073_81]
def tree073_611 : CoverTree := CoverTree.reject 163
def tree073_612 : CoverTree := CoverTree.split [tree073_495,tree073_611,tree073_85,tree073_87,tree073_89,tree073_14]
def tree073_613 : CoverTree := CoverTree.reject 342
def tree073_614 : CoverTree := CoverTree.split [tree073_488,tree073_488,tree073_578,tree073_613,tree073_14,tree073_14]
def tree073_615 : CoverTree := CoverTree.split [tree073_498,tree073_614,tree073_92,tree073_17,tree073_94,tree073_14]
def tree073_616 : CoverTree := CoverTree.split [tree073_608,tree073_610,tree073_612,tree073_615,tree073_580,tree073_493]
def tree073_617 : CoverTree := CoverTree.reject 138
def tree073_618 : CoverTree := CoverTree.reject 139
def tree073_619 : CoverTree := CoverTree.split [tree073_80,tree073_80,tree073_80,tree073_617,tree073_618,tree073_14]
def tree073_620 : CoverTree := CoverTree.split [tree073_539,tree073_619,tree073_81,tree073_81,tree073_81,tree073_81]
def tree073_621 : CoverTree := CoverTree.split [tree073_538,tree073_620,tree073_546,tree073_547,tree073_550,tree073_493]
def tree073_622 : CoverTree := CoverTree.split [tree073_588,tree073_592,tree073_597,tree073_607,tree073_616,tree073_621]
def tree073_623 : CoverTree := CoverTree.split [tree073_0,tree073_456,tree073_505,tree073_552,tree073_585,tree073_622]
def tree073_624 : CoverTree := CoverTree.reject 228
def tree073_625 : CoverTree := CoverTree.reject 161
def tree073_626 : CoverTree := CoverTree.reject 275
def tree073_627 : CoverTree := CoverTree.reject 276
def tree073_628 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_626,tree073_627,tree073_60,tree073_430]
def tree073_629 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_422,tree073_624,tree073_625,tree073_628]
def tree073_630 : CoverTree := CoverTree.reject 218
def tree073_631 : CoverTree := CoverTree.reject 127
def tree073_632 : CoverTree := CoverTree.reject 177
def tree073_633 : CoverTree := CoverTree.reject 178
def tree073_634 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_632,tree073_633,tree073_72,tree073_14]
def tree073_635 : CoverTree := CoverTree.reject 379
def tree073_636 : CoverTree := CoverTree.reject 380
def tree073_637 : CoverTree := CoverTree.split [tree073_16,tree073_635,tree073_636,tree073_14,tree073_14,tree073_14]
def tree073_638 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_287,tree073_637,tree073_14,tree073_14]
def tree073_639 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_630,tree073_631,tree073_634,tree073_638]
def tree073_640 : CoverTree := CoverTree.reject 116
def tree073_641 : CoverTree := CoverTree.reject 277
def tree073_642 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_443,tree073_641,tree073_94,tree073_14]
def tree073_643 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_640,tree073_642,tree073_447,tree073_448]
def tree073_644 : CoverTree := CoverTree.split [tree073_436,tree073_436,tree073_295,tree073_17,tree073_36,tree073_14]
def tree073_645 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_644,tree073_448,tree073_448,tree073_454]
def tree073_646 : CoverTree := CoverTree.split [tree073_101,tree073_101,tree073_629,tree073_639,tree073_643,tree073_645]
def tree073_647 : CoverTree := CoverTree.reject 300
def tree073_648 : CoverTree := CoverTree.reject 301
def tree073_649 : CoverTree := CoverTree.reject 335
def tree073_650 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_307,tree073_649,tree073_186]
def tree073_651 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_304,tree073_647,tree073_648,tree073_650]
def tree073_652 : CoverTree := CoverTree.reject 302
def tree073_653 : CoverTree := CoverTree.reject 78
def tree073_654 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_653,tree073_251,tree073_253]
def tree073_655 : CoverTree := CoverTree.reject 278
def tree073_656 : CoverTree := CoverTree.reject 381
def tree073_657 : CoverTree := CoverTree.split [tree073_16,tree073_656,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_658 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_655,tree073_657,tree073_60,tree073_318]
def tree073_659 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_652,tree073_654,tree073_193,tree073_658]
def tree073_660 : CoverTree := CoverTree.reject 282
def tree073_661 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_260,tree073_660,tree073_266,tree073_14]
def tree073_662 : CoverTree := CoverTree.reject 336
def tree073_663 : CoverTree := CoverTree.split [tree073_472,tree073_472,tree073_662,tree073_76,tree073_72,tree073_14]
def tree073_664 : CoverTree := CoverTree.split [tree073_475,tree073_476,tree073_15,tree073_479,tree073_14,tree073_14]
def tree073_665 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_661,tree073_471,tree073_663,tree073_664]
def tree073_666 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_482,tree073_87,tree073_89,tree073_14]
def tree073_667 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_329,tree073_17,tree073_94,tree073_14]
def tree073_668 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_666,tree073_667,tree073_487,tree073_493]
def tree073_669 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_546,tree073_547,tree073_503,tree073_493]
def tree073_670 : CoverTree := CoverTree.split [tree073_114,tree073_651,tree073_659,tree073_665,tree073_668,tree073_669]
def tree073_671 : CoverTree := CoverTree.reject 303
def tree073_672 : CoverTree := CoverTree.reject 304
def tree073_673 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_671,tree073_672,tree073_560,tree073_561]
def tree073_674 : CoverTree := CoverTree.reject 378
def tree073_675 : CoverTree := CoverTree.reject 219
def tree073_676 : CoverTree := CoverTree.reject 233
def tree073_677 : CoverTree := CoverTree.reject 234
def tree073_678 : CoverTree := CoverTree.split [tree073_13,tree073_676,tree073_677,tree073_14,tree073_14,tree073_14]
def tree073_679 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_678,tree073_151,tree073_60,tree073_14]
def tree073_680 : CoverTree := CoverTree.split [tree073_47,tree073_674,tree073_675,tree073_516,tree073_193,tree073_679]
def tree073_681 : CoverTree := CoverTree.split [tree073_472,tree073_472,tree073_74,tree073_76,tree073_72,tree073_14]
def tree073_682 : CoverTree := CoverTree.split [tree073_7,tree073_568,tree073_521,tree073_522,tree073_681,tree073_527]
def tree073_683 : CoverTree := CoverTree.reject 373
def tree073_684 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_79,tree073_683,tree073_81,tree073_81]
def tree073_685 : CoverTree := CoverTree.split [tree073_529,tree073_684,tree073_532,tree073_576,tree073_487,tree073_493]
def tree073_686 : CoverTree := CoverTree.split [tree073_139,tree073_673,tree073_680,tree073_682,tree073_685,tree073_551]
def tree073_687 : CoverTree := CoverTree.reject 305
def tree073_688 : CoverTree := CoverTree.reject 189
def tree073_689 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_212,tree073_213,tree073_687,tree073_688]
def tree073_690 : CoverTree := CoverTree.reject 306
def tree073_691 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_557,tree073_225,tree073_186]
def tree073_692 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_690,tree073_691,tree073_560,tree073_561]
def tree073_693 : CoverTree := CoverTree.reject 352
def tree073_694 : CoverTree := CoverTree.split [tree073_47,tree073_693,tree073_564,tree073_565,tree073_193,tree073_566]
def tree073_695 : CoverTree := CoverTree.split [tree073_689,tree073_692,tree073_694,tree073_573,tree073_581,tree073_621]
def tree073_696 : CoverTree := CoverTree.reject 190
def tree073_697 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_212,tree073_213,tree073_586,tree073_696]
def tree073_698 : CoverTree := CoverTree.split [tree073_697,tree073_592,tree073_597,tree073_607,tree073_616,tree073_621]
def tree073_699 : CoverTree := CoverTree.split [tree073_0,tree073_646,tree073_670,tree073_686,tree073_695,tree073_698]
def tree073_700 : CoverTree := CoverTree.reject 57
def tree073_701 : CoverTree := CoverTree.reject 167
def tree073_702 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_700,tree073_701,tree073_253]
def tree073_703 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_700,tree073_57,tree073_14]
def tree073_704 : CoverTree := CoverTree.reject 385
def tree073_705 : CoverTree := CoverTree.reject 386
def tree073_706 : CoverTree := CoverTree.reject 387
def tree073_707 : CoverTree := CoverTree.split [tree073_13,tree073_704,tree073_705,tree073_706,tree073_14,tree073_14]
def tree073_708 : CoverTree := CoverTree.reject 388
def tree073_709 : CoverTree := CoverTree.split [tree073_16,tree073_708,tree073_14,tree073_14,tree073_14,tree073_14]
def tree073_710 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_707,tree073_709,tree073_60,tree073_430]
def tree073_711 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_422,tree073_702,tree073_703,tree073_710]
def tree073_712 : CoverTree := CoverTree.reject 176
def tree073_713 : CoverTree := CoverTree.reject 119
def tree073_714 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_260,tree073_712,tree073_713,tree073_14]
def tree073_715 : CoverTree := CoverTree.reject 374
def tree073_716 : CoverTree := CoverTree.reject 343
def tree073_717 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_715,tree073_716,tree073_72,tree073_14]
def tree073_718 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_714,tree073_717,tree073_634,tree073_638]
def tree073_719 : CoverTree := CoverTree.reject 344
def tree073_720 : CoverTree := CoverTree.reject 280
def tree073_721 : CoverTree := CoverTree.reject 281
def tree073_722 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_719,tree073_720,tree073_721,tree073_14]
def tree073_723 : CoverTree := CoverTree.split [tree073_442,tree073_442,tree073_443,tree073_17,tree073_94,tree073_14]
def tree073_724 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_722,tree073_723,tree073_447,tree073_448]
def tree073_725 : CoverTree := CoverTree.split [tree073_101,tree073_101,tree073_711,tree073_718,tree073_724,tree073_645]
def tree073_726 : CoverTree := CoverTree.reject 135
def tree073_727 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_557,tree073_726,tree073_186]
def tree073_728 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_307,tree073_186,tree073_186]
def tree073_729 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_304,tree073_727,tree073_727,tree073_728]
def tree073_730 : CoverTree := CoverTree.reject 77
def tree073_731 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_238,tree073_730,tree073_245]
def tree073_732 : CoverTree := CoverTree.reject 389
def tree073_733 : CoverTree := CoverTree.reject 390
def tree073_734 : CoverTree := CoverTree.reject 391
def tree073_735 : CoverTree := CoverTree.split [tree073_13,tree073_732,tree073_733,tree073_734,tree073_14,tree073_14]
def tree073_736 : CoverTree := CoverTree.split [tree073_425,tree073_425,tree073_735,tree073_657,tree073_60,tree073_318]
def tree073_737 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_731,tree073_654,tree073_193,tree073_736]
def tree073_738 : CoverTree := CoverTree.split [tree073_105,tree073_105,tree073_661,tree073_471,tree073_681,tree073_664]
def tree073_739 : CoverTree := CoverTree.split [tree073_114,tree073_729,tree073_737,tree073_738,tree073_668,tree073_669]
def tree073_740 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_557,tree073_221,tree073_186]
def tree073_741 : CoverTree := CoverTree.reject 224
def tree073_742 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_557,tree073_741,tree073_186]
def tree073_743 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_740,tree073_742,tree073_560,tree073_561]
def tree073_744 : CoverTree := CoverTree.reject 232
def tree073_745 : CoverTree := CoverTree.split [tree073_80,tree073_80,tree073_80,tree073_744,tree073_14,tree073_14]
def tree073_746 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_406,tree073_407,tree073_745]
def tree073_747 : CoverTree := CoverTree.split [tree073_47,tree073_746,tree073_564,tree073_516,tree073_193,tree073_679]
def tree073_748 : CoverTree := CoverTree.split [tree073_529,tree073_574,tree073_532,tree073_576,tree073_487,tree073_493]
def tree073_749 : CoverTree := CoverTree.split [tree073_139,tree073_743,tree073_747,tree073_682,tree073_748,tree073_551]
def tree073_750 : CoverTree := CoverTree.reject 384
def tree073_751 : CoverTree := CoverTree.split [tree073_183,tree073_183,tree073_750,tree073_14,tree073_14,tree073_14]
def tree073_752 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_557,tree073_215,tree073_751]
def tree073_753 : CoverTree := CoverTree.reject 51
def tree073_754 : CoverTree := CoverTree.split [tree073_181,tree073_181,tree073_181,tree073_753,tree073_186,tree073_186]
def tree073_755 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_212,tree073_213,tree073_752,tree073_754]
def tree073_756 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_740,tree073_691,tree073_560,tree073_561]
def tree073_757 : CoverTree := CoverTree.split [tree073_192,tree073_192,tree073_192,tree073_406,tree073_407,tree073_81]
def tree073_758 : CoverTree := CoverTree.split [tree073_47,tree073_757,tree073_564,tree073_565,tree073_193,tree073_566]
def tree073_759 : CoverTree := CoverTree.split [tree073_755,tree073_756,tree073_758,tree073_573,tree073_581,tree073_621]
def tree073_760 : CoverTree := CoverTree.split [tree073_41,tree073_41,tree073_212,tree073_213,tree073_586,tree073_754]
def tree073_761 : CoverTree := CoverTree.split [tree073_760,tree073_592,tree073_597,tree073_607,tree073_616,tree073_621]
def tree073_762 : CoverTree := CoverTree.split [tree073_0,tree073_725,tree073_739,tree073_749,tree073_759,tree073_761]
def tree073_763 : CoverTree := CoverTree.split [tree073_100,tree073_279,tree073_419,tree073_623,tree073_699,tree073_762]
def tree073 : CoverTree := tree073_763

end Snake9.Shared89
