import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes093 : List Box := [
[(1,6),(1,5),(1,3),(1,5),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)],
[(1,3),(1,6),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,5),(1,5),(1,4)],
[(1,2),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,2),(1,2)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,5),(1,5),(1,4),(1,2),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,2)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,2),(1,5)],
[(1,6),(1,6),(1,2),(1,4),(1,5),(1,5)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,1)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,5),(1,3),(1,5)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,5),(1,2),(1,5),(1,4),(1,6)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
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
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(6,6),(4,4),(1,6)],
[(1,6),(1,2),(1,3),(1,5),(1,4),(1,6)],
[(1,6),(1,6),(6,6),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(5,5),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
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
[(1,6),(1,6),(5,5),(4,4),(3,3),(2,2)],
[(1,6),(3,3),(3,3),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(1,6),(1,6),(4,4),(6,6),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(5,5),(1,1)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(5,5),(1,6),(1,6)],
[(3,3),(2,2),(5,5),(5,5),(1,6),(1,6)],
[(5,5),(1,1),(6,6),(4,4),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(4,4),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(2,2)],
[(2,2),(3,3),(3,3),(6,6),(1,6),(1,6)],
[(1,6),(1,1),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,1),(5,5),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(6,6),(3,3),(3,3),(1,6)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(1,6)],
[(3,3),(2,2),(5,5),(4,4),(1,6),(1,6)],
[(5,5),(1,1),(6,6),(3,3),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(3,3),(1,6),(1,6)],
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
[(1,6),(1,6),(1,1),(5,5),(5,5),(1,6)],
[(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(4,4),(3,3)],
[(1,6),(2,2),(4,4),(3,3),(5,5),(1,6)],
[(1,6),(6,6),(1,1),(5,5),(6,6),(1,6)],
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
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,6),(2,2),(3,3),(5,5),(1,6)],
[(1,6),(1,6),(5,5),(5,5),(1,1),(1,6)],
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
[(5,5),(1,1),(5,5),(5,5),(1,6),(1,6)],
[(6,6),(1,1),(5,5),(5,5),(1,6),(1,6)],
[(5,5),(1,1),(5,5),(4,4),(1,6),(1,6)],
[(6,6),(1,1),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(1,1),(5,5),(6,6),(3,3),(1,6)],
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
[(1,6),(1,6),(1,1),(5,5),(4,4),(1,6)],
[(1,6),(2,2),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(4,4),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(4,4),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(4,4),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(5,5),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(5,5),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(1,1),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(5,5),(1,1),(1,6)],
[(1,1),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(2,2),(1,6),(1,6)],
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
[(3,3),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(4,4),(1,6),(1,6)],
[(3,3),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(4,4),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(4,4),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(5,5),(2,2),(3,3),(4,4),(1,6),(1,6)],
[(5,5),(4,4),(2,2),(4,4),(1,6),(1,6)],
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
[(6,6),(1,1),(5,5),(6,6),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(5,5)],
[(1,6),(2,2),(5,5),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(5,5),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(4,4),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(4,4),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(4,4),(5,5),(1,1),(5,5),(1,6),(1,6)],
[(4,4),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(5,5),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(5,5),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(5,5),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(5,5),(4,4),(2,2),(3,3),(1,6),(1,6)],
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
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(4,4)],
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
[(1,6),(4,4),(2,2),(4,4),(5,5),(1,6)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(4,4)],
[(1,6),(2,2),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(3,3),(4,4)],
[(4,4),(5,5),(2,2),(4,4),(5,5),(1,6)],
[(4,4),(5,5),(6,6),(2,2),(2,2),(1,6)],
[(3,3),(5,5),(2,2),(6,6),(5,5),(3,3)]
]

def root093 : Nat := 3788

def tree093_0 : CoverTree := CoverTree.reject 25
def tree093_1 : CoverTree := CoverTree.reject 17
def tree093_2 : CoverTree := CoverTree.reject 18
def tree093_3 : CoverTree := CoverTree.reject 12
def tree093_4 : CoverTree := CoverTree.reject 5
def tree093_5 : CoverTree := CoverTree.reject 41
def tree093_6 : CoverTree := CoverTree.reject 34
def tree093_7 : CoverTree := CoverTree.reject 206
def tree093_8 : CoverTree := CoverTree.reject 154
def tree093_9 : CoverTree := CoverTree.reject 129
def tree093_10 : CoverTree := CoverTree.reject 111
def tree093_11 : CoverTree := CoverTree.reject 2
def tree093_12 : CoverTree := CoverTree.reject 11
def tree093_13 : CoverTree := CoverTree.accept
def tree093_14 : CoverTree := CoverTree.split [tree093_12,tree093_13,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_15 : CoverTree := CoverTree.reject 9
def tree093_16 : CoverTree := CoverTree.split [tree093_15,tree093_13,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_17 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_18 : CoverTree := CoverTree.split [tree093_6,tree093_7,tree093_8,tree093_9,tree093_10,tree093_17]
def tree093_19 : CoverTree := CoverTree.reject 22
def tree093_20 : CoverTree := CoverTree.reject 19
def tree093_21 : CoverTree := CoverTree.reject 48
def tree093_22 : CoverTree := CoverTree.reject 49
def tree093_23 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_19,tree093_20,tree093_21,tree093_22]
def tree093_24 : CoverTree := CoverTree.reject 178
def tree093_25 : CoverTree := CoverTree.reject 119
def tree093_26 : CoverTree := CoverTree.reject 105
def tree093_27 : CoverTree := CoverTree.split [tree093_23,tree093_24,tree093_25,tree093_26,tree093_17,tree093_17]
def tree093_28 : CoverTree := CoverTree.reject 51
def tree093_29 : CoverTree := CoverTree.reject 52
def tree093_30 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_19,tree093_20,tree093_28,tree093_29]
def tree093_31 : CoverTree := CoverTree.reject 155
def tree093_32 : CoverTree := CoverTree.reject 66
def tree093_33 : CoverTree := CoverTree.split [tree093_12,tree093_32,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_34 : CoverTree := CoverTree.reject 44
def tree093_35 : CoverTree := CoverTree.split [tree093_34,tree093_13,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_36 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_33,tree093_16,tree093_35,tree093_13]
def tree093_37 : CoverTree := CoverTree.split [tree093_30,tree093_31,tree093_36,tree093_17,tree093_17,tree093_17]
def tree093_38 : CoverTree := CoverTree.split [tree093_4,tree093_4,tree093_5,tree093_18,tree093_27,tree093_37]
def tree093_39 : CoverTree := CoverTree.reject 35
def tree093_40 : CoverTree := CoverTree.reject 347
def tree093_41 : CoverTree := CoverTree.reject 203
def tree093_42 : CoverTree := CoverTree.reject 143
def tree093_43 : CoverTree := CoverTree.reject 38
def tree093_44 : CoverTree := CoverTree.split [tree093_12,tree093_43,tree093_43,tree093_43,tree093_43,tree093_13]
def tree093_45 : CoverTree := CoverTree.reject 101
def tree093_46 : CoverTree := CoverTree.split [tree093_15,tree093_45,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_47 : CoverTree := CoverTree.reject 24
def tree093_48 : CoverTree := CoverTree.reject 93
def tree093_49 : CoverTree := CoverTree.split [tree093_47,tree093_48,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_50 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_44,tree093_46,tree093_49,tree093_13]
def tree093_51 : CoverTree := CoverTree.reject 94
def tree093_52 : CoverTree := CoverTree.split [tree093_51,tree093_13,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_53 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_14,tree093_16,tree093_52,tree093_13]
def tree093_54 : CoverTree := CoverTree.split [tree093_39,tree093_40,tree093_41,tree093_42,tree093_50,tree093_53]
def tree093_55 : CoverTree := CoverTree.reject 207
def tree093_56 : CoverTree := CoverTree.reject 156
def tree093_57 : CoverTree := CoverTree.reject 45
def tree093_58 : CoverTree := CoverTree.reject 74
def tree093_59 : CoverTree := CoverTree.reject 75
def tree093_60 : CoverTree := CoverTree.split [tree093_12,tree093_57,tree093_58,tree093_59,tree093_13,tree093_13]
def tree093_61 : CoverTree := CoverTree.reject 76
def tree093_62 : CoverTree := CoverTree.reject 77
def tree093_63 : CoverTree := CoverTree.split [tree093_15,tree093_61,tree093_62,tree093_13,tree093_13,tree093_13]
def tree093_64 : CoverTree := CoverTree.split [tree093_47,tree093_13,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_65 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_60,tree093_63,tree093_64,tree093_13]
def tree093_66 : CoverTree := CoverTree.split [tree093_12,tree093_57,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_67 : CoverTree := CoverTree.reject 78
def tree093_68 : CoverTree := CoverTree.split [tree093_15,tree093_67,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_69 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_66,tree093_68,tree093_64,tree093_13]
def tree093_70 : CoverTree := CoverTree.split [tree093_6,tree093_55,tree093_56,tree093_65,tree093_69,tree093_17]
def tree093_71 : CoverTree := CoverTree.reject 50
def tree093_72 : CoverTree := CoverTree.reject 1
def tree093_73 : CoverTree := CoverTree.split [tree093_72,tree093_72,tree093_72,tree093_13,tree093_13,tree093_13]
def tree093_74 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_71,tree093_73,tree093_73,tree093_73]
def tree093_75 : CoverTree := CoverTree.reject 79
def tree093_76 : CoverTree := CoverTree.reject 80
def tree093_77 : CoverTree := CoverTree.split [tree093_12,tree093_75,tree093_76,tree093_13,tree093_13,tree093_13]
def tree093_78 : CoverTree := CoverTree.reject 81
def tree093_79 : CoverTree := CoverTree.split [tree093_15,tree093_78,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_80 : CoverTree := CoverTree.reject 67
def tree093_81 : CoverTree := CoverTree.split [tree093_34,tree093_80,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_82 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_77,tree093_79,tree093_81,tree093_13]
def tree093_83 : CoverTree := CoverTree.reject 82
def tree093_84 : CoverTree := CoverTree.split [tree093_12,tree093_83,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_85 : CoverTree := CoverTree.reject 68
def tree093_86 : CoverTree := CoverTree.split [tree093_85,tree093_13,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_87 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_84,tree093_16,tree093_86,tree093_13]
def tree093_88 : CoverTree := CoverTree.split [tree093_23,tree093_74,tree093_82,tree093_87,tree093_17,tree093_17]
def tree093_89 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_73,tree093_73,tree093_73,tree093_73]
def tree093_90 : CoverTree := CoverTree.split [tree093_30,tree093_89,tree093_36,tree093_17,tree093_17,tree093_17]
def tree093_91 : CoverTree := CoverTree.split [tree093_4,tree093_4,tree093_54,tree093_70,tree093_88,tree093_90]
def tree093_92 : CoverTree := CoverTree.split [tree093_0,tree093_1,tree093_2,tree093_3,tree093_38,tree093_91]
def tree093_93 : CoverTree := CoverTree.reject 26
def tree093_94 : CoverTree := CoverTree.reject 42
def tree093_95 : CoverTree := CoverTree.reject 39
def tree093_96 : CoverTree := CoverTree.reject 37
def tree093_97 : CoverTree := CoverTree.reject 3
def tree093_98 : CoverTree := CoverTree.reject 133
def tree093_99 : CoverTree := CoverTree.reject 95
def tree093_100 : CoverTree := CoverTree.reject 238
def tree093_101 : CoverTree := CoverTree.reject 239
def tree093_102 : CoverTree := CoverTree.split [tree093_12,tree093_100,tree093_101,tree093_13,tree093_13,tree093_13]
def tree093_103 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_102,tree093_16,tree093_13,tree093_13]
def tree093_104 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_98,tree093_99,tree093_17,tree093_103]
def tree093_105 : CoverTree := CoverTree.split [tree093_4,tree093_4,tree093_94,tree093_95,tree093_96,tree093_104]
def tree093_106 : CoverTree := CoverTree.reject 295
def tree093_107 : CoverTree := CoverTree.reject 193
def tree093_108 : CoverTree := CoverTree.reject 144
def tree093_109 : CoverTree := CoverTree.reject 102
def tree093_110 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_106,tree093_107,tree093_108,tree093_109]
def tree093_111 : CoverTree := CoverTree.reject 163
def tree093_112 : CoverTree := CoverTree.reject 134
def tree093_113 : CoverTree := CoverTree.reject 115
def tree093_114 : CoverTree := CoverTree.reject 245
def tree093_115 : CoverTree := CoverTree.reject 315
def tree093_116 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_114,tree093_115,tree093_13,tree093_13]
def tree093_117 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_111,tree093_112,tree093_113,tree093_116]
def tree093_118 : CoverTree := CoverTree.reject 120
def tree093_119 : CoverTree := CoverTree.reject 135
def tree093_120 : CoverTree := CoverTree.reject 96
def tree093_121 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_118,tree093_119,tree093_120,tree093_17]
def tree093_122 : CoverTree := CoverTree.reject 316
def tree093_123 : CoverTree := CoverTree.reject 246
def tree093_124 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_122,tree093_123,tree093_35,tree093_13]
def tree093_125 : CoverTree := CoverTree.reject 247
def tree093_126 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_125,tree093_16,tree093_13,tree093_13]
def tree093_127 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_124,tree093_126,tree093_17,tree093_17]
def tree093_128 : CoverTree := CoverTree.split [tree093_4,tree093_4,tree093_110,tree093_117,tree093_121,tree093_127]
def tree093_129 : CoverTree := CoverTree.reject 383
def tree093_130 : CoverTree := CoverTree.reject 210
def tree093_131 : CoverTree := CoverTree.reject 194
def tree093_132 : CoverTree := CoverTree.reject 145
def tree093_133 : CoverTree := CoverTree.reject 363
def tree093_134 : CoverTree := CoverTree.reject 244
def tree093_135 : CoverTree := CoverTree.split [tree093_15,tree093_134,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_136 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_133,tree093_135,tree093_52,tree093_13]
def tree093_137 : CoverTree := CoverTree.split [tree093_39,tree093_129,tree093_130,tree093_131,tree093_132,tree093_136]
def tree093_138 : CoverTree := CoverTree.reject 211
def tree093_139 : CoverTree := CoverTree.reject 164
def tree093_140 : CoverTree := CoverTree.reject 136
def tree093_141 : CoverTree := CoverTree.reject 317
def tree093_142 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_141,tree093_68,tree093_64,tree093_13]
def tree093_143 : CoverTree := CoverTree.reject 248
def tree093_144 : CoverTree := CoverTree.reject 249
def tree093_145 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_143,tree093_144,tree093_13,tree093_13]
def tree093_146 : CoverTree := CoverTree.split [tree093_6,tree093_138,tree093_139,tree093_140,tree093_142,tree093_145]
def tree093_147 : CoverTree := CoverTree.reject 185
def tree093_148 : CoverTree := CoverTree.reject 121
def tree093_149 : CoverTree := CoverTree.reject 318
def tree093_150 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_149,tree093_16,tree093_86,tree093_13]
def tree093_151 : CoverTree := CoverTree.split [tree093_23,tree093_147,tree093_148,tree093_150,tree093_17,tree093_17]
def tree093_152 : CoverTree := CoverTree.reject 165
def tree093_153 : CoverTree := CoverTree.reject 319
def tree093_154 : CoverTree := CoverTree.reject 250
def tree093_155 : CoverTree := CoverTree.reject 251
def tree093_156 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_153,tree093_154,tree093_155,tree093_13]
def tree093_157 : CoverTree := CoverTree.reject 252
def tree093_158 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_157,tree093_16,tree093_13,tree093_13]
def tree093_159 : CoverTree := CoverTree.split [tree093_30,tree093_152,tree093_156,tree093_158,tree093_17,tree093_17]
def tree093_160 : CoverTree := CoverTree.split [tree093_4,tree093_4,tree093_137,tree093_146,tree093_151,tree093_159]
def tree093_161 : CoverTree := CoverTree.reject 354
def tree093_162 : CoverTree := CoverTree.reject 212
def tree093_163 : CoverTree := CoverTree.reject 147
def tree093_164 : CoverTree := CoverTree.reject 0
def tree093_165 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_46,tree093_49,tree093_13]
def tree093_166 : CoverTree := CoverTree.reject 253
def tree093_167 : CoverTree := CoverTree.reject 254
def tree093_168 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_166,tree093_167,tree093_52,tree093_13]
def tree093_169 : CoverTree := CoverTree.split [tree093_39,tree093_161,tree093_162,tree093_163,tree093_165,tree093_168]
def tree093_170 : CoverTree := CoverTree.reject 213
def tree093_171 : CoverTree := CoverTree.reject 166
def tree093_172 : CoverTree := CoverTree.split [tree093_6,tree093_170,tree093_171,tree093_65,tree093_69,tree093_17]
def tree093_173 : CoverTree := CoverTree.reject 186
def tree093_174 : CoverTree := CoverTree.reject 320
def tree093_175 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_174,tree093_16,tree093_86,tree093_13]
def tree093_176 : CoverTree := CoverTree.split [tree093_23,tree093_173,tree093_82,tree093_175,tree093_17,tree093_17]
def tree093_177 : CoverTree := CoverTree.reject 364
def tree093_178 : CoverTree := CoverTree.reject 365
def tree093_179 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_177,tree093_178,tree093_73,tree093_73]
def tree093_180 : CoverTree := CoverTree.reject 321
def tree093_181 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_180,tree093_16,tree093_35,tree093_13]
def tree093_182 : CoverTree := CoverTree.split [tree093_30,tree093_179,tree093_181,tree093_17,tree093_17,tree093_17]
def tree093_183 : CoverTree := CoverTree.split [tree093_4,tree093_4,tree093_169,tree093_172,tree093_176,tree093_182]
def tree093_184 : CoverTree := CoverTree.reject 355
def tree093_185 : CoverTree := CoverTree.reject 228
def tree093_186 : CoverTree := CoverTree.reject 29
def tree093_187 : CoverTree := CoverTree.reject 112
def tree093_188 : CoverTree := CoverTree.reject 113
def tree093_189 : CoverTree := CoverTree.reject 114
def tree093_190 : CoverTree := CoverTree.split [tree093_47,tree093_187,tree093_188,tree093_189,tree093_13,tree093_13]
def tree093_191 : CoverTree := CoverTree.reject 88
def tree093_192 : CoverTree := CoverTree.reject 89
def tree093_193 : CoverTree := CoverTree.split [tree093_191,tree093_192,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_194 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_185,tree093_186,tree093_190,tree093_193]
def tree093_195 : CoverTree := CoverTree.reject 229
def tree093_196 : CoverTree := CoverTree.reject 366
def tree093_197 : CoverTree := CoverTree.reject 90
def tree093_198 : CoverTree := CoverTree.reject 91
def tree093_199 : CoverTree := CoverTree.split [tree093_47,tree093_197,tree093_198,tree093_13,tree093_13,tree093_13]
def tree093_200 : CoverTree := CoverTree.reject 92
def tree093_201 : CoverTree := CoverTree.split [tree093_200,tree093_13,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_202 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_195,tree093_196,tree093_199,tree093_201]
def tree093_203 : CoverTree := CoverTree.reject 255
def tree093_204 : CoverTree := CoverTree.reject 256
def tree093_205 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_203,tree093_204,tree093_52,tree093_13]
def tree093_206 : CoverTree := CoverTree.split [tree093_39,tree093_184,tree093_194,tree093_202,tree093_50,tree093_205]
def tree093_207 : CoverTree := CoverTree.reject 214
def tree093_208 : CoverTree := CoverTree.reject 30
def tree093_209 : CoverTree := CoverTree.reject 70
def tree093_210 : CoverTree := CoverTree.reject 71
def tree093_211 : CoverTree := CoverTree.reject 72
def tree093_212 : CoverTree := CoverTree.split [tree093_15,tree093_209,tree093_210,tree093_211,tree093_13,tree093_13]
def tree093_213 : CoverTree := CoverTree.reject 73
def tree093_214 : CoverTree := CoverTree.split [tree093_47,tree093_213,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_215 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_208,tree093_212,tree093_214,tree093_13]
def tree093_216 : CoverTree := CoverTree.split [tree093_6,tree093_207,tree093_215,tree093_65,tree093_69,tree093_17]
def tree093_217 : CoverTree := CoverTree.reject 367
def tree093_218 : CoverTree := CoverTree.reject 322
def tree093_219 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_217,tree093_218,tree093_81,tree093_13]
def tree093_220 : CoverTree := CoverTree.split [tree093_23,tree093_74,tree093_219,tree093_87,tree093_17,tree093_17]
def tree093_221 : CoverTree := CoverTree.reject 368
def tree093_222 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_221,tree093_73,tree093_73,tree093_73]
def tree093_223 : CoverTree := CoverTree.reject 323
def tree093_224 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_223,tree093_16,tree093_35,tree093_13]
def tree093_225 : CoverTree := CoverTree.split [tree093_30,tree093_222,tree093_224,tree093_17,tree093_17,tree093_17]
def tree093_226 : CoverTree := CoverTree.split [tree093_4,tree093_4,tree093_206,tree093_216,tree093_220,tree093_225]
def tree093_227 : CoverTree := CoverTree.split [tree093_93,tree093_105,tree093_128,tree093_160,tree093_183,tree093_226]
def tree093_228 : CoverTree := CoverTree.reject 27
def tree093_229 : CoverTree := CoverTree.reject 7
def tree093_230 : CoverTree := CoverTree.reject 43
def tree093_231 : CoverTree := CoverTree.reject 215
def tree093_232 : CoverTree := CoverTree.reject 137
def tree093_233 : CoverTree := CoverTree.reject 116
def tree093_234 : CoverTree := CoverTree.reject 360
def tree093_235 : CoverTree := CoverTree.reject 361
def tree093_236 : CoverTree := CoverTree.reject 362
def tree093_237 : CoverTree := CoverTree.split [tree093_12,tree093_234,tree093_235,tree093_236,tree093_13,tree093_13]
def tree093_238 : CoverTree := CoverTree.reject 257
def tree093_239 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_237,tree093_238,tree093_13,tree093_13]
def tree093_240 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_231,tree093_232,tree093_233,tree093_239]
def tree093_241 : CoverTree := CoverTree.reject 122
def tree093_242 : CoverTree := CoverTree.reject 108
def tree093_243 : CoverTree := CoverTree.reject 97
def tree093_244 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_241,tree093_242,tree093_243,tree093_17]
def tree093_245 : CoverTree := CoverTree.reject 106
def tree093_246 : CoverTree := CoverTree.reject 258
def tree093_247 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_245,tree093_246,tree093_35,tree093_13]
def tree093_248 : CoverTree := CoverTree.reject 259
def tree093_249 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_248,tree093_16,tree093_13,tree093_13]
def tree093_250 : CoverTree := CoverTree.reject 260
def tree093_251 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_250,tree093_16,tree093_13,tree093_13]
def tree093_252 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_247,tree093_249,tree093_251,tree093_103]
def tree093_253 : CoverTree := CoverTree.split [tree093_229,tree093_229,tree093_230,tree093_240,tree093_244,tree093_252]
def tree093_254 : CoverTree := CoverTree.reject 31
def tree093_255 : CoverTree := CoverTree.reject 104
def tree093_256 : CoverTree := CoverTree.reject 296
def tree093_257 : CoverTree := CoverTree.reject 297
def tree093_258 : CoverTree := CoverTree.reject 8
def tree093_259 : CoverTree := CoverTree.reject 161
def tree093_260 : CoverTree := CoverTree.reject 324
def tree093_261 : CoverTree := CoverTree.reject 14
def tree093_262 : CoverTree := CoverTree.split [tree093_261,tree093_261,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_263 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_258,tree093_259,tree093_260,tree093_262]
def tree093_264 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_255,tree093_256,tree093_257,tree093_263]
def tree093_265 : CoverTree := CoverTree.reject 298
def tree093_266 : CoverTree := CoverTree.reject 195
def tree093_267 : CoverTree := CoverTree.reject 146
def tree093_268 : CoverTree := CoverTree.reject 261
def tree093_269 : CoverTree := CoverTree.reject 262
def tree093_270 : CoverTree := CoverTree.reject 263
def tree093_271 : CoverTree := CoverTree.reject 313
def tree093_272 : CoverTree := CoverTree.split [tree093_13,tree093_271,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_273 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_268,tree093_269,tree093_270,tree093_272]
def tree093_274 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_265,tree093_266,tree093_267,tree093_273]
def tree093_275 : CoverTree := CoverTree.reject 167
def tree093_276 : CoverTree := CoverTree.reject 138
def tree093_277 : CoverTree := CoverTree.reject 117
def tree093_278 : CoverTree := CoverTree.reject 264
def tree093_279 : CoverTree := CoverTree.reject 325
def tree093_280 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_278,tree093_279,tree093_13,tree093_13]
def tree093_281 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_275,tree093_276,tree093_277,tree093_280]
def tree093_282 : CoverTree := CoverTree.reject 123
def tree093_283 : CoverTree := CoverTree.reject 107
def tree093_284 : CoverTree := CoverTree.reject 265
def tree093_285 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_283,tree093_284,tree093_86,tree093_13]
def tree093_286 : CoverTree := CoverTree.reject 266
def tree093_287 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_286,tree093_16,tree093_13,tree093_13]
def tree093_288 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_282,tree093_285,tree093_287,tree093_17]
def tree093_289 : CoverTree := CoverTree.reject 326
def tree093_290 : CoverTree := CoverTree.reject 267
def tree093_291 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_289,tree093_290,tree093_35,tree093_13]
def tree093_292 : CoverTree := CoverTree.reject 268
def tree093_293 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_292,tree093_16,tree093_13,tree093_13]
def tree093_294 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_291,tree093_293,tree093_17,tree093_17]
def tree093_295 : CoverTree := CoverTree.split [tree093_254,tree093_264,tree093_274,tree093_281,tree093_288,tree093_294]
def tree093_296 : CoverTree := CoverTree.reject 23
def tree093_297 : CoverTree := CoverTree.reject 54
def tree093_298 : CoverTree := CoverTree.reject 127
def tree093_299 : CoverTree := CoverTree.reject 299
def tree093_300 : CoverTree := CoverTree.reject 230
def tree093_301 : CoverTree := CoverTree.reject 216
def tree093_302 : CoverTree := CoverTree.reject 369
def tree093_303 : CoverTree := CoverTree.reject 327
def tree093_304 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_258,tree093_302,tree093_303,tree093_262]
def tree093_305 : CoverTree := CoverTree.split [tree093_297,tree093_298,tree093_299,tree093_300,tree093_301,tree093_304]
def tree093_306 : CoverTree := CoverTree.reject 384
def tree093_307 : CoverTree := CoverTree.reject 217
def tree093_308 : CoverTree := CoverTree.reject 196
def tree093_309 : CoverTree := CoverTree.reject 328
def tree093_310 : CoverTree := CoverTree.reject 329
def tree093_311 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_309,tree093_310,tree093_13]
def tree093_312 : CoverTree := CoverTree.reject 370
def tree093_313 : CoverTree := CoverTree.reject 330
def tree093_314 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_312,tree093_313,tree093_52,tree093_13]
def tree093_315 : CoverTree := CoverTree.split [tree093_39,tree093_306,tree093_307,tree093_308,tree093_311,tree093_314]
def tree093_316 : CoverTree := CoverTree.reject 218
def tree093_317 : CoverTree := CoverTree.reject 192
def tree093_318 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_208,tree093_317,tree093_214,tree093_13]
def tree093_319 : CoverTree := CoverTree.reject 331
def tree093_320 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_319,tree093_68,tree093_64,tree093_13]
def tree093_321 : CoverTree := CoverTree.split [tree093_6,tree093_316,tree093_318,tree093_65,tree093_320,tree093_17]
def tree093_322 : CoverTree := CoverTree.reject 187
def tree093_323 : CoverTree := CoverTree.reject 162
def tree093_324 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_323,tree093_79,tree093_81,tree093_13]
def tree093_325 : CoverTree := CoverTree.reject 332
def tree093_326 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_325,tree093_16,tree093_86,tree093_13]
def tree093_327 : CoverTree := CoverTree.split [tree093_23,tree093_322,tree093_324,tree093_326,tree093_17,tree093_17]
def tree093_328 : CoverTree := CoverTree.reject 390
def tree093_329 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_328,tree093_73,tree093_73,tree093_73]
def tree093_330 : CoverTree := CoverTree.split [tree093_30,tree093_329,tree093_36,tree093_17,tree093_17,tree093_17]
def tree093_331 : CoverTree := CoverTree.split [tree093_296,tree093_305,tree093_315,tree093_321,tree093_327,tree093_330]
def tree093_332 : CoverTree := CoverTree.reject 153
def tree093_333 : CoverTree := CoverTree.reject 128
def tree093_334 : CoverTree := CoverTree.reject 300
def tree093_335 : CoverTree := CoverTree.reject 231
def tree093_336 : CoverTree := CoverTree.reject 219
def tree093_337 : CoverTree := CoverTree.reject 371
def tree093_338 : CoverTree := CoverTree.reject 403
def tree093_339 : CoverTree := CoverTree.split [tree093_261,tree093_261,tree093_338,tree093_13,tree093_13,tree093_13]
def tree093_340 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_258,tree093_337,tree093_339,tree093_262]
def tree093_341 : CoverTree := CoverTree.split [tree093_297,tree093_333,tree093_334,tree093_335,tree093_336,tree093_340]
def tree093_342 : CoverTree := CoverTree.reject 356
def tree093_343 : CoverTree := CoverTree.reject 220
def tree093_344 : CoverTree := CoverTree.reject 372
def tree093_345 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_344,tree093_199,tree093_201]
def tree093_346 : CoverTree := CoverTree.reject 269
def tree093_347 : CoverTree := CoverTree.reject 270
def tree093_348 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_346,tree093_347,tree093_52,tree093_13]
def tree093_349 : CoverTree := CoverTree.split [tree093_39,tree093_342,tree093_343,tree093_345,tree093_165,tree093_348]
def tree093_350 : CoverTree := CoverTree.reject 221
def tree093_351 : CoverTree := CoverTree.reject 391
def tree093_352 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_208,tree093_351,tree093_214,tree093_13]
def tree093_353 : CoverTree := CoverTree.split [tree093_6,tree093_350,tree093_352,tree093_65,tree093_69,tree093_17]
def tree093_354 : CoverTree := CoverTree.reject 373
def tree093_355 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_71,tree093_354,tree093_73,tree093_73]
def tree093_356 : CoverTree := CoverTree.split [tree093_23,tree093_355,tree093_82,tree093_87,tree093_17,tree093_17]
def tree093_357 : CoverTree := CoverTree.reject 333
def tree093_358 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_357,tree093_16,tree093_35,tree093_13]
def tree093_359 : CoverTree := CoverTree.split [tree093_30,tree093_89,tree093_358,tree093_17,tree093_17,tree093_17]
def tree093_360 : CoverTree := CoverTree.split [tree093_332,tree093_341,tree093_349,tree093_353,tree093_356,tree093_359]
def tree093_361 : CoverTree := CoverTree.reject 63
def tree093_362 : CoverTree := CoverTree.reject 59
def tree093_363 : CoverTree := CoverTree.reject 57
def tree093_364 : CoverTree := CoverTree.reject 58
def tree093_365 : CoverTree := CoverTree.reject 188
def tree093_366 : CoverTree := CoverTree.reject 126
def tree093_367 : CoverTree := CoverTree.reject 132
def tree093_368 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_258,tree093_365,tree093_366,tree093_367]
def tree093_369 : CoverTree := CoverTree.reject 197
def tree093_370 : CoverTree := CoverTree.split [tree093_361,tree093_362,tree093_363,tree093_364,tree093_368,tree093_369]
def tree093_371 : CoverTree := CoverTree.reject 232
def tree093_372 : CoverTree := CoverTree.reject 289
def tree093_373 : CoverTree := CoverTree.reject 151
def tree093_374 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_258,tree093_372,tree093_373,tree093_262]
def tree093_375 : CoverTree := CoverTree.reject 290
def tree093_376 : CoverTree := CoverTree.reject 4
def tree093_377 : CoverTree := CoverTree.reject 21
def tree093_378 : CoverTree := CoverTree.split [tree093_376,tree093_376,tree093_376,tree093_376,tree093_377,tree093_13]
def tree093_379 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_258,tree093_375,tree093_378,tree093_262]
def tree093_380 : CoverTree := CoverTree.reject 291
def tree093_381 : CoverTree := CoverTree.split [tree093_376,tree093_376,tree093_376,tree093_376,tree093_380,tree093_13]
def tree093_382 : CoverTree := CoverTree.split [tree093_376,tree093_376,tree093_376,tree093_376,tree093_13,tree093_13]
def tree093_383 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_258,tree093_381,tree093_382,tree093_262]
def tree093_384 : CoverTree := CoverTree.reject 130
def tree093_385 : CoverTree := CoverTree.split [tree093_15,tree093_261,tree093_384,tree093_13,tree093_13,tree093_13]
def tree093_386 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_258,tree093_385,tree093_262,tree093_262]
def tree093_387 : CoverTree := CoverTree.split [tree093_297,tree093_371,tree093_374,tree093_379,tree093_383,tree093_386]
def tree093_388 : CoverTree := CoverTree.reject 204
def tree093_389 : CoverTree := CoverTree.reject 55
def tree093_390 : CoverTree := CoverTree.reject 56
def tree093_391 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_388,tree093_389,tree093_390,tree093_73]
def tree093_392 : CoverTree := CoverTree.reject 179
def tree093_393 : CoverTree := CoverTree.reject 180
def tree093_394 : CoverTree := CoverTree.split [tree093_15,tree093_392,tree093_393,tree093_13,tree093_13,tree093_13]
def tree093_395 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_195,tree093_394,tree093_199,tree093_201]
def tree093_396 : CoverTree := CoverTree.split [tree093_39,tree093_391,tree093_194,tree093_395,tree093_50,tree093_53]
def tree093_397 : CoverTree := CoverTree.reject 46
def tree093_398 : CoverTree := CoverTree.reject 47
def tree093_399 : CoverTree := CoverTree.split [tree093_11,tree093_11,tree093_397,tree093_398,tree093_73,tree093_73]
def tree093_400 : CoverTree := CoverTree.split [tree093_6,tree093_399,tree093_215,tree093_65,tree093_69,tree093_17]
def tree093_401 : CoverTree := CoverTree.split [tree093_370,tree093_387,tree093_396,tree093_400,tree093_88,tree093_90]
def tree093_402 : CoverTree := CoverTree.split [tree093_228,tree093_253,tree093_295,tree093_331,tree093_360,tree093_401]
def tree093_403 : CoverTree := CoverTree.reject 28
def tree093_404 : CoverTree := CoverTree.reject 208
def tree093_405 : CoverTree := CoverTree.reject 159
def tree093_406 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_186,tree093_404,tree093_405]
def tree093_407 : CoverTree := CoverTree.reject 233
def tree093_408 : CoverTree := CoverTree.reject 174
def tree093_409 : CoverTree := CoverTree.reject 13
def tree093_410 : CoverTree := CoverTree.reject 271
def tree093_411 : CoverTree := CoverTree.reject 272
def tree093_412 : CoverTree := CoverTree.reject 273
def tree093_413 : CoverTree := CoverTree.reject 359
def tree093_414 : CoverTree := CoverTree.split [tree093_13,tree093_413,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_415 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_410,tree093_411,tree093_412,tree093_414]
def tree093_416 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_406,tree093_407,tree093_408,tree093_415]
def tree093_417 : CoverTree := CoverTree.reject 222
def tree093_418 : CoverTree := CoverTree.reject 139
def tree093_419 : CoverTree := CoverTree.reject 118
def tree093_420 : CoverTree := CoverTree.reject 274
def tree093_421 : CoverTree := CoverTree.reject 275
def tree093_422 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_420,tree093_421,tree093_13,tree093_13]
def tree093_423 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_417,tree093_418,tree093_419,tree093_422]
def tree093_424 : CoverTree := CoverTree.reject 124
def tree093_425 : CoverTree := CoverTree.reject 10
def tree093_426 : CoverTree := CoverTree.reject 160
def tree093_427 : CoverTree := CoverTree.reject 276
def tree093_428 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_426,tree093_427,tree093_86,tree093_13]
def tree093_429 : CoverTree := CoverTree.reject 142
def tree093_430 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_429,tree093_16,tree093_13,tree093_13]
def tree093_431 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_432 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_424,tree093_428,tree093_430,tree093_431]
def tree093_433 : CoverTree := CoverTree.reject 277
def tree093_434 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_245,tree093_433,tree093_35,tree093_13]
def tree093_435 : CoverTree := CoverTree.reject 278
def tree093_436 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_435,tree093_16,tree093_13,tree093_13]
def tree093_437 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_102,tree093_16,tree093_13,tree093_13]
def tree093_438 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_434,tree093_436,tree093_431,tree093_437]
def tree093_439 : CoverTree := CoverTree.split [tree093_229,tree093_229,tree093_416,tree093_423,tree093_432,tree093_438]
def tree093_440 : CoverTree := CoverTree.reject 301
def tree093_441 : CoverTree := CoverTree.reject 302
def tree093_442 : CoverTree := CoverTree.reject 334
def tree093_443 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_259,tree093_442,tree093_262]
def tree093_444 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_255,tree093_440,tree093_441,tree093_443]
def tree093_445 : CoverTree := CoverTree.reject 303
def tree093_446 : CoverTree := CoverTree.reject 198
def tree093_447 : CoverTree := CoverTree.reject 32
def tree093_448 : CoverTree := CoverTree.reject 279
def tree093_449 : CoverTree := CoverTree.reject 280
def tree093_450 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_448,tree093_449,tree093_52,tree093_272]
def tree093_451 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_445,tree093_446,tree093_165,tree093_450]
def tree093_452 : CoverTree := CoverTree.reject 168
def tree093_453 : CoverTree := CoverTree.reject 209
def tree093_454 : CoverTree := CoverTree.reject 182
def tree093_455 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_453,tree093_454,tree093_64,tree093_13]
def tree093_456 : CoverTree := CoverTree.reject 53
def tree093_457 : CoverTree := CoverTree.reject 335
def tree093_458 : CoverTree := CoverTree.split [tree093_456,tree093_456,tree093_457,tree093_68,tree093_64,tree093_13]
def tree093_459 : CoverTree := CoverTree.reject 87
def tree093_460 : CoverTree := CoverTree.reject 183
def tree093_461 : CoverTree := CoverTree.reject 281
def tree093_462 : CoverTree := CoverTree.reject 240
def tree093_463 : CoverTree := CoverTree.split [tree093_15,tree093_462,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_464 : CoverTree := CoverTree.split [tree093_459,tree093_460,tree093_461,tree093_463,tree093_13,tree093_13]
def tree093_465 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_452,tree093_455,tree093_458,tree093_464]
def tree093_466 : CoverTree := CoverTree.reject 184
def tree093_467 : CoverTree := CoverTree.reject 336
def tree093_468 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_466,tree093_467,tree093_81,tree093_13]
def tree093_469 : CoverTree := CoverTree.reject 282
def tree093_470 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_283,tree093_469,tree093_86,tree093_13]
def tree093_471 : CoverTree := CoverTree.split [tree093_456,tree093_456,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_472 : CoverTree := CoverTree.reject 6
def tree093_473 : CoverTree := CoverTree.reject 36
def tree093_474 : CoverTree := CoverTree.reject 33
def tree093_475 : CoverTree := CoverTree.split [tree093_472,tree093_472,tree093_473,tree093_474,tree093_13,tree093_13]
def tree093_476 : CoverTree := CoverTree.split [tree093_472,tree093_472,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_477 : CoverTree := CoverTree.split [tree093_475,tree093_476,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_478 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_468,tree093_470,tree093_471,tree093_477]
def tree093_479 : CoverTree := CoverTree.reject 61
def tree093_480 : CoverTree := CoverTree.reject 374
def tree093_481 : CoverTree := CoverTree.split [tree093_479,tree093_480,tree093_33,tree093_16,tree093_35,tree093_13]
def tree093_482 : CoverTree := CoverTree.reject 62
def tree093_483 : CoverTree := CoverTree.reject 337
def tree093_484 : CoverTree := CoverTree.reject 283
def tree093_485 : CoverTree := CoverTree.split [tree093_482,tree093_483,tree093_484,tree093_16,tree093_13,tree093_13]
def tree093_486 : CoverTree := CoverTree.reject 351
def tree093_487 : CoverTree := CoverTree.split [tree093_486,tree093_476,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_488 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_481,tree093_485,tree093_487,tree093_477]
def tree093_489 : CoverTree := CoverTree.split [tree093_254,tree093_444,tree093_451,tree093_465,tree093_478,tree093_488]
def tree093_490 : CoverTree := CoverTree.reject 304
def tree093_491 : CoverTree := CoverTree.reject 234
def tree093_492 : CoverTree := CoverTree.reject 223
def tree093_493 : CoverTree := CoverTree.reject 375
def tree093_494 : CoverTree := CoverTree.reject 338
def tree093_495 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_493,tree093_494,tree093_262]
def tree093_496 : CoverTree := CoverTree.split [tree093_297,tree093_298,tree093_490,tree093_491,tree093_492,tree093_495]
def tree093_497 : CoverTree := CoverTree.reject 385
def tree093_498 : CoverTree := CoverTree.reject 224
def tree093_499 : CoverTree := CoverTree.reject 85
def tree093_500 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_499,tree093_199,tree093_201]
def tree093_501 : CoverTree := CoverTree.reject 376
def tree093_502 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_501,tree093_135,tree093_52,tree093_13]
def tree093_503 : CoverTree := CoverTree.split [tree093_39,tree093_497,tree093_498,tree093_500,tree093_165,tree093_502]
def tree093_504 : CoverTree := CoverTree.reject 225
def tree093_505 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_208,tree093_317,tree093_214,tree093_13]
def tree093_506 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_60,tree093_63,tree093_64,tree093_13]
def tree093_507 : CoverTree := CoverTree.reject 339
def tree093_508 : CoverTree := CoverTree.split [tree093_456,tree093_456,tree093_507,tree093_68,tree093_64,tree093_13]
def tree093_509 : CoverTree := CoverTree.reject 157
def tree093_510 : CoverTree := CoverTree.split [tree093_472,tree093_472,tree093_509,tree093_13,tree093_13,tree093_13]
def tree093_511 : CoverTree := CoverTree.split [tree093_459,tree093_510,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_512 : CoverTree := CoverTree.split [tree093_6,tree093_504,tree093_505,tree093_506,tree093_508,tree093_511]
def tree093_513 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_19,tree093_20,tree093_21,tree093_22]
def tree093_514 : CoverTree := CoverTree.reject 377
def tree093_515 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_71,tree093_514,tree093_73,tree093_73]
def tree093_516 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_323,tree093_79,tree093_81,tree093_13]
def tree093_517 : CoverTree := CoverTree.reject 340
def tree093_518 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_517,tree093_16,tree093_86,tree093_13]
def tree093_519 : CoverTree := CoverTree.split [tree093_513,tree093_515,tree093_516,tree093_518,tree093_471,tree093_477]
def tree093_520 : CoverTree := CoverTree.reject 86
def tree093_521 : CoverTree := CoverTree.reject 60
def tree093_522 : CoverTree := CoverTree.split [tree093_520,tree093_521,tree093_19,tree093_20,tree093_28,tree093_29]
def tree093_523 : CoverTree := CoverTree.reject 69
def tree093_524 : CoverTree := CoverTree.reject 352
def tree093_525 : CoverTree := CoverTree.reject 314
def tree093_526 : CoverTree := CoverTree.split [tree093_72,tree093_72,tree093_72,tree093_525,tree093_13,tree093_13]
def tree093_527 : CoverTree := CoverTree.split [tree093_523,tree093_524,tree093_526,tree093_73,tree093_73,tree093_73]
def tree093_528 : CoverTree := CoverTree.reject 141
def tree093_529 : CoverTree := CoverTree.split [tree093_472,tree093_472,tree093_528,tree093_13,tree093_13,tree093_13]
def tree093_530 : CoverTree := CoverTree.split [tree093_479,tree093_529,tree093_33,tree093_16,tree093_35,tree093_13]
def tree093_531 : CoverTree := CoverTree.split [tree093_482,tree093_476,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_532 : CoverTree := CoverTree.reject 158
def tree093_533 : CoverTree := CoverTree.split [tree093_472,tree093_472,tree093_473,tree093_474,tree093_13,tree093_532]
def tree093_534 : CoverTree := CoverTree.split [tree093_533,tree093_476,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_535 : CoverTree := CoverTree.split [tree093_522,tree093_527,tree093_530,tree093_531,tree093_534,tree093_477]
def tree093_536 : CoverTree := CoverTree.split [tree093_296,tree093_496,tree093_503,tree093_512,tree093_519,tree093_535]
def tree093_537 : CoverTree := CoverTree.reject 305
def tree093_538 : CoverTree := CoverTree.reject 199
def tree093_539 : CoverTree := CoverTree.split [tree093_361,tree093_362,tree093_363,tree093_364,tree093_537,tree093_538]
def tree093_540 : CoverTree := CoverTree.reject 306
def tree093_541 : CoverTree := CoverTree.reject 40
def tree093_542 : CoverTree := CoverTree.reject 401
def tree093_543 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_541,tree093_542,tree093_262]
def tree093_544 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_541,tree093_382,tree093_262]
def tree093_545 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_385,tree093_262,tree093_262]
def tree093_546 : CoverTree := CoverTree.split [tree093_297,tree093_333,tree093_540,tree093_543,tree093_544,tree093_545]
def tree093_547 : CoverTree := CoverTree.reject 357
def tree093_548 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_186,tree093_190,tree093_193]
def tree093_549 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_394,tree093_199,tree093_201]
def tree093_550 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_14,tree093_16,tree093_52,tree093_13]
def tree093_551 : CoverTree := CoverTree.split [tree093_39,tree093_547,tree093_548,tree093_549,tree093_165,tree093_550]
def tree093_552 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_397,tree093_398,tree093_73,tree093_73]
def tree093_553 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_208,tree093_212,tree093_214,tree093_13]
def tree093_554 : CoverTree := CoverTree.reject 205
def tree093_555 : CoverTree := CoverTree.reject 353
def tree093_556 : CoverTree := CoverTree.split [tree093_554,tree093_555,tree093_66,tree093_68,tree093_64,tree093_13]
def tree093_557 : CoverTree := CoverTree.split [tree093_6,tree093_552,tree093_553,tree093_506,tree093_556,tree093_511]
def tree093_558 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_71,tree093_73,tree093_73,tree093_73]
def tree093_559 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_77,tree093_79,tree093_81,tree093_13]
def tree093_560 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_84,tree093_16,tree093_86,tree093_13]
def tree093_561 : CoverTree := CoverTree.reject 152
def tree093_562 : CoverTree := CoverTree.reject 176
def tree093_563 : CoverTree := CoverTree.split [tree093_472,tree093_472,tree093_562,tree093_13,tree093_13,tree093_13]
def tree093_564 : CoverTree := CoverTree.split [tree093_561,tree093_563,tree093_14,tree093_16,tree093_13,tree093_13]
def tree093_565 : CoverTree := CoverTree.split [tree093_513,tree093_558,tree093_559,tree093_560,tree093_564,tree093_477]
def tree093_566 : CoverTree := CoverTree.reject 402
def tree093_567 : CoverTree := CoverTree.split [tree093_523,tree093_566,tree093_73,tree093_73,tree093_73,tree093_73]
def tree093_568 : CoverTree := CoverTree.split [tree093_522,tree093_567,tree093_530,tree093_531,tree093_534,tree093_477]
def tree093_569 : CoverTree := CoverTree.split [tree093_539,tree093_546,tree093_551,tree093_557,tree093_565,tree093_568]
def tree093_570 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_365,tree093_366,tree093_367]
def tree093_571 : CoverTree := CoverTree.reject 200
def tree093_572 : CoverTree := CoverTree.split [tree093_361,tree093_362,tree093_363,tree093_364,tree093_570,tree093_571]
def tree093_573 : CoverTree := CoverTree.reject 235
def tree093_574 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_372,tree093_373,tree093_262]
def tree093_575 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_375,tree093_378,tree093_262]
def tree093_576 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_381,tree093_382,tree093_262]
def tree093_577 : CoverTree := CoverTree.split [tree093_297,tree093_573,tree093_574,tree093_575,tree093_576,tree093_545]
def tree093_578 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_388,tree093_389,tree093_390,tree093_73]
def tree093_579 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_185,tree093_186,tree093_190,tree093_193]
def tree093_580 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_195,tree093_394,tree093_199,tree093_201]
def tree093_581 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_44,tree093_46,tree093_49,tree093_13]
def tree093_582 : CoverTree := CoverTree.split [tree093_39,tree093_578,tree093_579,tree093_580,tree093_581,tree093_550]
def tree093_583 : CoverTree := CoverTree.reject 343
def tree093_584 : CoverTree := CoverTree.split [tree093_523,tree093_583,tree093_397,tree093_398,tree093_73,tree093_73]
def tree093_585 : CoverTree := CoverTree.reject 344
def tree093_586 : CoverTree := CoverTree.split [tree093_479,tree093_585,tree093_208,tree093_212,tree093_214,tree093_13]
def tree093_587 : CoverTree := CoverTree.reject 345
def tree093_588 : CoverTree := CoverTree.split [tree093_482,tree093_587,tree093_60,tree093_63,tree093_64,tree093_13]
def tree093_589 : CoverTree := CoverTree.reject 20
def tree093_590 : CoverTree := CoverTree.split [tree093_472,tree093_472,tree093_589,tree093_589,tree093_589,tree093_13]
def tree093_591 : CoverTree := CoverTree.split [tree093_554,tree093_590,tree093_66,tree093_68,tree093_64,tree093_13]
def tree093_592 : CoverTree := CoverTree.split [tree093_6,tree093_584,tree093_586,tree093_588,tree093_591,tree093_511]
def tree093_593 : CoverTree := CoverTree.split [tree093_520,tree093_521,tree093_19,tree093_20,tree093_21,tree093_22]
def tree093_594 : CoverTree := CoverTree.reject 346
def tree093_595 : CoverTree := CoverTree.split [tree093_523,tree093_594,tree093_71,tree093_73,tree093_73,tree093_73]
def tree093_596 : CoverTree := CoverTree.reject 177
def tree093_597 : CoverTree := CoverTree.split [tree093_479,tree093_596,tree093_77,tree093_79,tree093_81,tree093_13]
def tree093_598 : CoverTree := CoverTree.reject 348
def tree093_599 : CoverTree := CoverTree.split [tree093_472,tree093_472,tree093_562,tree093_598,tree093_13,tree093_13]
def tree093_600 : CoverTree := CoverTree.split [tree093_482,tree093_599,tree093_84,tree093_16,tree093_86,tree093_13]
def tree093_601 : CoverTree := CoverTree.split [tree093_593,tree093_595,tree093_597,tree093_600,tree093_564,tree093_477]
def tree093_602 : CoverTree := CoverTree.reject 149
def tree093_603 : CoverTree := CoverTree.reject 150
def tree093_604 : CoverTree := CoverTree.split [tree093_72,tree093_72,tree093_72,tree093_602,tree093_603,tree093_13]
def tree093_605 : CoverTree := CoverTree.split [tree093_523,tree093_604,tree093_73,tree093_73,tree093_73,tree093_73]
def tree093_606 : CoverTree := CoverTree.split [tree093_522,tree093_605,tree093_530,tree093_531,tree093_534,tree093_477]
def tree093_607 : CoverTree := CoverTree.split [tree093_572,tree093_577,tree093_582,tree093_592,tree093_601,tree093_606]
def tree093_608 : CoverTree := CoverTree.split [tree093_403,tree093_439,tree093_489,tree093_536,tree093_569,tree093_607]
def tree093_609 : CoverTree := CoverTree.reject 15
def tree093_610 : CoverTree := CoverTree.reject 16
def tree093_611 : CoverTree := CoverTree.reject 103
def tree093_612 : CoverTree := CoverTree.reject 171
def tree093_613 : CoverTree := CoverTree.reject 169
def tree093_614 : CoverTree := CoverTree.reject 173
def tree093_615 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_614,tree093_16,tree093_13,tree093_13]
def tree093_616 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_611,tree093_612,tree093_613,tree093_615]
def tree093_617 : CoverTree := CoverTree.reject 109
def tree093_618 : CoverTree := CoverTree.reject 98
def tree093_619 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_617,tree093_618,tree093_431,tree093_431]
def tree093_620 : CoverTree := CoverTree.split [tree093_229,tree093_229,tree093_609,tree093_610,tree093_616,tree093_619]
def tree093_621 : CoverTree := CoverTree.reject 236
def tree093_622 : CoverTree := CoverTree.reject 175
def tree093_623 : CoverTree := CoverTree.reject 284
def tree093_624 : CoverTree := CoverTree.reject 285
def tree093_625 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_623,tree093_624,tree093_52,tree093_414]
def tree093_626 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_406,tree093_621,tree093_622,tree093_625]
def tree093_627 : CoverTree := CoverTree.reject 226
def tree093_628 : CoverTree := CoverTree.reject 140
def tree093_629 : CoverTree := CoverTree.reject 190
def tree093_630 : CoverTree := CoverTree.reject 191
def tree093_631 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_629,tree093_630,tree093_64,tree093_13]
def tree093_632 : CoverTree := CoverTree.reject 387
def tree093_633 : CoverTree := CoverTree.reject 388
def tree093_634 : CoverTree := CoverTree.split [tree093_15,tree093_632,tree093_633,tree093_13,tree093_13,tree093_13]
def tree093_635 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_237,tree093_634,tree093_13,tree093_13]
def tree093_636 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_627,tree093_628,tree093_631,tree093_635]
def tree093_637 : CoverTree := CoverTree.reject 125
def tree093_638 : CoverTree := CoverTree.reject 286
def tree093_639 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_426,tree093_638,tree093_86,tree093_13]
def tree093_640 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_637,tree093_639,tree093_430,tree093_431]
def tree093_641 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_245,tree093_16,tree093_35,tree093_13]
def tree093_642 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_641,tree093_431,tree093_431,tree093_437]
def tree093_643 : CoverTree := CoverTree.split [tree093_229,tree093_229,tree093_626,tree093_636,tree093_640,tree093_642]
def tree093_644 : CoverTree := CoverTree.reject 307
def tree093_645 : CoverTree := CoverTree.reject 308
def tree093_646 : CoverTree := CoverTree.reject 341
def tree093_647 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_259,tree093_646,tree093_262]
def tree093_648 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_255,tree093_644,tree093_645,tree093_647]
def tree093_649 : CoverTree := CoverTree.reject 309
def tree093_650 : CoverTree := CoverTree.reject 84
def tree093_651 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_650,tree093_199,tree093_201]
def tree093_652 : CoverTree := CoverTree.reject 287
def tree093_653 : CoverTree := CoverTree.reject 389
def tree093_654 : CoverTree := CoverTree.split [tree093_15,tree093_653,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_655 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_652,tree093_654,tree093_52,tree093_272]
def tree093_656 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_649,tree093_651,tree093_165,tree093_655]
def tree093_657 : CoverTree := CoverTree.reject 294
def tree093_658 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_208,tree093_657,tree093_214,tree093_13]
def tree093_659 : CoverTree := CoverTree.reject 342
def tree093_660 : CoverTree := CoverTree.split [tree093_456,tree093_456,tree093_659,tree093_68,tree093_64,tree093_13]
def tree093_661 : CoverTree := CoverTree.split [tree093_459,tree093_460,tree093_14,tree093_463,tree093_13,tree093_13]
def tree093_662 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_658,tree093_455,tree093_660,tree093_661]
def tree093_663 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_466,tree093_79,tree093_81,tree093_13]
def tree093_664 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_283,tree093_16,tree093_86,tree093_13]
def tree093_665 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_663,tree093_664,tree093_471,tree093_477]
def tree093_666 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_530,tree093_531,tree093_487,tree093_477]
def tree093_667 : CoverTree := CoverTree.split [tree093_254,tree093_648,tree093_656,tree093_662,tree093_665,tree093_666]
def tree093_668 : CoverTree := CoverTree.reject 310
def tree093_669 : CoverTree := CoverTree.reject 237
def tree093_670 : CoverTree := CoverTree.split [tree093_297,tree093_298,tree093_668,tree093_669,tree093_544,tree093_545]
def tree093_671 : CoverTree := CoverTree.reject 386
def tree093_672 : CoverTree := CoverTree.reject 227
def tree093_673 : CoverTree := CoverTree.reject 242
def tree093_674 : CoverTree := CoverTree.reject 243
def tree093_675 : CoverTree := CoverTree.split [tree093_12,tree093_673,tree093_674,tree093_13,tree093_13,tree093_13]
def tree093_676 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_675,tree093_135,tree093_52,tree093_13]
def tree093_677 : CoverTree := CoverTree.split [tree093_39,tree093_671,tree093_672,tree093_500,tree093_165,tree093_676]
def tree093_678 : CoverTree := CoverTree.split [tree093_456,tree093_456,tree093_66,tree093_68,tree093_64,tree093_13]
def tree093_679 : CoverTree := CoverTree.split [tree093_6,tree093_552,tree093_505,tree093_506,tree093_678,tree093_511]
def tree093_680 : CoverTree := CoverTree.reject 378
def tree093_681 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_71,tree093_680,tree093_73,tree093_73]
def tree093_682 : CoverTree := CoverTree.split [tree093_513,tree093_681,tree093_516,tree093_560,tree093_471,tree093_477]
def tree093_683 : CoverTree := CoverTree.split [tree093_296,tree093_670,tree093_677,tree093_679,tree093_682,tree093_535]
def tree093_684 : CoverTree := CoverTree.reject 311
def tree093_685 : CoverTree := CoverTree.reject 201
def tree093_686 : CoverTree := CoverTree.split [tree093_361,tree093_362,tree093_363,tree093_364,tree093_684,tree093_685]
def tree093_687 : CoverTree := CoverTree.reject 312
def tree093_688 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_541,tree093_378,tree093_262]
def tree093_689 : CoverTree := CoverTree.split [tree093_297,tree093_333,tree093_687,tree093_688,tree093_544,tree093_545]
def tree093_690 : CoverTree := CoverTree.reject 358
def tree093_691 : CoverTree := CoverTree.split [tree093_39,tree093_690,tree093_548,tree093_549,tree093_165,tree093_550]
def tree093_692 : CoverTree := CoverTree.split [tree093_686,tree093_689,tree093_691,tree093_557,tree093_565,tree093_606]
def tree093_693 : CoverTree := CoverTree.reject 202
def tree093_694 : CoverTree := CoverTree.split [tree093_361,tree093_362,tree093_363,tree093_364,tree093_570,tree093_693]
def tree093_695 : CoverTree := CoverTree.reject 379
def tree093_696 : CoverTree := CoverTree.reject 380
def tree093_697 : CoverTree := CoverTree.reject 381
def tree093_698 : CoverTree := CoverTree.split [tree093_72,tree093_72,tree093_72,tree093_697,tree093_13,tree093_13]
def tree093_699 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_695,tree093_696,tree093_698]
def tree093_700 : CoverTree := CoverTree.split [tree093_297,tree093_699,tree093_574,tree093_575,tree093_576,tree093_545]
def tree093_701 : CoverTree := CoverTree.split [tree093_694,tree093_700,tree093_582,tree093_592,tree093_601,tree093_606]
def tree093_702 : CoverTree := CoverTree.split [tree093_620,tree093_643,tree093_667,tree093_683,tree093_692,tree093_701]
def tree093_703 : CoverTree := CoverTree.reject 172
def tree093_704 : CoverTree := CoverTree.reject 170
def tree093_705 : CoverTree := CoverTree.reject 288
def tree093_706 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_614,tree093_705,tree093_13,tree093_13]
def tree093_707 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_611,tree093_703,tree093_704,tree093_706]
def tree093_708 : CoverTree := CoverTree.reject 110
def tree093_709 : CoverTree := CoverTree.reject 99
def tree093_710 : CoverTree := CoverTree.reject 100
def tree093_711 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_708,tree093_709,tree093_710,tree093_431]
def tree093_712 : CoverTree := CoverTree.split [tree093_229,tree093_229,tree093_609,tree093_610,tree093_707,tree093_711]
def tree093_713 : CoverTree := CoverTree.reject 65
def tree093_714 : CoverTree := CoverTree.reject 181
def tree093_715 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_713,tree093_714,tree093_201]
def tree093_716 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_713,tree093_49,tree093_13]
def tree093_717 : CoverTree := CoverTree.reject 394
def tree093_718 : CoverTree := CoverTree.reject 395
def tree093_719 : CoverTree := CoverTree.reject 396
def tree093_720 : CoverTree := CoverTree.split [tree093_12,tree093_717,tree093_718,tree093_719,tree093_13,tree093_13]
def tree093_721 : CoverTree := CoverTree.reject 397
def tree093_722 : CoverTree := CoverTree.split [tree093_15,tree093_721,tree093_13,tree093_13,tree093_13,tree093_13]
def tree093_723 : CoverTree := CoverTree.split [tree093_409,tree093_409,tree093_720,tree093_722,tree093_52,tree093_414]
def tree093_724 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_406,tree093_715,tree093_716,tree093_723]
def tree093_725 : CoverTree := CoverTree.reject 189
def tree093_726 : CoverTree := CoverTree.reject 131
def tree093_727 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_208,tree093_725,tree093_726,tree093_13]
def tree093_728 : CoverTree := CoverTree.reject 382
def tree093_729 : CoverTree := CoverTree.reject 349
def tree093_730 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_728,tree093_729,tree093_64,tree093_13]
def tree093_731 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_727,tree093_730,tree093_631,tree093_635]
def tree093_732 : CoverTree := CoverTree.reject 350
def tree093_733 : CoverTree := CoverTree.reject 292
def tree093_734 : CoverTree := CoverTree.reject 293
def tree093_735 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_732,tree093_733,tree093_734,tree093_13]
def tree093_736 : CoverTree := CoverTree.split [tree093_425,tree093_425,tree093_426,tree093_16,tree093_86,tree093_13]
def tree093_737 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_735,tree093_736,tree093_430,tree093_431]
def tree093_738 : CoverTree := CoverTree.split [tree093_229,tree093_229,tree093_724,tree093_731,tree093_737,tree093_642]
def tree093_739 : CoverTree := CoverTree.reject 148
def tree093_740 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_541,tree093_739,tree093_262]
def tree093_741 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_259,tree093_262,tree093_262]
def tree093_742 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_255,tree093_740,tree093_740,tree093_741]
def tree093_743 : CoverTree := CoverTree.reject 83
def tree093_744 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_186,tree093_743,tree093_193]
def tree093_745 : CoverTree := CoverTree.reject 398
def tree093_746 : CoverTree := CoverTree.reject 399
def tree093_747 : CoverTree := CoverTree.reject 400
def tree093_748 : CoverTree := CoverTree.split [tree093_12,tree093_745,tree093_746,tree093_747,tree093_13,tree093_13]
def tree093_749 : CoverTree := CoverTree.split [tree093_447,tree093_447,tree093_748,tree093_654,tree093_52,tree093_272]
def tree093_750 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_744,tree093_651,tree093_165,tree093_749]
def tree093_751 : CoverTree := CoverTree.split [tree093_97,tree093_97,tree093_658,tree093_455,tree093_678,tree093_661]
def tree093_752 : CoverTree := CoverTree.split [tree093_254,tree093_742,tree093_750,tree093_751,tree093_665,tree093_666]
def tree093_753 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_541,tree093_373,tree093_262]
def tree093_754 : CoverTree := CoverTree.reject 393
def tree093_755 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_541,tree093_754,tree093_262]
def tree093_756 : CoverTree := CoverTree.split [tree093_297,tree093_298,tree093_753,tree093_755,tree093_544,tree093_545]
def tree093_757 : CoverTree := CoverTree.reject 241
def tree093_758 : CoverTree := CoverTree.split [tree093_72,tree093_72,tree093_72,tree093_757,tree093_13,tree093_13]
def tree093_759 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_389,tree093_390,tree093_758]
def tree093_760 : CoverTree := CoverTree.split [tree093_39,tree093_759,tree093_548,tree093_500,tree093_165,tree093_676]
def tree093_761 : CoverTree := CoverTree.split [tree093_513,tree093_558,tree093_516,tree093_560,tree093_471,tree093_477]
def tree093_762 : CoverTree := CoverTree.split [tree093_296,tree093_756,tree093_760,tree093_679,tree093_761,tree093_535]
def tree093_763 : CoverTree := CoverTree.reject 392
def tree093_764 : CoverTree := CoverTree.split [tree093_261,tree093_261,tree093_763,tree093_13,tree093_13,tree093_13]
def tree093_765 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_541,tree093_366,tree093_764]
def tree093_766 : CoverTree := CoverTree.reject 64
def tree093_767 : CoverTree := CoverTree.split [tree093_258,tree093_258,tree093_258,tree093_766,tree093_262,tree093_262]
def tree093_768 : CoverTree := CoverTree.split [tree093_361,tree093_362,tree093_363,tree093_364,tree093_765,tree093_767]
def tree093_769 : CoverTree := CoverTree.split [tree093_297,tree093_333,tree093_753,tree093_688,tree093_544,tree093_545]
def tree093_770 : CoverTree := CoverTree.split [tree093_164,tree093_164,tree093_164,tree093_389,tree093_390,tree093_73]
def tree093_771 : CoverTree := CoverTree.split [tree093_39,tree093_770,tree093_548,tree093_549,tree093_165,tree093_550]
def tree093_772 : CoverTree := CoverTree.split [tree093_768,tree093_769,tree093_771,tree093_557,tree093_565,tree093_606]
def tree093_773 : CoverTree := CoverTree.split [tree093_361,tree093_362,tree093_363,tree093_364,tree093_570,tree093_767]
def tree093_774 : CoverTree := CoverTree.split [tree093_773,tree093_700,tree093_582,tree093_592,tree093_601,tree093_606]
def tree093_775 : CoverTree := CoverTree.split [tree093_712,tree093_738,tree093_752,tree093_762,tree093_772,tree093_774]
def tree093_776 : CoverTree := CoverTree.split [tree093_92,tree093_227,tree093_402,tree093_608,tree093_702,tree093_775]
def tree093 : CoverTree := tree093_776

end Snake9.Shared89
