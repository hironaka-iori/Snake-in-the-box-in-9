import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes009 : List Box := [
[(1,6),(1,5),(1,3),(1,5),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)],
[(1,3),(1,6),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,5),(1,5),(1,4)],
[(1,6),(1,6),(1,6),(1,6),(1,2),(1,2)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,5),(1,5),(1,4),(1,2),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,6),(1,3),(1,6),(1,2),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,2)],
[(1,6),(1,6),(1,2),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,1)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,5),(1,2),(1,5),(1,4),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,5),(1,3),(1,5)],
[(1,6),(1,6),(1,4),(1,5),(1,2),(1,5)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,2),(1,4),(1,5),(1,5)],
[(1,6),(1,6),(1,4),(1,5),(1,3),(1,2)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(6,6),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(1,6)],
[(1,6),(1,4),(1,5),(1,5),(1,2),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(1,2),(1,3),(1,5),(1,4),(1,6)],
[(1,6),(1,6),(6,6),(3,3),(3,3),(2,2)],
[(1,1),(5,5),(2,2),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(2,2),(1,6),(1,6),(1,6)],
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
[(1,6),(1,6),(2,2),(3,3),(5,5),(1,6)],
[(1,1),(5,5),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(4,4),(3,3)],
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
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(1,6),(1,6),(5,5),(5,5),(1,1),(1,6)],
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
[(1,1),(6,6),(2,2),(6,6),(1,6),(1,6)],
[(2,2),(4,4),(2,2),(6,6),(1,6),(1,6)],
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
[(1,1),(6,6),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(4,4),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(2,2),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(4,4),(1,6),(1,6)],
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
[(6,6),(1,1),(5,5),(6,6),(4,4),(1,6)],
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
[(4,4),(5,5),(2,2),(3,3),(1,6),(1,6)],
[(5,5),(3,3),(2,2),(4,4),(1,6),(1,6)],
[(5,5),(3,3),(2,2),(5,5),(1,6),(1,6)],
[(5,5),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(5,5),(4,4),(2,2),(3,3),(1,6),(1,6)],
[(5,5),(4,4),(2,2),(4,4),(1,6),(1,6)],
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

def root009 : Nat := 1489

def tree009_0 : CoverTree := CoverTree.reject 23
def tree009_1 : CoverTree := CoverTree.reject 16
def tree009_2 : CoverTree := CoverTree.reject 13
def tree009_3 : CoverTree := CoverTree.reject 10
def tree009_4 : CoverTree := CoverTree.reject 3
def tree009_5 : CoverTree := CoverTree.reject 60
def tree009_6 : CoverTree := CoverTree.reject 39
def tree009_7 : CoverTree := CoverTree.reject 20
def tree009_8 : CoverTree := CoverTree.reject 195
def tree009_9 : CoverTree := CoverTree.reject 144
def tree009_10 : CoverTree := CoverTree.reject 123
def tree009_11 : CoverTree := CoverTree.reject 107
def tree009_12 : CoverTree := CoverTree.reject 2
def tree009_13 : CoverTree := CoverTree.reject 11
def tree009_14 : CoverTree := CoverTree.accept
def tree009_15 : CoverTree := CoverTree.split [tree009_13,tree009_14,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_16 : CoverTree := CoverTree.reject 8
def tree009_17 : CoverTree := CoverTree.split [tree009_16,tree009_14,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_18 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_19 : CoverTree := CoverTree.split [tree009_7,tree009_8,tree009_9,tree009_10,tree009_11,tree009_18]
def tree009_20 : CoverTree := CoverTree.reject 32
def tree009_21 : CoverTree := CoverTree.reject 33
def tree009_22 : CoverTree := CoverTree.reject 47
def tree009_23 : CoverTree := CoverTree.reject 48
def tree009_24 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_20,tree009_21,tree009_22,tree009_23]
def tree009_25 : CoverTree := CoverTree.reject 170
def tree009_26 : CoverTree := CoverTree.reject 115
def tree009_27 : CoverTree := CoverTree.reject 100
def tree009_28 : CoverTree := CoverTree.split [tree009_24,tree009_25,tree009_26,tree009_27,tree009_18,tree009_18]
def tree009_29 : CoverTree := CoverTree.reject 50
def tree009_30 : CoverTree := CoverTree.reject 51
def tree009_31 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_20,tree009_21,tree009_29,tree009_30]
def tree009_32 : CoverTree := CoverTree.reject 145
def tree009_33 : CoverTree := CoverTree.reject 59
def tree009_34 : CoverTree := CoverTree.split [tree009_13,tree009_33,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_35 : CoverTree := CoverTree.reject 42
def tree009_36 : CoverTree := CoverTree.split [tree009_35,tree009_14,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_37 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_34,tree009_17,tree009_36,tree009_14]
def tree009_38 : CoverTree := CoverTree.split [tree009_31,tree009_32,tree009_37,tree009_18,tree009_18,tree009_18]
def tree009_39 : CoverTree := CoverTree.split [tree009_4,tree009_5,tree009_6,tree009_19,tree009_28,tree009_38]
def tree009_40 : CoverTree := CoverTree.reject 19
def tree009_41 : CoverTree := CoverTree.reject 279
def tree009_42 : CoverTree := CoverTree.reject 221
def tree009_43 : CoverTree := CoverTree.reject 180
def tree009_44 : CoverTree := CoverTree.reject 161
def tree009_45 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_41,tree009_42,tree009_43,tree009_44]
def tree009_46 : CoverTree := CoverTree.reject 21
def tree009_47 : CoverTree := CoverTree.reject 339
def tree009_48 : CoverTree := CoverTree.reject 190
def tree009_49 : CoverTree := CoverTree.reject 135
def tree009_50 : CoverTree := CoverTree.reject 36
def tree009_51 : CoverTree := CoverTree.split [tree009_13,tree009_50,tree009_50,tree009_50,tree009_50,tree009_14]
def tree009_52 : CoverTree := CoverTree.reject 96
def tree009_53 : CoverTree := CoverTree.split [tree009_16,tree009_52,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_54 : CoverTree := CoverTree.reject 22
def tree009_55 : CoverTree := CoverTree.reject 88
def tree009_56 : CoverTree := CoverTree.split [tree009_54,tree009_55,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_57 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_51,tree009_53,tree009_56,tree009_14]
def tree009_58 : CoverTree := CoverTree.reject 89
def tree009_59 : CoverTree := CoverTree.split [tree009_58,tree009_14,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_60 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_15,tree009_17,tree009_59,tree009_14]
def tree009_61 : CoverTree := CoverTree.split [tree009_46,tree009_47,tree009_48,tree009_49,tree009_57,tree009_60]
def tree009_62 : CoverTree := CoverTree.reject 196
def tree009_63 : CoverTree := CoverTree.reject 146
def tree009_64 : CoverTree := CoverTree.reject 44
def tree009_65 : CoverTree := CoverTree.reject 69
def tree009_66 : CoverTree := CoverTree.reject 70
def tree009_67 : CoverTree := CoverTree.split [tree009_13,tree009_64,tree009_65,tree009_66,tree009_14,tree009_14]
def tree009_68 : CoverTree := CoverTree.reject 71
def tree009_69 : CoverTree := CoverTree.reject 72
def tree009_70 : CoverTree := CoverTree.split [tree009_16,tree009_68,tree009_69,tree009_14,tree009_14,tree009_14]
def tree009_71 : CoverTree := CoverTree.split [tree009_54,tree009_14,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_72 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_67,tree009_70,tree009_71,tree009_14]
def tree009_73 : CoverTree := CoverTree.split [tree009_13,tree009_64,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_74 : CoverTree := CoverTree.reject 73
def tree009_75 : CoverTree := CoverTree.split [tree009_16,tree009_74,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_76 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_73,tree009_75,tree009_71,tree009_14]
def tree009_77 : CoverTree := CoverTree.split [tree009_7,tree009_62,tree009_63,tree009_72,tree009_76,tree009_18]
def tree009_78 : CoverTree := CoverTree.reject 49
def tree009_79 : CoverTree := CoverTree.reject 1
def tree009_80 : CoverTree := CoverTree.split [tree009_79,tree009_79,tree009_79,tree009_14,tree009_14,tree009_14]
def tree009_81 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_78,tree009_80,tree009_80,tree009_80]
def tree009_82 : CoverTree := CoverTree.reject 74
def tree009_83 : CoverTree := CoverTree.reject 75
def tree009_84 : CoverTree := CoverTree.split [tree009_13,tree009_82,tree009_83,tree009_14,tree009_14,tree009_14]
def tree009_85 : CoverTree := CoverTree.reject 76
def tree009_86 : CoverTree := CoverTree.split [tree009_16,tree009_85,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_87 : CoverTree := CoverTree.reject 62
def tree009_88 : CoverTree := CoverTree.split [tree009_35,tree009_87,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_89 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_84,tree009_86,tree009_88,tree009_14]
def tree009_90 : CoverTree := CoverTree.reject 77
def tree009_91 : CoverTree := CoverTree.split [tree009_13,tree009_90,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_92 : CoverTree := CoverTree.reject 63
def tree009_93 : CoverTree := CoverTree.split [tree009_92,tree009_14,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_94 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_91,tree009_17,tree009_93,tree009_14]
def tree009_95 : CoverTree := CoverTree.split [tree009_24,tree009_81,tree009_89,tree009_94,tree009_18,tree009_18]
def tree009_96 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_80,tree009_80,tree009_80,tree009_80]
def tree009_97 : CoverTree := CoverTree.split [tree009_31,tree009_96,tree009_37,tree009_18,tree009_18,tree009_18]
def tree009_98 : CoverTree := CoverTree.split [tree009_4,tree009_45,tree009_61,tree009_77,tree009_95,tree009_97]
def tree009_99 : CoverTree := CoverTree.split [tree009_0,tree009_1,tree009_2,tree009_3,tree009_39,tree009_98]
def tree009_100 : CoverTree := CoverTree.reject 24
def tree009_101 : CoverTree := CoverTree.reject 7
def tree009_102 : CoverTree := CoverTree.reject 40
def tree009_103 : CoverTree := CoverTree.reject 38
def tree009_104 : CoverTree := CoverTree.reject 35
def tree009_105 : CoverTree := CoverTree.reject 4
def tree009_106 : CoverTree := CoverTree.reject 125
def tree009_107 : CoverTree := CoverTree.reject 90
def tree009_108 : CoverTree := CoverTree.reject 228
def tree009_109 : CoverTree := CoverTree.reject 229
def tree009_110 : CoverTree := CoverTree.split [tree009_13,tree009_108,tree009_109,tree009_14,tree009_14,tree009_14]
def tree009_111 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_110,tree009_17,tree009_14,tree009_14]
def tree009_112 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_106,tree009_107,tree009_18,tree009_111]
def tree009_113 : CoverTree := CoverTree.split [tree009_4,tree009_101,tree009_102,tree009_103,tree009_104,tree009_112]
def tree009_114 : CoverTree := CoverTree.reject 61
def tree009_115 : CoverTree := CoverTree.reject 283
def tree009_116 : CoverTree := CoverTree.reject 185
def tree009_117 : CoverTree := CoverTree.reject 136
def tree009_118 : CoverTree := CoverTree.reject 97
def tree009_119 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_115,tree009_116,tree009_117,tree009_118]
def tree009_120 : CoverTree := CoverTree.reject 153
def tree009_121 : CoverTree := CoverTree.reject 126
def tree009_122 : CoverTree := CoverTree.reject 111
def tree009_123 : CoverTree := CoverTree.reject 235
def tree009_124 : CoverTree := CoverTree.reject 307
def tree009_125 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_123,tree009_124,tree009_14,tree009_14]
def tree009_126 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_120,tree009_121,tree009_122,tree009_125]
def tree009_127 : CoverTree := CoverTree.reject 116
def tree009_128 : CoverTree := CoverTree.reject 127
def tree009_129 : CoverTree := CoverTree.reject 91
def tree009_130 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_127,tree009_128,tree009_129,tree009_18]
def tree009_131 : CoverTree := CoverTree.reject 308
def tree009_132 : CoverTree := CoverTree.reject 236
def tree009_133 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_131,tree009_132,tree009_36,tree009_14]
def tree009_134 : CoverTree := CoverTree.reject 237
def tree009_135 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_134,tree009_17,tree009_14,tree009_14]
def tree009_136 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_133,tree009_135,tree009_18,tree009_18]
def tree009_137 : CoverTree := CoverTree.split [tree009_4,tree009_114,tree009_119,tree009_126,tree009_130,tree009_136]
def tree009_138 : CoverTree := CoverTree.reject 284
def tree009_139 : CoverTree := CoverTree.reject 285
def tree009_140 : CoverTree := CoverTree.reject 199
def tree009_141 : CoverTree := CoverTree.reject 162
def tree009_142 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_138,tree009_139,tree009_140,tree009_141]
def tree009_143 : CoverTree := CoverTree.reject 373
def tree009_144 : CoverTree := CoverTree.reject 200
def tree009_145 : CoverTree := CoverTree.reject 186
def tree009_146 : CoverTree := CoverTree.reject 137
def tree009_147 : CoverTree := CoverTree.reject 355
def tree009_148 : CoverTree := CoverTree.reject 234
def tree009_149 : CoverTree := CoverTree.split [tree009_16,tree009_148,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_150 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_147,tree009_149,tree009_59,tree009_14]
def tree009_151 : CoverTree := CoverTree.split [tree009_46,tree009_143,tree009_144,tree009_145,tree009_146,tree009_150]
def tree009_152 : CoverTree := CoverTree.reject 201
def tree009_153 : CoverTree := CoverTree.reject 154
def tree009_154 : CoverTree := CoverTree.reject 128
def tree009_155 : CoverTree := CoverTree.reject 309
def tree009_156 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_155,tree009_75,tree009_71,tree009_14]
def tree009_157 : CoverTree := CoverTree.reject 238
def tree009_158 : CoverTree := CoverTree.reject 239
def tree009_159 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_157,tree009_158,tree009_14,tree009_14]
def tree009_160 : CoverTree := CoverTree.split [tree009_7,tree009_152,tree009_153,tree009_154,tree009_156,tree009_159]
def tree009_161 : CoverTree := CoverTree.reject 177
def tree009_162 : CoverTree := CoverTree.reject 117
def tree009_163 : CoverTree := CoverTree.reject 310
def tree009_164 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_163,tree009_17,tree009_93,tree009_14]
def tree009_165 : CoverTree := CoverTree.split [tree009_24,tree009_161,tree009_162,tree009_164,tree009_18,tree009_18]
def tree009_166 : CoverTree := CoverTree.reject 155
def tree009_167 : CoverTree := CoverTree.reject 311
def tree009_168 : CoverTree := CoverTree.reject 240
def tree009_169 : CoverTree := CoverTree.reject 241
def tree009_170 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_167,tree009_168,tree009_169,tree009_14]
def tree009_171 : CoverTree := CoverTree.reject 242
def tree009_172 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_171,tree009_17,tree009_14,tree009_14]
def tree009_173 : CoverTree := CoverTree.split [tree009_31,tree009_166,tree009_170,tree009_172,tree009_18,tree009_18]
def tree009_174 : CoverTree := CoverTree.split [tree009_4,tree009_142,tree009_151,tree009_160,tree009_165,tree009_173]
def tree009_175 : CoverTree := CoverTree.reject 286
def tree009_176 : CoverTree := CoverTree.reject 224
def tree009_177 : CoverTree := CoverTree.reject 202
def tree009_178 : CoverTree := CoverTree.reject 30
def tree009_179 : CoverTree := CoverTree.reject 356
def tree009_180 : CoverTree := CoverTree.reject 18
def tree009_181 : CoverTree := CoverTree.reject 391
def tree009_182 : CoverTree := CoverTree.split [tree009_180,tree009_180,tree009_181,tree009_14,tree009_14,tree009_14]
def tree009_183 : CoverTree := CoverTree.split [tree009_180,tree009_180,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_184 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_178,tree009_179,tree009_182,tree009_183]
def tree009_185 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_175,tree009_176,tree009_177,tree009_184]
def tree009_186 : CoverTree := CoverTree.reject 346
def tree009_187 : CoverTree := CoverTree.reject 203
def tree009_188 : CoverTree := CoverTree.reject 139
def tree009_189 : CoverTree := CoverTree.reject 0
def tree009_190 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_53,tree009_56,tree009_14]
def tree009_191 : CoverTree := CoverTree.reject 243
def tree009_192 : CoverTree := CoverTree.reject 244
def tree009_193 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_191,tree009_192,tree009_59,tree009_14]
def tree009_194 : CoverTree := CoverTree.split [tree009_46,tree009_186,tree009_187,tree009_188,tree009_190,tree009_193]
def tree009_195 : CoverTree := CoverTree.reject 204
def tree009_196 : CoverTree := CoverTree.reject 156
def tree009_197 : CoverTree := CoverTree.split [tree009_7,tree009_195,tree009_196,tree009_72,tree009_76,tree009_18]
def tree009_198 : CoverTree := CoverTree.reject 178
def tree009_199 : CoverTree := CoverTree.reject 312
def tree009_200 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_199,tree009_17,tree009_93,tree009_14]
def tree009_201 : CoverTree := CoverTree.split [tree009_24,tree009_198,tree009_89,tree009_200,tree009_18,tree009_18]
def tree009_202 : CoverTree := CoverTree.reject 357
def tree009_203 : CoverTree := CoverTree.reject 358
def tree009_204 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_202,tree009_203,tree009_80,tree009_80]
def tree009_205 : CoverTree := CoverTree.reject 313
def tree009_206 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_205,tree009_17,tree009_36,tree009_14]
def tree009_207 : CoverTree := CoverTree.split [tree009_31,tree009_204,tree009_206,tree009_18,tree009_18,tree009_18]
def tree009_208 : CoverTree := CoverTree.split [tree009_4,tree009_185,tree009_194,tree009_197,tree009_201,tree009_207]
def tree009_209 : CoverTree := CoverTree.reject 191
def tree009_210 : CoverTree := CoverTree.reject 99
def tree009_211 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_178,tree009_209,tree009_210,tree009_183]
def tree009_212 : CoverTree := CoverTree.reject 192
def tree009_213 : CoverTree := CoverTree.reject 5
def tree009_214 : CoverTree := CoverTree.reject 43
def tree009_215 : CoverTree := CoverTree.split [tree009_213,tree009_213,tree009_213,tree009_213,tree009_214,tree009_14]
def tree009_216 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_178,tree009_212,tree009_215,tree009_183]
def tree009_217 : CoverTree := CoverTree.reject 222
def tree009_218 : CoverTree := CoverTree.split [tree009_213,tree009_213,tree009_213,tree009_213,tree009_217,tree009_14]
def tree009_219 : CoverTree := CoverTree.split [tree009_213,tree009_213,tree009_213,tree009_213,tree009_14,tree009_14]
def tree009_220 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_178,tree009_218,tree009_219,tree009_183]
def tree009_221 : CoverTree := CoverTree.reject 101
def tree009_222 : CoverTree := CoverTree.split [tree009_16,tree009_180,tree009_221,tree009_14,tree009_14,tree009_14]
def tree009_223 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_178,tree009_222,tree009_183,tree009_183]
def tree009_224 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_211,tree009_216,tree009_220,tree009_223]
def tree009_225 : CoverTree := CoverTree.reject 347
def tree009_226 : CoverTree := CoverTree.reject 219
def tree009_227 : CoverTree := CoverTree.reject 28
def tree009_228 : CoverTree := CoverTree.reject 108
def tree009_229 : CoverTree := CoverTree.reject 109
def tree009_230 : CoverTree := CoverTree.reject 110
def tree009_231 : CoverTree := CoverTree.split [tree009_54,tree009_228,tree009_229,tree009_230,tree009_14,tree009_14]
def tree009_232 : CoverTree := CoverTree.reject 83
def tree009_233 : CoverTree := CoverTree.reject 84
def tree009_234 : CoverTree := CoverTree.split [tree009_232,tree009_233,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_235 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_226,tree009_227,tree009_231,tree009_234]
def tree009_236 : CoverTree := CoverTree.reject 220
def tree009_237 : CoverTree := CoverTree.reject 359
def tree009_238 : CoverTree := CoverTree.reject 85
def tree009_239 : CoverTree := CoverTree.reject 86
def tree009_240 : CoverTree := CoverTree.split [tree009_54,tree009_238,tree009_239,tree009_14,tree009_14,tree009_14]
def tree009_241 : CoverTree := CoverTree.reject 87
def tree009_242 : CoverTree := CoverTree.split [tree009_241,tree009_14,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_243 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_236,tree009_237,tree009_240,tree009_242]
def tree009_244 : CoverTree := CoverTree.reject 245
def tree009_245 : CoverTree := CoverTree.reject 246
def tree009_246 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_244,tree009_245,tree009_59,tree009_14]
def tree009_247 : CoverTree := CoverTree.split [tree009_46,tree009_225,tree009_235,tree009_243,tree009_57,tree009_246]
def tree009_248 : CoverTree := CoverTree.reject 205
def tree009_249 : CoverTree := CoverTree.reject 29
def tree009_250 : CoverTree := CoverTree.reject 65
def tree009_251 : CoverTree := CoverTree.reject 66
def tree009_252 : CoverTree := CoverTree.reject 67
def tree009_253 : CoverTree := CoverTree.split [tree009_16,tree009_250,tree009_251,tree009_252,tree009_14,tree009_14]
def tree009_254 : CoverTree := CoverTree.reject 68
def tree009_255 : CoverTree := CoverTree.split [tree009_54,tree009_254,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_256 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_249,tree009_253,tree009_255,tree009_14]
def tree009_257 : CoverTree := CoverTree.split [tree009_7,tree009_248,tree009_256,tree009_72,tree009_76,tree009_18]
def tree009_258 : CoverTree := CoverTree.reject 360
def tree009_259 : CoverTree := CoverTree.reject 314
def tree009_260 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_258,tree009_259,tree009_88,tree009_14]
def tree009_261 : CoverTree := CoverTree.split [tree009_24,tree009_81,tree009_260,tree009_94,tree009_18,tree009_18]
def tree009_262 : CoverTree := CoverTree.reject 361
def tree009_263 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_262,tree009_80,tree009_80,tree009_80]
def tree009_264 : CoverTree := CoverTree.reject 315
def tree009_265 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_264,tree009_17,tree009_36,tree009_14]
def tree009_266 : CoverTree := CoverTree.split [tree009_31,tree009_263,tree009_265,tree009_18,tree009_18,tree009_18]
def tree009_267 : CoverTree := CoverTree.split [tree009_4,tree009_224,tree009_247,tree009_257,tree009_261,tree009_266]
def tree009_268 : CoverTree := CoverTree.split [tree009_100,tree009_113,tree009_137,tree009_174,tree009_208,tree009_267]
def tree009_269 : CoverTree := CoverTree.reject 25
def tree009_270 : CoverTree := CoverTree.reject 41
def tree009_271 : CoverTree := CoverTree.reject 206
def tree009_272 : CoverTree := CoverTree.reject 129
def tree009_273 : CoverTree := CoverTree.reject 112
def tree009_274 : CoverTree := CoverTree.reject 352
def tree009_275 : CoverTree := CoverTree.reject 353
def tree009_276 : CoverTree := CoverTree.reject 354
def tree009_277 : CoverTree := CoverTree.split [tree009_13,tree009_274,tree009_275,tree009_276,tree009_14,tree009_14]
def tree009_278 : CoverTree := CoverTree.reject 247
def tree009_279 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_277,tree009_278,tree009_14,tree009_14]
def tree009_280 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_271,tree009_272,tree009_273,tree009_279]
def tree009_281 : CoverTree := CoverTree.reject 118
def tree009_282 : CoverTree := CoverTree.reject 104
def tree009_283 : CoverTree := CoverTree.reject 92
def tree009_284 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_281,tree009_282,tree009_283,tree009_18]
def tree009_285 : CoverTree := CoverTree.reject 102
def tree009_286 : CoverTree := CoverTree.reject 248
def tree009_287 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_285,tree009_286,tree009_36,tree009_14]
def tree009_288 : CoverTree := CoverTree.reject 249
def tree009_289 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_288,tree009_17,tree009_14,tree009_14]
def tree009_290 : CoverTree := CoverTree.reject 250
def tree009_291 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_290,tree009_17,tree009_14,tree009_14]
def tree009_292 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_287,tree009_289,tree009_291,tree009_111]
def tree009_293 : CoverTree := CoverTree.split [tree009_4,tree009_101,tree009_270,tree009_280,tree009_284,tree009_292]
def tree009_294 : CoverTree := CoverTree.reject 122
def tree009_295 : CoverTree := CoverTree.reject 287
def tree009_296 : CoverTree := CoverTree.reject 288
def tree009_297 : CoverTree := CoverTree.reject 151
def tree009_298 : CoverTree := CoverTree.reject 316
def tree009_299 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_178,tree009_297,tree009_298,tree009_183]
def tree009_300 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_294,tree009_295,tree009_296,tree009_299]
def tree009_301 : CoverTree := CoverTree.reject 289
def tree009_302 : CoverTree := CoverTree.reject 187
def tree009_303 : CoverTree := CoverTree.reject 138
def tree009_304 : CoverTree := CoverTree.reject 251
def tree009_305 : CoverTree := CoverTree.reject 252
def tree009_306 : CoverTree := CoverTree.reject 253
def tree009_307 : CoverTree := CoverTree.reject 305
def tree009_308 : CoverTree := CoverTree.split [tree009_14,tree009_307,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_309 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_304,tree009_305,tree009_306,tree009_308]
def tree009_310 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_301,tree009_302,tree009_303,tree009_309]
def tree009_311 : CoverTree := CoverTree.reject 157
def tree009_312 : CoverTree := CoverTree.reject 130
def tree009_313 : CoverTree := CoverTree.reject 113
def tree009_314 : CoverTree := CoverTree.reject 254
def tree009_315 : CoverTree := CoverTree.reject 317
def tree009_316 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_314,tree009_315,tree009_14,tree009_14]
def tree009_317 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_311,tree009_312,tree009_313,tree009_316]
def tree009_318 : CoverTree := CoverTree.reject 119
def tree009_319 : CoverTree := CoverTree.reject 103
def tree009_320 : CoverTree := CoverTree.reject 255
def tree009_321 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_319,tree009_320,tree009_93,tree009_14]
def tree009_322 : CoverTree := CoverTree.reject 256
def tree009_323 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_322,tree009_17,tree009_14,tree009_14]
def tree009_324 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_318,tree009_321,tree009_323,tree009_18]
def tree009_325 : CoverTree := CoverTree.reject 318
def tree009_326 : CoverTree := CoverTree.reject 257
def tree009_327 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_325,tree009_326,tree009_36,tree009_14]
def tree009_328 : CoverTree := CoverTree.reject 258
def tree009_329 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_328,tree009_17,tree009_14,tree009_14]
def tree009_330 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_327,tree009_329,tree009_18,tree009_18]
def tree009_331 : CoverTree := CoverTree.split [tree009_4,tree009_300,tree009_310,tree009_317,tree009_324,tree009_330]
def tree009_332 : CoverTree := CoverTree.reject 290
def tree009_333 : CoverTree := CoverTree.reject 291
def tree009_334 : CoverTree := CoverTree.reject 207
def tree009_335 : CoverTree := CoverTree.reject 362
def tree009_336 : CoverTree := CoverTree.reject 319
def tree009_337 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_178,tree009_335,tree009_336,tree009_183]
def tree009_338 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_332,tree009_333,tree009_334,tree009_337]
def tree009_339 : CoverTree := CoverTree.reject 374
def tree009_340 : CoverTree := CoverTree.reject 208
def tree009_341 : CoverTree := CoverTree.reject 188
def tree009_342 : CoverTree := CoverTree.reject 320
def tree009_343 : CoverTree := CoverTree.reject 321
def tree009_344 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_342,tree009_343,tree009_14]
def tree009_345 : CoverTree := CoverTree.reject 363
def tree009_346 : CoverTree := CoverTree.reject 322
def tree009_347 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_345,tree009_346,tree009_59,tree009_14]
def tree009_348 : CoverTree := CoverTree.split [tree009_46,tree009_339,tree009_340,tree009_341,tree009_344,tree009_347]
def tree009_349 : CoverTree := CoverTree.reject 209
def tree009_350 : CoverTree := CoverTree.reject 184
def tree009_351 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_249,tree009_350,tree009_255,tree009_14]
def tree009_352 : CoverTree := CoverTree.reject 323
def tree009_353 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_352,tree009_75,tree009_71,tree009_14]
def tree009_354 : CoverTree := CoverTree.split [tree009_7,tree009_349,tree009_351,tree009_72,tree009_353,tree009_18]
def tree009_355 : CoverTree := CoverTree.reject 179
def tree009_356 : CoverTree := CoverTree.reject 152
def tree009_357 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_356,tree009_86,tree009_88,tree009_14]
def tree009_358 : CoverTree := CoverTree.reject 324
def tree009_359 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_358,tree009_17,tree009_93,tree009_14]
def tree009_360 : CoverTree := CoverTree.split [tree009_24,tree009_355,tree009_357,tree009_359,tree009_18,tree009_18]
def tree009_361 : CoverTree := CoverTree.reject 380
def tree009_362 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_361,tree009_80,tree009_80,tree009_80]
def tree009_363 : CoverTree := CoverTree.split [tree009_31,tree009_362,tree009_37,tree009_18,tree009_18,tree009_18]
def tree009_364 : CoverTree := CoverTree.split [tree009_4,tree009_338,tree009_348,tree009_354,tree009_360,tree009_363]
def tree009_365 : CoverTree := CoverTree.reject 292
def tree009_366 : CoverTree := CoverTree.reject 225
def tree009_367 : CoverTree := CoverTree.reject 210
def tree009_368 : CoverTree := CoverTree.reject 364
def tree009_369 : CoverTree := CoverTree.reject 392
def tree009_370 : CoverTree := CoverTree.split [tree009_180,tree009_180,tree009_369,tree009_14,tree009_14,tree009_14]
def tree009_371 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_178,tree009_368,tree009_370,tree009_183]
def tree009_372 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_365,tree009_366,tree009_367,tree009_371]
def tree009_373 : CoverTree := CoverTree.reject 348
def tree009_374 : CoverTree := CoverTree.reject 211
def tree009_375 : CoverTree := CoverTree.reject 365
def tree009_376 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_375,tree009_240,tree009_242]
def tree009_377 : CoverTree := CoverTree.reject 259
def tree009_378 : CoverTree := CoverTree.reject 260
def tree009_379 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_377,tree009_378,tree009_59,tree009_14]
def tree009_380 : CoverTree := CoverTree.split [tree009_46,tree009_373,tree009_374,tree009_376,tree009_190,tree009_379]
def tree009_381 : CoverTree := CoverTree.reject 212
def tree009_382 : CoverTree := CoverTree.reject 381
def tree009_383 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_249,tree009_382,tree009_255,tree009_14]
def tree009_384 : CoverTree := CoverTree.split [tree009_7,tree009_381,tree009_383,tree009_72,tree009_76,tree009_18]
def tree009_385 : CoverTree := CoverTree.reject 366
def tree009_386 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_78,tree009_385,tree009_80,tree009_80]
def tree009_387 : CoverTree := CoverTree.split [tree009_24,tree009_386,tree009_89,tree009_94,tree009_18,tree009_18]
def tree009_388 : CoverTree := CoverTree.reject 325
def tree009_389 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_388,tree009_17,tree009_36,tree009_14]
def tree009_390 : CoverTree := CoverTree.split [tree009_31,tree009_96,tree009_389,tree009_18,tree009_18,tree009_18]
def tree009_391 : CoverTree := CoverTree.split [tree009_4,tree009_372,tree009_380,tree009_384,tree009_387,tree009_390]
def tree009_392 : CoverTree := CoverTree.reject 193
def tree009_393 : CoverTree := CoverTree.reject 53
def tree009_394 : CoverTree := CoverTree.reject 54
def tree009_395 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_392,tree009_393,tree009_394,tree009_80]
def tree009_396 : CoverTree := CoverTree.reject 171
def tree009_397 : CoverTree := CoverTree.reject 172
def tree009_398 : CoverTree := CoverTree.split [tree009_16,tree009_396,tree009_397,tree009_14,tree009_14,tree009_14]
def tree009_399 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_236,tree009_398,tree009_240,tree009_242]
def tree009_400 : CoverTree := CoverTree.split [tree009_46,tree009_395,tree009_235,tree009_399,tree009_57,tree009_60]
def tree009_401 : CoverTree := CoverTree.reject 45
def tree009_402 : CoverTree := CoverTree.reject 46
def tree009_403 : CoverTree := CoverTree.split [tree009_12,tree009_12,tree009_401,tree009_402,tree009_80,tree009_80]
def tree009_404 : CoverTree := CoverTree.split [tree009_7,tree009_403,tree009_256,tree009_72,tree009_76,tree009_18]
def tree009_405 : CoverTree := CoverTree.split [tree009_4,tree009_224,tree009_400,tree009_404,tree009_95,tree009_97]
def tree009_406 : CoverTree := CoverTree.split [tree009_269,tree009_293,tree009_331,tree009_364,tree009_391,tree009_405]
def tree009_407 : CoverTree := CoverTree.reject 26
def tree009_408 : CoverTree := CoverTree.reject 197
def tree009_409 : CoverTree := CoverTree.reject 149
def tree009_410 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_227,tree009_408,tree009_409]
def tree009_411 : CoverTree := CoverTree.reject 226
def tree009_412 : CoverTree := CoverTree.reject 166
def tree009_413 : CoverTree := CoverTree.reject 12
def tree009_414 : CoverTree := CoverTree.reject 261
def tree009_415 : CoverTree := CoverTree.reject 262
def tree009_416 : CoverTree := CoverTree.reject 263
def tree009_417 : CoverTree := CoverTree.reject 351
def tree009_418 : CoverTree := CoverTree.split [tree009_14,tree009_417,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_419 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_414,tree009_415,tree009_416,tree009_418]
def tree009_420 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_410,tree009_411,tree009_412,tree009_419]
def tree009_421 : CoverTree := CoverTree.reject 213
def tree009_422 : CoverTree := CoverTree.reject 131
def tree009_423 : CoverTree := CoverTree.reject 114
def tree009_424 : CoverTree := CoverTree.reject 17
def tree009_425 : CoverTree := CoverTree.reject 264
def tree009_426 : CoverTree := CoverTree.reject 265
def tree009_427 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_425,tree009_426,tree009_14,tree009_14]
def tree009_428 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_421,tree009_422,tree009_423,tree009_427]
def tree009_429 : CoverTree := CoverTree.reject 120
def tree009_430 : CoverTree := CoverTree.reject 9
def tree009_431 : CoverTree := CoverTree.reject 150
def tree009_432 : CoverTree := CoverTree.reject 266
def tree009_433 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_431,tree009_432,tree009_93,tree009_14]
def tree009_434 : CoverTree := CoverTree.reject 134
def tree009_435 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_434,tree009_17,tree009_14,tree009_14]
def tree009_436 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_437 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_429,tree009_433,tree009_435,tree009_436]
def tree009_438 : CoverTree := CoverTree.reject 267
def tree009_439 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_285,tree009_438,tree009_36,tree009_14]
def tree009_440 : CoverTree := CoverTree.reject 268
def tree009_441 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_440,tree009_17,tree009_14,tree009_14]
def tree009_442 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_110,tree009_17,tree009_14,tree009_14]
def tree009_443 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_439,tree009_441,tree009_436,tree009_442]
def tree009_444 : CoverTree := CoverTree.split [tree009_4,tree009_101,tree009_420,tree009_428,tree009_437,tree009_443]
def tree009_445 : CoverTree := CoverTree.reject 293
def tree009_446 : CoverTree := CoverTree.reject 294
def tree009_447 : CoverTree := CoverTree.reject 326
def tree009_448 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_178,tree009_297,tree009_447,tree009_183]
def tree009_449 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_294,tree009_445,tree009_446,tree009_448]
def tree009_450 : CoverTree := CoverTree.reject 295
def tree009_451 : CoverTree := CoverTree.reject 189
def tree009_452 : CoverTree := CoverTree.reject 269
def tree009_453 : CoverTree := CoverTree.reject 270
def tree009_454 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_452,tree009_453,tree009_59,tree009_308]
def tree009_455 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_450,tree009_451,tree009_190,tree009_454]
def tree009_456 : CoverTree := CoverTree.reject 158
def tree009_457 : CoverTree := CoverTree.reject 198
def tree009_458 : CoverTree := CoverTree.reject 174
def tree009_459 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_457,tree009_458,tree009_71,tree009_14]
def tree009_460 : CoverTree := CoverTree.reject 52
def tree009_461 : CoverTree := CoverTree.reject 327
def tree009_462 : CoverTree := CoverTree.split [tree009_460,tree009_460,tree009_461,tree009_75,tree009_71,tree009_14]
def tree009_463 : CoverTree := CoverTree.reject 82
def tree009_464 : CoverTree := CoverTree.reject 175
def tree009_465 : CoverTree := CoverTree.reject 271
def tree009_466 : CoverTree := CoverTree.reject 230
def tree009_467 : CoverTree := CoverTree.split [tree009_16,tree009_466,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_468 : CoverTree := CoverTree.split [tree009_463,tree009_464,tree009_465,tree009_467,tree009_14,tree009_14]
def tree009_469 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_456,tree009_459,tree009_462,tree009_468]
def tree009_470 : CoverTree := CoverTree.reject 176
def tree009_471 : CoverTree := CoverTree.reject 328
def tree009_472 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_470,tree009_471,tree009_88,tree009_14]
def tree009_473 : CoverTree := CoverTree.reject 272
def tree009_474 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_319,tree009_473,tree009_93,tree009_14]
def tree009_475 : CoverTree := CoverTree.split [tree009_460,tree009_460,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_476 : CoverTree := CoverTree.reject 6
def tree009_477 : CoverTree := CoverTree.reject 31
def tree009_478 : CoverTree := CoverTree.reject 27
def tree009_479 : CoverTree := CoverTree.split [tree009_476,tree009_476,tree009_477,tree009_478,tree009_14,tree009_14]
def tree009_480 : CoverTree := CoverTree.split [tree009_476,tree009_476,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_481 : CoverTree := CoverTree.split [tree009_479,tree009_480,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_482 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_472,tree009_474,tree009_475,tree009_481]
def tree009_483 : CoverTree := CoverTree.reject 56
def tree009_484 : CoverTree := CoverTree.reject 367
def tree009_485 : CoverTree := CoverTree.split [tree009_483,tree009_484,tree009_34,tree009_17,tree009_36,tree009_14]
def tree009_486 : CoverTree := CoverTree.reject 57
def tree009_487 : CoverTree := CoverTree.reject 329
def tree009_488 : CoverTree := CoverTree.reject 273
def tree009_489 : CoverTree := CoverTree.split [tree009_486,tree009_487,tree009_488,tree009_17,tree009_14,tree009_14]
def tree009_490 : CoverTree := CoverTree.reject 343
def tree009_491 : CoverTree := CoverTree.split [tree009_490,tree009_480,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_492 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_485,tree009_489,tree009_491,tree009_481]
def tree009_493 : CoverTree := CoverTree.split [tree009_4,tree009_449,tree009_455,tree009_469,tree009_482,tree009_492]
def tree009_494 : CoverTree := CoverTree.reject 296
def tree009_495 : CoverTree := CoverTree.reject 297
def tree009_496 : CoverTree := CoverTree.reject 214
def tree009_497 : CoverTree := CoverTree.reject 368
def tree009_498 : CoverTree := CoverTree.reject 330
def tree009_499 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_178,tree009_497,tree009_498,tree009_183]
def tree009_500 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_494,tree009_495,tree009_496,tree009_499]
def tree009_501 : CoverTree := CoverTree.reject 375
def tree009_502 : CoverTree := CoverTree.reject 215
def tree009_503 : CoverTree := CoverTree.reject 80
def tree009_504 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_503,tree009_240,tree009_242]
def tree009_505 : CoverTree := CoverTree.reject 369
def tree009_506 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_505,tree009_149,tree009_59,tree009_14]
def tree009_507 : CoverTree := CoverTree.split [tree009_46,tree009_501,tree009_502,tree009_504,tree009_190,tree009_506]
def tree009_508 : CoverTree := CoverTree.reject 216
def tree009_509 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_249,tree009_350,tree009_255,tree009_14]
def tree009_510 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_67,tree009_70,tree009_71,tree009_14]
def tree009_511 : CoverTree := CoverTree.reject 331
def tree009_512 : CoverTree := CoverTree.split [tree009_460,tree009_460,tree009_511,tree009_75,tree009_71,tree009_14]
def tree009_513 : CoverTree := CoverTree.reject 147
def tree009_514 : CoverTree := CoverTree.split [tree009_476,tree009_476,tree009_513,tree009_14,tree009_14,tree009_14]
def tree009_515 : CoverTree := CoverTree.split [tree009_463,tree009_514,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_516 : CoverTree := CoverTree.split [tree009_7,tree009_508,tree009_509,tree009_510,tree009_512,tree009_515]
def tree009_517 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_20,tree009_21,tree009_22,tree009_23]
def tree009_518 : CoverTree := CoverTree.reject 370
def tree009_519 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_78,tree009_518,tree009_80,tree009_80]
def tree009_520 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_356,tree009_86,tree009_88,tree009_14]
def tree009_521 : CoverTree := CoverTree.reject 332
def tree009_522 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_521,tree009_17,tree009_93,tree009_14]
def tree009_523 : CoverTree := CoverTree.split [tree009_517,tree009_519,tree009_520,tree009_522,tree009_475,tree009_481]
def tree009_524 : CoverTree := CoverTree.reject 81
def tree009_525 : CoverTree := CoverTree.reject 55
def tree009_526 : CoverTree := CoverTree.split [tree009_524,tree009_525,tree009_20,tree009_21,tree009_29,tree009_30]
def tree009_527 : CoverTree := CoverTree.reject 64
def tree009_528 : CoverTree := CoverTree.reject 344
def tree009_529 : CoverTree := CoverTree.reject 306
def tree009_530 : CoverTree := CoverTree.split [tree009_79,tree009_79,tree009_79,tree009_529,tree009_14,tree009_14]
def tree009_531 : CoverTree := CoverTree.split [tree009_527,tree009_528,tree009_530,tree009_80,tree009_80,tree009_80]
def tree009_532 : CoverTree := CoverTree.reject 133
def tree009_533 : CoverTree := CoverTree.split [tree009_476,tree009_476,tree009_532,tree009_14,tree009_14,tree009_14]
def tree009_534 : CoverTree := CoverTree.split [tree009_483,tree009_533,tree009_34,tree009_17,tree009_36,tree009_14]
def tree009_535 : CoverTree := CoverTree.split [tree009_486,tree009_480,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_536 : CoverTree := CoverTree.reject 148
def tree009_537 : CoverTree := CoverTree.split [tree009_476,tree009_476,tree009_477,tree009_478,tree009_14,tree009_536]
def tree009_538 : CoverTree := CoverTree.split [tree009_537,tree009_480,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_539 : CoverTree := CoverTree.split [tree009_526,tree009_531,tree009_534,tree009_535,tree009_538,tree009_481]
def tree009_540 : CoverTree := CoverTree.split [tree009_4,tree009_500,tree009_507,tree009_516,tree009_523,tree009_539]
def tree009_541 : CoverTree := CoverTree.reject 298
def tree009_542 : CoverTree := CoverTree.reject 34
def tree009_543 : CoverTree := CoverTree.reject 389
def tree009_544 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_542,tree009_543,tree009_183]
def tree009_545 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_542,tree009_219,tree009_183]
def tree009_546 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_178,tree009_222,tree009_183,tree009_183]
def tree009_547 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_541,tree009_544,tree009_545,tree009_546]
def tree009_548 : CoverTree := CoverTree.reject 349
def tree009_549 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_227,tree009_231,tree009_234]
def tree009_550 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_398,tree009_240,tree009_242]
def tree009_551 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_15,tree009_17,tree009_59,tree009_14]
def tree009_552 : CoverTree := CoverTree.split [tree009_46,tree009_548,tree009_549,tree009_550,tree009_190,tree009_551]
def tree009_553 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_401,tree009_402,tree009_80,tree009_80]
def tree009_554 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_249,tree009_253,tree009_255,tree009_14]
def tree009_555 : CoverTree := CoverTree.reject 194
def tree009_556 : CoverTree := CoverTree.reject 345
def tree009_557 : CoverTree := CoverTree.split [tree009_555,tree009_556,tree009_73,tree009_75,tree009_71,tree009_14]
def tree009_558 : CoverTree := CoverTree.split [tree009_7,tree009_553,tree009_554,tree009_510,tree009_557,tree009_515]
def tree009_559 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_78,tree009_80,tree009_80,tree009_80]
def tree009_560 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_84,tree009_86,tree009_88,tree009_14]
def tree009_561 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_91,tree009_17,tree009_93,tree009_14]
def tree009_562 : CoverTree := CoverTree.reject 143
def tree009_563 : CoverTree := CoverTree.reject 168
def tree009_564 : CoverTree := CoverTree.split [tree009_476,tree009_476,tree009_563,tree009_14,tree009_14,tree009_14]
def tree009_565 : CoverTree := CoverTree.split [tree009_562,tree009_564,tree009_15,tree009_17,tree009_14,tree009_14]
def tree009_566 : CoverTree := CoverTree.split [tree009_517,tree009_559,tree009_560,tree009_561,tree009_565,tree009_481]
def tree009_567 : CoverTree := CoverTree.reject 390
def tree009_568 : CoverTree := CoverTree.split [tree009_527,tree009_567,tree009_80,tree009_80,tree009_80,tree009_80]
def tree009_569 : CoverTree := CoverTree.split [tree009_526,tree009_568,tree009_534,tree009_535,tree009_538,tree009_481]
def tree009_570 : CoverTree := CoverTree.split [tree009_4,tree009_547,tree009_552,tree009_558,tree009_566,tree009_569]
def tree009_571 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_178,tree009_209,tree009_210,tree009_183]
def tree009_572 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_178,tree009_212,tree009_215,tree009_183]
def tree009_573 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_178,tree009_218,tree009_219,tree009_183]
def tree009_574 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_571,tree009_572,tree009_573,tree009_546]
def tree009_575 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_392,tree009_393,tree009_394,tree009_80]
def tree009_576 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_226,tree009_227,tree009_231,tree009_234]
def tree009_577 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_236,tree009_398,tree009_240,tree009_242]
def tree009_578 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_51,tree009_53,tree009_56,tree009_14]
def tree009_579 : CoverTree := CoverTree.split [tree009_46,tree009_575,tree009_576,tree009_577,tree009_578,tree009_551]
def tree009_580 : CoverTree := CoverTree.reject 335
def tree009_581 : CoverTree := CoverTree.split [tree009_527,tree009_580,tree009_401,tree009_402,tree009_80,tree009_80]
def tree009_582 : CoverTree := CoverTree.reject 336
def tree009_583 : CoverTree := CoverTree.split [tree009_483,tree009_582,tree009_249,tree009_253,tree009_255,tree009_14]
def tree009_584 : CoverTree := CoverTree.reject 337
def tree009_585 : CoverTree := CoverTree.split [tree009_486,tree009_584,tree009_67,tree009_70,tree009_71,tree009_14]
def tree009_586 : CoverTree := CoverTree.reject 37
def tree009_587 : CoverTree := CoverTree.split [tree009_476,tree009_476,tree009_586,tree009_586,tree009_586,tree009_14]
def tree009_588 : CoverTree := CoverTree.split [tree009_555,tree009_587,tree009_73,tree009_75,tree009_71,tree009_14]
def tree009_589 : CoverTree := CoverTree.split [tree009_7,tree009_581,tree009_583,tree009_585,tree009_588,tree009_515]
def tree009_590 : CoverTree := CoverTree.split [tree009_524,tree009_525,tree009_20,tree009_21,tree009_22,tree009_23]
def tree009_591 : CoverTree := CoverTree.reject 338
def tree009_592 : CoverTree := CoverTree.split [tree009_527,tree009_591,tree009_78,tree009_80,tree009_80,tree009_80]
def tree009_593 : CoverTree := CoverTree.reject 169
def tree009_594 : CoverTree := CoverTree.split [tree009_483,tree009_593,tree009_84,tree009_86,tree009_88,tree009_14]
def tree009_595 : CoverTree := CoverTree.reject 340
def tree009_596 : CoverTree := CoverTree.split [tree009_476,tree009_476,tree009_563,tree009_595,tree009_14,tree009_14]
def tree009_597 : CoverTree := CoverTree.split [tree009_486,tree009_596,tree009_91,tree009_17,tree009_93,tree009_14]
def tree009_598 : CoverTree := CoverTree.split [tree009_590,tree009_592,tree009_594,tree009_597,tree009_565,tree009_481]
def tree009_599 : CoverTree := CoverTree.reject 141
def tree009_600 : CoverTree := CoverTree.reject 142
def tree009_601 : CoverTree := CoverTree.split [tree009_79,tree009_79,tree009_79,tree009_599,tree009_600,tree009_14]
def tree009_602 : CoverTree := CoverTree.split [tree009_527,tree009_601,tree009_80,tree009_80,tree009_80,tree009_80]
def tree009_603 : CoverTree := CoverTree.split [tree009_526,tree009_602,tree009_534,tree009_535,tree009_538,tree009_481]
def tree009_604 : CoverTree := CoverTree.split [tree009_4,tree009_574,tree009_579,tree009_589,tree009_598,tree009_603]
def tree009_605 : CoverTree := CoverTree.split [tree009_407,tree009_444,tree009_493,tree009_540,tree009_570,tree009_604]
def tree009_606 : CoverTree := CoverTree.reject 15
def tree009_607 : CoverTree := CoverTree.reject 14
def tree009_608 : CoverTree := CoverTree.reject 98
def tree009_609 : CoverTree := CoverTree.reject 163
def tree009_610 : CoverTree := CoverTree.reject 159
def tree009_611 : CoverTree := CoverTree.reject 165
def tree009_612 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_611,tree009_17,tree009_14,tree009_14]
def tree009_613 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_608,tree009_609,tree009_610,tree009_612]
def tree009_614 : CoverTree := CoverTree.reject 105
def tree009_615 : CoverTree := CoverTree.reject 93
def tree009_616 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_614,tree009_615,tree009_436,tree009_436]
def tree009_617 : CoverTree := CoverTree.split [tree009_4,tree009_101,tree009_606,tree009_607,tree009_613,tree009_616]
def tree009_618 : CoverTree := CoverTree.reject 227
def tree009_619 : CoverTree := CoverTree.reject 167
def tree009_620 : CoverTree := CoverTree.reject 274
def tree009_621 : CoverTree := CoverTree.reject 275
def tree009_622 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_620,tree009_621,tree009_59,tree009_418]
def tree009_623 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_410,tree009_618,tree009_619,tree009_622]
def tree009_624 : CoverTree := CoverTree.reject 217
def tree009_625 : CoverTree := CoverTree.reject 132
def tree009_626 : CoverTree := CoverTree.reject 182
def tree009_627 : CoverTree := CoverTree.reject 183
def tree009_628 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_626,tree009_627,tree009_71,tree009_14]
def tree009_629 : CoverTree := CoverTree.reject 377
def tree009_630 : CoverTree := CoverTree.reject 378
def tree009_631 : CoverTree := CoverTree.split [tree009_16,tree009_629,tree009_630,tree009_14,tree009_14,tree009_14]
def tree009_632 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_277,tree009_631,tree009_14,tree009_14]
def tree009_633 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_624,tree009_625,tree009_628,tree009_632]
def tree009_634 : CoverTree := CoverTree.reject 121
def tree009_635 : CoverTree := CoverTree.reject 276
def tree009_636 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_431,tree009_635,tree009_93,tree009_14]
def tree009_637 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_634,tree009_636,tree009_435,tree009_436]
def tree009_638 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_285,tree009_17,tree009_36,tree009_14]
def tree009_639 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_638,tree009_436,tree009_436,tree009_442]
def tree009_640 : CoverTree := CoverTree.split [tree009_4,tree009_101,tree009_623,tree009_633,tree009_637,tree009_639]
def tree009_641 : CoverTree := CoverTree.reject 299
def tree009_642 : CoverTree := CoverTree.reject 300
def tree009_643 : CoverTree := CoverTree.reject 333
def tree009_644 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_178,tree009_297,tree009_643,tree009_183]
def tree009_645 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_294,tree009_641,tree009_642,tree009_644]
def tree009_646 : CoverTree := CoverTree.reject 301
def tree009_647 : CoverTree := CoverTree.reject 79
def tree009_648 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_647,tree009_240,tree009_242]
def tree009_649 : CoverTree := CoverTree.reject 277
def tree009_650 : CoverTree := CoverTree.reject 379
def tree009_651 : CoverTree := CoverTree.split [tree009_16,tree009_650,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_652 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_649,tree009_651,tree009_59,tree009_308]
def tree009_653 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_646,tree009_648,tree009_190,tree009_652]
def tree009_654 : CoverTree := CoverTree.reject 282
def tree009_655 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_249,tree009_654,tree009_255,tree009_14]
def tree009_656 : CoverTree := CoverTree.reject 334
def tree009_657 : CoverTree := CoverTree.split [tree009_460,tree009_460,tree009_656,tree009_75,tree009_71,tree009_14]
def tree009_658 : CoverTree := CoverTree.split [tree009_463,tree009_464,tree009_15,tree009_467,tree009_14,tree009_14]
def tree009_659 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_655,tree009_459,tree009_657,tree009_658]
def tree009_660 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_470,tree009_86,tree009_88,tree009_14]
def tree009_661 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_319,tree009_17,tree009_93,tree009_14]
def tree009_662 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_660,tree009_661,tree009_475,tree009_481]
def tree009_663 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_534,tree009_535,tree009_491,tree009_481]
def tree009_664 : CoverTree := CoverTree.split [tree009_4,tree009_645,tree009_653,tree009_659,tree009_662,tree009_663]
def tree009_665 : CoverTree := CoverTree.reject 302
def tree009_666 : CoverTree := CoverTree.reject 303
def tree009_667 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_665,tree009_666,tree009_545,tree009_546]
def tree009_668 : CoverTree := CoverTree.reject 376
def tree009_669 : CoverTree := CoverTree.reject 218
def tree009_670 : CoverTree := CoverTree.reject 232
def tree009_671 : CoverTree := CoverTree.reject 233
def tree009_672 : CoverTree := CoverTree.split [tree009_13,tree009_670,tree009_671,tree009_14,tree009_14,tree009_14]
def tree009_673 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_672,tree009_149,tree009_59,tree009_14]
def tree009_674 : CoverTree := CoverTree.split [tree009_46,tree009_668,tree009_669,tree009_504,tree009_190,tree009_673]
def tree009_675 : CoverTree := CoverTree.split [tree009_460,tree009_460,tree009_73,tree009_75,tree009_71,tree009_14]
def tree009_676 : CoverTree := CoverTree.split [tree009_7,tree009_553,tree009_509,tree009_510,tree009_675,tree009_515]
def tree009_677 : CoverTree := CoverTree.reject 371
def tree009_678 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_78,tree009_677,tree009_80,tree009_80]
def tree009_679 : CoverTree := CoverTree.split [tree009_517,tree009_678,tree009_520,tree009_561,tree009_475,tree009_481]
def tree009_680 : CoverTree := CoverTree.split [tree009_4,tree009_667,tree009_674,tree009_676,tree009_679,tree009_539]
def tree009_681 : CoverTree := CoverTree.reject 304
def tree009_682 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_542,tree009_215,tree009_183]
def tree009_683 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_681,tree009_682,tree009_545,tree009_546]
def tree009_684 : CoverTree := CoverTree.reject 350
def tree009_685 : CoverTree := CoverTree.split [tree009_46,tree009_684,tree009_549,tree009_550,tree009_190,tree009_551]
def tree009_686 : CoverTree := CoverTree.split [tree009_4,tree009_683,tree009_685,tree009_558,tree009_566,tree009_603]
def tree009_687 : CoverTree := CoverTree.split [tree009_617,tree009_640,tree009_664,tree009_680,tree009_686,tree009_604]
def tree009_688 : CoverTree := CoverTree.reject 164
def tree009_689 : CoverTree := CoverTree.reject 160
def tree009_690 : CoverTree := CoverTree.reject 278
def tree009_691 : CoverTree := CoverTree.split [tree009_424,tree009_424,tree009_611,tree009_690,tree009_14,tree009_14]
def tree009_692 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_608,tree009_688,tree009_689,tree009_691]
def tree009_693 : CoverTree := CoverTree.reject 106
def tree009_694 : CoverTree := CoverTree.reject 94
def tree009_695 : CoverTree := CoverTree.reject 95
def tree009_696 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_693,tree009_694,tree009_695,tree009_436]
def tree009_697 : CoverTree := CoverTree.split [tree009_4,tree009_101,tree009_606,tree009_607,tree009_692,tree009_696]
def tree009_698 : CoverTree := CoverTree.reject 58
def tree009_699 : CoverTree := CoverTree.reject 173
def tree009_700 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_698,tree009_699,tree009_242]
def tree009_701 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_698,tree009_56,tree009_14]
def tree009_702 : CoverTree := CoverTree.reject 382
def tree009_703 : CoverTree := CoverTree.reject 383
def tree009_704 : CoverTree := CoverTree.reject 384
def tree009_705 : CoverTree := CoverTree.split [tree009_13,tree009_702,tree009_703,tree009_704,tree009_14,tree009_14]
def tree009_706 : CoverTree := CoverTree.reject 385
def tree009_707 : CoverTree := CoverTree.split [tree009_16,tree009_706,tree009_14,tree009_14,tree009_14,tree009_14]
def tree009_708 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_705,tree009_707,tree009_59,tree009_418]
def tree009_709 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_410,tree009_700,tree009_701,tree009_708]
def tree009_710 : CoverTree := CoverTree.reject 181
def tree009_711 : CoverTree := CoverTree.reject 124
def tree009_712 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_249,tree009_710,tree009_711,tree009_14]
def tree009_713 : CoverTree := CoverTree.reject 372
def tree009_714 : CoverTree := CoverTree.reject 341
def tree009_715 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_713,tree009_714,tree009_71,tree009_14]
def tree009_716 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_712,tree009_715,tree009_628,tree009_632]
def tree009_717 : CoverTree := CoverTree.reject 342
def tree009_718 : CoverTree := CoverTree.reject 280
def tree009_719 : CoverTree := CoverTree.reject 281
def tree009_720 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_717,tree009_718,tree009_719,tree009_14]
def tree009_721 : CoverTree := CoverTree.split [tree009_430,tree009_430,tree009_431,tree009_17,tree009_93,tree009_14]
def tree009_722 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_720,tree009_721,tree009_435,tree009_436]
def tree009_723 : CoverTree := CoverTree.split [tree009_4,tree009_101,tree009_709,tree009_716,tree009_722,tree009_639]
def tree009_724 : CoverTree := CoverTree.reject 140
def tree009_725 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_542,tree009_724,tree009_183]
def tree009_726 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_178,tree009_297,tree009_183,tree009_183]
def tree009_727 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_294,tree009_725,tree009_725,tree009_726]
def tree009_728 : CoverTree := CoverTree.reject 78
def tree009_729 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_227,tree009_728,tree009_234]
def tree009_730 : CoverTree := CoverTree.reject 386
def tree009_731 : CoverTree := CoverTree.reject 387
def tree009_732 : CoverTree := CoverTree.reject 388
def tree009_733 : CoverTree := CoverTree.split [tree009_13,tree009_730,tree009_731,tree009_732,tree009_14,tree009_14]
def tree009_734 : CoverTree := CoverTree.split [tree009_413,tree009_413,tree009_733,tree009_651,tree009_59,tree009_308]
def tree009_735 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_729,tree009_648,tree009_190,tree009_734]
def tree009_736 : CoverTree := CoverTree.split [tree009_105,tree009_105,tree009_655,tree009_459,tree009_675,tree009_658]
def tree009_737 : CoverTree := CoverTree.split [tree009_4,tree009_727,tree009_735,tree009_736,tree009_662,tree009_663]
def tree009_738 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_542,tree009_210,tree009_183]
def tree009_739 : CoverTree := CoverTree.reject 223
def tree009_740 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_542,tree009_739,tree009_183]
def tree009_741 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_738,tree009_740,tree009_545,tree009_546]
def tree009_742 : CoverTree := CoverTree.reject 231
def tree009_743 : CoverTree := CoverTree.split [tree009_79,tree009_79,tree009_79,tree009_742,tree009_14,tree009_14]
def tree009_744 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_393,tree009_394,tree009_743]
def tree009_745 : CoverTree := CoverTree.split [tree009_46,tree009_744,tree009_549,tree009_504,tree009_190,tree009_673]
def tree009_746 : CoverTree := CoverTree.split [tree009_517,tree009_559,tree009_520,tree009_561,tree009_475,tree009_481]
def tree009_747 : CoverTree := CoverTree.split [tree009_4,tree009_741,tree009_745,tree009_676,tree009_746,tree009_539]
def tree009_748 : CoverTree := CoverTree.split [tree009_40,tree009_40,tree009_738,tree009_682,tree009_545,tree009_546]
def tree009_749 : CoverTree := CoverTree.split [tree009_189,tree009_189,tree009_189,tree009_393,tree009_394,tree009_80]
def tree009_750 : CoverTree := CoverTree.split [tree009_46,tree009_749,tree009_549,tree009_550,tree009_190,tree009_551]
def tree009_751 : CoverTree := CoverTree.split [tree009_4,tree009_748,tree009_750,tree009_558,tree009_566,tree009_603]
def tree009_752 : CoverTree := CoverTree.split [tree009_697,tree009_723,tree009_737,tree009_747,tree009_751,tree009_604]
def tree009_753 : CoverTree := CoverTree.split [tree009_99,tree009_268,tree009_406,tree009_605,tree009_687,tree009_752]
def tree009 : CoverTree := tree009_753

end Snake9.Shared89
