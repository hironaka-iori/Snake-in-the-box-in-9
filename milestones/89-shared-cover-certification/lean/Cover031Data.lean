import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes031 : List Box := [
[(1,6),(1,5),(1,3),(1,5),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)],
[(1,3),(1,6),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,5),(1,5),(1,4)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,2),(1,2)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,2)],
[(1,6),(1,5),(1,5),(1,4),(1,2),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,6),(1,2),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,6),(1,2),(1,6)],
[(1,6),(1,5),(1,2),(1,5),(1,4),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,1)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,6),(1,2),(1,4),(1,5),(1,5)],
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

def root031 : Nat := 2703

def tree031_0 : CoverTree := CoverTree.reject 26
def tree031_1 : CoverTree := CoverTree.reject 18
def tree031_2 : CoverTree := CoverTree.reject 14
def tree031_3 : CoverTree := CoverTree.reject 8
def tree031_4 : CoverTree := CoverTree.reject 147
def tree031_5 : CoverTree := CoverTree.reject 64
def tree031_6 : CoverTree := CoverTree.reject 41
def tree031_7 : CoverTree := CoverTree.reject 19
def tree031_8 : CoverTree := CoverTree.reject 212
def tree031_9 : CoverTree := CoverTree.reject 154
def tree031_10 : CoverTree := CoverTree.reject 129
def tree031_11 : CoverTree := CoverTree.reject 113
def tree031_12 : CoverTree := CoverTree.reject 2
def tree031_13 : CoverTree := CoverTree.reject 13
def tree031_14 : CoverTree := CoverTree.accept
def tree031_15 : CoverTree := CoverTree.split [tree031_13,tree031_14,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_16 : CoverTree := CoverTree.reject 11
def tree031_17 : CoverTree := CoverTree.split [tree031_16,tree031_14,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_18 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_19 : CoverTree := CoverTree.split [tree031_7,tree031_8,tree031_9,tree031_10,tree031_11,tree031_18]
def tree031_20 : CoverTree := CoverTree.reject 34
def tree031_21 : CoverTree := CoverTree.reject 35
def tree031_22 : CoverTree := CoverTree.reject 50
def tree031_23 : CoverTree := CoverTree.reject 51
def tree031_24 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_20,tree031_21,tree031_22,tree031_23]
def tree031_25 : CoverTree := CoverTree.reject 180
def tree031_26 : CoverTree := CoverTree.reject 121
def tree031_27 : CoverTree := CoverTree.reject 106
def tree031_28 : CoverTree := CoverTree.split [tree031_24,tree031_25,tree031_26,tree031_27,tree031_18,tree031_18]
def tree031_29 : CoverTree := CoverTree.reject 53
def tree031_30 : CoverTree := CoverTree.reject 54
def tree031_31 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_20,tree031_21,tree031_29,tree031_30]
def tree031_32 : CoverTree := CoverTree.reject 155
def tree031_33 : CoverTree := CoverTree.reject 63
def tree031_34 : CoverTree := CoverTree.split [tree031_13,tree031_33,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_35 : CoverTree := CoverTree.reject 46
def tree031_36 : CoverTree := CoverTree.split [tree031_35,tree031_14,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_37 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_34,tree031_17,tree031_36,tree031_14]
def tree031_38 : CoverTree := CoverTree.split [tree031_31,tree031_32,tree031_37,tree031_18,tree031_18,tree031_18]
def tree031_39 : CoverTree := CoverTree.split [tree031_4,tree031_5,tree031_6,tree031_19,tree031_28,tree031_38]
def tree031_40 : CoverTree := CoverTree.reject 190
def tree031_41 : CoverTree := CoverTree.reject 12
def tree031_42 : CoverTree := CoverTree.reject 296
def tree031_43 : CoverTree := CoverTree.reject 238
def tree031_44 : CoverTree := CoverTree.reject 191
def tree031_45 : CoverTree := CoverTree.reject 171
def tree031_46 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_42,tree031_43,tree031_44,tree031_45]
def tree031_47 : CoverTree := CoverTree.reject 22
def tree031_48 : CoverTree := CoverTree.reject 358
def tree031_49 : CoverTree := CoverTree.reject 207
def tree031_50 : CoverTree := CoverTree.reject 141
def tree031_51 : CoverTree := CoverTree.reject 38
def tree031_52 : CoverTree := CoverTree.split [tree031_13,tree031_51,tree031_51,tree031_51,tree031_51,tree031_14]
def tree031_53 : CoverTree := CoverTree.reject 102
def tree031_54 : CoverTree := CoverTree.split [tree031_16,tree031_53,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_55 : CoverTree := CoverTree.reject 23
def tree031_56 : CoverTree := CoverTree.reject 93
def tree031_57 : CoverTree := CoverTree.split [tree031_55,tree031_56,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_58 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_52,tree031_54,tree031_57,tree031_14]
def tree031_59 : CoverTree := CoverTree.reject 94
def tree031_60 : CoverTree := CoverTree.split [tree031_59,tree031_14,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_61 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_15,tree031_17,tree031_60,tree031_14]
def tree031_62 : CoverTree := CoverTree.split [tree031_47,tree031_48,tree031_49,tree031_50,tree031_58,tree031_61]
def tree031_63 : CoverTree := CoverTree.reject 213
def tree031_64 : CoverTree := CoverTree.reject 156
def tree031_65 : CoverTree := CoverTree.reject 47
def tree031_66 : CoverTree := CoverTree.reject 73
def tree031_67 : CoverTree := CoverTree.reject 74
def tree031_68 : CoverTree := CoverTree.split [tree031_13,tree031_65,tree031_66,tree031_67,tree031_14,tree031_14]
def tree031_69 : CoverTree := CoverTree.reject 75
def tree031_70 : CoverTree := CoverTree.reject 76
def tree031_71 : CoverTree := CoverTree.split [tree031_16,tree031_69,tree031_70,tree031_14,tree031_14,tree031_14]
def tree031_72 : CoverTree := CoverTree.split [tree031_55,tree031_14,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_73 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_68,tree031_71,tree031_72,tree031_14]
def tree031_74 : CoverTree := CoverTree.split [tree031_13,tree031_65,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_75 : CoverTree := CoverTree.reject 77
def tree031_76 : CoverTree := CoverTree.split [tree031_16,tree031_75,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_77 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_74,tree031_76,tree031_72,tree031_14]
def tree031_78 : CoverTree := CoverTree.split [tree031_7,tree031_63,tree031_64,tree031_73,tree031_77,tree031_18]
def tree031_79 : CoverTree := CoverTree.reject 52
def tree031_80 : CoverTree := CoverTree.reject 1
def tree031_81 : CoverTree := CoverTree.split [tree031_80,tree031_80,tree031_80,tree031_14,tree031_14,tree031_14]
def tree031_82 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_79,tree031_81,tree031_81,tree031_81]
def tree031_83 : CoverTree := CoverTree.reject 78
def tree031_84 : CoverTree := CoverTree.reject 79
def tree031_85 : CoverTree := CoverTree.split [tree031_13,tree031_83,tree031_84,tree031_14,tree031_14,tree031_14]
def tree031_86 : CoverTree := CoverTree.reject 80
def tree031_87 : CoverTree := CoverTree.split [tree031_16,tree031_86,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_88 : CoverTree := CoverTree.reject 66
def tree031_89 : CoverTree := CoverTree.split [tree031_35,tree031_88,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_90 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_85,tree031_87,tree031_89,tree031_14]
def tree031_91 : CoverTree := CoverTree.reject 81
def tree031_92 : CoverTree := CoverTree.split [tree031_13,tree031_91,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_93 : CoverTree := CoverTree.reject 67
def tree031_94 : CoverTree := CoverTree.split [tree031_93,tree031_14,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_95 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_92,tree031_17,tree031_94,tree031_14]
def tree031_96 : CoverTree := CoverTree.split [tree031_24,tree031_82,tree031_90,tree031_95,tree031_18,tree031_18]
def tree031_97 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_81,tree031_81,tree031_81,tree031_81]
def tree031_98 : CoverTree := CoverTree.split [tree031_31,tree031_97,tree031_37,tree031_18,tree031_18,tree031_18]
def tree031_99 : CoverTree := CoverTree.split [tree031_40,tree031_46,tree031_62,tree031_78,tree031_96,tree031_98]
def tree031_100 : CoverTree := CoverTree.split [tree031_0,tree031_1,tree031_2,tree031_3,tree031_39,tree031_99]
def tree031_101 : CoverTree := CoverTree.reject 27
def tree031_102 : CoverTree := CoverTree.reject 5
def tree031_103 : CoverTree := CoverTree.reject 44
def tree031_104 : CoverTree := CoverTree.reject 40
def tree031_105 : CoverTree := CoverTree.reject 37
def tree031_106 : CoverTree := CoverTree.reject 3
def tree031_107 : CoverTree := CoverTree.reject 131
def tree031_108 : CoverTree := CoverTree.reject 96
def tree031_109 : CoverTree := CoverTree.reject 245
def tree031_110 : CoverTree := CoverTree.reject 246
def tree031_111 : CoverTree := CoverTree.split [tree031_13,tree031_109,tree031_110,tree031_14,tree031_14,tree031_14]
def tree031_112 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_111,tree031_17,tree031_14,tree031_14]
def tree031_113 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_107,tree031_108,tree031_18,tree031_112]
def tree031_114 : CoverTree := CoverTree.split [tree031_102,tree031_102,tree031_103,tree031_104,tree031_105,tree031_113]
def tree031_115 : CoverTree := CoverTree.reject 24
def tree031_116 : CoverTree := CoverTree.reject 65
def tree031_117 : CoverTree := CoverTree.reject 300
def tree031_118 : CoverTree := CoverTree.reject 196
def tree031_119 : CoverTree := CoverTree.reject 142
def tree031_120 : CoverTree := CoverTree.reject 103
def tree031_121 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_117,tree031_118,tree031_119,tree031_120]
def tree031_122 : CoverTree := CoverTree.reject 163
def tree031_123 : CoverTree := CoverTree.reject 132
def tree031_124 : CoverTree := CoverTree.reject 117
def tree031_125 : CoverTree := CoverTree.reject 252
def tree031_126 : CoverTree := CoverTree.reject 326
def tree031_127 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_125,tree031_126,tree031_14,tree031_14]
def tree031_128 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_122,tree031_123,tree031_124,tree031_127]
def tree031_129 : CoverTree := CoverTree.reject 122
def tree031_130 : CoverTree := CoverTree.reject 133
def tree031_131 : CoverTree := CoverTree.reject 97
def tree031_132 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_129,tree031_130,tree031_131,tree031_18]
def tree031_133 : CoverTree := CoverTree.reject 327
def tree031_134 : CoverTree := CoverTree.reject 253
def tree031_135 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_133,tree031_134,tree031_36,tree031_14]
def tree031_136 : CoverTree := CoverTree.reject 254
def tree031_137 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_136,tree031_17,tree031_14,tree031_14]
def tree031_138 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_135,tree031_137,tree031_18,tree031_18]
def tree031_139 : CoverTree := CoverTree.split [tree031_115,tree031_116,tree031_121,tree031_128,tree031_132,tree031_138]
def tree031_140 : CoverTree := CoverTree.reject 25
def tree031_141 : CoverTree := CoverTree.reject 301
def tree031_142 : CoverTree := CoverTree.reject 302
def tree031_143 : CoverTree := CoverTree.reject 216
def tree031_144 : CoverTree := CoverTree.reject 172
def tree031_145 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_141,tree031_142,tree031_143,tree031_144]
def tree031_146 : CoverTree := CoverTree.reject 392
def tree031_147 : CoverTree := CoverTree.reject 217
def tree031_148 : CoverTree := CoverTree.reject 197
def tree031_149 : CoverTree := CoverTree.reject 143
def tree031_150 : CoverTree := CoverTree.reject 374
def tree031_151 : CoverTree := CoverTree.reject 251
def tree031_152 : CoverTree := CoverTree.split [tree031_16,tree031_151,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_153 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_150,tree031_152,tree031_60,tree031_14]
def tree031_154 : CoverTree := CoverTree.split [tree031_47,tree031_146,tree031_147,tree031_148,tree031_149,tree031_153]
def tree031_155 : CoverTree := CoverTree.reject 218
def tree031_156 : CoverTree := CoverTree.reject 164
def tree031_157 : CoverTree := CoverTree.reject 134
def tree031_158 : CoverTree := CoverTree.reject 328
def tree031_159 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_158,tree031_76,tree031_72,tree031_14]
def tree031_160 : CoverTree := CoverTree.reject 255
def tree031_161 : CoverTree := CoverTree.reject 256
def tree031_162 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_160,tree031_161,tree031_14,tree031_14]
def tree031_163 : CoverTree := CoverTree.split [tree031_7,tree031_155,tree031_156,tree031_157,tree031_159,tree031_162]
def tree031_164 : CoverTree := CoverTree.reject 187
def tree031_165 : CoverTree := CoverTree.reject 123
def tree031_166 : CoverTree := CoverTree.reject 329
def tree031_167 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_166,tree031_17,tree031_94,tree031_14]
def tree031_168 : CoverTree := CoverTree.split [tree031_24,tree031_164,tree031_165,tree031_167,tree031_18,tree031_18]
def tree031_169 : CoverTree := CoverTree.reject 165
def tree031_170 : CoverTree := CoverTree.reject 330
def tree031_171 : CoverTree := CoverTree.reject 257
def tree031_172 : CoverTree := CoverTree.reject 258
def tree031_173 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_170,tree031_171,tree031_172,tree031_14]
def tree031_174 : CoverTree := CoverTree.reject 259
def tree031_175 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_174,tree031_17,tree031_14,tree031_14]
def tree031_176 : CoverTree := CoverTree.split [tree031_31,tree031_169,tree031_173,tree031_175,tree031_18,tree031_18]
def tree031_177 : CoverTree := CoverTree.split [tree031_140,tree031_145,tree031_154,tree031_163,tree031_168,tree031_176]
def tree031_178 : CoverTree := CoverTree.reject 152
def tree031_179 : CoverTree := CoverTree.reject 303
def tree031_180 : CoverTree := CoverTree.reject 241
def tree031_181 : CoverTree := CoverTree.reject 219
def tree031_182 : CoverTree := CoverTree.reject 7
def tree031_183 : CoverTree := CoverTree.reject 375
def tree031_184 : CoverTree := CoverTree.reject 9
def tree031_185 : CoverTree := CoverTree.reject 411
def tree031_186 : CoverTree := CoverTree.split [tree031_184,tree031_184,tree031_185,tree031_14,tree031_14,tree031_14]
def tree031_187 : CoverTree := CoverTree.split [tree031_184,tree031_184,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_188 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_183,tree031_186,tree031_187]
def tree031_189 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_179,tree031_180,tree031_181,tree031_188]
def tree031_190 : CoverTree := CoverTree.reject 365
def tree031_191 : CoverTree := CoverTree.reject 220
def tree031_192 : CoverTree := CoverTree.reject 145
def tree031_193 : CoverTree := CoverTree.reject 0
def tree031_194 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_54,tree031_57,tree031_14]
def tree031_195 : CoverTree := CoverTree.reject 260
def tree031_196 : CoverTree := CoverTree.reject 261
def tree031_197 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_195,tree031_196,tree031_60,tree031_14]
def tree031_198 : CoverTree := CoverTree.split [tree031_47,tree031_190,tree031_191,tree031_192,tree031_194,tree031_197]
def tree031_199 : CoverTree := CoverTree.reject 221
def tree031_200 : CoverTree := CoverTree.reject 166
def tree031_201 : CoverTree := CoverTree.split [tree031_7,tree031_199,tree031_200,tree031_73,tree031_77,tree031_18]
def tree031_202 : CoverTree := CoverTree.reject 188
def tree031_203 : CoverTree := CoverTree.reject 331
def tree031_204 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_203,tree031_17,tree031_94,tree031_14]
def tree031_205 : CoverTree := CoverTree.split [tree031_24,tree031_202,tree031_90,tree031_204,tree031_18,tree031_18]
def tree031_206 : CoverTree := CoverTree.reject 376
def tree031_207 : CoverTree := CoverTree.reject 377
def tree031_208 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_206,tree031_207,tree031_81,tree031_81]
def tree031_209 : CoverTree := CoverTree.reject 332
def tree031_210 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_209,tree031_17,tree031_36,tree031_14]
def tree031_211 : CoverTree := CoverTree.split [tree031_31,tree031_208,tree031_210,tree031_18,tree031_18,tree031_18]
def tree031_212 : CoverTree := CoverTree.split [tree031_178,tree031_189,tree031_198,tree031_201,tree031_205,tree031_211]
def tree031_213 : CoverTree := CoverTree.reject 42
def tree031_214 : CoverTree := CoverTree.reject 43
def tree031_215 : CoverTree := CoverTree.reject 148
def tree031_216 : CoverTree := CoverTree.reject 86
def tree031_217 : CoverTree := CoverTree.reject 95
def tree031_218 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_215,tree031_216,tree031_217]
def tree031_219 : CoverTree := CoverTree.reject 198
def tree031_220 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_213,tree031_214,tree031_218,tree031_219]
def tree031_221 : CoverTree := CoverTree.reject 208
def tree031_222 : CoverTree := CoverTree.reject 105
def tree031_223 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_221,tree031_222,tree031_187]
def tree031_224 : CoverTree := CoverTree.reject 209
def tree031_225 : CoverTree := CoverTree.reject 4
def tree031_226 : CoverTree := CoverTree.reject 36
def tree031_227 : CoverTree := CoverTree.split [tree031_225,tree031_225,tree031_225,tree031_225,tree031_226,tree031_14]
def tree031_228 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_224,tree031_227,tree031_187]
def tree031_229 : CoverTree := CoverTree.reject 239
def tree031_230 : CoverTree := CoverTree.split [tree031_225,tree031_225,tree031_225,tree031_225,tree031_229,tree031_14]
def tree031_231 : CoverTree := CoverTree.split [tree031_225,tree031_225,tree031_225,tree031_225,tree031_14,tree031_14]
def tree031_232 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_230,tree031_231,tree031_187]
def tree031_233 : CoverTree := CoverTree.reject 107
def tree031_234 : CoverTree := CoverTree.split [tree031_184,tree031_184,tree031_233,tree031_14,tree031_14,tree031_14]
def tree031_235 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_234,tree031_187,tree031_187]
def tree031_236 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_223,tree031_228,tree031_232,tree031_235]
def tree031_237 : CoverTree := CoverTree.reject 366
def tree031_238 : CoverTree := CoverTree.reject 236
def tree031_239 : CoverTree := CoverTree.reject 31
def tree031_240 : CoverTree := CoverTree.reject 114
def tree031_241 : CoverTree := CoverTree.reject 115
def tree031_242 : CoverTree := CoverTree.reject 116
def tree031_243 : CoverTree := CoverTree.split [tree031_55,tree031_240,tree031_241,tree031_242,tree031_14,tree031_14]
def tree031_244 : CoverTree := CoverTree.reject 88
def tree031_245 : CoverTree := CoverTree.reject 89
def tree031_246 : CoverTree := CoverTree.split [tree031_244,tree031_245,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_247 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_238,tree031_239,tree031_243,tree031_246]
def tree031_248 : CoverTree := CoverTree.reject 237
def tree031_249 : CoverTree := CoverTree.reject 378
def tree031_250 : CoverTree := CoverTree.reject 90
def tree031_251 : CoverTree := CoverTree.reject 91
def tree031_252 : CoverTree := CoverTree.split [tree031_55,tree031_250,tree031_251,tree031_14,tree031_14,tree031_14]
def tree031_253 : CoverTree := CoverTree.reject 92
def tree031_254 : CoverTree := CoverTree.split [tree031_253,tree031_14,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_255 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_248,tree031_249,tree031_252,tree031_254]
def tree031_256 : CoverTree := CoverTree.reject 262
def tree031_257 : CoverTree := CoverTree.reject 263
def tree031_258 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_256,tree031_257,tree031_60,tree031_14]
def tree031_259 : CoverTree := CoverTree.split [tree031_47,tree031_237,tree031_247,tree031_255,tree031_58,tree031_258]
def tree031_260 : CoverTree := CoverTree.reject 222
def tree031_261 : CoverTree := CoverTree.reject 32
def tree031_262 : CoverTree := CoverTree.reject 69
def tree031_263 : CoverTree := CoverTree.reject 70
def tree031_264 : CoverTree := CoverTree.reject 71
def tree031_265 : CoverTree := CoverTree.split [tree031_16,tree031_262,tree031_263,tree031_264,tree031_14,tree031_14]
def tree031_266 : CoverTree := CoverTree.reject 72
def tree031_267 : CoverTree := CoverTree.split [tree031_55,tree031_266,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_268 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_261,tree031_265,tree031_267,tree031_14]
def tree031_269 : CoverTree := CoverTree.split [tree031_7,tree031_260,tree031_268,tree031_73,tree031_77,tree031_18]
def tree031_270 : CoverTree := CoverTree.reject 379
def tree031_271 : CoverTree := CoverTree.reject 333
def tree031_272 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_270,tree031_271,tree031_89,tree031_14]
def tree031_273 : CoverTree := CoverTree.split [tree031_24,tree031_82,tree031_272,tree031_95,tree031_18,tree031_18]
def tree031_274 : CoverTree := CoverTree.reject 380
def tree031_275 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_274,tree031_81,tree031_81,tree031_81]
def tree031_276 : CoverTree := CoverTree.reject 334
def tree031_277 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_276,tree031_17,tree031_36,tree031_14]
def tree031_278 : CoverTree := CoverTree.split [tree031_31,tree031_275,tree031_277,tree031_18,tree031_18,tree031_18]
def tree031_279 : CoverTree := CoverTree.split [tree031_220,tree031_236,tree031_259,tree031_269,tree031_273,tree031_278]
def tree031_280 : CoverTree := CoverTree.split [tree031_101,tree031_114,tree031_139,tree031_177,tree031_212,tree031_279]
def tree031_281 : CoverTree := CoverTree.reject 28
def tree031_282 : CoverTree := CoverTree.reject 45
def tree031_283 : CoverTree := CoverTree.reject 223
def tree031_284 : CoverTree := CoverTree.reject 135
def tree031_285 : CoverTree := CoverTree.reject 118
def tree031_286 : CoverTree := CoverTree.reject 371
def tree031_287 : CoverTree := CoverTree.reject 372
def tree031_288 : CoverTree := CoverTree.reject 373
def tree031_289 : CoverTree := CoverTree.split [tree031_13,tree031_286,tree031_287,tree031_288,tree031_14,tree031_14]
def tree031_290 : CoverTree := CoverTree.reject 264
def tree031_291 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_289,tree031_290,tree031_14,tree031_14]
def tree031_292 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_283,tree031_284,tree031_285,tree031_291]
def tree031_293 : CoverTree := CoverTree.reject 124
def tree031_294 : CoverTree := CoverTree.reject 110
def tree031_295 : CoverTree := CoverTree.reject 98
def tree031_296 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_293,tree031_294,tree031_295,tree031_18]
def tree031_297 : CoverTree := CoverTree.reject 108
def tree031_298 : CoverTree := CoverTree.reject 265
def tree031_299 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_297,tree031_298,tree031_36,tree031_14]
def tree031_300 : CoverTree := CoverTree.reject 266
def tree031_301 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_300,tree031_17,tree031_14,tree031_14]
def tree031_302 : CoverTree := CoverTree.reject 267
def tree031_303 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_302,tree031_17,tree031_14,tree031_14]
def tree031_304 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_299,tree031_301,tree031_303,tree031_112]
def tree031_305 : CoverTree := CoverTree.split [tree031_102,tree031_102,tree031_282,tree031_292,tree031_296,tree031_304]
def tree031_306 : CoverTree := CoverTree.reject 128
def tree031_307 : CoverTree := CoverTree.reject 304
def tree031_308 : CoverTree := CoverTree.reject 305
def tree031_309 : CoverTree := CoverTree.reject 161
def tree031_310 : CoverTree := CoverTree.reject 335
def tree031_311 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_309,tree031_310,tree031_187]
def tree031_312 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_306,tree031_307,tree031_308,tree031_311]
def tree031_313 : CoverTree := CoverTree.reject 306
def tree031_314 : CoverTree := CoverTree.reject 199
def tree031_315 : CoverTree := CoverTree.reject 144
def tree031_316 : CoverTree := CoverTree.reject 268
def tree031_317 : CoverTree := CoverTree.reject 269
def tree031_318 : CoverTree := CoverTree.reject 270
def tree031_319 : CoverTree := CoverTree.reject 324
def tree031_320 : CoverTree := CoverTree.split [tree031_14,tree031_319,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_321 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_316,tree031_317,tree031_318,tree031_320]
def tree031_322 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_313,tree031_314,tree031_315,tree031_321]
def tree031_323 : CoverTree := CoverTree.reject 167
def tree031_324 : CoverTree := CoverTree.reject 136
def tree031_325 : CoverTree := CoverTree.reject 119
def tree031_326 : CoverTree := CoverTree.reject 271
def tree031_327 : CoverTree := CoverTree.reject 336
def tree031_328 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_326,tree031_327,tree031_14,tree031_14]
def tree031_329 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_323,tree031_324,tree031_325,tree031_328]
def tree031_330 : CoverTree := CoverTree.reject 125
def tree031_331 : CoverTree := CoverTree.reject 109
def tree031_332 : CoverTree := CoverTree.reject 272
def tree031_333 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_331,tree031_332,tree031_94,tree031_14]
def tree031_334 : CoverTree := CoverTree.reject 273
def tree031_335 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_334,tree031_17,tree031_14,tree031_14]
def tree031_336 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_330,tree031_333,tree031_335,tree031_18]
def tree031_337 : CoverTree := CoverTree.reject 337
def tree031_338 : CoverTree := CoverTree.reject 274
def tree031_339 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_337,tree031_338,tree031_36,tree031_14]
def tree031_340 : CoverTree := CoverTree.reject 275
def tree031_341 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_340,tree031_17,tree031_14,tree031_14]
def tree031_342 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_339,tree031_341,tree031_18,tree031_18]
def tree031_343 : CoverTree := CoverTree.split [tree031_115,tree031_312,tree031_322,tree031_329,tree031_336,tree031_342]
def tree031_344 : CoverTree := CoverTree.reject 307
def tree031_345 : CoverTree := CoverTree.reject 308
def tree031_346 : CoverTree := CoverTree.reject 224
def tree031_347 : CoverTree := CoverTree.reject 381
def tree031_348 : CoverTree := CoverTree.reject 338
def tree031_349 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_347,tree031_348,tree031_187]
def tree031_350 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_344,tree031_345,tree031_346,tree031_349]
def tree031_351 : CoverTree := CoverTree.reject 393
def tree031_352 : CoverTree := CoverTree.reject 225
def tree031_353 : CoverTree := CoverTree.reject 200
def tree031_354 : CoverTree := CoverTree.reject 339
def tree031_355 : CoverTree := CoverTree.reject 340
def tree031_356 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_354,tree031_355,tree031_14]
def tree031_357 : CoverTree := CoverTree.reject 382
def tree031_358 : CoverTree := CoverTree.reject 341
def tree031_359 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_357,tree031_358,tree031_60,tree031_14]
def tree031_360 : CoverTree := CoverTree.split [tree031_47,tree031_351,tree031_352,tree031_353,tree031_356,tree031_359]
def tree031_361 : CoverTree := CoverTree.reject 226
def tree031_362 : CoverTree := CoverTree.reject 195
def tree031_363 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_261,tree031_362,tree031_267,tree031_14]
def tree031_364 : CoverTree := CoverTree.reject 342
def tree031_365 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_364,tree031_76,tree031_72,tree031_14]
def tree031_366 : CoverTree := CoverTree.split [tree031_7,tree031_361,tree031_363,tree031_73,tree031_365,tree031_18]
def tree031_367 : CoverTree := CoverTree.reject 189
def tree031_368 : CoverTree := CoverTree.reject 162
def tree031_369 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_368,tree031_87,tree031_89,tree031_14]
def tree031_370 : CoverTree := CoverTree.reject 343
def tree031_371 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_370,tree031_17,tree031_94,tree031_14]
def tree031_372 : CoverTree := CoverTree.split [tree031_24,tree031_367,tree031_369,tree031_371,tree031_18,tree031_18]
def tree031_373 : CoverTree := CoverTree.reject 399
def tree031_374 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_373,tree031_81,tree031_81,tree031_81]
def tree031_375 : CoverTree := CoverTree.split [tree031_31,tree031_374,tree031_37,tree031_18,tree031_18,tree031_18]
def tree031_376 : CoverTree := CoverTree.split [tree031_140,tree031_350,tree031_360,tree031_366,tree031_372,tree031_375]
def tree031_377 : CoverTree := CoverTree.reject 153
def tree031_378 : CoverTree := CoverTree.reject 309
def tree031_379 : CoverTree := CoverTree.reject 242
def tree031_380 : CoverTree := CoverTree.reject 227
def tree031_381 : CoverTree := CoverTree.reject 383
def tree031_382 : CoverTree := CoverTree.reject 412
def tree031_383 : CoverTree := CoverTree.split [tree031_184,tree031_184,tree031_382,tree031_14,tree031_14,tree031_14]
def tree031_384 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_182,tree031_381,tree031_383,tree031_187]
def tree031_385 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_378,tree031_379,tree031_380,tree031_384]
def tree031_386 : CoverTree := CoverTree.reject 367
def tree031_387 : CoverTree := CoverTree.reject 228
def tree031_388 : CoverTree := CoverTree.reject 384
def tree031_389 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_388,tree031_252,tree031_254]
def tree031_390 : CoverTree := CoverTree.reject 276
def tree031_391 : CoverTree := CoverTree.reject 277
def tree031_392 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_390,tree031_391,tree031_60,tree031_14]
def tree031_393 : CoverTree := CoverTree.split [tree031_47,tree031_386,tree031_387,tree031_389,tree031_194,tree031_392]
def tree031_394 : CoverTree := CoverTree.reject 229
def tree031_395 : CoverTree := CoverTree.reject 400
def tree031_396 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_261,tree031_395,tree031_267,tree031_14]
def tree031_397 : CoverTree := CoverTree.split [tree031_7,tree031_394,tree031_396,tree031_73,tree031_77,tree031_18]
def tree031_398 : CoverTree := CoverTree.reject 385
def tree031_399 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_79,tree031_398,tree031_81,tree031_81]
def tree031_400 : CoverTree := CoverTree.split [tree031_24,tree031_399,tree031_90,tree031_95,tree031_18,tree031_18]
def tree031_401 : CoverTree := CoverTree.reject 344
def tree031_402 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_401,tree031_17,tree031_36,tree031_14]
def tree031_403 : CoverTree := CoverTree.split [tree031_31,tree031_97,tree031_402,tree031_18,tree031_18,tree031_18]
def tree031_404 : CoverTree := CoverTree.split [tree031_377,tree031_385,tree031_393,tree031_397,tree031_400,tree031_403]
def tree031_405 : CoverTree := CoverTree.reject 201
def tree031_406 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_213,tree031_214,tree031_218,tree031_405]
def tree031_407 : CoverTree := CoverTree.reject 210
def tree031_408 : CoverTree := CoverTree.reject 57
def tree031_409 : CoverTree := CoverTree.reject 58
def tree031_410 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_407,tree031_408,tree031_409,tree031_81]
def tree031_411 : CoverTree := CoverTree.reject 181
def tree031_412 : CoverTree := CoverTree.reject 182
def tree031_413 : CoverTree := CoverTree.split [tree031_16,tree031_411,tree031_412,tree031_14,tree031_14,tree031_14]
def tree031_414 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_248,tree031_413,tree031_252,tree031_254]
def tree031_415 : CoverTree := CoverTree.split [tree031_47,tree031_410,tree031_247,tree031_414,tree031_58,tree031_61]
def tree031_416 : CoverTree := CoverTree.reject 48
def tree031_417 : CoverTree := CoverTree.reject 49
def tree031_418 : CoverTree := CoverTree.split [tree031_12,tree031_12,tree031_416,tree031_417,tree031_81,tree031_81]
def tree031_419 : CoverTree := CoverTree.split [tree031_7,tree031_418,tree031_268,tree031_73,tree031_77,tree031_18]
def tree031_420 : CoverTree := CoverTree.split [tree031_406,tree031_236,tree031_415,tree031_419,tree031_96,tree031_98]
def tree031_421 : CoverTree := CoverTree.split [tree031_281,tree031_305,tree031_343,tree031_376,tree031_404,tree031_420]
def tree031_422 : CoverTree := CoverTree.reject 29
def tree031_423 : CoverTree := CoverTree.reject 214
def tree031_424 : CoverTree := CoverTree.reject 159
def tree031_425 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_239,tree031_423,tree031_424]
def tree031_426 : CoverTree := CoverTree.reject 243
def tree031_427 : CoverTree := CoverTree.reject 176
def tree031_428 : CoverTree := CoverTree.reject 15
def tree031_429 : CoverTree := CoverTree.reject 278
def tree031_430 : CoverTree := CoverTree.reject 279
def tree031_431 : CoverTree := CoverTree.reject 280
def tree031_432 : CoverTree := CoverTree.reject 370
def tree031_433 : CoverTree := CoverTree.split [tree031_14,tree031_432,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_434 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_429,tree031_430,tree031_431,tree031_433]
def tree031_435 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_425,tree031_426,tree031_427,tree031_434]
def tree031_436 : CoverTree := CoverTree.reject 230
def tree031_437 : CoverTree := CoverTree.reject 137
def tree031_438 : CoverTree := CoverTree.reject 120
def tree031_439 : CoverTree := CoverTree.reject 281
def tree031_440 : CoverTree := CoverTree.reject 282
def tree031_441 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_439,tree031_440,tree031_14,tree031_14]
def tree031_442 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_436,tree031_437,tree031_438,tree031_441]
def tree031_443 : CoverTree := CoverTree.reject 126
def tree031_444 : CoverTree := CoverTree.reject 10
def tree031_445 : CoverTree := CoverTree.reject 160
def tree031_446 : CoverTree := CoverTree.reject 283
def tree031_447 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_445,tree031_446,tree031_94,tree031_14]
def tree031_448 : CoverTree := CoverTree.reject 140
def tree031_449 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_448,tree031_17,tree031_14,tree031_14]
def tree031_450 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_451 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_443,tree031_447,tree031_449,tree031_450]
def tree031_452 : CoverTree := CoverTree.reject 284
def tree031_453 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_297,tree031_452,tree031_36,tree031_14]
def tree031_454 : CoverTree := CoverTree.reject 285
def tree031_455 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_454,tree031_17,tree031_14,tree031_14]
def tree031_456 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_111,tree031_17,tree031_14,tree031_14]
def tree031_457 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_453,tree031_455,tree031_450,tree031_456]
def tree031_458 : CoverTree := CoverTree.split [tree031_102,tree031_102,tree031_435,tree031_442,tree031_451,tree031_457]
def tree031_459 : CoverTree := CoverTree.reject 310
def tree031_460 : CoverTree := CoverTree.reject 311
def tree031_461 : CoverTree := CoverTree.reject 345
def tree031_462 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_309,tree031_461,tree031_187]
def tree031_463 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_306,tree031_459,tree031_460,tree031_462]
def tree031_464 : CoverTree := CoverTree.reject 312
def tree031_465 : CoverTree := CoverTree.reject 202
def tree031_466 : CoverTree := CoverTree.reject 20
def tree031_467 : CoverTree := CoverTree.reject 286
def tree031_468 : CoverTree := CoverTree.reject 287
def tree031_469 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_467,tree031_468,tree031_60,tree031_320]
def tree031_470 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_464,tree031_465,tree031_194,tree031_469]
def tree031_471 : CoverTree := CoverTree.reject 168
def tree031_472 : CoverTree := CoverTree.reject 215
def tree031_473 : CoverTree := CoverTree.reject 184
def tree031_474 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_472,tree031_473,tree031_72,tree031_14]
def tree031_475 : CoverTree := CoverTree.reject 55
def tree031_476 : CoverTree := CoverTree.reject 346
def tree031_477 : CoverTree := CoverTree.split [tree031_475,tree031_475,tree031_476,tree031_76,tree031_72,tree031_14]
def tree031_478 : CoverTree := CoverTree.reject 87
def tree031_479 : CoverTree := CoverTree.reject 185
def tree031_480 : CoverTree := CoverTree.reject 288
def tree031_481 : CoverTree := CoverTree.reject 247
def tree031_482 : CoverTree := CoverTree.split [tree031_16,tree031_481,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_483 : CoverTree := CoverTree.split [tree031_478,tree031_479,tree031_480,tree031_482,tree031_14,tree031_14]
def tree031_484 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_471,tree031_474,tree031_477,tree031_483]
def tree031_485 : CoverTree := CoverTree.reject 186
def tree031_486 : CoverTree := CoverTree.reject 347
def tree031_487 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_485,tree031_486,tree031_89,tree031_14]
def tree031_488 : CoverTree := CoverTree.reject 289
def tree031_489 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_331,tree031_488,tree031_94,tree031_14]
def tree031_490 : CoverTree := CoverTree.split [tree031_475,tree031_475,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_491 : CoverTree := CoverTree.reject 6
def tree031_492 : CoverTree := CoverTree.reject 33
def tree031_493 : CoverTree := CoverTree.reject 30
def tree031_494 : CoverTree := CoverTree.split [tree031_491,tree031_491,tree031_492,tree031_493,tree031_14,tree031_14]
def tree031_495 : CoverTree := CoverTree.split [tree031_491,tree031_491,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_496 : CoverTree := CoverTree.split [tree031_494,tree031_495,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_497 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_487,tree031_489,tree031_490,tree031_496]
def tree031_498 : CoverTree := CoverTree.reject 60
def tree031_499 : CoverTree := CoverTree.reject 386
def tree031_500 : CoverTree := CoverTree.split [tree031_498,tree031_499,tree031_34,tree031_17,tree031_36,tree031_14]
def tree031_501 : CoverTree := CoverTree.reject 61
def tree031_502 : CoverTree := CoverTree.reject 348
def tree031_503 : CoverTree := CoverTree.reject 290
def tree031_504 : CoverTree := CoverTree.split [tree031_501,tree031_502,tree031_503,tree031_17,tree031_14,tree031_14]
def tree031_505 : CoverTree := CoverTree.reject 362
def tree031_506 : CoverTree := CoverTree.split [tree031_505,tree031_495,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_507 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_500,tree031_504,tree031_506,tree031_496]
def tree031_508 : CoverTree := CoverTree.split [tree031_115,tree031_463,tree031_470,tree031_484,tree031_497,tree031_507]
def tree031_509 : CoverTree := CoverTree.reject 313
def tree031_510 : CoverTree := CoverTree.reject 314
def tree031_511 : CoverTree := CoverTree.reject 231
def tree031_512 : CoverTree := CoverTree.reject 387
def tree031_513 : CoverTree := CoverTree.reject 349
def tree031_514 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_512,tree031_513,tree031_187]
def tree031_515 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_509,tree031_510,tree031_511,tree031_514]
def tree031_516 : CoverTree := CoverTree.reject 394
def tree031_517 : CoverTree := CoverTree.reject 232
def tree031_518 : CoverTree := CoverTree.reject 84
def tree031_519 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_518,tree031_252,tree031_254]
def tree031_520 : CoverTree := CoverTree.reject 388
def tree031_521 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_520,tree031_152,tree031_60,tree031_14]
def tree031_522 : CoverTree := CoverTree.split [tree031_47,tree031_516,tree031_517,tree031_519,tree031_194,tree031_521]
def tree031_523 : CoverTree := CoverTree.reject 233
def tree031_524 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_261,tree031_362,tree031_267,tree031_14]
def tree031_525 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_68,tree031_71,tree031_72,tree031_14]
def tree031_526 : CoverTree := CoverTree.reject 350
def tree031_527 : CoverTree := CoverTree.split [tree031_475,tree031_475,tree031_526,tree031_76,tree031_72,tree031_14]
def tree031_528 : CoverTree := CoverTree.reject 157
def tree031_529 : CoverTree := CoverTree.split [tree031_491,tree031_491,tree031_528,tree031_14,tree031_14,tree031_14]
def tree031_530 : CoverTree := CoverTree.split [tree031_478,tree031_529,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_531 : CoverTree := CoverTree.split [tree031_7,tree031_523,tree031_524,tree031_525,tree031_527,tree031_530]
def tree031_532 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_20,tree031_21,tree031_22,tree031_23]
def tree031_533 : CoverTree := CoverTree.reject 389
def tree031_534 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_79,tree031_533,tree031_81,tree031_81]
def tree031_535 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_368,tree031_87,tree031_89,tree031_14]
def tree031_536 : CoverTree := CoverTree.reject 351
def tree031_537 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_536,tree031_17,tree031_94,tree031_14]
def tree031_538 : CoverTree := CoverTree.split [tree031_532,tree031_534,tree031_535,tree031_537,tree031_490,tree031_496]
def tree031_539 : CoverTree := CoverTree.reject 85
def tree031_540 : CoverTree := CoverTree.reject 59
def tree031_541 : CoverTree := CoverTree.split [tree031_539,tree031_540,tree031_20,tree031_21,tree031_29,tree031_30]
def tree031_542 : CoverTree := CoverTree.reject 68
def tree031_543 : CoverTree := CoverTree.reject 363
def tree031_544 : CoverTree := CoverTree.reject 325
def tree031_545 : CoverTree := CoverTree.split [tree031_80,tree031_80,tree031_80,tree031_544,tree031_14,tree031_14]
def tree031_546 : CoverTree := CoverTree.split [tree031_542,tree031_543,tree031_545,tree031_81,tree031_81,tree031_81]
def tree031_547 : CoverTree := CoverTree.reject 139
def tree031_548 : CoverTree := CoverTree.split [tree031_491,tree031_491,tree031_547,tree031_14,tree031_14,tree031_14]
def tree031_549 : CoverTree := CoverTree.split [tree031_498,tree031_548,tree031_34,tree031_17,tree031_36,tree031_14]
def tree031_550 : CoverTree := CoverTree.split [tree031_501,tree031_495,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_551 : CoverTree := CoverTree.reject 158
def tree031_552 : CoverTree := CoverTree.split [tree031_491,tree031_491,tree031_492,tree031_493,tree031_14,tree031_551]
def tree031_553 : CoverTree := CoverTree.split [tree031_552,tree031_495,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_554 : CoverTree := CoverTree.split [tree031_541,tree031_546,tree031_549,tree031_550,tree031_553,tree031_496]
def tree031_555 : CoverTree := CoverTree.split [tree031_140,tree031_515,tree031_522,tree031_531,tree031_538,tree031_554]
def tree031_556 : CoverTree := CoverTree.reject 315
def tree031_557 : CoverTree := CoverTree.reject 203
def tree031_558 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_213,tree031_214,tree031_556,tree031_557]
def tree031_559 : CoverTree := CoverTree.reject 316
def tree031_560 : CoverTree := CoverTree.reject 21
def tree031_561 : CoverTree := CoverTree.reject 409
def tree031_562 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_560,tree031_561,tree031_187]
def tree031_563 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_560,tree031_231,tree031_187]
def tree031_564 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_234,tree031_187,tree031_187]
def tree031_565 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_559,tree031_562,tree031_563,tree031_564]
def tree031_566 : CoverTree := CoverTree.reject 368
def tree031_567 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_239,tree031_243,tree031_246]
def tree031_568 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_413,tree031_252,tree031_254]
def tree031_569 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_15,tree031_17,tree031_60,tree031_14]
def tree031_570 : CoverTree := CoverTree.split [tree031_47,tree031_566,tree031_567,tree031_568,tree031_194,tree031_569]
def tree031_571 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_416,tree031_417,tree031_81,tree031_81]
def tree031_572 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_261,tree031_265,tree031_267,tree031_14]
def tree031_573 : CoverTree := CoverTree.reject 211
def tree031_574 : CoverTree := CoverTree.reject 364
def tree031_575 : CoverTree := CoverTree.split [tree031_573,tree031_574,tree031_74,tree031_76,tree031_72,tree031_14]
def tree031_576 : CoverTree := CoverTree.split [tree031_7,tree031_571,tree031_572,tree031_525,tree031_575,tree031_530]
def tree031_577 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_79,tree031_81,tree031_81,tree031_81]
def tree031_578 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_85,tree031_87,tree031_89,tree031_14]
def tree031_579 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_92,tree031_17,tree031_94,tree031_14]
def tree031_580 : CoverTree := CoverTree.reject 151
def tree031_581 : CoverTree := CoverTree.reject 178
def tree031_582 : CoverTree := CoverTree.split [tree031_491,tree031_491,tree031_581,tree031_14,tree031_14,tree031_14]
def tree031_583 : CoverTree := CoverTree.split [tree031_580,tree031_582,tree031_15,tree031_17,tree031_14,tree031_14]
def tree031_584 : CoverTree := CoverTree.split [tree031_532,tree031_577,tree031_578,tree031_579,tree031_583,tree031_496]
def tree031_585 : CoverTree := CoverTree.reject 410
def tree031_586 : CoverTree := CoverTree.split [tree031_542,tree031_585,tree031_81,tree031_81,tree031_81,tree031_81]
def tree031_587 : CoverTree := CoverTree.split [tree031_541,tree031_586,tree031_549,tree031_550,tree031_553,tree031_496]
def tree031_588 : CoverTree := CoverTree.split [tree031_558,tree031_565,tree031_570,tree031_576,tree031_584,tree031_587]
def tree031_589 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_215,tree031_216,tree031_217]
def tree031_590 : CoverTree := CoverTree.reject 204
def tree031_591 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_213,tree031_214,tree031_589,tree031_590]
def tree031_592 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_221,tree031_222,tree031_187]
def tree031_593 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_224,tree031_227,tree031_187]
def tree031_594 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_230,tree031_231,tree031_187]
def tree031_595 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_592,tree031_593,tree031_594,tree031_564]
def tree031_596 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_407,tree031_408,tree031_409,tree031_81]
def tree031_597 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_238,tree031_239,tree031_243,tree031_246]
def tree031_598 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_248,tree031_413,tree031_252,tree031_254]
def tree031_599 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_52,tree031_54,tree031_57,tree031_14]
def tree031_600 : CoverTree := CoverTree.split [tree031_47,tree031_596,tree031_597,tree031_598,tree031_599,tree031_569]
def tree031_601 : CoverTree := CoverTree.reject 354
def tree031_602 : CoverTree := CoverTree.split [tree031_542,tree031_601,tree031_416,tree031_417,tree031_81,tree031_81]
def tree031_603 : CoverTree := CoverTree.reject 355
def tree031_604 : CoverTree := CoverTree.split [tree031_498,tree031_603,tree031_261,tree031_265,tree031_267,tree031_14]
def tree031_605 : CoverTree := CoverTree.reject 356
def tree031_606 : CoverTree := CoverTree.split [tree031_501,tree031_605,tree031_68,tree031_71,tree031_72,tree031_14]
def tree031_607 : CoverTree := CoverTree.reject 39
def tree031_608 : CoverTree := CoverTree.split [tree031_491,tree031_491,tree031_607,tree031_607,tree031_607,tree031_14]
def tree031_609 : CoverTree := CoverTree.split [tree031_573,tree031_608,tree031_74,tree031_76,tree031_72,tree031_14]
def tree031_610 : CoverTree := CoverTree.split [tree031_7,tree031_602,tree031_604,tree031_606,tree031_609,tree031_530]
def tree031_611 : CoverTree := CoverTree.split [tree031_539,tree031_540,tree031_20,tree031_21,tree031_22,tree031_23]
def tree031_612 : CoverTree := CoverTree.reject 357
def tree031_613 : CoverTree := CoverTree.split [tree031_542,tree031_612,tree031_79,tree031_81,tree031_81,tree031_81]
def tree031_614 : CoverTree := CoverTree.reject 179
def tree031_615 : CoverTree := CoverTree.split [tree031_498,tree031_614,tree031_85,tree031_87,tree031_89,tree031_14]
def tree031_616 : CoverTree := CoverTree.reject 359
def tree031_617 : CoverTree := CoverTree.split [tree031_491,tree031_491,tree031_581,tree031_616,tree031_14,tree031_14]
def tree031_618 : CoverTree := CoverTree.split [tree031_501,tree031_617,tree031_92,tree031_17,tree031_94,tree031_14]
def tree031_619 : CoverTree := CoverTree.split [tree031_611,tree031_613,tree031_615,tree031_618,tree031_583,tree031_496]
def tree031_620 : CoverTree := CoverTree.reject 149
def tree031_621 : CoverTree := CoverTree.reject 150
def tree031_622 : CoverTree := CoverTree.split [tree031_80,tree031_80,tree031_80,tree031_620,tree031_621,tree031_14]
def tree031_623 : CoverTree := CoverTree.split [tree031_542,tree031_622,tree031_81,tree031_81,tree031_81,tree031_81]
def tree031_624 : CoverTree := CoverTree.split [tree031_541,tree031_623,tree031_549,tree031_550,tree031_553,tree031_496]
def tree031_625 : CoverTree := CoverTree.split [tree031_591,tree031_595,tree031_600,tree031_610,tree031_619,tree031_624]
def tree031_626 : CoverTree := CoverTree.split [tree031_422,tree031_458,tree031_508,tree031_555,tree031_588,tree031_625]
def tree031_627 : CoverTree := CoverTree.reject 16
def tree031_628 : CoverTree := CoverTree.reject 17
def tree031_629 : CoverTree := CoverTree.reject 104
def tree031_630 : CoverTree := CoverTree.reject 173
def tree031_631 : CoverTree := CoverTree.reject 169
def tree031_632 : CoverTree := CoverTree.reject 175
def tree031_633 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_632,tree031_17,tree031_14,tree031_14]
def tree031_634 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_629,tree031_630,tree031_631,tree031_633]
def tree031_635 : CoverTree := CoverTree.reject 111
def tree031_636 : CoverTree := CoverTree.reject 99
def tree031_637 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_635,tree031_636,tree031_450,tree031_450]
def tree031_638 : CoverTree := CoverTree.split [tree031_102,tree031_102,tree031_627,tree031_628,tree031_634,tree031_637]
def tree031_639 : CoverTree := CoverTree.reject 244
def tree031_640 : CoverTree := CoverTree.reject 177
def tree031_641 : CoverTree := CoverTree.reject 291
def tree031_642 : CoverTree := CoverTree.reject 292
def tree031_643 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_641,tree031_642,tree031_60,tree031_433]
def tree031_644 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_425,tree031_639,tree031_640,tree031_643]
def tree031_645 : CoverTree := CoverTree.reject 234
def tree031_646 : CoverTree := CoverTree.reject 138
def tree031_647 : CoverTree := CoverTree.reject 193
def tree031_648 : CoverTree := CoverTree.reject 194
def tree031_649 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_647,tree031_648,tree031_72,tree031_14]
def tree031_650 : CoverTree := CoverTree.reject 396
def tree031_651 : CoverTree := CoverTree.reject 397
def tree031_652 : CoverTree := CoverTree.split [tree031_16,tree031_650,tree031_651,tree031_14,tree031_14,tree031_14]
def tree031_653 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_289,tree031_652,tree031_14,tree031_14]
def tree031_654 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_645,tree031_646,tree031_649,tree031_653]
def tree031_655 : CoverTree := CoverTree.reject 127
def tree031_656 : CoverTree := CoverTree.reject 293
def tree031_657 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_445,tree031_656,tree031_94,tree031_14]
def tree031_658 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_655,tree031_657,tree031_449,tree031_450]
def tree031_659 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_297,tree031_17,tree031_36,tree031_14]
def tree031_660 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_659,tree031_450,tree031_450,tree031_456]
def tree031_661 : CoverTree := CoverTree.split [tree031_102,tree031_102,tree031_644,tree031_654,tree031_658,tree031_660]
def tree031_662 : CoverTree := CoverTree.reject 317
def tree031_663 : CoverTree := CoverTree.reject 318
def tree031_664 : CoverTree := CoverTree.reject 352
def tree031_665 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_309,tree031_664,tree031_187]
def tree031_666 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_306,tree031_662,tree031_663,tree031_665]
def tree031_667 : CoverTree := CoverTree.reject 319
def tree031_668 : CoverTree := CoverTree.reject 83
def tree031_669 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_668,tree031_252,tree031_254]
def tree031_670 : CoverTree := CoverTree.reject 294
def tree031_671 : CoverTree := CoverTree.reject 398
def tree031_672 : CoverTree := CoverTree.split [tree031_16,tree031_671,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_673 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_670,tree031_672,tree031_60,tree031_320]
def tree031_674 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_667,tree031_669,tree031_194,tree031_673]
def tree031_675 : CoverTree := CoverTree.reject 299
def tree031_676 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_261,tree031_675,tree031_267,tree031_14]
def tree031_677 : CoverTree := CoverTree.reject 353
def tree031_678 : CoverTree := CoverTree.split [tree031_475,tree031_475,tree031_677,tree031_76,tree031_72,tree031_14]
def tree031_679 : CoverTree := CoverTree.split [tree031_478,tree031_479,tree031_15,tree031_482,tree031_14,tree031_14]
def tree031_680 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_676,tree031_474,tree031_678,tree031_679]
def tree031_681 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_485,tree031_87,tree031_89,tree031_14]
def tree031_682 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_331,tree031_17,tree031_94,tree031_14]
def tree031_683 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_681,tree031_682,tree031_490,tree031_496]
def tree031_684 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_549,tree031_550,tree031_506,tree031_496]
def tree031_685 : CoverTree := CoverTree.split [tree031_115,tree031_666,tree031_674,tree031_680,tree031_683,tree031_684]
def tree031_686 : CoverTree := CoverTree.reject 320
def tree031_687 : CoverTree := CoverTree.reject 321
def tree031_688 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_686,tree031_687,tree031_563,tree031_564]
def tree031_689 : CoverTree := CoverTree.reject 395
def tree031_690 : CoverTree := CoverTree.reject 235
def tree031_691 : CoverTree := CoverTree.reject 249
def tree031_692 : CoverTree := CoverTree.reject 250
def tree031_693 : CoverTree := CoverTree.split [tree031_13,tree031_691,tree031_692,tree031_14,tree031_14,tree031_14]
def tree031_694 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_693,tree031_152,tree031_60,tree031_14]
def tree031_695 : CoverTree := CoverTree.split [tree031_47,tree031_689,tree031_690,tree031_519,tree031_194,tree031_694]
def tree031_696 : CoverTree := CoverTree.split [tree031_475,tree031_475,tree031_74,tree031_76,tree031_72,tree031_14]
def tree031_697 : CoverTree := CoverTree.split [tree031_7,tree031_571,tree031_524,tree031_525,tree031_696,tree031_530]
def tree031_698 : CoverTree := CoverTree.reject 390
def tree031_699 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_79,tree031_698,tree031_81,tree031_81]
def tree031_700 : CoverTree := CoverTree.split [tree031_532,tree031_699,tree031_535,tree031_579,tree031_490,tree031_496]
def tree031_701 : CoverTree := CoverTree.split [tree031_140,tree031_688,tree031_695,tree031_697,tree031_700,tree031_554]
def tree031_702 : CoverTree := CoverTree.reject 322
def tree031_703 : CoverTree := CoverTree.reject 205
def tree031_704 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_213,tree031_214,tree031_702,tree031_703]
def tree031_705 : CoverTree := CoverTree.reject 323
def tree031_706 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_560,tree031_227,tree031_187]
def tree031_707 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_705,tree031_706,tree031_563,tree031_564]
def tree031_708 : CoverTree := CoverTree.reject 369
def tree031_709 : CoverTree := CoverTree.split [tree031_47,tree031_708,tree031_567,tree031_568,tree031_194,tree031_569]
def tree031_710 : CoverTree := CoverTree.split [tree031_704,tree031_707,tree031_709,tree031_576,tree031_584,tree031_624]
def tree031_711 : CoverTree := CoverTree.reject 206
def tree031_712 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_213,tree031_214,tree031_589,tree031_711]
def tree031_713 : CoverTree := CoverTree.split [tree031_712,tree031_595,tree031_600,tree031_610,tree031_619,tree031_624]
def tree031_714 : CoverTree := CoverTree.split [tree031_638,tree031_661,tree031_685,tree031_701,tree031_710,tree031_713]
def tree031_715 : CoverTree := CoverTree.reject 174
def tree031_716 : CoverTree := CoverTree.reject 170
def tree031_717 : CoverTree := CoverTree.reject 295
def tree031_718 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_632,tree031_717,tree031_14,tree031_14]
def tree031_719 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_629,tree031_715,tree031_716,tree031_718]
def tree031_720 : CoverTree := CoverTree.reject 112
def tree031_721 : CoverTree := CoverTree.reject 100
def tree031_722 : CoverTree := CoverTree.reject 101
def tree031_723 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_720,tree031_721,tree031_722,tree031_450]
def tree031_724 : CoverTree := CoverTree.split [tree031_102,tree031_102,tree031_627,tree031_628,tree031_719,tree031_723]
def tree031_725 : CoverTree := CoverTree.reject 62
def tree031_726 : CoverTree := CoverTree.reject 183
def tree031_727 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_725,tree031_726,tree031_254]
def tree031_728 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_725,tree031_57,tree031_14]
def tree031_729 : CoverTree := CoverTree.reject 402
def tree031_730 : CoverTree := CoverTree.reject 403
def tree031_731 : CoverTree := CoverTree.reject 404
def tree031_732 : CoverTree := CoverTree.split [tree031_13,tree031_729,tree031_730,tree031_731,tree031_14,tree031_14]
def tree031_733 : CoverTree := CoverTree.reject 405
def tree031_734 : CoverTree := CoverTree.split [tree031_16,tree031_733,tree031_14,tree031_14,tree031_14,tree031_14]
def tree031_735 : CoverTree := CoverTree.split [tree031_428,tree031_428,tree031_732,tree031_734,tree031_60,tree031_433]
def tree031_736 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_425,tree031_727,tree031_728,tree031_735]
def tree031_737 : CoverTree := CoverTree.reject 192
def tree031_738 : CoverTree := CoverTree.reject 130
def tree031_739 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_261,tree031_737,tree031_738,tree031_14]
def tree031_740 : CoverTree := CoverTree.reject 391
def tree031_741 : CoverTree := CoverTree.reject 360
def tree031_742 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_740,tree031_741,tree031_72,tree031_14]
def tree031_743 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_739,tree031_742,tree031_649,tree031_653]
def tree031_744 : CoverTree := CoverTree.reject 361
def tree031_745 : CoverTree := CoverTree.reject 297
def tree031_746 : CoverTree := CoverTree.reject 298
def tree031_747 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_744,tree031_745,tree031_746,tree031_14]
def tree031_748 : CoverTree := CoverTree.split [tree031_444,tree031_444,tree031_445,tree031_17,tree031_94,tree031_14]
def tree031_749 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_747,tree031_748,tree031_449,tree031_450]
def tree031_750 : CoverTree := CoverTree.split [tree031_102,tree031_102,tree031_736,tree031_743,tree031_749,tree031_660]
def tree031_751 : CoverTree := CoverTree.reject 146
def tree031_752 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_560,tree031_751,tree031_187]
def tree031_753 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_309,tree031_187,tree031_187]
def tree031_754 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_306,tree031_752,tree031_752,tree031_753]
def tree031_755 : CoverTree := CoverTree.reject 82
def tree031_756 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_239,tree031_755,tree031_246]
def tree031_757 : CoverTree := CoverTree.reject 406
def tree031_758 : CoverTree := CoverTree.reject 407
def tree031_759 : CoverTree := CoverTree.reject 408
def tree031_760 : CoverTree := CoverTree.split [tree031_13,tree031_757,tree031_758,tree031_759,tree031_14,tree031_14]
def tree031_761 : CoverTree := CoverTree.split [tree031_466,tree031_466,tree031_760,tree031_672,tree031_60,tree031_320]
def tree031_762 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_756,tree031_669,tree031_194,tree031_761]
def tree031_763 : CoverTree := CoverTree.split [tree031_106,tree031_106,tree031_676,tree031_474,tree031_696,tree031_679]
def tree031_764 : CoverTree := CoverTree.split [tree031_115,tree031_754,tree031_762,tree031_763,tree031_683,tree031_684]
def tree031_765 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_560,tree031_222,tree031_187]
def tree031_766 : CoverTree := CoverTree.reject 240
def tree031_767 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_560,tree031_766,tree031_187]
def tree031_768 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_765,tree031_767,tree031_563,tree031_564]
def tree031_769 : CoverTree := CoverTree.reject 248
def tree031_770 : CoverTree := CoverTree.split [tree031_80,tree031_80,tree031_80,tree031_769,tree031_14,tree031_14]
def tree031_771 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_408,tree031_409,tree031_770]
def tree031_772 : CoverTree := CoverTree.split [tree031_47,tree031_771,tree031_567,tree031_519,tree031_194,tree031_694]
def tree031_773 : CoverTree := CoverTree.split [tree031_532,tree031_577,tree031_535,tree031_579,tree031_490,tree031_496]
def tree031_774 : CoverTree := CoverTree.split [tree031_140,tree031_768,tree031_772,tree031_697,tree031_773,tree031_554]
def tree031_775 : CoverTree := CoverTree.reject 401
def tree031_776 : CoverTree := CoverTree.split [tree031_184,tree031_184,tree031_775,tree031_14,tree031_14,tree031_14]
def tree031_777 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_560,tree031_216,tree031_776]
def tree031_778 : CoverTree := CoverTree.reject 56
def tree031_779 : CoverTree := CoverTree.split [tree031_182,tree031_182,tree031_182,tree031_778,tree031_187,tree031_187]
def tree031_780 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_213,tree031_214,tree031_777,tree031_779]
def tree031_781 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_765,tree031_706,tree031_563,tree031_564]
def tree031_782 : CoverTree := CoverTree.split [tree031_193,tree031_193,tree031_193,tree031_408,tree031_409,tree031_81]
def tree031_783 : CoverTree := CoverTree.split [tree031_47,tree031_782,tree031_567,tree031_568,tree031_194,tree031_569]
def tree031_784 : CoverTree := CoverTree.split [tree031_780,tree031_781,tree031_783,tree031_576,tree031_584,tree031_624]
def tree031_785 : CoverTree := CoverTree.split [tree031_41,tree031_41,tree031_213,tree031_214,tree031_589,tree031_779]
def tree031_786 : CoverTree := CoverTree.split [tree031_785,tree031_595,tree031_600,tree031_610,tree031_619,tree031_624]
def tree031_787 : CoverTree := CoverTree.split [tree031_724,tree031_750,tree031_764,tree031_774,tree031_784,tree031_786]
def tree031_788 : CoverTree := CoverTree.split [tree031_100,tree031_280,tree031_421,tree031_626,tree031_714,tree031_787]
def tree031 : CoverTree := tree031_788

end Snake9.Shared89
