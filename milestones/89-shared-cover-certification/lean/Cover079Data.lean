import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes079 : List Box := [
[(1,6),(1,5),(1,3),(1,5),(1,3),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,3)],
[(1,2),(1,6),(1,3),(1,6),(1,6),(1,6)],
[(1,3),(1,6),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,3),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,5),(1,5),(1,4)],
[(1,6),(1,6),(1,6),(1,6),(1,2),(1,2)],
[(1,6),(1,2),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,6),(1,4),(1,5),(1,5),(1,2),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,2)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,2),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,4),(1,5),(1,5)],
[(1,6),(1,6),(1,4),(1,5),(1,2),(1,5)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,1)],
[(1,6),(1,6),(4,4),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(1,6)],
[(1,6),(1,5),(1,5),(1,4),(1,2),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,5),(1,2),(1,5),(1,4),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,3),(1,2)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(5,5),(1,1),(6,6),(1,6)],
[(1,6),(1,6),(5,5),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(6,6),(1,6)],
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,5),(1,3),(1,5)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(5,5),(1,6)],
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
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(1,6),(1,6),(4,4),(6,6),(1,1),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(5,5),(1,6),(1,6)],
[(3,3),(2,2),(5,5),(5,5),(1,6),(1,6)],
[(5,5),(1,1),(6,6),(4,4),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(4,4),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(5,5),(1,6),(1,6)],
[(1,6),(1,1),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,1),(5,5),(5,5),(4,4),(1,6),(1,6)],
[(1,6),(2,2),(6,6),(3,3),(3,3),(1,6)],
[(1,6),(3,3),(3,3),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(3,3),(4,4),(4,4),(1,6)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(4,4),(4,4),(1,6)],
[(3,3),(2,2),(5,5),(4,4),(1,6),(1,6)],
[(5,5),(1,1),(6,6),(3,3),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(3,3),(1,6),(1,6)],
[(1,1),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(5,5),(1,1)],
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
[(1,6),(1,6),(3,3),(5,5),(4,4),(2,2)],
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
[(1,6),(1,6),(3,3),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(3,3)],
[(1,6),(1,6),(3,3),(3,3),(5,5),(4,4)],
[(1,6),(2,2),(5,5),(5,5),(3,3),(1,6)],
[(3,3),(3,3),(3,3),(5,5),(1,6),(1,6)],
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
[(1,6),(2,2),(3,3),(4,4),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(4,4),(1,6)],
[(1,6),(3,3),(4,4),(6,6),(2,2),(1,6)],
[(1,6),(3,3),(5,5),(3,3),(3,3),(1,6)],
[(2,2),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(2,2),(5,5),(5,5),(2,2),(1,6),(1,6)],
[(3,3),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)],
[(1,6),(2,2),(4,4),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(3,3),(1,6)],
[(1,6),(2,2),(4,4),(5,5),(4,4),(1,6)],
[(1,6),(4,4),(4,4),(3,3),(4,4),(1,6)],
[(3,3),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(4,4),(1,6),(1,6)],
[(4,4),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(4,4),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(5,5),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(5,5),(6,6),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(5,5),(1,1),(1,6)],
[(1,1),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(4,4),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(2,2),(1,6),(1,6)],
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
[(2,2),(3,3),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(4,4),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(3,3),(1,6)],
[(2,2),(4,4),(4,4),(6,6),(4,4),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(4,4),(1,6)],
[(2,2),(4,4),(6,6),(3,3),(5,5),(1,6)],
[(2,2),(4,4),(6,6),(4,4),(3,3),(1,6)],
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
[(3,3),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(3,3),(4,4),(3,3),(6,6),(4,4),(1,6)],
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
[(4,4),(4,4),(3,3),(6,6),(3,3),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(3,3),(1,6)],
[(5,5),(2,2),(3,3),(6,6),(4,4),(1,6)],
[(5,5),(2,2),(5,5),(4,4),(4,4),(1,6)],
[(5,5),(3,3),(3,3),(6,6),(3,3),(1,6)],
[(6,6),(1,1),(5,5),(6,6),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(3,3),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(5,5)],
[(1,6),(2,2),(5,5),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(5,5),(3,3),(5,5),(1,6)],
[(1,6),(3,3),(4,4),(3,3),(4,4),(1,6)],
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
[(1,6),(4,4),(3,3),(2,2),(6,6),(4,4)],
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
[(1,6),(1,6),(5,5),(4,4),(2,2),(4,4)],
[(1,6),(2,2),(4,4),(4,4),(4,4),(1,6)],
[(1,6),(2,2),(5,5),(3,3),(3,3),(1,6)],
[(1,6),(3,3),(6,6),(5,5),(1,1),(1,6)],
[(1,6),(4,4),(6,6),(2,2),(2,2),(1,6)],
[(1,6),(5,5),(4,4),(5,5),(2,2),(1,6)],
[(3,3),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(4,4),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(5,5),(5,5),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(3,3),(6,6),(6,6),(2,2)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(2,2)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(3,3)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(4,4)],
[(1,6),(4,4),(3,3),(6,6),(4,4),(2,2)],
[(2,2),(5,5),(6,6),(2,2),(3,3),(1,6)],
[(2,2),(5,5),(6,6),(2,2),(4,4),(1,6)],
[(2,2),(6,6),(5,5),(3,3),(3,3),(1,6)],
[(2,2),(6,6),(6,6),(2,2),(3,3),(1,6)],
[(3,3),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(3,3),(5,5),(2,2),(6,6),(4,4),(1,6)],
[(3,3),(5,5),(3,3),(4,4),(4,4),(1,6)],
[(3,3),(5,5),(5,5),(2,2),(4,4),(1,6)],
[(4,4),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(4,4),(4,4),(2,2),(6,6),(4,4),(1,6)],
[(4,4),(4,4),(5,5),(2,2),(4,4),(1,6)],
[(5,5),(4,4),(5,5),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(4,4)],
[(1,6),(2,2),(4,4),(4,4),(3,3),(1,6)],
[(3,3),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(5,5),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(6,6),(4,4),(2,2)],
[(1,6),(2,2),(4,4),(6,6),(4,4),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(4,4),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(3,3)],
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

def root079 : Nat := 3544

def tree079_0 : CoverTree := CoverTree.reject 24
def tree079_1 : CoverTree := CoverTree.reject 17
def tree079_2 : CoverTree := CoverTree.reject 18
def tree079_3 : CoverTree := CoverTree.reject 14
def tree079_4 : CoverTree := CoverTree.reject 2
def tree079_5 : CoverTree := CoverTree.reject 19
def tree079_6 : CoverTree := CoverTree.reject 195
def tree079_7 : CoverTree := CoverTree.reject 147
def tree079_8 : CoverTree := CoverTree.reject 122
def tree079_9 : CoverTree := CoverTree.reject 100
def tree079_10 : CoverTree := CoverTree.reject 3
def tree079_11 : CoverTree := CoverTree.reject 12
def tree079_12 : CoverTree := CoverTree.accept
def tree079_13 : CoverTree := CoverTree.split [tree079_11,tree079_12,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_14 : CoverTree := CoverTree.reject 11
def tree079_15 : CoverTree := CoverTree.split [tree079_14,tree079_12,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_16 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_17 : CoverTree := CoverTree.split [tree079_5,tree079_6,tree079_7,tree079_8,tree079_9,tree079_16]
def tree079_18 : CoverTree := CoverTree.reject 33
def tree079_19 : CoverTree := CoverTree.reject 23
def tree079_20 : CoverTree := CoverTree.reject 46
def tree079_21 : CoverTree := CoverTree.reject 47
def tree079_22 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_18,tree079_19,tree079_20,tree079_21]
def tree079_23 : CoverTree := CoverTree.reject 171
def tree079_24 : CoverTree := CoverTree.reject 112
def tree079_25 : CoverTree := CoverTree.reject 91
def tree079_26 : CoverTree := CoverTree.split [tree079_22,tree079_23,tree079_24,tree079_25,tree079_16,tree079_16]
def tree079_27 : CoverTree := CoverTree.reject 49
def tree079_28 : CoverTree := CoverTree.reject 50
def tree079_29 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_18,tree079_19,tree079_27,tree079_28]
def tree079_30 : CoverTree := CoverTree.reject 148
def tree079_31 : CoverTree := CoverTree.reject 64
def tree079_32 : CoverTree := CoverTree.split [tree079_11,tree079_31,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_33 : CoverTree := CoverTree.reject 43
def tree079_34 : CoverTree := CoverTree.split [tree079_33,tree079_12,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_35 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_32,tree079_15,tree079_34,tree079_12]
def tree079_36 : CoverTree := CoverTree.split [tree079_29,tree079_30,tree079_35,tree079_16,tree079_16,tree079_16]
def tree079_37 : CoverTree := CoverTree.split [tree079_4,tree079_4,tree079_4,tree079_17,tree079_26,tree079_36]
def tree079_38 : CoverTree := CoverTree.reject 196
def tree079_39 : CoverTree := CoverTree.reject 149
def tree079_40 : CoverTree := CoverTree.reject 42
def tree079_41 : CoverTree := CoverTree.reject 72
def tree079_42 : CoverTree := CoverTree.reject 73
def tree079_43 : CoverTree := CoverTree.split [tree079_11,tree079_40,tree079_41,tree079_42,tree079_12,tree079_12]
def tree079_44 : CoverTree := CoverTree.reject 74
def tree079_45 : CoverTree := CoverTree.reject 75
def tree079_46 : CoverTree := CoverTree.split [tree079_14,tree079_44,tree079_45,tree079_12,tree079_12,tree079_12]
def tree079_47 : CoverTree := CoverTree.reject 28
def tree079_48 : CoverTree := CoverTree.split [tree079_47,tree079_12,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_49 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_43,tree079_46,tree079_48,tree079_12]
def tree079_50 : CoverTree := CoverTree.split [tree079_11,tree079_40,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_51 : CoverTree := CoverTree.reject 76
def tree079_52 : CoverTree := CoverTree.split [tree079_14,tree079_51,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_53 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_50,tree079_52,tree079_48,tree079_12]
def tree079_54 : CoverTree := CoverTree.split [tree079_5,tree079_38,tree079_39,tree079_49,tree079_53,tree079_16]
def tree079_55 : CoverTree := CoverTree.reject 48
def tree079_56 : CoverTree := CoverTree.reject 1
def tree079_57 : CoverTree := CoverTree.split [tree079_56,tree079_56,tree079_56,tree079_12,tree079_12,tree079_12]
def tree079_58 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_55,tree079_57,tree079_57,tree079_57]
def tree079_59 : CoverTree := CoverTree.reject 77
def tree079_60 : CoverTree := CoverTree.reject 78
def tree079_61 : CoverTree := CoverTree.split [tree079_11,tree079_59,tree079_60,tree079_12,tree079_12,tree079_12]
def tree079_62 : CoverTree := CoverTree.reject 79
def tree079_63 : CoverTree := CoverTree.split [tree079_14,tree079_62,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_64 : CoverTree := CoverTree.reject 65
def tree079_65 : CoverTree := CoverTree.split [tree079_33,tree079_64,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_66 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_61,tree079_63,tree079_65,tree079_12]
def tree079_67 : CoverTree := CoverTree.reject 80
def tree079_68 : CoverTree := CoverTree.split [tree079_11,tree079_67,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_69 : CoverTree := CoverTree.reject 66
def tree079_70 : CoverTree := CoverTree.split [tree079_69,tree079_12,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_71 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_68,tree079_15,tree079_70,tree079_12]
def tree079_72 : CoverTree := CoverTree.split [tree079_22,tree079_58,tree079_66,tree079_71,tree079_16,tree079_16]
def tree079_73 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_57,tree079_57,tree079_57,tree079_57]
def tree079_74 : CoverTree := CoverTree.split [tree079_29,tree079_73,tree079_35,tree079_16,tree079_16,tree079_16]
def tree079_75 : CoverTree := CoverTree.split [tree079_4,tree079_4,tree079_4,tree079_54,tree079_72,tree079_74]
def tree079_76 : CoverTree := CoverTree.split [tree079_0,tree079_1,tree079_2,tree079_3,tree079_37,tree079_75]
def tree079_77 : CoverTree := CoverTree.reject 25
def tree079_78 : CoverTree := CoverTree.reject 38
def tree079_79 : CoverTree := CoverTree.reject 36
def tree079_80 : CoverTree := CoverTree.reject 4
def tree079_81 : CoverTree := CoverTree.reject 127
def tree079_82 : CoverTree := CoverTree.reject 83
def tree079_83 : CoverTree := CoverTree.reject 223
def tree079_84 : CoverTree := CoverTree.reject 224
def tree079_85 : CoverTree := CoverTree.split [tree079_11,tree079_83,tree079_84,tree079_12,tree079_12,tree079_12]
def tree079_86 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_85,tree079_15,tree079_12,tree079_12]
def tree079_87 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_81,tree079_82,tree079_16,tree079_86]
def tree079_88 : CoverTree := CoverTree.split [tree079_4,tree079_4,tree079_4,tree079_78,tree079_79,tree079_87]
def tree079_89 : CoverTree := CoverTree.reject 156
def tree079_90 : CoverTree := CoverTree.reject 128
def tree079_91 : CoverTree := CoverTree.reject 108
def tree079_92 : CoverTree := CoverTree.reject 226
def tree079_93 : CoverTree := CoverTree.reject 298
def tree079_94 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_92,tree079_93,tree079_12,tree079_12]
def tree079_95 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_89,tree079_90,tree079_91,tree079_94]
def tree079_96 : CoverTree := CoverTree.reject 113
def tree079_97 : CoverTree := CoverTree.reject 129
def tree079_98 : CoverTree := CoverTree.reject 84
def tree079_99 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_96,tree079_97,tree079_98,tree079_16]
def tree079_100 : CoverTree := CoverTree.reject 299
def tree079_101 : CoverTree := CoverTree.reject 227
def tree079_102 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_100,tree079_101,tree079_34,tree079_12]
def tree079_103 : CoverTree := CoverTree.reject 228
def tree079_104 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_103,tree079_15,tree079_12,tree079_12]
def tree079_105 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_102,tree079_104,tree079_16,tree079_16]
def tree079_106 : CoverTree := CoverTree.split [tree079_4,tree079_4,tree079_4,tree079_95,tree079_99,tree079_105]
def tree079_107 : CoverTree := CoverTree.reject 199
def tree079_108 : CoverTree := CoverTree.reject 157
def tree079_109 : CoverTree := CoverTree.reject 130
def tree079_110 : CoverTree := CoverTree.reject 300
def tree079_111 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_110,tree079_52,tree079_48,tree079_12]
def tree079_112 : CoverTree := CoverTree.reject 229
def tree079_113 : CoverTree := CoverTree.reject 230
def tree079_114 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_112,tree079_113,tree079_12,tree079_12]
def tree079_115 : CoverTree := CoverTree.split [tree079_5,tree079_107,tree079_108,tree079_109,tree079_111,tree079_114]
def tree079_116 : CoverTree := CoverTree.reject 176
def tree079_117 : CoverTree := CoverTree.reject 114
def tree079_118 : CoverTree := CoverTree.reject 301
def tree079_119 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_118,tree079_15,tree079_70,tree079_12]
def tree079_120 : CoverTree := CoverTree.split [tree079_22,tree079_116,tree079_117,tree079_119,tree079_16,tree079_16]
def tree079_121 : CoverTree := CoverTree.reject 158
def tree079_122 : CoverTree := CoverTree.reject 302
def tree079_123 : CoverTree := CoverTree.reject 231
def tree079_124 : CoverTree := CoverTree.reject 232
def tree079_125 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_122,tree079_123,tree079_124,tree079_12]
def tree079_126 : CoverTree := CoverTree.reject 233
def tree079_127 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_126,tree079_15,tree079_12,tree079_12]
def tree079_128 : CoverTree := CoverTree.split [tree079_29,tree079_121,tree079_125,tree079_127,tree079_16,tree079_16]
def tree079_129 : CoverTree := CoverTree.split [tree079_4,tree079_4,tree079_4,tree079_115,tree079_120,tree079_128]
def tree079_130 : CoverTree := CoverTree.reject 200
def tree079_131 : CoverTree := CoverTree.reject 159
def tree079_132 : CoverTree := CoverTree.split [tree079_5,tree079_130,tree079_131,tree079_49,tree079_53,tree079_16]
def tree079_133 : CoverTree := CoverTree.reject 177
def tree079_134 : CoverTree := CoverTree.reject 303
def tree079_135 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_134,tree079_15,tree079_70,tree079_12]
def tree079_136 : CoverTree := CoverTree.split [tree079_22,tree079_133,tree079_66,tree079_135,tree079_16,tree079_16]
def tree079_137 : CoverTree := CoverTree.reject 343
def tree079_138 : CoverTree := CoverTree.reject 344
def tree079_139 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_137,tree079_138,tree079_57,tree079_57]
def tree079_140 : CoverTree := CoverTree.reject 304
def tree079_141 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_140,tree079_15,tree079_34,tree079_12]
def tree079_142 : CoverTree := CoverTree.split [tree079_29,tree079_139,tree079_141,tree079_16,tree079_16,tree079_16]
def tree079_143 : CoverTree := CoverTree.split [tree079_4,tree079_4,tree079_4,tree079_132,tree079_136,tree079_142]
def tree079_144 : CoverTree := CoverTree.reject 201
def tree079_145 : CoverTree := CoverTree.reject 29
def tree079_146 : CoverTree := CoverTree.reject 68
def tree079_147 : CoverTree := CoverTree.reject 69
def tree079_148 : CoverTree := CoverTree.reject 70
def tree079_149 : CoverTree := CoverTree.split [tree079_14,tree079_146,tree079_147,tree079_148,tree079_12,tree079_12]
def tree079_150 : CoverTree := CoverTree.reject 71
def tree079_151 : CoverTree := CoverTree.split [tree079_47,tree079_150,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_152 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_145,tree079_149,tree079_151,tree079_12]
def tree079_153 : CoverTree := CoverTree.split [tree079_5,tree079_144,tree079_152,tree079_49,tree079_53,tree079_16]
def tree079_154 : CoverTree := CoverTree.reject 345
def tree079_155 : CoverTree := CoverTree.reject 305
def tree079_156 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_154,tree079_155,tree079_65,tree079_12]
def tree079_157 : CoverTree := CoverTree.split [tree079_22,tree079_58,tree079_156,tree079_71,tree079_16,tree079_16]
def tree079_158 : CoverTree := CoverTree.reject 346
def tree079_159 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_158,tree079_57,tree079_57,tree079_57]
def tree079_160 : CoverTree := CoverTree.reject 306
def tree079_161 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_160,tree079_15,tree079_34,tree079_12]
def tree079_162 : CoverTree := CoverTree.split [tree079_29,tree079_159,tree079_161,tree079_16,tree079_16,tree079_16]
def tree079_163 : CoverTree := CoverTree.split [tree079_4,tree079_4,tree079_4,tree079_153,tree079_157,tree079_162]
def tree079_164 : CoverTree := CoverTree.split [tree079_77,tree079_88,tree079_106,tree079_129,tree079_143,tree079_163]
def tree079_165 : CoverTree := CoverTree.reject 26
def tree079_166 : CoverTree := CoverTree.reject 7
def tree079_167 : CoverTree := CoverTree.reject 41
def tree079_168 : CoverTree := CoverTree.reject 202
def tree079_169 : CoverTree := CoverTree.reject 131
def tree079_170 : CoverTree := CoverTree.reject 109
def tree079_171 : CoverTree := CoverTree.reject 339
def tree079_172 : CoverTree := CoverTree.reject 340
def tree079_173 : CoverTree := CoverTree.reject 341
def tree079_174 : CoverTree := CoverTree.split [tree079_11,tree079_171,tree079_172,tree079_173,tree079_12,tree079_12]
def tree079_175 : CoverTree := CoverTree.reject 234
def tree079_176 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_174,tree079_175,tree079_12,tree079_12]
def tree079_177 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_168,tree079_169,tree079_170,tree079_176]
def tree079_178 : CoverTree := CoverTree.reject 115
def tree079_179 : CoverTree := CoverTree.reject 97
def tree079_180 : CoverTree := CoverTree.reject 85
def tree079_181 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_178,tree079_179,tree079_180,tree079_16]
def tree079_182 : CoverTree := CoverTree.reject 92
def tree079_183 : CoverTree := CoverTree.reject 235
def tree079_184 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_182,tree079_183,tree079_34,tree079_12]
def tree079_185 : CoverTree := CoverTree.reject 236
def tree079_186 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_185,tree079_15,tree079_12,tree079_12]
def tree079_187 : CoverTree := CoverTree.reject 237
def tree079_188 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_187,tree079_15,tree079_12,tree079_12]
def tree079_189 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_184,tree079_186,tree079_188,tree079_86]
def tree079_190 : CoverTree := CoverTree.split [tree079_166,tree079_166,tree079_167,tree079_177,tree079_181,tree079_189]
def tree079_191 : CoverTree := CoverTree.reject 31
def tree079_192 : CoverTree := CoverTree.reject 90
def tree079_193 : CoverTree := CoverTree.reject 278
def tree079_194 : CoverTree := CoverTree.reject 279
def tree079_195 : CoverTree := CoverTree.reject 9
def tree079_196 : CoverTree := CoverTree.reject 154
def tree079_197 : CoverTree := CoverTree.reject 307
def tree079_198 : CoverTree := CoverTree.reject 13
def tree079_199 : CoverTree := CoverTree.split [tree079_198,tree079_198,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_200 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_195,tree079_196,tree079_197,tree079_199]
def tree079_201 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_192,tree079_193,tree079_194,tree079_200]
def tree079_202 : CoverTree := CoverTree.reject 280
def tree079_203 : CoverTree := CoverTree.reject 186
def tree079_204 : CoverTree := CoverTree.reject 140
def tree079_205 : CoverTree := CoverTree.reject 238
def tree079_206 : CoverTree := CoverTree.reject 239
def tree079_207 : CoverTree := CoverTree.reject 240
def tree079_208 : CoverTree := CoverTree.reject 295
def tree079_209 : CoverTree := CoverTree.split [tree079_12,tree079_208,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_210 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_205,tree079_206,tree079_207,tree079_209]
def tree079_211 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_202,tree079_203,tree079_204,tree079_210]
def tree079_212 : CoverTree := CoverTree.reject 160
def tree079_213 : CoverTree := CoverTree.reject 132
def tree079_214 : CoverTree := CoverTree.reject 110
def tree079_215 : CoverTree := CoverTree.reject 241
def tree079_216 : CoverTree := CoverTree.reject 308
def tree079_217 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_215,tree079_216,tree079_12,tree079_12]
def tree079_218 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_212,tree079_213,tree079_214,tree079_217]
def tree079_219 : CoverTree := CoverTree.reject 116
def tree079_220 : CoverTree := CoverTree.reject 95
def tree079_221 : CoverTree := CoverTree.reject 242
def tree079_222 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_220,tree079_221,tree079_70,tree079_12]
def tree079_223 : CoverTree := CoverTree.reject 243
def tree079_224 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_223,tree079_15,tree079_12,tree079_12]
def tree079_225 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_219,tree079_222,tree079_224,tree079_16]
def tree079_226 : CoverTree := CoverTree.reject 309
def tree079_227 : CoverTree := CoverTree.reject 244
def tree079_228 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_226,tree079_227,tree079_34,tree079_12]
def tree079_229 : CoverTree := CoverTree.reject 245
def tree079_230 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_229,tree079_15,tree079_12,tree079_12]
def tree079_231 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_228,tree079_230,tree079_16,tree079_16]
def tree079_232 : CoverTree := CoverTree.split [tree079_191,tree079_201,tree079_211,tree079_218,tree079_225,tree079_231]
def tree079_233 : CoverTree := CoverTree.reject 22
def tree079_234 : CoverTree := CoverTree.reject 51
def tree079_235 : CoverTree := CoverTree.reject 120
def tree079_236 : CoverTree := CoverTree.reject 281
def tree079_237 : CoverTree := CoverTree.reject 215
def tree079_238 : CoverTree := CoverTree.reject 203
def tree079_239 : CoverTree := CoverTree.reject 347
def tree079_240 : CoverTree := CoverTree.reject 310
def tree079_241 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_195,tree079_239,tree079_240,tree079_199]
def tree079_242 : CoverTree := CoverTree.split [tree079_234,tree079_235,tree079_236,tree079_237,tree079_238,tree079_241]
def tree079_243 : CoverTree := CoverTree.reject 40
def tree079_244 : CoverTree := CoverTree.reject 359
def tree079_245 : CoverTree := CoverTree.reject 204
def tree079_246 : CoverTree := CoverTree.reject 187
def tree079_247 : CoverTree := CoverTree.reject 0
def tree079_248 : CoverTree := CoverTree.reject 311
def tree079_249 : CoverTree := CoverTree.reject 312
def tree079_250 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_248,tree079_249,tree079_12]
def tree079_251 : CoverTree := CoverTree.reject 246
def tree079_252 : CoverTree := CoverTree.reject 247
def tree079_253 : CoverTree := CoverTree.reject 107
def tree079_254 : CoverTree := CoverTree.split [tree079_253,tree079_12,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_255 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_251,tree079_252,tree079_254,tree079_12]
def tree079_256 : CoverTree := CoverTree.split [tree079_243,tree079_244,tree079_245,tree079_246,tree079_250,tree079_255]
def tree079_257 : CoverTree := CoverTree.reject 205
def tree079_258 : CoverTree := CoverTree.reject 185
def tree079_259 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_145,tree079_258,tree079_151,tree079_12]
def tree079_260 : CoverTree := CoverTree.reject 313
def tree079_261 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_260,tree079_52,tree079_48,tree079_12]
def tree079_262 : CoverTree := CoverTree.split [tree079_5,tree079_257,tree079_259,tree079_49,tree079_261,tree079_16]
def tree079_263 : CoverTree := CoverTree.reject 178
def tree079_264 : CoverTree := CoverTree.reject 155
def tree079_265 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_264,tree079_63,tree079_65,tree079_12]
def tree079_266 : CoverTree := CoverTree.reject 314
def tree079_267 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_266,tree079_15,tree079_70,tree079_12]
def tree079_268 : CoverTree := CoverTree.split [tree079_22,tree079_263,tree079_265,tree079_267,tree079_16,tree079_16]
def tree079_269 : CoverTree := CoverTree.reject 367
def tree079_270 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_269,tree079_57,tree079_57,tree079_57]
def tree079_271 : CoverTree := CoverTree.split [tree079_29,tree079_270,tree079_35,tree079_16,tree079_16,tree079_16]
def tree079_272 : CoverTree := CoverTree.split [tree079_233,tree079_242,tree079_256,tree079_262,tree079_268,tree079_271]
def tree079_273 : CoverTree := CoverTree.reject 146
def tree079_274 : CoverTree := CoverTree.reject 121
def tree079_275 : CoverTree := CoverTree.reject 282
def tree079_276 : CoverTree := CoverTree.reject 216
def tree079_277 : CoverTree := CoverTree.reject 206
def tree079_278 : CoverTree := CoverTree.reject 348
def tree079_279 : CoverTree := CoverTree.reject 380
def tree079_280 : CoverTree := CoverTree.split [tree079_198,tree079_198,tree079_279,tree079_12,tree079_12,tree079_12]
def tree079_281 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_195,tree079_278,tree079_280,tree079_199]
def tree079_282 : CoverTree := CoverTree.split [tree079_234,tree079_274,tree079_275,tree079_276,tree079_277,tree079_281]
def tree079_283 : CoverTree := CoverTree.reject 335
def tree079_284 : CoverTree := CoverTree.reject 207
def tree079_285 : CoverTree := CoverTree.reject 349
def tree079_286 : CoverTree := CoverTree.reject 103
def tree079_287 : CoverTree := CoverTree.reject 104
def tree079_288 : CoverTree := CoverTree.split [tree079_47,tree079_286,tree079_287,tree079_12,tree079_12,tree079_12]
def tree079_289 : CoverTree := CoverTree.reject 105
def tree079_290 : CoverTree := CoverTree.split [tree079_289,tree079_12,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_291 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_285,tree079_288,tree079_290]
def tree079_292 : CoverTree := CoverTree.reject 124
def tree079_293 : CoverTree := CoverTree.split [tree079_14,tree079_292,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_294 : CoverTree := CoverTree.reject 106
def tree079_295 : CoverTree := CoverTree.split [tree079_47,tree079_294,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_296 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_293,tree079_295,tree079_12]
def tree079_297 : CoverTree := CoverTree.reject 248
def tree079_298 : CoverTree := CoverTree.reject 249
def tree079_299 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_297,tree079_298,tree079_254,tree079_12]
def tree079_300 : CoverTree := CoverTree.split [tree079_243,tree079_283,tree079_284,tree079_291,tree079_296,tree079_299]
def tree079_301 : CoverTree := CoverTree.reject 208
def tree079_302 : CoverTree := CoverTree.reject 368
def tree079_303 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_145,tree079_302,tree079_151,tree079_12]
def tree079_304 : CoverTree := CoverTree.split [tree079_5,tree079_301,tree079_303,tree079_49,tree079_53,tree079_16]
def tree079_305 : CoverTree := CoverTree.reject 350
def tree079_306 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_55,tree079_305,tree079_57,tree079_57]
def tree079_307 : CoverTree := CoverTree.split [tree079_22,tree079_306,tree079_66,tree079_71,tree079_16,tree079_16]
def tree079_308 : CoverTree := CoverTree.reject 315
def tree079_309 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_308,tree079_15,tree079_34,tree079_12]
def tree079_310 : CoverTree := CoverTree.split [tree079_29,tree079_73,tree079_309,tree079_16,tree079_16,tree079_16]
def tree079_311 : CoverTree := CoverTree.split [tree079_273,tree079_282,tree079_300,tree079_304,tree079_307,tree079_310]
def tree079_312 : CoverTree := CoverTree.reject 61
def tree079_313 : CoverTree := CoverTree.reject 55
def tree079_314 : CoverTree := CoverTree.reject 53
def tree079_315 : CoverTree := CoverTree.reject 54
def tree079_316 : CoverTree := CoverTree.reject 179
def tree079_317 : CoverTree := CoverTree.reject 119
def tree079_318 : CoverTree := CoverTree.reject 126
def tree079_319 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_195,tree079_316,tree079_317,tree079_318]
def tree079_320 : CoverTree := CoverTree.reject 188
def tree079_321 : CoverTree := CoverTree.split [tree079_312,tree079_313,tree079_314,tree079_315,tree079_319,tree079_320]
def tree079_322 : CoverTree := CoverTree.reject 217
def tree079_323 : CoverTree := CoverTree.reject 269
def tree079_324 : CoverTree := CoverTree.reject 144
def tree079_325 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_195,tree079_323,tree079_324,tree079_199]
def tree079_326 : CoverTree := CoverTree.reject 270
def tree079_327 : CoverTree := CoverTree.reject 5
def tree079_328 : CoverTree := CoverTree.reject 20
def tree079_329 : CoverTree := CoverTree.split [tree079_327,tree079_327,tree079_327,tree079_327,tree079_328,tree079_12]
def tree079_330 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_195,tree079_326,tree079_329,tree079_199]
def tree079_331 : CoverTree := CoverTree.reject 274
def tree079_332 : CoverTree := CoverTree.split [tree079_327,tree079_327,tree079_327,tree079_327,tree079_331,tree079_12]
def tree079_333 : CoverTree := CoverTree.split [tree079_327,tree079_327,tree079_327,tree079_327,tree079_12,tree079_12]
def tree079_334 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_195,tree079_332,tree079_333,tree079_199]
def tree079_335 : CoverTree := CoverTree.reject 123
def tree079_336 : CoverTree := CoverTree.split [tree079_14,tree079_198,tree079_335,tree079_12,tree079_12,tree079_12]
def tree079_337 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_195,tree079_336,tree079_199,tree079_199]
def tree079_338 : CoverTree := CoverTree.split [tree079_234,tree079_322,tree079_325,tree079_330,tree079_334,tree079_337]
def tree079_339 : CoverTree := CoverTree.reject 271
def tree079_340 : CoverTree := CoverTree.reject 57
def tree079_341 : CoverTree := CoverTree.reject 58
def tree079_342 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_339,tree079_340,tree079_341,tree079_57]
def tree079_343 : CoverTree := CoverTree.reject 272
def tree079_344 : CoverTree := CoverTree.reject 34
def tree079_345 : CoverTree := CoverTree.reject 136
def tree079_346 : CoverTree := CoverTree.reject 137
def tree079_347 : CoverTree := CoverTree.reject 138
def tree079_348 : CoverTree := CoverTree.split [tree079_47,tree079_345,tree079_346,tree079_347,tree079_12,tree079_12]
def tree079_349 : CoverTree := CoverTree.reject 101
def tree079_350 : CoverTree := CoverTree.reject 102
def tree079_351 : CoverTree := CoverTree.split [tree079_349,tree079_350,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_352 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_343,tree079_344,tree079_348,tree079_351]
def tree079_353 : CoverTree := CoverTree.reject 273
def tree079_354 : CoverTree := CoverTree.reject 180
def tree079_355 : CoverTree := CoverTree.reject 181
def tree079_356 : CoverTree := CoverTree.split [tree079_14,tree079_354,tree079_355,tree079_12,tree079_12,tree079_12]
def tree079_357 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_353,tree079_356,tree079_288,tree079_290]
def tree079_358 : CoverTree := CoverTree.reject 52
def tree079_359 : CoverTree := CoverTree.split [tree079_11,tree079_40,tree079_358,tree079_358,tree079_358,tree079_12]
def tree079_360 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_359,tree079_293,tree079_295,tree079_12]
def tree079_361 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_13,tree079_15,tree079_254,tree079_12]
def tree079_362 : CoverTree := CoverTree.split [tree079_243,tree079_342,tree079_352,tree079_357,tree079_360,tree079_361]
def tree079_363 : CoverTree := CoverTree.reject 44
def tree079_364 : CoverTree := CoverTree.reject 45
def tree079_365 : CoverTree := CoverTree.split [tree079_10,tree079_10,tree079_363,tree079_364,tree079_57,tree079_57]
def tree079_366 : CoverTree := CoverTree.split [tree079_5,tree079_365,tree079_152,tree079_49,tree079_53,tree079_16]
def tree079_367 : CoverTree := CoverTree.split [tree079_321,tree079_338,tree079_362,tree079_366,tree079_72,tree079_74]
def tree079_368 : CoverTree := CoverTree.split [tree079_165,tree079_190,tree079_232,tree079_272,tree079_311,tree079_367]
def tree079_369 : CoverTree := CoverTree.reject 27
def tree079_370 : CoverTree := CoverTree.reject 197
def tree079_371 : CoverTree := CoverTree.reject 152
def tree079_372 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_344,tree079_370,tree079_371]
def tree079_373 : CoverTree := CoverTree.reject 218
def tree079_374 : CoverTree := CoverTree.reject 167
def tree079_375 : CoverTree := CoverTree.reject 16
def tree079_376 : CoverTree := CoverTree.reject 250
def tree079_377 : CoverTree := CoverTree.reject 251
def tree079_378 : CoverTree := CoverTree.reject 252
def tree079_379 : CoverTree := CoverTree.reject 338
def tree079_380 : CoverTree := CoverTree.split [tree079_12,tree079_379,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_381 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_376,tree079_377,tree079_378,tree079_380]
def tree079_382 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_372,tree079_373,tree079_374,tree079_381]
def tree079_383 : CoverTree := CoverTree.reject 209
def tree079_384 : CoverTree := CoverTree.reject 133
def tree079_385 : CoverTree := CoverTree.reject 111
def tree079_386 : CoverTree := CoverTree.reject 253
def tree079_387 : CoverTree := CoverTree.reject 254
def tree079_388 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_386,tree079_387,tree079_12,tree079_12]
def tree079_389 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_383,tree079_384,tree079_385,tree079_388]
def tree079_390 : CoverTree := CoverTree.reject 117
def tree079_391 : CoverTree := CoverTree.reject 10
def tree079_392 : CoverTree := CoverTree.reject 153
def tree079_393 : CoverTree := CoverTree.reject 255
def tree079_394 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_392,tree079_393,tree079_70,tree079_12]
def tree079_395 : CoverTree := CoverTree.reject 139
def tree079_396 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_395,tree079_15,tree079_12,tree079_12]
def tree079_397 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_398 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_390,tree079_394,tree079_396,tree079_397]
def tree079_399 : CoverTree := CoverTree.reject 256
def tree079_400 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_182,tree079_399,tree079_34,tree079_12]
def tree079_401 : CoverTree := CoverTree.reject 257
def tree079_402 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_401,tree079_15,tree079_12,tree079_12]
def tree079_403 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_85,tree079_15,tree079_12,tree079_12]
def tree079_404 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_400,tree079_402,tree079_397,tree079_403]
def tree079_405 : CoverTree := CoverTree.split [tree079_166,tree079_166,tree079_382,tree079_389,tree079_398,tree079_404]
def tree079_406 : CoverTree := CoverTree.reject 283
def tree079_407 : CoverTree := CoverTree.reject 284
def tree079_408 : CoverTree := CoverTree.reject 316
def tree079_409 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_196,tree079_408,tree079_199]
def tree079_410 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_192,tree079_406,tree079_407,tree079_409]
def tree079_411 : CoverTree := CoverTree.reject 285
def tree079_412 : CoverTree := CoverTree.reject 189
def tree079_413 : CoverTree := CoverTree.reject 32
def tree079_414 : CoverTree := CoverTree.reject 258
def tree079_415 : CoverTree := CoverTree.reject 259
def tree079_416 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_414,tree079_415,tree079_254,tree079_209]
def tree079_417 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_411,tree079_412,tree079_296,tree079_416]
def tree079_418 : CoverTree := CoverTree.reject 161
def tree079_419 : CoverTree := CoverTree.reject 198
def tree079_420 : CoverTree := CoverTree.reject 173
def tree079_421 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_419,tree079_420,tree079_48,tree079_12]
def tree079_422 : CoverTree := CoverTree.reject 317
def tree079_423 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_422,tree079_52,tree079_48,tree079_12]
def tree079_424 : CoverTree := CoverTree.reject 82
def tree079_425 : CoverTree := CoverTree.reject 174
def tree079_426 : CoverTree := CoverTree.reject 260
def tree079_427 : CoverTree := CoverTree.reject 225
def tree079_428 : CoverTree := CoverTree.split [tree079_14,tree079_427,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_429 : CoverTree := CoverTree.split [tree079_424,tree079_425,tree079_426,tree079_428,tree079_12,tree079_12]
def tree079_430 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_418,tree079_421,tree079_423,tree079_429]
def tree079_431 : CoverTree := CoverTree.reject 175
def tree079_432 : CoverTree := CoverTree.reject 318
def tree079_433 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_431,tree079_432,tree079_65,tree079_12]
def tree079_434 : CoverTree := CoverTree.reject 261
def tree079_435 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_220,tree079_434,tree079_70,tree079_12]
def tree079_436 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_437 : CoverTree := CoverTree.reject 6
def tree079_438 : CoverTree := CoverTree.reject 37
def tree079_439 : CoverTree := CoverTree.reject 30
def tree079_440 : CoverTree := CoverTree.split [tree079_437,tree079_437,tree079_438,tree079_439,tree079_12,tree079_12]
def tree079_441 : CoverTree := CoverTree.split [tree079_437,tree079_437,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_442 : CoverTree := CoverTree.split [tree079_440,tree079_441,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_443 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_433,tree079_435,tree079_436,tree079_442]
def tree079_444 : CoverTree := CoverTree.reject 59
def tree079_445 : CoverTree := CoverTree.reject 351
def tree079_446 : CoverTree := CoverTree.split [tree079_444,tree079_445,tree079_32,tree079_15,tree079_34,tree079_12]
def tree079_447 : CoverTree := CoverTree.reject 60
def tree079_448 : CoverTree := CoverTree.reject 319
def tree079_449 : CoverTree := CoverTree.reject 262
def tree079_450 : CoverTree := CoverTree.split [tree079_447,tree079_448,tree079_449,tree079_15,tree079_12,tree079_12]
def tree079_451 : CoverTree := CoverTree.reject 332
def tree079_452 : CoverTree := CoverTree.split [tree079_451,tree079_441,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_453 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_446,tree079_450,tree079_452,tree079_442]
def tree079_454 : CoverTree := CoverTree.split [tree079_191,tree079_410,tree079_417,tree079_430,tree079_443,tree079_453]
def tree079_455 : CoverTree := CoverTree.reject 286
def tree079_456 : CoverTree := CoverTree.reject 219
def tree079_457 : CoverTree := CoverTree.reject 210
def tree079_458 : CoverTree := CoverTree.reject 352
def tree079_459 : CoverTree := CoverTree.reject 320
def tree079_460 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_458,tree079_459,tree079_199]
def tree079_461 : CoverTree := CoverTree.split [tree079_234,tree079_235,tree079_455,tree079_456,tree079_457,tree079_460]
def tree079_462 : CoverTree := CoverTree.reject 360
def tree079_463 : CoverTree := CoverTree.reject 211
def tree079_464 : CoverTree := CoverTree.reject 96
def tree079_465 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_464,tree079_288,tree079_290]
def tree079_466 : CoverTree := CoverTree.reject 263
def tree079_467 : CoverTree := CoverTree.reject 342
def tree079_468 : CoverTree := CoverTree.split [tree079_14,tree079_467,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_469 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_466,tree079_468,tree079_254,tree079_12]
def tree079_470 : CoverTree := CoverTree.split [tree079_243,tree079_462,tree079_463,tree079_465,tree079_296,tree079_469]
def tree079_471 : CoverTree := CoverTree.reject 212
def tree079_472 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_145,tree079_258,tree079_151,tree079_12]
def tree079_473 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_43,tree079_46,tree079_48,tree079_12]
def tree079_474 : CoverTree := CoverTree.reject 321
def tree079_475 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_474,tree079_52,tree079_48,tree079_12]
def tree079_476 : CoverTree := CoverTree.reject 150
def tree079_477 : CoverTree := CoverTree.split [tree079_437,tree079_437,tree079_476,tree079_12,tree079_12,tree079_12]
def tree079_478 : CoverTree := CoverTree.split [tree079_424,tree079_477,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_479 : CoverTree := CoverTree.split [tree079_5,tree079_471,tree079_472,tree079_473,tree079_475,tree079_478]
def tree079_480 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_18,tree079_19,tree079_20,tree079_21]
def tree079_481 : CoverTree := CoverTree.reject 353
def tree079_482 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_55,tree079_481,tree079_57,tree079_57]
def tree079_483 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_264,tree079_63,tree079_65,tree079_12]
def tree079_484 : CoverTree := CoverTree.reject 322
def tree079_485 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_484,tree079_15,tree079_70,tree079_12]
def tree079_486 : CoverTree := CoverTree.split [tree079_480,tree079_482,tree079_483,tree079_485,tree079_436,tree079_442]
def tree079_487 : CoverTree := CoverTree.reject 81
def tree079_488 : CoverTree := CoverTree.reject 56
def tree079_489 : CoverTree := CoverTree.split [tree079_487,tree079_488,tree079_18,tree079_19,tree079_27,tree079_28]
def tree079_490 : CoverTree := CoverTree.reject 67
def tree079_491 : CoverTree := CoverTree.reject 333
def tree079_492 : CoverTree := CoverTree.reject 297
def tree079_493 : CoverTree := CoverTree.split [tree079_56,tree079_56,tree079_56,tree079_492,tree079_12,tree079_12]
def tree079_494 : CoverTree := CoverTree.split [tree079_490,tree079_491,tree079_493,tree079_57,tree079_57,tree079_57]
def tree079_495 : CoverTree := CoverTree.reject 135
def tree079_496 : CoverTree := CoverTree.split [tree079_437,tree079_437,tree079_495,tree079_12,tree079_12,tree079_12]
def tree079_497 : CoverTree := CoverTree.split [tree079_444,tree079_496,tree079_32,tree079_15,tree079_34,tree079_12]
def tree079_498 : CoverTree := CoverTree.split [tree079_447,tree079_441,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_499 : CoverTree := CoverTree.reject 151
def tree079_500 : CoverTree := CoverTree.split [tree079_437,tree079_437,tree079_438,tree079_439,tree079_12,tree079_499]
def tree079_501 : CoverTree := CoverTree.split [tree079_500,tree079_441,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_502 : CoverTree := CoverTree.split [tree079_489,tree079_494,tree079_497,tree079_498,tree079_501,tree079_442]
def tree079_503 : CoverTree := CoverTree.split [tree079_233,tree079_461,tree079_470,tree079_479,tree079_486,tree079_502]
def tree079_504 : CoverTree := CoverTree.reject 287
def tree079_505 : CoverTree := CoverTree.reject 190
def tree079_506 : CoverTree := CoverTree.split [tree079_312,tree079_313,tree079_314,tree079_315,tree079_504,tree079_505]
def tree079_507 : CoverTree := CoverTree.reject 288
def tree079_508 : CoverTree := CoverTree.reject 39
def tree079_509 : CoverTree := CoverTree.reject 378
def tree079_510 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_508,tree079_509,tree079_199]
def tree079_511 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_508,tree079_333,tree079_199]
def tree079_512 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_336,tree079_199,tree079_199]
def tree079_513 : CoverTree := CoverTree.split [tree079_234,tree079_274,tree079_507,tree079_510,tree079_511,tree079_512]
def tree079_514 : CoverTree := CoverTree.reject 336
def tree079_515 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_344,tree079_348,tree079_351]
def tree079_516 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_356,tree079_288,tree079_290]
def tree079_517 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_13,tree079_15,tree079_254,tree079_12]
def tree079_518 : CoverTree := CoverTree.split [tree079_243,tree079_514,tree079_515,tree079_516,tree079_296,tree079_517]
def tree079_519 : CoverTree := CoverTree.reject 35
def tree079_520 : CoverTree := CoverTree.split [tree079_519,tree079_519,tree079_363,tree079_364,tree079_57,tree079_57]
def tree079_521 : CoverTree := CoverTree.split [tree079_519,tree079_519,tree079_145,tree079_149,tree079_151,tree079_12]
def tree079_522 : CoverTree := CoverTree.split [tree079_519,tree079_519,tree079_43,tree079_46,tree079_48,tree079_12]
def tree079_523 : CoverTree := CoverTree.reject 194
def tree079_524 : CoverTree := CoverTree.reject 334
def tree079_525 : CoverTree := CoverTree.split [tree079_523,tree079_524,tree079_50,tree079_52,tree079_48,tree079_12]
def tree079_526 : CoverTree := CoverTree.split [tree079_5,tree079_520,tree079_521,tree079_522,tree079_525,tree079_478]
def tree079_527 : CoverTree := CoverTree.split [tree079_519,tree079_519,tree079_18,tree079_19,tree079_20,tree079_21]
def tree079_528 : CoverTree := CoverTree.split [tree079_519,tree079_519,tree079_55,tree079_57,tree079_57,tree079_57]
def tree079_529 : CoverTree := CoverTree.split [tree079_519,tree079_519,tree079_61,tree079_63,tree079_65,tree079_12]
def tree079_530 : CoverTree := CoverTree.split [tree079_519,tree079_519,tree079_68,tree079_15,tree079_70,tree079_12]
def tree079_531 : CoverTree := CoverTree.reject 145
def tree079_532 : CoverTree := CoverTree.reject 169
def tree079_533 : CoverTree := CoverTree.split [tree079_437,tree079_437,tree079_532,tree079_12,tree079_12,tree079_12]
def tree079_534 : CoverTree := CoverTree.split [tree079_531,tree079_533,tree079_13,tree079_15,tree079_12,tree079_12]
def tree079_535 : CoverTree := CoverTree.split [tree079_527,tree079_528,tree079_529,tree079_530,tree079_534,tree079_442]
def tree079_536 : CoverTree := CoverTree.reject 379
def tree079_537 : CoverTree := CoverTree.split [tree079_490,tree079_536,tree079_57,tree079_57,tree079_57,tree079_57]
def tree079_538 : CoverTree := CoverTree.split [tree079_489,tree079_537,tree079_497,tree079_498,tree079_501,tree079_442]
def tree079_539 : CoverTree := CoverTree.split [tree079_506,tree079_513,tree079_518,tree079_526,tree079_535,tree079_538]
def tree079_540 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_316,tree079_317,tree079_318]
def tree079_541 : CoverTree := CoverTree.reject 191
def tree079_542 : CoverTree := CoverTree.split [tree079_312,tree079_313,tree079_314,tree079_315,tree079_540,tree079_541]
def tree079_543 : CoverTree := CoverTree.reject 220
def tree079_544 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_323,tree079_324,tree079_199]
def tree079_545 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_326,tree079_329,tree079_199]
def tree079_546 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_332,tree079_333,tree079_199]
def tree079_547 : CoverTree := CoverTree.split [tree079_234,tree079_543,tree079_544,tree079_545,tree079_546,tree079_512]
def tree079_548 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_339,tree079_340,tree079_341,tree079_57]
def tree079_549 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_343,tree079_344,tree079_348,tree079_351]
def tree079_550 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_353,tree079_356,tree079_288,tree079_290]
def tree079_551 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_359,tree079_293,tree079_295,tree079_12]
def tree079_552 : CoverTree := CoverTree.split [tree079_243,tree079_548,tree079_549,tree079_550,tree079_551,tree079_517]
def tree079_553 : CoverTree := CoverTree.reject 325
def tree079_554 : CoverTree := CoverTree.split [tree079_490,tree079_553,tree079_363,tree079_364,tree079_57,tree079_57]
def tree079_555 : CoverTree := CoverTree.reject 326
def tree079_556 : CoverTree := CoverTree.split [tree079_444,tree079_555,tree079_145,tree079_149,tree079_151,tree079_12]
def tree079_557 : CoverTree := CoverTree.reject 327
def tree079_558 : CoverTree := CoverTree.split [tree079_447,tree079_557,tree079_43,tree079_46,tree079_48,tree079_12]
def tree079_559 : CoverTree := CoverTree.reject 21
def tree079_560 : CoverTree := CoverTree.split [tree079_437,tree079_437,tree079_559,tree079_559,tree079_559,tree079_12]
def tree079_561 : CoverTree := CoverTree.split [tree079_523,tree079_560,tree079_50,tree079_52,tree079_48,tree079_12]
def tree079_562 : CoverTree := CoverTree.split [tree079_5,tree079_554,tree079_556,tree079_558,tree079_561,tree079_478]
def tree079_563 : CoverTree := CoverTree.split [tree079_487,tree079_488,tree079_18,tree079_19,tree079_20,tree079_21]
def tree079_564 : CoverTree := CoverTree.reject 328
def tree079_565 : CoverTree := CoverTree.split [tree079_490,tree079_564,tree079_55,tree079_57,tree079_57,tree079_57]
def tree079_566 : CoverTree := CoverTree.reject 170
def tree079_567 : CoverTree := CoverTree.split [tree079_444,tree079_566,tree079_61,tree079_63,tree079_65,tree079_12]
def tree079_568 : CoverTree := CoverTree.reject 329
def tree079_569 : CoverTree := CoverTree.split [tree079_437,tree079_437,tree079_532,tree079_568,tree079_12,tree079_12]
def tree079_570 : CoverTree := CoverTree.split [tree079_447,tree079_569,tree079_68,tree079_15,tree079_70,tree079_12]
def tree079_571 : CoverTree := CoverTree.split [tree079_563,tree079_565,tree079_567,tree079_570,tree079_534,tree079_442]
def tree079_572 : CoverTree := CoverTree.reject 142
def tree079_573 : CoverTree := CoverTree.reject 143
def tree079_574 : CoverTree := CoverTree.split [tree079_56,tree079_56,tree079_56,tree079_572,tree079_573,tree079_12]
def tree079_575 : CoverTree := CoverTree.split [tree079_490,tree079_574,tree079_57,tree079_57,tree079_57,tree079_57]
def tree079_576 : CoverTree := CoverTree.split [tree079_489,tree079_575,tree079_497,tree079_498,tree079_501,tree079_442]
def tree079_577 : CoverTree := CoverTree.split [tree079_542,tree079_547,tree079_552,tree079_562,tree079_571,tree079_576]
def tree079_578 : CoverTree := CoverTree.split [tree079_369,tree079_405,tree079_454,tree079_503,tree079_539,tree079_577]
def tree079_579 : CoverTree := CoverTree.reject 15
def tree079_580 : CoverTree := CoverTree.reject 8
def tree079_581 : CoverTree := CoverTree.reject 89
def tree079_582 : CoverTree := CoverTree.reject 164
def tree079_583 : CoverTree := CoverTree.reject 162
def tree079_584 : CoverTree := CoverTree.reject 166
def tree079_585 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_584,tree079_15,tree079_12,tree079_12]
def tree079_586 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_581,tree079_582,tree079_583,tree079_585]
def tree079_587 : CoverTree := CoverTree.reject 98
def tree079_588 : CoverTree := CoverTree.reject 86
def tree079_589 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_587,tree079_588,tree079_397,tree079_397]
def tree079_590 : CoverTree := CoverTree.split [tree079_166,tree079_166,tree079_579,tree079_580,tree079_586,tree079_589]
def tree079_591 : CoverTree := CoverTree.reject 221
def tree079_592 : CoverTree := CoverTree.reject 168
def tree079_593 : CoverTree := CoverTree.reject 264
def tree079_594 : CoverTree := CoverTree.reject 265
def tree079_595 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_593,tree079_594,tree079_254,tree079_380]
def tree079_596 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_372,tree079_591,tree079_592,tree079_595]
def tree079_597 : CoverTree := CoverTree.reject 213
def tree079_598 : CoverTree := CoverTree.reject 134
def tree079_599 : CoverTree := CoverTree.reject 183
def tree079_600 : CoverTree := CoverTree.reject 184
def tree079_601 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_599,tree079_600,tree079_48,tree079_12]
def tree079_602 : CoverTree := CoverTree.reject 362
def tree079_603 : CoverTree := CoverTree.reject 363
def tree079_604 : CoverTree := CoverTree.split [tree079_14,tree079_602,tree079_603,tree079_12,tree079_12,tree079_12]
def tree079_605 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_174,tree079_604,tree079_12,tree079_12]
def tree079_606 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_597,tree079_598,tree079_601,tree079_605]
def tree079_607 : CoverTree := CoverTree.reject 118
def tree079_608 : CoverTree := CoverTree.reject 266
def tree079_609 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_392,tree079_608,tree079_70,tree079_12]
def tree079_610 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_607,tree079_609,tree079_396,tree079_397]
def tree079_611 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_182,tree079_15,tree079_34,tree079_12]
def tree079_612 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_611,tree079_397,tree079_397,tree079_403]
def tree079_613 : CoverTree := CoverTree.split [tree079_166,tree079_166,tree079_596,tree079_606,tree079_610,tree079_612]
def tree079_614 : CoverTree := CoverTree.reject 289
def tree079_615 : CoverTree := CoverTree.reject 290
def tree079_616 : CoverTree := CoverTree.reject 323
def tree079_617 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_196,tree079_616,tree079_199]
def tree079_618 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_192,tree079_614,tree079_615,tree079_617]
def tree079_619 : CoverTree := CoverTree.reject 291
def tree079_620 : CoverTree := CoverTree.reject 94
def tree079_621 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_620,tree079_288,tree079_290]
def tree079_622 : CoverTree := CoverTree.reject 267
def tree079_623 : CoverTree := CoverTree.reject 364
def tree079_624 : CoverTree := CoverTree.split [tree079_14,tree079_623,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_625 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_622,tree079_624,tree079_254,tree079_209]
def tree079_626 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_619,tree079_621,tree079_296,tree079_625]
def tree079_627 : CoverTree := CoverTree.reject 277
def tree079_628 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_145,tree079_627,tree079_151,tree079_12]
def tree079_629 : CoverTree := CoverTree.reject 324
def tree079_630 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_629,tree079_52,tree079_48,tree079_12]
def tree079_631 : CoverTree := CoverTree.split [tree079_424,tree079_425,tree079_13,tree079_428,tree079_12,tree079_12]
def tree079_632 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_628,tree079_421,tree079_630,tree079_631]
def tree079_633 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_431,tree079_63,tree079_65,tree079_12]
def tree079_634 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_220,tree079_15,tree079_70,tree079_12]
def tree079_635 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_633,tree079_634,tree079_436,tree079_442]
def tree079_636 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_497,tree079_498,tree079_452,tree079_442]
def tree079_637 : CoverTree := CoverTree.split [tree079_191,tree079_618,tree079_626,tree079_632,tree079_635,tree079_636]
def tree079_638 : CoverTree := CoverTree.reject 292
def tree079_639 : CoverTree := CoverTree.reject 222
def tree079_640 : CoverTree := CoverTree.split [tree079_234,tree079_235,tree079_638,tree079_639,tree079_511,tree079_512]
def tree079_641 : CoverTree := CoverTree.reject 361
def tree079_642 : CoverTree := CoverTree.reject 214
def tree079_643 : CoverTree := CoverTree.reject 365
def tree079_644 : CoverTree := CoverTree.reject 366
def tree079_645 : CoverTree := CoverTree.split [tree079_11,tree079_643,tree079_644,tree079_12,tree079_12,tree079_12]
def tree079_646 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_645,tree079_468,tree079_254,tree079_12]
def tree079_647 : CoverTree := CoverTree.split [tree079_243,tree079_641,tree079_642,tree079_465,tree079_296,tree079_646]
def tree079_648 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_363,tree079_364,tree079_57,tree079_57]
def tree079_649 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_50,tree079_52,tree079_48,tree079_12]
def tree079_650 : CoverTree := CoverTree.split [tree079_5,tree079_648,tree079_472,tree079_473,tree079_649,tree079_478]
def tree079_651 : CoverTree := CoverTree.reject 354
def tree079_652 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_55,tree079_651,tree079_57,tree079_57]
def tree079_653 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_68,tree079_15,tree079_70,tree079_12]
def tree079_654 : CoverTree := CoverTree.split [tree079_480,tree079_652,tree079_483,tree079_653,tree079_436,tree079_442]
def tree079_655 : CoverTree := CoverTree.split [tree079_233,tree079_640,tree079_647,tree079_650,tree079_654,tree079_502]
def tree079_656 : CoverTree := CoverTree.reject 293
def tree079_657 : CoverTree := CoverTree.reject 192
def tree079_658 : CoverTree := CoverTree.split [tree079_312,tree079_313,tree079_314,tree079_315,tree079_656,tree079_657]
def tree079_659 : CoverTree := CoverTree.reject 294
def tree079_660 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_508,tree079_329,tree079_199]
def tree079_661 : CoverTree := CoverTree.split [tree079_234,tree079_274,tree079_659,tree079_660,tree079_511,tree079_512]
def tree079_662 : CoverTree := CoverTree.reject 337
def tree079_663 : CoverTree := CoverTree.split [tree079_243,tree079_662,tree079_515,tree079_516,tree079_296,tree079_517]
def tree079_664 : CoverTree := CoverTree.split [tree079_658,tree079_661,tree079_663,tree079_526,tree079_535,tree079_576]
def tree079_665 : CoverTree := CoverTree.reject 193
def tree079_666 : CoverTree := CoverTree.split [tree079_312,tree079_313,tree079_314,tree079_315,tree079_540,tree079_665]
def tree079_667 : CoverTree := CoverTree.reject 355
def tree079_668 : CoverTree := CoverTree.reject 356
def tree079_669 : CoverTree := CoverTree.reject 357
def tree079_670 : CoverTree := CoverTree.split [tree079_56,tree079_56,tree079_56,tree079_669,tree079_12,tree079_12]
def tree079_671 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_667,tree079_668,tree079_670]
def tree079_672 : CoverTree := CoverTree.split [tree079_234,tree079_671,tree079_544,tree079_545,tree079_546,tree079_512]
def tree079_673 : CoverTree := CoverTree.split [tree079_666,tree079_672,tree079_552,tree079_562,tree079_571,tree079_576]
def tree079_674 : CoverTree := CoverTree.split [tree079_590,tree079_613,tree079_637,tree079_655,tree079_664,tree079_673]
def tree079_675 : CoverTree := CoverTree.reject 165
def tree079_676 : CoverTree := CoverTree.reject 163
def tree079_677 : CoverTree := CoverTree.reject 268
def tree079_678 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_584,tree079_677,tree079_12,tree079_12]
def tree079_679 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_581,tree079_675,tree079_676,tree079_678]
def tree079_680 : CoverTree := CoverTree.reject 99
def tree079_681 : CoverTree := CoverTree.reject 87
def tree079_682 : CoverTree := CoverTree.reject 88
def tree079_683 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_680,tree079_681,tree079_682,tree079_397]
def tree079_684 : CoverTree := CoverTree.split [tree079_166,tree079_166,tree079_579,tree079_580,tree079_679,tree079_683]
def tree079_685 : CoverTree := CoverTree.reject 63
def tree079_686 : CoverTree := CoverTree.reject 172
def tree079_687 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_685,tree079_686,tree079_290]
def tree079_688 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_685,tree079_295,tree079_12]
def tree079_689 : CoverTree := CoverTree.reject 371
def tree079_690 : CoverTree := CoverTree.reject 372
def tree079_691 : CoverTree := CoverTree.reject 373
def tree079_692 : CoverTree := CoverTree.split [tree079_11,tree079_689,tree079_690,tree079_691,tree079_12,tree079_12]
def tree079_693 : CoverTree := CoverTree.reject 374
def tree079_694 : CoverTree := CoverTree.split [tree079_14,tree079_693,tree079_12,tree079_12,tree079_12,tree079_12]
def tree079_695 : CoverTree := CoverTree.split [tree079_375,tree079_375,tree079_692,tree079_694,tree079_254,tree079_380]
def tree079_696 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_372,tree079_687,tree079_688,tree079_695]
def tree079_697 : CoverTree := CoverTree.reject 182
def tree079_698 : CoverTree := CoverTree.reject 125
def tree079_699 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_145,tree079_697,tree079_698,tree079_12]
def tree079_700 : CoverTree := CoverTree.reject 358
def tree079_701 : CoverTree := CoverTree.reject 330
def tree079_702 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_700,tree079_701,tree079_48,tree079_12]
def tree079_703 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_699,tree079_702,tree079_601,tree079_605]
def tree079_704 : CoverTree := CoverTree.reject 331
def tree079_705 : CoverTree := CoverTree.reject 275
def tree079_706 : CoverTree := CoverTree.reject 276
def tree079_707 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_704,tree079_705,tree079_706,tree079_12]
def tree079_708 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_392,tree079_15,tree079_70,tree079_12]
def tree079_709 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_707,tree079_708,tree079_396,tree079_397]
def tree079_710 : CoverTree := CoverTree.split [tree079_166,tree079_166,tree079_696,tree079_703,tree079_709,tree079_612]
def tree079_711 : CoverTree := CoverTree.reject 141
def tree079_712 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_508,tree079_711,tree079_199]
def tree079_713 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_196,tree079_199,tree079_199]
def tree079_714 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_192,tree079_712,tree079_712,tree079_713]
def tree079_715 : CoverTree := CoverTree.reject 93
def tree079_716 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_344,tree079_715,tree079_351]
def tree079_717 : CoverTree := CoverTree.reject 375
def tree079_718 : CoverTree := CoverTree.reject 376
def tree079_719 : CoverTree := CoverTree.reject 377
def tree079_720 : CoverTree := CoverTree.split [tree079_11,tree079_717,tree079_718,tree079_719,tree079_12,tree079_12]
def tree079_721 : CoverTree := CoverTree.split [tree079_413,tree079_413,tree079_720,tree079_624,tree079_254,tree079_209]
def tree079_722 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_716,tree079_621,tree079_296,tree079_721]
def tree079_723 : CoverTree := CoverTree.split [tree079_80,tree079_80,tree079_628,tree079_421,tree079_649,tree079_631]
def tree079_724 : CoverTree := CoverTree.split [tree079_191,tree079_714,tree079_722,tree079_723,tree079_635,tree079_636]
def tree079_725 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_508,tree079_324,tree079_199]
def tree079_726 : CoverTree := CoverTree.reject 370
def tree079_727 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_508,tree079_726,tree079_199]
def tree079_728 : CoverTree := CoverTree.split [tree079_234,tree079_235,tree079_725,tree079_727,tree079_511,tree079_512]
def tree079_729 : CoverTree := CoverTree.reject 296
def tree079_730 : CoverTree := CoverTree.split [tree079_56,tree079_56,tree079_56,tree079_729,tree079_12,tree079_12]
def tree079_731 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_340,tree079_341,tree079_730]
def tree079_732 : CoverTree := CoverTree.split [tree079_243,tree079_731,tree079_515,tree079_465,tree079_296,tree079_646]
def tree079_733 : CoverTree := CoverTree.split [tree079_391,tree079_391,tree079_55,tree079_57,tree079_57,tree079_57]
def tree079_734 : CoverTree := CoverTree.split [tree079_480,tree079_733,tree079_483,tree079_653,tree079_436,tree079_442]
def tree079_735 : CoverTree := CoverTree.split [tree079_233,tree079_728,tree079_732,tree079_650,tree079_734,tree079_502]
def tree079_736 : CoverTree := CoverTree.reject 369
def tree079_737 : CoverTree := CoverTree.split [tree079_198,tree079_198,tree079_736,tree079_12,tree079_12,tree079_12]
def tree079_738 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_508,tree079_317,tree079_737]
def tree079_739 : CoverTree := CoverTree.reject 62
def tree079_740 : CoverTree := CoverTree.split [tree079_195,tree079_195,tree079_195,tree079_739,tree079_199,tree079_199]
def tree079_741 : CoverTree := CoverTree.split [tree079_312,tree079_313,tree079_314,tree079_315,tree079_738,tree079_740]
def tree079_742 : CoverTree := CoverTree.split [tree079_234,tree079_274,tree079_725,tree079_660,tree079_511,tree079_512]
def tree079_743 : CoverTree := CoverTree.split [tree079_247,tree079_247,tree079_247,tree079_340,tree079_341,tree079_57]
def tree079_744 : CoverTree := CoverTree.split [tree079_243,tree079_743,tree079_515,tree079_516,tree079_296,tree079_517]
def tree079_745 : CoverTree := CoverTree.split [tree079_741,tree079_742,tree079_744,tree079_526,tree079_535,tree079_576]
def tree079_746 : CoverTree := CoverTree.split [tree079_312,tree079_313,tree079_314,tree079_315,tree079_540,tree079_740]
def tree079_747 : CoverTree := CoverTree.split [tree079_746,tree079_672,tree079_552,tree079_562,tree079_571,tree079_576]
def tree079_748 : CoverTree := CoverTree.split [tree079_684,tree079_710,tree079_724,tree079_735,tree079_745,tree079_747]
def tree079_749 : CoverTree := CoverTree.split [tree079_76,tree079_164,tree079_368,tree079_578,tree079_674,tree079_748]
def tree079 : CoverTree := tree079_749

end Snake9.Shared89
