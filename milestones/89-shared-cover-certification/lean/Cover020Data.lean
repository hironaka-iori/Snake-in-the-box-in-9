import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes020 : List Box := [
[(1,6),(1,3),(1,6),(1,3),(1,6),(1,6)],
[(1,2),(1,6),(1,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,3),(1,6)],
[(1,6),(1,3),(1,6),(1,6),(1,2),(1,6)],
[(1,2),(1,6),(1,6),(1,3),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,5),(1,5),(1,4)],
[(1,6),(1,6),(1,4),(1,5),(1,2),(1,5)],
[(1,2),(1,4),(1,5),(1,5),(1,6),(1,6)],
[(1,3),(1,5),(1,3),(1,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,5),(1,5),(1,4),(1,2),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,3),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,4),(1,5),(1,2),(1,5),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,5),(1,3),(1,5)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,5),(1,5),(1,2),(1,3)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
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
[(1,1),(5,5),(5,5),(1,6),(1,6),(1,6)],
[(4,4),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(1,6),(1,6),(1,6)],
[(5,5),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
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
[(1,6),(1,6),(4,4),(6,6),(1,1),(1,6)],
[(1,6),(1,6),(5,5),(5,5),(1,1),(1,6)],
[(3,3),(4,4),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,5),(1,2),(1,5),(1,4),(1,6)],
[(2,2),(4,4),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(6,6),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(6,6),(1,1),(1,6)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
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
[(1,6),(2,2),(5,5),(5,5),(3,3),(1,6)],
[(1,6),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(1,6),(4,4),(5,5),(3,3),(3,3),(1,6)],
[(1,6),(1,6),(3,3),(6,6),(5,5),(1,1)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(2,2)],
[(1,6),(1,6),(3,3),(5,5),(5,5),(2,2)],
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
[(1,6),(1,6),(1,6),(2,2),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(3,3)],
[(1,6),(2,2),(2,2),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(1,1)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(3,3)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(4,4)],
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
[(1,6),(1,6),(3,3),(5,5),(1,1),(1,6)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(1,6)],
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

def root020 : Nat := 2418

def tree020_0 : CoverTree := CoverTree.reject 35
def tree020_1 : CoverTree := CoverTree.reject 32
def tree020_2 : CoverTree := CoverTree.reject 33
def tree020_3 : CoverTree := CoverTree.reject 21
def tree020_4 : CoverTree := CoverTree.reject 1
def tree020_5 : CoverTree := CoverTree.reject 66
def tree020_6 : CoverTree := CoverTree.reject 60
def tree020_7 : CoverTree := CoverTree.reject 4
def tree020_8 : CoverTree := CoverTree.reject 64
def tree020_9 : CoverTree := CoverTree.reject 28
def tree020_10 : CoverTree := CoverTree.reject 110
def tree020_11 : CoverTree := CoverTree.reject 208
def tree020_12 : CoverTree := CoverTree.accept
def tree020_13 : CoverTree := CoverTree.split [tree020_9,tree020_10,tree020_11,tree020_12,tree020_12,tree020_12]
def tree020_14 : CoverTree := CoverTree.reject 11
def tree020_15 : CoverTree := CoverTree.split [tree020_14,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_16 : CoverTree := CoverTree.reject 9
def tree020_17 : CoverTree := CoverTree.split [tree020_16,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_18 : CoverTree := CoverTree.split [tree020_8,tree020_13,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_19 : CoverTree := CoverTree.reject 25
def tree020_20 : CoverTree := CoverTree.reject 26
def tree020_21 : CoverTree := CoverTree.reject 27
def tree020_22 : CoverTree := CoverTree.reject 20
def tree020_23 : CoverTree := CoverTree.reject 119
def tree020_24 : CoverTree := CoverTree.split [tree020_19,tree020_20,tree020_21,tree020_22,tree020_12,tree020_23]
def tree020_25 : CoverTree := CoverTree.reject 111
def tree020_26 : CoverTree := CoverTree.split [tree020_9,tree020_25,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_27 : CoverTree := CoverTree.split [tree020_24,tree020_26,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_28 : CoverTree := CoverTree.split [tree020_19,tree020_20,tree020_21,tree020_22,tree020_12,tree020_12]
def tree020_29 : CoverTree := CoverTree.split [tree020_9,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_30 : CoverTree := CoverTree.split [tree020_28,tree020_29,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_31 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_18,tree020_27,tree020_30]
def tree020_32 : CoverTree := CoverTree.split [tree020_4,tree020_4,tree020_4,tree020_5,tree020_6,tree020_31]
def tree020_33 : CoverTree := CoverTree.reject 39
def tree020_34 : CoverTree := CoverTree.reject 18
def tree020_35 : CoverTree := CoverTree.reject 203
def tree020_36 : CoverTree := CoverTree.split [tree020_34,tree020_34,tree020_34,tree020_35,tree020_12,tree020_12]
def tree020_37 : CoverTree := CoverTree.reject 104
def tree020_38 : CoverTree := CoverTree.split [tree020_14,tree020_37,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_39 : CoverTree := CoverTree.reject 105
def tree020_40 : CoverTree := CoverTree.split [tree020_39,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_41 : CoverTree := CoverTree.split [tree020_8,tree020_36,tree020_38,tree020_17,tree020_40,tree020_12]
def tree020_42 : CoverTree := CoverTree.reject 81
def tree020_43 : CoverTree := CoverTree.split [tree020_34,tree020_34,tree020_34,tree020_12,tree020_12,tree020_12]
def tree020_44 : CoverTree := CoverTree.split [tree020_42,tree020_43,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_45 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_41,tree020_44,tree020_30]
def tree020_46 : CoverTree := CoverTree.split [tree020_9,tree020_10,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_47 : CoverTree := CoverTree.split [tree020_8,tree020_46,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_48 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_47,tree020_27,tree020_30]
def tree020_49 : CoverTree := CoverTree.split [tree020_4,tree020_4,tree020_4,tree020_33,tree020_45,tree020_48]
def tree020_50 : CoverTree := CoverTree.split [tree020_0,tree020_1,tree020_2,tree020_3,tree020_32,tree020_49]
def tree020_51 : CoverTree := CoverTree.reject 36
def tree020_52 : CoverTree := CoverTree.reject 91
def tree020_53 : CoverTree := CoverTree.reject 92
def tree020_54 : CoverTree := CoverTree.reject 0
def tree020_55 : CoverTree := CoverTree.reject 97
def tree020_56 : CoverTree := CoverTree.reject 3
def tree020_57 : CoverTree := CoverTree.reject 271
def tree020_58 : CoverTree := CoverTree.reject 213
def tree020_59 : CoverTree := CoverTree.split [tree020_16,tree020_58,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_60 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_57,tree020_59,tree020_12,tree020_12]
def tree020_61 : CoverTree := CoverTree.reject 214
def tree020_62 : CoverTree := CoverTree.reject 215
def tree020_63 : CoverTree := CoverTree.split [tree020_14,tree020_61,tree020_62,tree020_12,tree020_12,tree020_12]
def tree020_64 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_63,tree020_17,tree020_12,tree020_12]
def tree020_65 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_55,tree020_60,tree020_64]
def tree020_66 : CoverTree := CoverTree.split [tree020_4,tree020_4,tree020_4,tree020_52,tree020_53,tree020_65]
def tree020_67 : CoverTree := CoverTree.reject 93
def tree020_68 : CoverTree := CoverTree.reject 94
def tree020_69 : CoverTree := CoverTree.reject 216
def tree020_70 : CoverTree := CoverTree.reject 217
def tree020_71 : CoverTree := CoverTree.reject 218
def tree020_72 : CoverTree := CoverTree.split [tree020_14,tree020_69,tree020_70,tree020_71,tree020_12,tree020_12]
def tree020_73 : CoverTree := CoverTree.reject 219
def tree020_74 : CoverTree := CoverTree.split [tree020_16,tree020_73,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_75 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_72,tree020_74,tree020_12,tree020_12]
def tree020_76 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_77 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_75,tree020_76,tree020_76]
def tree020_78 : CoverTree := CoverTree.split [tree020_4,tree020_4,tree020_4,tree020_67,tree020_68,tree020_77]
def tree020_79 : CoverTree := CoverTree.reject 84
def tree020_80 : CoverTree := CoverTree.reject 7
def tree020_81 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_80,tree020_80,tree020_30]
def tree020_82 : CoverTree := CoverTree.reject 220
def tree020_83 : CoverTree := CoverTree.reject 221
def tree020_84 : CoverTree := CoverTree.split [tree020_9,tree020_10,tree020_82,tree020_83,tree020_12,tree020_12]
def tree020_85 : CoverTree := CoverTree.reject 222
def tree020_86 : CoverTree := CoverTree.split [tree020_14,tree020_85,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_87 : CoverTree := CoverTree.reject 223
def tree020_88 : CoverTree := CoverTree.split [tree020_16,tree020_87,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_89 : CoverTree := CoverTree.split [tree020_8,tree020_84,tree020_86,tree020_88,tree020_12,tree020_12]
def tree020_90 : CoverTree := CoverTree.reject 224
def tree020_91 : CoverTree := CoverTree.split [tree020_28,tree020_90,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_92 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_89,tree020_27,tree020_91]
def tree020_93 : CoverTree := CoverTree.split [tree020_4,tree020_4,tree020_4,tree020_79,tree020_81,tree020_92]
def tree020_94 : CoverTree := CoverTree.reject 37
def tree020_95 : CoverTree := CoverTree.reject 98
def tree020_96 : CoverTree := CoverTree.reject 80
def tree020_97 : CoverTree := CoverTree.reject 127
def tree020_98 : CoverTree := CoverTree.reject 128
def tree020_99 : CoverTree := CoverTree.split [tree020_9,tree020_97,tree020_98,tree020_12,tree020_12,tree020_12]
def tree020_100 : CoverTree := CoverTree.split [tree020_96,tree020_99,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_101 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_94,tree020_95,tree020_100]
def tree020_102 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_94,tree020_44,tree020_30]
def tree020_103 : CoverTree := CoverTree.split [tree020_4,tree020_4,tree020_4,tree020_101,tree020_102,tree020_31]
def tree020_104 : CoverTree := CoverTree.reject 209
def tree020_105 : CoverTree := CoverTree.reject 49
def tree020_106 : CoverTree := CoverTree.reject 115
def tree020_107 : CoverTree := CoverTree.reject 116
def tree020_108 : CoverTree := CoverTree.split [tree020_14,tree020_105,tree020_106,tree020_107,tree020_12,tree020_12]
def tree020_109 : CoverTree := CoverTree.reject 117
def tree020_110 : CoverTree := CoverTree.reject 118
def tree020_111 : CoverTree := CoverTree.split [tree020_16,tree020_109,tree020_110,tree020_12,tree020_12,tree020_12]
def tree020_112 : CoverTree := CoverTree.reject 24
def tree020_113 : CoverTree := CoverTree.split [tree020_112,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_114 : CoverTree := CoverTree.split [tree020_8,tree020_104,tree020_108,tree020_111,tree020_113,tree020_12]
def tree020_115 : CoverTree := CoverTree.reject 169
def tree020_116 : CoverTree := CoverTree.reject 6
def tree020_117 : CoverTree := CoverTree.split [tree020_116,tree020_116,tree020_116,tree020_116,tree020_116,tree020_12]
def tree020_118 : CoverTree := CoverTree.split [tree020_14,tree020_105,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_119 : CoverTree := CoverTree.reject 109
def tree020_120 : CoverTree := CoverTree.split [tree020_16,tree020_119,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_121 : CoverTree := CoverTree.split [tree020_115,tree020_117,tree020_118,tree020_120,tree020_113,tree020_12]
def tree020_122 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_114,tree020_121,tree020_100]
def tree020_123 : CoverTree := CoverTree.reject 272
def tree020_124 : CoverTree := CoverTree.split [tree020_8,tree020_123,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_125 : CoverTree := CoverTree.split [tree020_7,tree020_7,tree020_7,tree020_124,tree020_27,tree020_30]
def tree020_126 : CoverTree := CoverTree.split [tree020_4,tree020_4,tree020_4,tree020_122,tree020_45,tree020_125]
def tree020_127 : CoverTree := CoverTree.split [tree020_51,tree020_66,tree020_78,tree020_93,tree020_103,tree020_126]
def tree020_128 : CoverTree := CoverTree.reject 22
def tree020_129 : CoverTree := CoverTree.reject 13
def tree020_130 : CoverTree := CoverTree.reject 95
def tree020_131 : CoverTree := CoverTree.reject 55
def tree020_132 : CoverTree := CoverTree.reject 50
def tree020_133 : CoverTree := CoverTree.reject 244
def tree020_134 : CoverTree := CoverTree.reject 245
def tree020_135 : CoverTree := CoverTree.reject 246
def tree020_136 : CoverTree := CoverTree.split [tree020_14,tree020_133,tree020_134,tree020_135,tree020_12,tree020_12]
def tree020_137 : CoverTree := CoverTree.reject 247
def tree020_138 : CoverTree := CoverTree.reject 248
def tree020_139 : CoverTree := CoverTree.split [tree020_16,tree020_137,tree020_138,tree020_12,tree020_12,tree020_12]
def tree020_140 : CoverTree := CoverTree.reject 249
def tree020_141 : CoverTree := CoverTree.reject 250
def tree020_142 : CoverTree := CoverTree.split [tree020_140,tree020_141,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_143 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_136,tree020_139,tree020_142,tree020_12]
def tree020_144 : CoverTree := CoverTree.reject 212
def tree020_145 : CoverTree := CoverTree.split [tree020_14,tree020_12,tree020_12,tree020_144,tree020_12,tree020_12]
def tree020_146 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_145,tree020_59,tree020_12,tree020_12]
def tree020_147 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_143,tree020_146,tree020_64]
def tree020_148 : CoverTree := CoverTree.split [tree020_129,tree020_129,tree020_130,tree020_131,tree020_132,tree020_147]
def tree020_149 : CoverTree := CoverTree.reject 96
def tree020_150 : CoverTree := CoverTree.reject 56
def tree020_151 : CoverTree := CoverTree.reject 99
def tree020_152 : CoverTree := CoverTree.reject 251
def tree020_153 : CoverTree := CoverTree.split [tree020_16,tree020_152,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_154 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_15,tree020_153,tree020_12,tree020_12]
def tree020_155 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_151,tree020_154,tree020_76]
def tree020_156 : CoverTree := CoverTree.reject 225
def tree020_157 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_156,tree020_17,tree020_12,tree020_12]
def tree020_158 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_75,tree020_157,tree020_76]
def tree020_159 : CoverTree := CoverTree.split [tree020_129,tree020_129,tree020_149,tree020_150,tree020_155,tree020_158]
def tree020_160 : CoverTree := CoverTree.reject 82
def tree020_161 : CoverTree := CoverTree.reject 15
def tree020_162 : CoverTree := CoverTree.reject 198
def tree020_163 : CoverTree := CoverTree.reject 167
def tree020_164 : CoverTree := CoverTree.reject 10
def tree020_165 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_108,tree020_111,tree020_113,tree020_12]
def tree020_166 : CoverTree := CoverTree.reject 102
def tree020_167 : CoverTree := CoverTree.split [tree020_166,tree020_166,tree020_118,tree020_120,tree020_113,tree020_12]
def tree020_168 : CoverTree := CoverTree.split [tree020_161,tree020_162,tree020_163,tree020_165,tree020_167,tree020_100]
def tree020_169 : CoverTree := CoverTree.reject 29
def tree020_170 : CoverTree := CoverTree.reject 19
def tree020_171 : CoverTree := CoverTree.reject 41
def tree020_172 : CoverTree := CoverTree.reject 42
def tree020_173 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_169,tree020_170,tree020_171,tree020_172]
def tree020_174 : CoverTree := CoverTree.reject 120
def tree020_175 : CoverTree := CoverTree.reject 101
def tree020_176 : CoverTree := CoverTree.reject 252
def tree020_177 : CoverTree := CoverTree.split [tree020_14,tree020_37,tree020_176,tree020_12,tree020_12,tree020_12]
def tree020_178 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_177,tree020_17,tree020_40,tree020_12]
def tree020_179 : CoverTree := CoverTree.split [tree020_42,tree020_166,tree020_15,tree020_17,tree020_12,tree020_12]
def tree020_180 : CoverTree := CoverTree.split [tree020_173,tree020_174,tree020_175,tree020_178,tree020_179,tree020_30]
def tree020_181 : CoverTree := CoverTree.reject 79
def tree020_182 : CoverTree := CoverTree.reject 40
def tree020_183 : CoverTree := CoverTree.reject 43
def tree020_184 : CoverTree := CoverTree.reject 44
def tree020_185 : CoverTree := CoverTree.split [tree020_181,tree020_182,tree020_169,tree020_170,tree020_183,tree020_184]
def tree020_186 : CoverTree := CoverTree.reject 74
def tree020_187 : CoverTree := CoverTree.reject 107
def tree020_188 : CoverTree := CoverTree.reject 134
def tree020_189 : CoverTree := CoverTree.reject 149
def tree020_190 : CoverTree := CoverTree.reject 253
def tree020_191 : CoverTree := CoverTree.reject 254
def tree020_192 : CoverTree := CoverTree.split [tree020_14,tree020_188,tree020_189,tree020_190,tree020_191,tree020_12]
def tree020_193 : CoverTree := CoverTree.reject 255
def tree020_194 : CoverTree := CoverTree.reject 256
def tree020_195 : CoverTree := CoverTree.reject 257
def tree020_196 : CoverTree := CoverTree.split [tree020_16,tree020_193,tree020_194,tree020_195,tree020_12,tree020_12]
def tree020_197 : CoverTree := CoverTree.reject 86
def tree020_198 : CoverTree := CoverTree.reject 258
def tree020_199 : CoverTree := CoverTree.split [tree020_197,tree020_198,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_200 : CoverTree := CoverTree.reject 259
def tree020_201 : CoverTree := CoverTree.split [tree020_12,tree020_200,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_202 : CoverTree := CoverTree.split [tree020_186,tree020_187,tree020_192,tree020_196,tree020_199,tree020_201]
def tree020_203 : CoverTree := CoverTree.reject 75
def tree020_204 : CoverTree := CoverTree.reject 135
def tree020_205 : CoverTree := CoverTree.reject 136
def tree020_206 : CoverTree := CoverTree.reject 260
def tree020_207 : CoverTree := CoverTree.split [tree020_9,tree020_204,tree020_205,tree020_12,tree020_206,tree020_12]
def tree020_208 : CoverTree := CoverTree.reject 150
def tree020_209 : CoverTree := CoverTree.reject 261
def tree020_210 : CoverTree := CoverTree.split [tree020_14,tree020_208,tree020_209,tree020_12,tree020_12,tree020_12]
def tree020_211 : CoverTree := CoverTree.reject 262
def tree020_212 : CoverTree := CoverTree.split [tree020_16,tree020_211,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_213 : CoverTree := CoverTree.reject 87
def tree020_214 : CoverTree := CoverTree.reject 263
def tree020_215 : CoverTree := CoverTree.split [tree020_213,tree020_214,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_216 : CoverTree := CoverTree.split [tree020_203,tree020_207,tree020_210,tree020_212,tree020_215,tree020_12]
def tree020_217 : CoverTree := CoverTree.split [tree020_185,tree020_202,tree020_216,tree020_89,tree020_27,tree020_30]
def tree020_218 : CoverTree := CoverTree.split [tree020_129,tree020_129,tree020_160,tree020_168,tree020_180,tree020_217]
def tree020_219 : CoverTree := CoverTree.reject 8
def tree020_220 : CoverTree := CoverTree.reject 90
def tree020_221 : CoverTree := CoverTree.reject 183
def tree020_222 : CoverTree := CoverTree.reject 184
def tree020_223 : CoverTree := CoverTree.reject 185
def tree020_224 : CoverTree := CoverTree.split [tree020_9,tree020_221,tree020_222,tree020_223,tree020_12,tree020_12]
def tree020_225 : CoverTree := CoverTree.reject 126
def tree020_226 : CoverTree := CoverTree.split [tree020_225,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_227 : CoverTree := CoverTree.split [tree020_220,tree020_224,tree020_15,tree020_17,tree020_226,tree020_12]
def tree020_228 : CoverTree := CoverTree.split [tree020_219,tree020_219,tree020_219,tree020_219,tree020_219,tree020_227]
def tree020_229 : CoverTree := CoverTree.reject 199
def tree020_230 : CoverTree := CoverTree.reject 72
def tree020_231 : CoverTree := CoverTree.reject 360
def tree020_232 : CoverTree := CoverTree.reject 148
def tree020_233 : CoverTree := CoverTree.reject 264
def tree020_234 : CoverTree := CoverTree.split [tree020_112,tree020_232,tree020_233,tree020_12,tree020_12,tree020_12]
def tree020_235 : CoverTree := CoverTree.reject 265
def tree020_236 : CoverTree := CoverTree.split [tree020_12,tree020_235,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_237 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_230,tree020_231,tree020_234,tree020_236]
def tree020_238 : CoverTree := CoverTree.reject 243
def tree020_239 : CoverTree := CoverTree.split [tree020_115,tree020_238,tree020_118,tree020_120,tree020_113,tree020_12]
def tree020_240 : CoverTree := CoverTree.split [tree020_161,tree020_229,tree020_237,tree020_165,tree020_239,tree020_100]
def tree020_241 : CoverTree := CoverTree.reject 121
def tree020_242 : CoverTree := CoverTree.reject 189
def tree020_243 : CoverTree := CoverTree.reject 190
def tree020_244 : CoverTree := CoverTree.reject 266
def tree020_245 : CoverTree := CoverTree.split [tree020_14,tree020_242,tree020_243,tree020_244,tree020_12,tree020_12]
def tree020_246 : CoverTree := CoverTree.reject 155
def tree020_247 : CoverTree := CoverTree.reject 267
def tree020_248 : CoverTree := CoverTree.split [tree020_16,tree020_246,tree020_247,tree020_12,tree020_12,tree020_12]
def tree020_249 : CoverTree := CoverTree.reject 156
def tree020_250 : CoverTree := CoverTree.split [tree020_213,tree020_249,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_251 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_245,tree020_248,tree020_250,tree020_12]
def tree020_252 : CoverTree := CoverTree.reject 268
def tree020_253 : CoverTree := CoverTree.split [tree020_14,tree020_37,tree020_252,tree020_12,tree020_12,tree020_12]
def tree020_254 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_253,tree020_17,tree020_40,tree020_12]
def tree020_255 : CoverTree := CoverTree.split [tree020_173,tree020_241,tree020_251,tree020_254,tree020_44,tree020_30]
def tree020_256 : CoverTree := CoverTree.reject 387
def tree020_257 : CoverTree := CoverTree.reject 269
def tree020_258 : CoverTree := CoverTree.split [tree020_14,tree020_188,tree020_189,tree020_257,tree020_12,tree020_12]
def tree020_259 : CoverTree := CoverTree.reject 270
def tree020_260 : CoverTree := CoverTree.split [tree020_197,tree020_259,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_261 : CoverTree := CoverTree.split [tree020_186,tree020_256,tree020_258,tree020_17,tree020_260,tree020_12]
def tree020_262 : CoverTree := CoverTree.split [tree020_9,tree020_204,tree020_205,tree020_12,tree020_12,tree020_12]
def tree020_263 : CoverTree := CoverTree.reject 273
def tree020_264 : CoverTree := CoverTree.split [tree020_213,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_265 : CoverTree := CoverTree.split [tree020_203,tree020_262,tree020_263,tree020_17,tree020_264,tree020_12]
def tree020_266 : CoverTree := CoverTree.split [tree020_185,tree020_261,tree020_265,tree020_18,tree020_27,tree020_30]
def tree020_267 : CoverTree := CoverTree.split [tree020_129,tree020_129,tree020_228,tree020_240,tree020_255,tree020_266]
def tree020_268 : CoverTree := CoverTree.reject 30
def tree020_269 : CoverTree := CoverTree.reject 228
def tree020_270 : CoverTree := CoverTree.reject 229
def tree020_271 : CoverTree := CoverTree.reject 67
def tree020_272 : CoverTree := CoverTree.reject 68
def tree020_273 : CoverTree := CoverTree.reject 180
def tree020_274 : CoverTree := CoverTree.reject 181
def tree020_275 : CoverTree := CoverTree.reject 182
def tree020_276 : CoverTree := CoverTree.split [tree020_273,tree020_274,tree020_275,tree020_12,tree020_12,tree020_12]
def tree020_277 : CoverTree := CoverTree.split [tree020_186,tree020_269,tree020_270,tree020_271,tree020_272,tree020_276]
def tree020_278 : CoverTree := CoverTree.reject 230
def tree020_279 : CoverTree := CoverTree.reject 231
def tree020_280 : CoverTree := CoverTree.reject 69
def tree020_281 : CoverTree := CoverTree.reject 172
def tree020_282 : CoverTree := CoverTree.reject 173
def tree020_283 : CoverTree := CoverTree.reject 174
def tree020_284 : CoverTree := CoverTree.split [tree020_112,tree020_281,tree020_282,tree020_283,tree020_12,tree020_12]
def tree020_285 : CoverTree := CoverTree.reject 175
def tree020_286 : CoverTree := CoverTree.reject 176
def tree020_287 : CoverTree := CoverTree.split [tree020_285,tree020_286,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_288 : CoverTree := CoverTree.split [tree020_203,tree020_278,tree020_279,tree020_280,tree020_284,tree020_287]
def tree020_289 : CoverTree := CoverTree.reject 232
def tree020_290 : CoverTree := CoverTree.reject 233
def tree020_291 : CoverTree := CoverTree.reject 139
def tree020_292 : CoverTree := CoverTree.reject 140
def tree020_293 : CoverTree := CoverTree.split [tree020_16,tree020_291,tree020_292,tree020_12,tree020_12,tree020_12]
def tree020_294 : CoverTree := CoverTree.reject 141
def tree020_295 : CoverTree := CoverTree.reject 142
def tree020_296 : CoverTree := CoverTree.split [tree020_112,tree020_294,tree020_295,tree020_12,tree020_12,tree020_12]
def tree020_297 : CoverTree := CoverTree.reject 143
def tree020_298 : CoverTree := CoverTree.split [tree020_297,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_299 : CoverTree := CoverTree.split [tree020_8,tree020_289,tree020_290,tree020_293,tree020_296,tree020_298]
def tree020_300 : CoverTree := CoverTree.reject 234
def tree020_301 : CoverTree := CoverTree.reject 235
def tree020_302 : CoverTree := CoverTree.reject 16
def tree020_303 : CoverTree := CoverTree.split [tree020_14,tree020_302,tree020_302,tree020_302,tree020_302,tree020_12]
def tree020_304 : CoverTree := CoverTree.reject 129
def tree020_305 : CoverTree := CoverTree.split [tree020_16,tree020_304,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_306 : CoverTree := CoverTree.reject 130
def tree020_307 : CoverTree := CoverTree.split [tree020_112,tree020_306,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_308 : CoverTree := CoverTree.split [tree020_300,tree020_301,tree020_303,tree020_305,tree020_307,tree020_12]
def tree020_309 : CoverTree := CoverTree.split [tree020_268,tree020_277,tree020_288,tree020_299,tree020_308,tree020_227]
def tree020_310 : CoverTree := CoverTree.reject 236
def tree020_311 : CoverTree := CoverTree.reject 71
def tree020_312 : CoverTree := CoverTree.reject 58
def tree020_313 : CoverTree := CoverTree.reject 144
def tree020_314 : CoverTree := CoverTree.reject 145
def tree020_315 : CoverTree := CoverTree.split [tree020_112,tree020_313,tree020_314,tree020_12,tree020_12,tree020_12]
def tree020_316 : CoverTree := CoverTree.reject 146
def tree020_317 : CoverTree := CoverTree.reject 147
def tree020_318 : CoverTree := CoverTree.split [tree020_316,tree020_317,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_319 : CoverTree := CoverTree.split [tree020_186,tree020_310,tree020_311,tree020_312,tree020_315,tree020_318]
def tree020_320 : CoverTree := CoverTree.reject 237
def tree020_321 : CoverTree := CoverTree.reject 186
def tree020_322 : CoverTree := CoverTree.reject 187
def tree020_323 : CoverTree := CoverTree.reject 188
def tree020_324 : CoverTree := CoverTree.split [tree020_16,tree020_321,tree020_322,tree020_323,tree020_12,tree020_12]
def tree020_325 : CoverTree := CoverTree.split [tree020_112,tree020_232,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_326 : CoverTree := CoverTree.split [tree020_203,tree020_320,tree020_230,tree020_324,tree020_325,tree020_12]
def tree020_327 : CoverTree := CoverTree.split [tree020_161,tree020_319,tree020_326,tree020_114,tree020_121,tree020_100]
def tree020_328 : CoverTree := CoverTree.split [tree020_181,tree020_182,tree020_169,tree020_170,tree020_171,tree020_172]
def tree020_329 : CoverTree := CoverTree.reject 238
def tree020_330 : CoverTree := CoverTree.reject 59
def tree020_331 : CoverTree := CoverTree.reject 162
def tree020_332 : CoverTree := CoverTree.reject 163
def tree020_333 : CoverTree := CoverTree.split [tree020_16,tree020_331,tree020_332,tree020_12,tree020_12,tree020_12]
def tree020_334 : CoverTree := CoverTree.reject 164
def tree020_335 : CoverTree := CoverTree.reject 165
def tree020_336 : CoverTree := CoverTree.split [tree020_197,tree020_334,tree020_335,tree020_12,tree020_12,tree020_12]
def tree020_337 : CoverTree := CoverTree.reject 166
def tree020_338 : CoverTree := CoverTree.split [tree020_337,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_339 : CoverTree := CoverTree.split [tree020_186,tree020_329,tree020_330,tree020_333,tree020_336,tree020_338]
def tree020_340 : CoverTree := CoverTree.reject 137
def tree020_341 : CoverTree := CoverTree.split [tree020_14,tree020_242,tree020_243,tree020_12,tree020_12,tree020_12]
def tree020_342 : CoverTree := CoverTree.split [tree020_16,tree020_246,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_343 : CoverTree := CoverTree.split [tree020_203,tree020_340,tree020_341,tree020_342,tree020_250,tree020_12]
def tree020_344 : CoverTree := CoverTree.split [tree020_328,tree020_339,tree020_343,tree020_41,tree020_44,tree020_30]
def tree020_345 : CoverTree := CoverTree.reject 177
def tree020_346 : CoverTree := CoverTree.reject 178
def tree020_347 : CoverTree := CoverTree.reject 132
def tree020_348 : CoverTree := CoverTree.reject 133
def tree020_349 : CoverTree := CoverTree.split [tree020_9,tree020_345,tree020_346,tree020_347,tree020_348,tree020_12]
def tree020_350 : CoverTree := CoverTree.split [tree020_14,tree020_188,tree020_189,tree020_12,tree020_12,tree020_12]
def tree020_351 : CoverTree := CoverTree.split [tree020_197,tree020_12,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_352 : CoverTree := CoverTree.split [tree020_186,tree020_349,tree020_350,tree020_17,tree020_351,tree020_12]
def tree020_353 : CoverTree := CoverTree.split [tree020_14,tree020_208,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_354 : CoverTree := CoverTree.split [tree020_203,tree020_262,tree020_353,tree020_17,tree020_264,tree020_12]
def tree020_355 : CoverTree := CoverTree.split [tree020_185,tree020_352,tree020_354,tree020_47,tree020_27,tree020_30]
def tree020_356 : CoverTree := CoverTree.split [tree020_129,tree020_129,tree020_309,tree020_327,tree020_344,tree020_355]
def tree020_357 : CoverTree := CoverTree.split [tree020_128,tree020_148,tree020_159,tree020_218,tree020_267,tree020_356]
def tree020_358 : CoverTree := CoverTree.reject 12
def tree020_359 : CoverTree := CoverTree.reject 45
def tree020_360 : CoverTree := CoverTree.reject 112
def tree020_361 : CoverTree := CoverTree.reject 61
def tree020_362 : CoverTree := CoverTree.reject 57
def tree020_363 : CoverTree := CoverTree.reject 151
def tree020_364 : CoverTree := CoverTree.reject 282
def tree020_365 : CoverTree := CoverTree.reject 283
def tree020_366 : CoverTree := CoverTree.split [tree020_16,tree020_364,tree020_365,tree020_12,tree020_12,tree020_12]
def tree020_367 : CoverTree := CoverTree.reject 284
def tree020_368 : CoverTree := CoverTree.reject 285
def tree020_369 : CoverTree := CoverTree.split [tree020_39,tree020_367,tree020_368,tree020_12,tree020_12,tree020_12]
def tree020_370 : CoverTree := CoverTree.reject 286
def tree020_371 : CoverTree := CoverTree.split [tree020_12,tree020_370,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_372 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_363,tree020_366,tree020_369,tree020_371]
def tree020_373 : CoverTree := CoverTree.reject 123
def tree020_374 : CoverTree := CoverTree.reject 287
def tree020_375 : CoverTree := CoverTree.split [tree020_16,tree020_374,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_376 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_373,tree020_375,tree020_12,tree020_12]
def tree020_377 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_372,tree020_376,tree020_76]
def tree020_378 : CoverTree := CoverTree.split [tree020_359,tree020_360,tree020_361,tree020_362,tree020_377,tree020_147]
def tree020_379 : CoverTree := CoverTree.reject 46
def tree020_380 : CoverTree := CoverTree.reject 113
def tree020_381 : CoverTree := CoverTree.reject 62
def tree020_382 : CoverTree := CoverTree.reject 108
def tree020_383 : CoverTree := CoverTree.reject 274
def tree020_384 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_383,tree020_120,tree020_113,tree020_12]
def tree020_385 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_382,tree020_384,tree020_76]
def tree020_386 : CoverTree := CoverTree.reject 152
def tree020_387 : CoverTree := CoverTree.reject 288
def tree020_388 : CoverTree := CoverTree.reject 289
def tree020_389 : CoverTree := CoverTree.split [tree020_16,tree020_387,tree020_388,tree020_12,tree020_12,tree020_12]
def tree020_390 : CoverTree := CoverTree.reject 290
def tree020_391 : CoverTree := CoverTree.split [tree020_39,tree020_390,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_392 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_386,tree020_389,tree020_391,tree020_12]
def tree020_393 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_392,tree020_154,tree020_76]
def tree020_394 : CoverTree := CoverTree.split [tree020_379,tree020_380,tree020_381,tree020_385,tree020_393,tree020_77]
def tree020_395 : CoverTree := CoverTree.reject 23
def tree020_396 : CoverTree := CoverTree.reject 114
def tree020_397 : CoverTree := CoverTree.reject 131
def tree020_398 : CoverTree := CoverTree.reject 157
def tree020_399 : CoverTree := CoverTree.reject 122
def tree020_400 : CoverTree := CoverTree.reject 73
def tree020_401 : CoverTree := CoverTree.reject 291
def tree020_402 : CoverTree := CoverTree.split [tree020_12,tree020_401,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_403 : CoverTree := CoverTree.split [tree020_400,tree020_400,tree020_400,tree020_305,tree020_307,tree020_402]
def tree020_404 : CoverTree := CoverTree.reject 124
def tree020_405 : CoverTree := CoverTree.reject 292
def tree020_406 : CoverTree := CoverTree.split [tree020_14,tree020_405,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_407 : CoverTree := CoverTree.reject 293
def tree020_408 : CoverTree := CoverTree.split [tree020_16,tree020_407,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_409 : CoverTree := CoverTree.split [tree020_220,tree020_404,tree020_406,tree020_408,tree020_226,tree020_12]
def tree020_410 : CoverTree := CoverTree.split [tree020_268,tree020_397,tree020_398,tree020_399,tree020_403,tree020_409]
def tree020_411 : CoverTree := CoverTree.reject 200
def tree020_412 : CoverTree := CoverTree.reject 168
def tree020_413 : CoverTree := CoverTree.split [tree020_161,tree020_411,tree020_412,tree020_165,tree020_167,tree020_100]
def tree020_414 : CoverTree := CoverTree.reject 294
def tree020_415 : CoverTree := CoverTree.reject 295
def tree020_416 : CoverTree := CoverTree.split [tree020_16,tree020_331,tree020_332,tree020_414,tree020_415,tree020_12]
def tree020_417 : CoverTree := CoverTree.reject 296
def tree020_418 : CoverTree := CoverTree.reject 297
def tree020_419 : CoverTree := CoverTree.split [tree020_197,tree020_334,tree020_335,tree020_417,tree020_418,tree020_12]
def tree020_420 : CoverTree := CoverTree.reject 298
def tree020_421 : CoverTree := CoverTree.reject 299
def tree020_422 : CoverTree := CoverTree.split [tree020_337,tree020_420,tree020_421,tree020_12,tree020_12,tree020_12]
def tree020_423 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_330,tree020_416,tree020_419,tree020_422]
def tree020_424 : CoverTree := CoverTree.reject 125
def tree020_425 : CoverTree := CoverTree.reject 300
def tree020_426 : CoverTree := CoverTree.split [tree020_16,tree020_246,tree020_425,tree020_12,tree020_12,tree020_12]
def tree020_427 : CoverTree := CoverTree.reject 301
def tree020_428 : CoverTree := CoverTree.split [tree020_213,tree020_249,tree020_427,tree020_12,tree020_12,tree020_12]
def tree020_429 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_424,tree020_426,tree020_428,tree020_12]
def tree020_430 : CoverTree := CoverTree.split [tree020_173,tree020_423,tree020_429,tree020_178,tree020_179,tree020_30]
def tree020_431 : CoverTree := CoverTree.split [tree020_395,tree020_396,tree020_410,tree020_413,tree020_430,tree020_217]
def tree020_432 : CoverTree := CoverTree.reject 138
def tree020_433 : CoverTree := CoverTree.reject 14
def tree020_434 : CoverTree := CoverTree.reject 2
def tree020_435 : CoverTree := CoverTree.reject 158
def tree020_436 : CoverTree := CoverTree.reject 159
def tree020_437 : CoverTree := CoverTree.split [tree020_16,tree020_435,tree020_436,tree020_12,tree020_12,tree020_12]
def tree020_438 : CoverTree := CoverTree.reject 160
def tree020_439 : CoverTree := CoverTree.reject 161
def tree020_440 : CoverTree := CoverTree.split [tree020_438,tree020_439,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_441 : CoverTree := CoverTree.reject 302
def tree020_442 : CoverTree := CoverTree.split [tree020_12,tree020_441,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_443 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_437,tree020_440,tree020_442]
def tree020_444 : CoverTree := CoverTree.split [tree020_433,tree020_433,tree020_433,tree020_433,tree020_433,tree020_443]
def tree020_445 : CoverTree := CoverTree.reject 303
def tree020_446 : CoverTree := CoverTree.split [tree020_285,tree020_286,tree020_445,tree020_12,tree020_12,tree020_12]
def tree020_447 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_400,tree020_280,tree020_284,tree020_446]
def tree020_448 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_400,tree020_293,tree020_296,tree020_298]
def tree020_449 : CoverTree := CoverTree.split [tree020_400,tree020_400,tree020_400,tree020_305,tree020_307,tree020_12]
def tree020_450 : CoverTree := CoverTree.split [tree020_268,tree020_397,tree020_447,tree020_448,tree020_449,tree020_227]
def tree020_451 : CoverTree := CoverTree.reject 201
def tree020_452 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_230,tree020_324,tree020_234,tree020_236]
def tree020_453 : CoverTree := CoverTree.split [tree020_161,tree020_451,tree020_452,tree020_165,tree020_239,tree020_100]
def tree020_454 : CoverTree := CoverTree.reject 304
def tree020_455 : CoverTree := CoverTree.reject 305
def tree020_456 : CoverTree := CoverTree.split [tree020_16,tree020_331,tree020_332,tree020_454,tree020_455,tree020_12]
def tree020_457 : CoverTree := CoverTree.reject 306
def tree020_458 : CoverTree := CoverTree.split [tree020_197,tree020_334,tree020_335,tree020_457,tree020_12,tree020_12]
def tree020_459 : CoverTree := CoverTree.reject 307
def tree020_460 : CoverTree := CoverTree.split [tree020_337,tree020_459,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_461 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_330,tree020_456,tree020_458,tree020_460]
def tree020_462 : CoverTree := CoverTree.split [tree020_173,tree020_461,tree020_251,tree020_254,tree020_44,tree020_30]
def tree020_463 : CoverTree := CoverTree.split [tree020_186,tree020_349,tree020_258,tree020_17,tree020_260,tree020_12]
def tree020_464 : CoverTree := CoverTree.split [tree020_185,tree020_463,tree020_354,tree020_18,tree020_27,tree020_30]
def tree020_465 : CoverTree := CoverTree.split [tree020_432,tree020_444,tree020_450,tree020_453,tree020_462,tree020_464]
def tree020_466 : CoverTree := CoverTree.reject 70
def tree020_467 : CoverTree := CoverTree.reject 76
def tree020_468 : CoverTree := CoverTree.reject 193
def tree020_469 : CoverTree := CoverTree.reject 194
def tree020_470 : CoverTree := CoverTree.reject 276
def tree020_471 : CoverTree := CoverTree.reject 5
def tree020_472 : CoverTree := CoverTree.reject 38
def tree020_473 : CoverTree := CoverTree.split [tree020_471,tree020_471,tree020_471,tree020_471,tree020_472,tree020_12]
def tree020_474 : CoverTree := CoverTree.reject 170
def tree020_475 : CoverTree := CoverTree.reject 171
def tree020_476 : CoverTree := CoverTree.split [tree020_474,tree020_475,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_477 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_470,tree020_473,tree020_476]
def tree020_478 : CoverTree := CoverTree.reject 277
def tree020_479 : CoverTree := CoverTree.split [tree020_471,tree020_471,tree020_471,tree020_471,tree020_478,tree020_12]
def tree020_480 : CoverTree := CoverTree.split [tree020_471,tree020_471,tree020_471,tree020_471,tree020_12,tree020_12]
def tree020_481 : CoverTree := CoverTree.reject 308
def tree020_482 : CoverTree := CoverTree.split [tree020_12,tree020_481,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_483 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_479,tree020_480,tree020_482]
def tree020_484 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_437,tree020_440,tree020_12]
def tree020_485 : CoverTree := CoverTree.split [tree020_467,tree020_468,tree020_469,tree020_477,tree020_483,tree020_484]
def tree020_486 : CoverTree := CoverTree.split [tree020_466,tree020_485,tree020_309,tree020_327,tree020_344,tree020_355]
def tree020_487 : CoverTree := CoverTree.split [tree020_358,tree020_378,tree020_394,tree020_431,tree020_465,tree020_486]
def tree020_488 : CoverTree := CoverTree.reject 65
def tree020_489 : CoverTree := CoverTree.reject 47
def tree020_490 : CoverTree := CoverTree.reject 31
def tree020_491 : CoverTree := CoverTree.reject 17
def tree020_492 : CoverTree := CoverTree.reject 51
def tree020_493 : CoverTree := CoverTree.reject 52
def tree020_494 : CoverTree := CoverTree.split [tree020_488,tree020_489,tree020_490,tree020_491,tree020_492,tree020_493]
def tree020_495 : CoverTree := CoverTree.reject 77
def tree020_496 : CoverTree := CoverTree.reject 63
def tree020_497 : CoverTree := CoverTree.reject 241
def tree020_498 : CoverTree := CoverTree.reject 204
def tree020_499 : CoverTree := CoverTree.reject 316
def tree020_500 : CoverTree := CoverTree.reject 317
def tree020_501 : CoverTree := CoverTree.split [tree020_112,tree020_499,tree020_500,tree020_12,tree020_12,tree020_12]
def tree020_502 : CoverTree := CoverTree.reject 318
def tree020_503 : CoverTree := CoverTree.reject 319
def tree020_504 : CoverTree := CoverTree.reject 320
def tree020_505 : CoverTree := CoverTree.split [tree020_12,tree020_502,tree020_503,tree020_504,tree020_12,tree020_12]
def tree020_506 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_497,tree020_498,tree020_501,tree020_505]
def tree020_507 : CoverTree := CoverTree.reject 191
def tree020_508 : CoverTree := CoverTree.reject 192
def tree020_509 : CoverTree := CoverTree.reject 321
def tree020_510 : CoverTree := CoverTree.reject 322
def tree020_511 : CoverTree := CoverTree.split [tree020_112,tree020_509,tree020_510,tree020_12,tree020_12,tree020_12]
def tree020_512 : CoverTree := CoverTree.reject 323
def tree020_513 : CoverTree := CoverTree.split [tree020_12,tree020_512,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_514 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_507,tree020_508,tree020_511,tree020_513]
def tree020_515 : CoverTree := CoverTree.reject 324
def tree020_516 : CoverTree := CoverTree.reject 325
def tree020_517 : CoverTree := CoverTree.reject 326
def tree020_518 : CoverTree := CoverTree.split [tree020_14,tree020_515,tree020_516,tree020_517,tree020_12,tree020_12]
def tree020_519 : CoverTree := CoverTree.reject 327
def tree020_520 : CoverTree := CoverTree.split [tree020_16,tree020_519,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_521 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_518,tree020_520,tree020_12,tree020_12]
def tree020_522 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_506,tree020_514,tree020_521]
def tree020_523 : CoverTree := CoverTree.split [tree020_359,tree020_495,tree020_496,tree020_522,tree020_377,tree020_147]
def tree020_524 : CoverTree := CoverTree.reject 78
def tree020_525 : CoverTree := CoverTree.reject 205
def tree020_526 : CoverTree := CoverTree.reject 328
def tree020_527 : CoverTree := CoverTree.reject 329
def tree020_528 : CoverTree := CoverTree.split [tree020_112,tree020_294,tree020_295,tree020_526,tree020_527,tree020_12]
def tree020_529 : CoverTree := CoverTree.reject 330
def tree020_530 : CoverTree := CoverTree.reject 331
def tree020_531 : CoverTree := CoverTree.split [tree020_297,tree020_529,tree020_530,tree020_12,tree020_12,tree020_12]
def tree020_532 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_400,tree020_525,tree020_528,tree020_531]
def tree020_533 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_400,tree020_305,tree020_307,tree020_12]
def tree020_534 : CoverTree := CoverTree.reject 332
def tree020_535 : CoverTree := CoverTree.reject 333
def tree020_536 : CoverTree := CoverTree.split [tree020_14,tree020_534,tree020_535,tree020_12,tree020_12,tree020_12]
def tree020_537 : CoverTree := CoverTree.reject 334
def tree020_538 : CoverTree := CoverTree.split [tree020_16,tree020_537,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_539 : CoverTree := CoverTree.reject 335
def tree020_540 : CoverTree := CoverTree.split [tree020_12,tree020_539,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_541 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_536,tree020_538,tree020_226,tree020_540]
def tree020_542 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_532,tree020_533,tree020_541]
def tree020_543 : CoverTree := CoverTree.reject 242
def tree020_544 : CoverTree := CoverTree.reject 206
def tree020_545 : CoverTree := CoverTree.reject 336
def tree020_546 : CoverTree := CoverTree.reject 337
def tree020_547 : CoverTree := CoverTree.split [tree020_112,tree020_545,tree020_546,tree020_12,tree020_12,tree020_12]
def tree020_548 : CoverTree := CoverTree.reject 338
def tree020_549 : CoverTree := CoverTree.split [tree020_12,tree020_548,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_550 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_543,tree020_544,tree020_547,tree020_549]
def tree020_551 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_118,tree020_120,tree020_113,tree020_12]
def tree020_552 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_550,tree020_551,tree020_76]
def tree020_553 : CoverTree := CoverTree.split [tree020_379,tree020_524,tree020_542,tree020_552,tree020_393,tree020_77]
def tree020_554 : CoverTree := CoverTree.reject 48
def tree020_555 : CoverTree := CoverTree.reject 211
def tree020_556 : CoverTree := CoverTree.reject 83
def tree020_557 : CoverTree := CoverTree.reject 339
def tree020_558 : CoverTree := CoverTree.split [tree020_12,tree020_557,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_559 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_480,tree020_558]
def tree020_560 : CoverTree := CoverTree.reject 340
def tree020_561 : CoverTree := CoverTree.split [tree020_12,tree020_560,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_562 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_437,tree020_440,tree020_561]
def tree020_563 : CoverTree := CoverTree.split [tree020_554,tree020_554,tree020_554,tree020_555,tree020_559,tree020_562]
def tree020_564 : CoverTree := CoverTree.reject 281
def tree020_565 : CoverTree := CoverTree.reject 341
def tree020_566 : CoverTree := CoverTree.split [tree020_112,tree020_281,tree020_282,tree020_283,tree020_565,tree020_12]
def tree020_567 : CoverTree := CoverTree.reject 342
def tree020_568 : CoverTree := CoverTree.split [tree020_285,tree020_286,tree020_567,tree020_12,tree020_12,tree020_12]
def tree020_569 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_400,tree020_280,tree020_566,tree020_568]
def tree020_570 : CoverTree := CoverTree.reject 207
def tree020_571 : CoverTree := CoverTree.reject 343
def tree020_572 : CoverTree := CoverTree.reject 344
def tree020_573 : CoverTree := CoverTree.split [tree020_297,tree020_571,tree020_572,tree020_12,tree020_12,tree020_12]
def tree020_574 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_400,tree020_570,tree020_296,tree020_573]
def tree020_575 : CoverTree := CoverTree.split [tree020_268,tree020_564,tree020_569,tree020_574,tree020_403,tree020_409]
def tree020_576 : CoverTree := CoverTree.reject 345
def tree020_577 : CoverTree := CoverTree.reject 346
def tree020_578 : CoverTree := CoverTree.split [tree020_112,tree020_313,tree020_314,tree020_576,tree020_577,tree020_12]
def tree020_579 : CoverTree := CoverTree.reject 347
def tree020_580 : CoverTree := CoverTree.reject 348
def tree020_581 : CoverTree := CoverTree.split [tree020_316,tree020_317,tree020_579,tree020_580,tree020_12,tree020_12]
def tree020_582 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_311,tree020_312,tree020_578,tree020_581]
def tree020_583 : CoverTree := CoverTree.reject 106
def tree020_584 : CoverTree := CoverTree.reject 349
def tree020_585 : CoverTree := CoverTree.split [tree020_112,tree020_232,tree020_584,tree020_12,tree020_12,tree020_12]
def tree020_586 : CoverTree := CoverTree.reject 350
def tree020_587 : CoverTree := CoverTree.reject 351
def tree020_588 : CoverTree := CoverTree.split [tree020_12,tree020_586,tree020_587,tree020_12,tree020_12,tree020_12]
def tree020_589 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_230,tree020_583,tree020_585,tree020_588]
def tree020_590 : CoverTree := CoverTree.split [tree020_161,tree020_582,tree020_589,tree020_165,tree020_167,tree020_100]
def tree020_591 : CoverTree := CoverTree.split [tree020_395,tree020_563,tree020_575,tree020_590,tree020_430,tree020_217]
def tree020_592 : CoverTree := CoverTree.reject 103
def tree020_593 : CoverTree := CoverTree.reject 352
def tree020_594 : CoverTree := CoverTree.split [tree020_474,tree020_475,tree020_593,tree020_12,tree020_12,tree020_12]
def tree020_595 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_473,tree020_594]
def tree020_596 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_480,tree020_12]
def tree020_597 : CoverTree := CoverTree.split [tree020_554,tree020_554,tree020_554,tree020_595,tree020_596,tree020_443]
def tree020_598 : CoverTree := CoverTree.reject 353
def tree020_599 : CoverTree := CoverTree.split [tree020_273,tree020_274,tree020_275,tree020_598,tree020_12,tree020_12]
def tree020_600 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_400,tree020_271,tree020_272,tree020_599]
def tree020_601 : CoverTree := CoverTree.split [tree020_268,tree020_600,tree020_447,tree020_448,tree020_449,tree020_227]
def tree020_602 : CoverTree := CoverTree.reject 354
def tree020_603 : CoverTree := CoverTree.reject 355
def tree020_604 : CoverTree := CoverTree.split [tree020_112,tree020_313,tree020_314,tree020_602,tree020_603,tree020_12]
def tree020_605 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_311,tree020_312,tree020_604,tree020_318]
def tree020_606 : CoverTree := CoverTree.split [tree020_161,tree020_605,tree020_452,tree020_165,tree020_239,tree020_100]
def tree020_607 : CoverTree := CoverTree.split [tree020_592,tree020_597,tree020_601,tree020_606,tree020_462,tree020_464]
def tree020_608 : CoverTree := CoverTree.reject 100
def tree020_609 : CoverTree := CoverTree.reject 88
def tree020_610 : CoverTree := CoverTree.reject 89
def tree020_611 : CoverTree := CoverTree.reject 34
def tree020_612 : CoverTree := CoverTree.reject 226
def tree020_613 : CoverTree := CoverTree.reject 202
def tree020_614 : CoverTree := CoverTree.reject 153
def tree020_615 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_612,tree020_613,tree020_614]
def tree020_616 : CoverTree := CoverTree.reject 85
def tree020_617 : CoverTree := CoverTree.reject 356
def tree020_618 : CoverTree := CoverTree.reject 357
def tree020_619 : CoverTree := CoverTree.reject 358
def tree020_620 : CoverTree := CoverTree.split [tree020_617,tree020_618,tree020_619,tree020_12,tree020_12,tree020_12]
def tree020_621 : CoverTree := CoverTree.reject 359
def tree020_622 : CoverTree := CoverTree.split [tree020_12,tree020_621,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_623 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_616,tree020_620,tree020_622]
def tree020_624 : CoverTree := CoverTree.split [tree020_608,tree020_609,tree020_610,tree020_611,tree020_615,tree020_623]
def tree020_625 : CoverTree := CoverTree.reject 309
def tree020_626 : CoverTree := CoverTree.reject 310
def tree020_627 : CoverTree := CoverTree.reject 312
def tree020_628 : CoverTree := CoverTree.reject 313
def tree020_629 : CoverTree := CoverTree.reject 314
def tree020_630 : CoverTree := CoverTree.reject 315
def tree020_631 : CoverTree := CoverTree.split [tree020_627,tree020_628,tree020_629,tree020_630,tree020_12,tree020_12]
def tree020_632 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_625,tree020_626,tree020_631]
def tree020_633 : CoverTree := CoverTree.reject 311
def tree020_634 : CoverTree := CoverTree.reject 227
def tree020_635 : CoverTree := CoverTree.reject 239
def tree020_636 : CoverTree := CoverTree.reject 240
def tree020_637 : CoverTree := CoverTree.split [tree020_635,tree020_636,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_638 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_633,tree020_634,tree020_637]
def tree020_639 : CoverTree := CoverTree.split [tree020_467,tree020_632,tree020_638,tree020_477,tree020_483,tree020_484]
def tree020_640 : CoverTree := CoverTree.split [tree020_624,tree020_639,tree020_309,tree020_327,tree020_344,tree020_355]
def tree020_641 : CoverTree := CoverTree.split [tree020_494,tree020_523,tree020_553,tree020_591,tree020_607,tree020_640]
def tree020_642 : CoverTree := CoverTree.reject 53
def tree020_643 : CoverTree := CoverTree.reject 54
def tree020_644 : CoverTree := CoverTree.split [tree020_488,tree020_489,tree020_490,tree020_491,tree020_642,tree020_643]
def tree020_645 : CoverTree := CoverTree.reject 210
def tree020_646 : CoverTree := CoverTree.reject 179
def tree020_647 : CoverTree := CoverTree.reject 278
def tree020_648 : CoverTree := CoverTree.reject 364
def tree020_649 : CoverTree := CoverTree.split [tree020_438,tree020_439,tree020_648,tree020_12,tree020_12,tree020_12]
def tree020_650 : CoverTree := CoverTree.reject 365
def tree020_651 : CoverTree := CoverTree.split [tree020_12,tree020_650,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_652 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_647,tree020_649,tree020_651]
def tree020_653 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_645,tree020_646,tree020_652]
def tree020_654 : CoverTree := CoverTree.reject 195
def tree020_655 : CoverTree := CoverTree.reject 279
def tree020_656 : CoverTree := CoverTree.reject 366
def tree020_657 : CoverTree := CoverTree.reject 367
def tree020_658 : CoverTree := CoverTree.reject 368
def tree020_659 : CoverTree := CoverTree.split [tree020_297,tree020_656,tree020_657,tree020_658,tree020_12,tree020_12]
def tree020_660 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_400,tree020_654,tree020_655,tree020_659]
def tree020_661 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_400,tree020_654,tree020_307,tree020_12]
def tree020_662 : CoverTree := CoverTree.reject 369
def tree020_663 : CoverTree := CoverTree.reject 370
def tree020_664 : CoverTree := CoverTree.reject 371
def tree020_665 : CoverTree := CoverTree.split [tree020_14,tree020_662,tree020_663,tree020_664,tree020_12,tree020_12]
def tree020_666 : CoverTree := CoverTree.reject 372
def tree020_667 : CoverTree := CoverTree.split [tree020_16,tree020_666,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_668 : CoverTree := CoverTree.reject 373
def tree020_669 : CoverTree := CoverTree.split [tree020_12,tree020_668,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_670 : CoverTree := CoverTree.split [tree020_56,tree020_56,tree020_665,tree020_667,tree020_226,tree020_669]
def tree020_671 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_660,tree020_661,tree020_670]
def tree020_672 : CoverTree := CoverTree.split [tree020_359,tree020_653,tree020_671,tree020_522,tree020_377,tree020_147]
def tree020_673 : CoverTree := CoverTree.reject 275
def tree020_674 : CoverTree := CoverTree.reject 374
def tree020_675 : CoverTree := CoverTree.reject 375
def tree020_676 : CoverTree := CoverTree.reject 376
def tree020_677 : CoverTree := CoverTree.split [tree020_474,tree020_475,tree020_674,tree020_675,tree020_676,tree020_12]
def tree020_678 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_673,tree020_677]
def tree020_679 : CoverTree := CoverTree.reject 377
def tree020_680 : CoverTree := CoverTree.split [tree020_12,tree020_679,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_681 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_673,tree020_680]
def tree020_682 : CoverTree := CoverTree.reject 280
def tree020_683 : CoverTree := CoverTree.reject 378
def tree020_684 : CoverTree := CoverTree.split [tree020_438,tree020_439,tree020_683,tree020_12,tree020_12,tree020_12]
def tree020_685 : CoverTree := CoverTree.reject 379
def tree020_686 : CoverTree := CoverTree.split [tree020_12,tree020_685,tree020_12,tree020_12,tree020_12,tree020_12]
def tree020_687 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_682,tree020_684,tree020_686]
def tree020_688 : CoverTree := CoverTree.split [tree020_54,tree020_54,tree020_54,tree020_678,tree020_681,tree020_687]
def tree020_689 : CoverTree := CoverTree.split [tree020_379,tree020_688,tree020_542,tree020_552,tree020_393,tree020_77]
def tree020_690 : CoverTree := CoverTree.reject 196
def tree020_691 : CoverTree := CoverTree.reject 380
def tree020_692 : CoverTree := CoverTree.split [tree020_635,tree020_636,tree020_691,tree020_12,tree020_12,tree020_12]
def tree020_693 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_634,tree020_692]
def tree020_694 : CoverTree := CoverTree.reject 363
def tree020_695 : CoverTree := CoverTree.reject 381
def tree020_696 : CoverTree := CoverTree.reject 382
def tree020_697 : CoverTree := CoverTree.split [tree020_474,tree020_475,tree020_695,tree020_696,tree020_12,tree020_12]
def tree020_698 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_694,tree020_697]
def tree020_699 : CoverTree := CoverTree.split [tree020_467,tree020_690,tree020_693,tree020_698,tree020_559,tree020_562]
def tree020_700 : CoverTree := CoverTree.reject 383
def tree020_701 : CoverTree := CoverTree.reject 384
def tree020_702 : CoverTree := CoverTree.split [tree020_273,tree020_274,tree020_275,tree020_700,tree020_701,tree020_12]
def tree020_703 : CoverTree := CoverTree.split [tree020_164,tree020_164,tree020_400,tree020_271,tree020_272,tree020_702]
def tree020_704 : CoverTree := CoverTree.split [tree020_268,tree020_703,tree020_569,tree020_574,tree020_403,tree020_409]
def tree020_705 : CoverTree := CoverTree.split [tree020_395,tree020_699,tree020_704,tree020_590,tree020_430,tree020_217]
def tree020_706 : CoverTree := CoverTree.reject 361
def tree020_707 : CoverTree := CoverTree.reject 362
def tree020_708 : CoverTree := CoverTree.split [tree020_12,tree020_706,tree020_707,tree020_12,tree020_12,tree020_12]
def tree020_709 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_613,tree020_708]
def tree020_710 : CoverTree := CoverTree.reject 154
def tree020_711 : CoverTree := CoverTree.split [tree020_608,tree020_609,tree020_610,tree020_611,tree020_709,tree020_710]
def tree020_712 : CoverTree := CoverTree.reject 197
def tree020_713 : CoverTree := CoverTree.reject 385
def tree020_714 : CoverTree := CoverTree.reject 386
def tree020_715 : CoverTree := CoverTree.split [tree020_635,tree020_636,tree020_713,tree020_714,tree020_12,tree020_12]
def tree020_716 : CoverTree := CoverTree.split [tree020_434,tree020_434,tree020_434,tree020_556,tree020_634,tree020_715]
def tree020_717 : CoverTree := CoverTree.split [tree020_467,tree020_712,tree020_716,tree020_595,tree020_596,tree020_443]
def tree020_718 : CoverTree := CoverTree.split [tree020_711,tree020_717,tree020_601,tree020_606,tree020_462,tree020_464]
def tree020_719 : CoverTree := CoverTree.split [tree020_644,tree020_672,tree020_689,tree020_705,tree020_718,tree020_640]
def tree020_720 : CoverTree := CoverTree.split [tree020_50,tree020_127,tree020_357,tree020_487,tree020_641,tree020_719]
def tree020 : CoverTree := tree020_720

end Snake9.Shared89
