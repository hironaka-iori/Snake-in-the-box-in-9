import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes016 : List Box := [
[(1,3),(1,5),(1,3),(1,5),(1,6),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,6),(1,3)],
[(1,2),(1,6),(1,6),(1,6),(1,3),(1,6)],
[(1,6),(1,6),(1,5),(1,3),(1,5),(1,3)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,2)],
[(1,3),(1,6),(1,6),(1,6),(1,2),(1,6)],
[(1,6),(1,6),(1,3),(1,2),(1,5),(1,5)],
[(1,2),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,6),(1,6),(1,2)],
[(1,4),(1,5),(1,2),(1,5),(1,6),(1,6)],
[(1,2),(1,6),(1,3),(1,6),(1,6),(1,6)],
[(1,2),(1,4),(1,5),(1,5),(1,6),(1,6)],
[(1,6),(1,6),(1,5),(1,5),(1,4),(1,2)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(4,4)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,2)],
[(1,5),(1,5),(1,2),(1,3),(1,6),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,5),(1,2),(1,5),(1,4)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(3,3)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(1,1),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(2,2),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,2),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,2)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(4,4)],
[(1,6),(1,1),(2,2),(1,6),(1,6),(1,6)],
[(4,4),(3,3),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(6,6),(1,1),(6,6)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(5,5)],
[(1,6),(1,6),(1,6),(5,5),(1,1),(6,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(1,1),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(3,3)],
[(3,3),(3,3),(4,4),(1,6),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(5,5)],
[(5,5),(1,1),(6,6),(1,6),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(4,4),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(5,5),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(3,3)],
[(3,3),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(5,5),(1,1),(5,5),(1,6),(1,6),(1,6)],
[(6,6),(1,1),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(5,5)],
[(5,5),(3,3),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(3,3)],
[(3,3),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(1,6),(4,4),(6,6),(1,1)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(4,4)],
[(4,4),(6,6),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,1)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(2,2)],
[(2,2),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(5,5)],
[(5,5),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(3,3)],
[(3,3),(6,6),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(5,5)],
[(5,5),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(5,5),(1,1)],
[(1,1),(5,5),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(5,5),(1,1)],
[(1,6),(1,6),(1,1),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(4,4),(3,3)],
[(3,3),(4,4),(3,3),(1,6),(1,6),(1,6)],
[(1,4),(1,5),(1,5),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(1,5),(1,5),(1,4)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(4,4)],
[(1,6),(1,6),(1,6),(2,2),(4,4),(4,4)],
[(4,4),(3,3),(2,2),(1,6),(1,6),(1,6)],
[(4,4),(4,4),(2,2),(1,6),(1,6),(1,6)],
[(4,4),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(6,6),(1,1),(5,5),(6,6)],
[(6,6),(5,5),(1,1),(6,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(4,4),(4,4)],
[(4,4),(4,4),(3,3),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(1,6),(4,4),(4,4),(2,2)],
[(2,2),(4,4),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(4,4),(5,5)],
[(1,6),(1,6),(4,4),(4,4),(3,3),(4,4)],
[(5,5),(4,4),(2,2),(4,4),(1,6),(1,6)],
[(1,4),(1,5),(1,3),(1,2),(1,6),(1,6)],
[(1,6),(1,6),(1,2),(1,3),(1,5),(1,4)],
[(1,6),(1,6),(1,6),(1,1),(5,5),(3,3)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(3,3)],
[(1,6),(1,6),(1,6),(2,2),(4,4),(3,3)],
[(1,6),(1,6),(1,6),(2,2),(5,5),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(3,3)],
[(3,3),(3,3),(2,2),(1,6),(1,6),(1,6)],
[(3,3),(3,3),(3,3),(1,6),(1,6),(1,6)],
[(3,3),(4,4),(2,2),(1,6),(1,6),(1,6)],
[(3,3),(5,5),(1,1),(1,6),(1,6),(1,6)],
[(3,3),(5,5),(2,2),(1,6),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(4,4)],
[(1,6),(1,6),(5,5),(2,2),(2,2),(1,6)],
[(1,6),(2,2),(2,2),(5,5),(1,6),(1,6)],
[(4,4),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(6,6),(3,3)],
[(1,6),(1,6),(4,4),(5,5),(3,3),(3,3)],
[(3,3),(3,3),(5,5),(4,4),(1,6),(1,6)],
[(3,3),(6,6),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(2,2),(2,2),(1,6)],
[(1,6),(2,2),(2,2),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(2,2)],
[(2,2),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(4,4),(3,3),(6,6),(2,2)],
[(3,3),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(5,5),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(5,5),(3,3),(2,2)],
[(2,2),(3,3),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(6,6),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(4,4),(3,3),(4,4)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(4,4)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(4,4)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(5,5)],
[(1,6),(1,6),(3,3),(5,5),(3,3),(3,3)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(3,3)],
[(3,3),(3,3),(5,5),(3,3),(1,6),(1,6)],
[(4,4),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(5,5),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(6,6),(2,2),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(4,4)],
[(1,6),(1,6),(3,3),(4,4),(2,2),(5,5)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(6,6),(5,5),(1,1)],
[(3,3),(2,2),(6,6),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(5,5),(2,2),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(2,2),(1,6)],
[(1,6),(2,2),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(2,2),(4,4)],
[(1,6),(1,6),(2,2),(6,6),(3,3),(3,3)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(3,3)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(5,5)],
[(1,6),(1,6),(3,3),(3,3),(4,4),(4,4)],
[(3,3),(3,3),(6,6),(2,2),(1,6),(1,6)],
[(3,3),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(4,4),(2,2),(6,6),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(3,3),(3,3)],
[(1,6),(1,6),(2,2),(5,5),(3,3),(4,4)],
[(1,6),(1,6),(2,2),(5,5),(3,3),(5,5)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(5,5),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(6,6),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(3,3),(2,2),(6,6)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(2,2)],
[(2,2),(2,2),(6,6),(3,3),(1,6),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(2,2),(6,6),(2,2),(1,6),(1,6)],
[(3,3),(3,3),(5,5),(2,2),(1,6),(1,6)],
[(3,3),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(5,5),(2,2),(1,6),(1,6)],
[(4,4),(3,3),(5,5),(2,2),(1,6),(1,6)],
[(5,5),(3,3),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(3,3),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(4,4),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(5,5),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(4,4)],
[(1,6),(1,6),(2,2),(5,5),(2,2),(4,4)],
[(1,6),(1,6),(2,2),(5,5),(2,2),(5,5)],
[(4,4),(2,2),(5,5),(2,2),(1,6),(1,6)],
[(5,5),(2,2),(5,5),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(2,2),(1,6)],
[(1,6),(1,6),(2,2),(2,2),(6,6),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(2,2),(5,5)],
[(1,6),(1,6),(2,2),(4,4),(3,3),(4,4)],
[(1,6),(1,6),(2,2),(4,4),(3,3),(5,5)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(4,4),(4,4)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(4,4),(5,5),(4,4)],
[(3,3),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(2,2),(1,6),(1,6)],
[(4,4),(4,4),(4,4),(2,2),(1,6),(1,6)],
[(4,4),(5,5),(4,4),(2,2),(1,6),(1,6)],
[(5,5),(2,2),(4,4),(2,2),(1,6),(1,6)],
[(5,5),(3,3),(4,4),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(2,2),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(3,3),(1,6)],
[(1,6),(2,2),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(3,3),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(2,2),(1,6)],
[(1,6),(2,2),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(3,3),(3,3),(5,5)],
[(1,6),(1,6),(2,2),(3,3),(3,3),(6,6)],
[(1,6),(1,6),(2,2),(3,3),(4,4),(5,5)],
[(1,6),(2,2),(4,4),(4,4),(2,2),(1,6)],
[(1,6),(3,3),(3,3),(2,2),(6,6),(1,6)],
[(5,5),(4,4),(3,3),(2,2),(1,6),(1,6)],
[(1,6),(2,2),(6,6),(5,5),(3,3),(4,4)],
[(1,6),(3,3),(5,5),(6,6),(3,3),(3,3)],
[(1,6),(6,6),(4,4),(2,2),(3,3),(6,6)],
[(3,3),(3,3),(6,6),(5,5),(3,3),(1,6)],
[(4,4),(3,3),(5,5),(6,6),(2,2),(1,6)],
[(6,6),(3,3),(2,2),(4,4),(6,6),(1,6)],
[(1,6),(1,6),(1,1),(5,5),(4,4),(5,5)],
[(1,6),(1,6),(1,1),(5,5),(6,6),(3,3)],
[(3,3),(6,6),(5,5),(1,1),(1,6),(1,6)],
[(5,5),(4,4),(5,5),(1,1),(1,6),(1,6)],
[(1,6),(2,2),(5,5),(6,6),(2,2),(4,4)],
[(1,6),(2,2),(6,6),(3,3),(4,4),(4,4)],
[(1,6),(3,3),(4,4),(5,5),(2,2),(4,4)],
[(1,6),(3,3),(5,5),(3,3),(3,3),(5,5)],
[(1,6),(3,3),(5,5),(3,3),(4,4),(4,4)],
[(1,6),(3,3),(5,5),(4,4),(3,3),(4,4)],
[(1,6),(4,4),(3,3),(6,6),(3,3),(2,2)],
[(1,6),(4,4),(4,4),(4,4),(2,2),(5,5)],
[(1,6),(4,4),(5,5),(2,2),(4,4),(5,5)],
[(1,6),(4,4),(5,5),(6,6),(2,2),(2,2)],
[(2,2),(2,2),(6,6),(5,5),(4,4),(1,6)],
[(2,2),(3,3),(6,6),(3,3),(4,4),(1,6)],
[(4,4),(2,2),(5,5),(4,4),(3,3),(1,6)],
[(4,4),(2,2),(6,6),(5,5),(2,2),(1,6)],
[(4,4),(3,3),(4,4),(5,5),(3,3),(1,6)],
[(4,4),(4,4),(3,3),(5,5),(3,3),(1,6)],
[(4,4),(4,4),(3,3),(6,6),(2,2),(1,6)],
[(5,5),(2,2),(4,4),(4,4),(4,4),(1,6)],
[(5,5),(3,3),(3,3),(5,5),(3,3),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(4,4),(1,6)],
[(1,6),(2,2),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(3,3),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(4,4),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(5,5),(2,2),(2,2),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(6,6),(2,2),(3,3)],
[(1,6),(1,6),(1,1),(6,6),(2,2),(4,4)],
[(1,6),(1,6),(1,1),(6,6),(2,2),(5,5)],
[(1,6),(1,6),(1,1),(6,6),(3,3),(3,3)],
[(1,6),(1,6),(1,1),(6,6),(4,4),(3,3)],
[(1,6),(2,2),(4,4),(2,2),(5,5),(1,6)],
[(1,6),(3,3),(3,3),(2,2),(4,4),(1,6)],
[(1,6),(3,3),(3,3),(2,2),(5,5),(1,6)],
[(1,6),(5,5),(2,2),(3,3),(5,5),(1,6)],
[(1,6),(5,5),(2,2),(4,4),(2,2),(1,6)],
[(1,6),(5,5),(3,3),(2,2),(5,5),(1,6)],
[(3,3),(2,2),(6,6),(1,1),(1,6),(1,6)],
[(3,3),(3,3),(6,6),(1,1),(1,6),(1,6)],
[(3,3),(4,4),(6,6),(1,1),(1,6),(1,6)],
[(3,3),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(4,4),(2,2),(6,6),(1,1),(1,6),(1,6)],
[(4,4),(6,6),(2,2),(2,2),(1,6),(1,6)],
[(5,5),(2,2),(6,6),(1,1),(1,6),(1,6)],
[(1,6),(2,2),(4,4),(4,4),(3,3),(5,5)],
[(1,6),(2,2),(4,4),(5,5),(2,2),(4,4)],
[(1,6),(2,2),(4,4),(5,5),(3,3),(4,4)],
[(1,6),(2,2),(4,4),(6,6),(2,2),(4,4)],
[(1,6),(2,2),(4,4),(6,6),(2,2),(5,5)],
[(1,6),(2,2),(4,4),(6,6),(3,3),(4,4)],
[(1,6),(3,3),(3,3),(4,4),(2,2),(6,6)],
[(1,6),(3,3),(3,3),(4,4),(5,5),(3,3)],
[(1,6),(3,3),(3,3),(4,4),(6,6),(3,3)],
[(1,6),(3,3),(3,3),(6,6),(2,2),(4,4)],
[(1,6),(3,3),(4,4),(4,4),(5,5),(3,3)],
[(1,6),(4,4),(3,3),(4,4),(5,5),(3,3)],
[(1,6),(4,4),(4,4),(2,2),(3,3),(6,6)],
[(1,6),(5,5),(4,4),(2,2),(3,3),(6,6)],
[(1,6),(6,6),(1,1),(6,6),(2,2),(6,6)],
[(1,6),(6,6),(1,1),(6,6),(3,3),(4,4)],
[(3,3),(5,5),(4,4),(3,3),(3,3),(1,6)],
[(3,3),(5,5),(4,4),(3,3),(4,4),(1,6)],
[(3,3),(5,5),(4,4),(4,4),(3,3),(1,6)],
[(3,3),(6,6),(4,4),(3,3),(3,3),(1,6)],
[(4,4),(2,2),(5,5),(4,4),(2,2),(1,6)],
[(4,4),(2,2),(6,6),(3,3),(3,3),(1,6)],
[(4,4),(2,2),(6,6),(4,4),(2,2),(1,6)],
[(4,4),(3,3),(5,5),(4,4),(2,2),(1,6)],
[(4,4),(3,3),(6,6),(1,1),(6,6),(1,6)],
[(4,4),(3,3),(6,6),(4,4),(2,2),(1,6)],
[(5,5),(2,2),(6,6),(4,4),(2,2),(1,6)],
[(5,5),(3,3),(4,4),(4,4),(2,2),(1,6)],
[(6,6),(2,2),(4,4),(3,3),(3,3),(1,6)],
[(6,6),(2,2),(6,6),(1,1),(6,6),(1,6)],
[(6,6),(3,3),(2,2),(4,4),(4,4),(1,6)],
[(6,6),(3,3),(2,2),(4,4),(5,5),(1,6)],
[(1,6),(2,2),(3,3),(4,4),(2,2),(1,6)],
[(1,6),(2,2),(3,3),(5,5),(2,2),(1,6)],
[(1,6),(2,2),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(2,2),(4,4),(2,2),(4,4),(1,6)],
[(1,6),(2,2),(4,4),(3,3),(2,2),(1,6)],
[(1,6),(2,2),(5,5),(2,2),(3,3),(1,6)],
[(1,6),(2,2),(5,5),(3,3),(2,2),(1,6)],
[(1,6),(3,3),(2,2),(4,4),(2,2),(1,6)],
[(1,6),(3,3),(2,2),(4,4),(3,3),(1,6)],
[(1,6),(3,3),(2,2),(5,5),(2,2),(1,6)],
[(1,6),(3,3),(4,4),(2,2),(3,3),(1,6)],
[(1,6),(4,4),(2,2),(4,4),(2,2),(1,6)],
[(1,6),(4,4),(3,3),(2,2),(5,5),(1,6)],
[(1,6),(4,4),(5,5),(1,1),(5,5),(1,6)],
[(1,6),(5,5),(1,1),(5,5),(4,4),(1,6)],
[(1,6),(5,5),(2,2),(3,3),(4,4),(1,6)],
[(1,6),(2,2),(2,2),(6,6),(2,2),(5,5)],
[(1,6),(2,2),(2,2),(6,6),(2,2),(6,6)],
[(1,6),(2,2),(2,2),(6,6),(3,3),(4,4)],
[(1,6),(2,2),(2,2),(6,6),(3,3),(5,5)],
[(1,6),(2,2),(2,2),(6,6),(3,3),(6,6)],
[(1,6),(2,2),(3,3),(4,4),(3,3),(5,5)],
[(1,6),(2,2),(3,3),(4,4),(3,3),(6,6)],
[(1,6),(2,2),(3,3),(5,5),(3,3),(4,4)],
[(1,6),(2,2),(3,3),(6,6),(2,2),(4,4)],
[(1,6),(2,2),(3,3),(6,6),(2,2),(5,5)],
[(1,6),(2,2),(3,3),(6,6),(2,2),(6,6)],
[(1,6),(2,2),(3,3),(6,6),(3,3),(4,4)],
[(1,6),(2,2),(4,4),(2,2),(6,6),(4,4)],
[(1,6),(2,2),(4,4),(2,2),(6,6),(5,5)],
[(1,6),(2,2),(4,4),(3,3),(4,4),(5,5)],
[(1,6),(2,2),(5,5),(2,2),(4,4),(5,5)],
[(1,6),(2,2),(5,5),(3,3),(3,3),(5,5)],
[(1,6),(2,2),(5,5),(3,3),(4,4),(4,4)],
[(1,6),(3,3),(2,2),(5,5),(4,4),(4,4)],
[(1,6),(3,3),(2,2),(6,6),(2,2),(6,6)],
[(1,6),(3,3),(5,5),(2,2),(4,4),(5,5)],
[(4,4),(2,2),(6,6),(3,3),(2,2),(1,6)],
[(4,4),(3,3),(5,5),(3,3),(2,2),(1,6)],
[(4,4),(3,3),(6,6),(2,2),(2,2),(1,6)],
[(4,4),(3,3),(6,6),(3,3),(2,2),(1,6)],
[(4,4),(4,4),(3,3),(5,5),(2,2),(1,6)],
[(4,4),(4,4),(5,5),(2,2),(3,3),(1,6)],
[(4,4),(6,6),(2,2),(4,4),(2,2),(1,6)],
[(5,5),(2,2),(6,6),(2,2),(2,2),(1,6)],
[(5,5),(2,2),(6,6),(3,3),(2,2),(1,6)],
[(5,5),(3,3),(3,3),(5,5),(2,2),(1,6)],
[(5,5),(3,3),(4,4),(3,3),(2,2),(1,6)],
[(5,5),(3,3),(6,6),(2,2),(2,2),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(2,2),(1,6)],
[(5,5),(4,4),(2,2),(5,5),(3,3),(1,6)],
[(5,5),(4,4),(3,3),(4,4),(2,2),(1,6)],
[(5,5),(6,6),(2,2),(4,4),(2,2),(1,6)],
[(6,6),(2,2),(6,6),(2,2),(2,2),(1,6)],
[(6,6),(2,2),(6,6),(2,2),(3,3),(1,6)],
[(6,6),(2,2),(6,6),(3,3),(2,2),(1,6)],
[(6,6),(3,3),(4,4),(3,3),(2,2),(1,6)],
[(6,6),(3,3),(6,6),(2,2),(2,2),(1,6)]
]

def root016 : Nat := 2162

def tree016_0 : CoverTree := CoverTree.reject 75
def tree016_1 : CoverTree := CoverTree.reject 70
def tree016_2 : CoverTree := CoverTree.reject 47
def tree016_3 : CoverTree := CoverTree.reject 35
def tree016_4 : CoverTree := CoverTree.reject 10
def tree016_5 : CoverTree := CoverTree.reject 87
def tree016_6 : CoverTree := CoverTree.reject 85
def tree016_7 : CoverTree := CoverTree.reject 7
def tree016_8 : CoverTree := CoverTree.reject 151
def tree016_9 : CoverTree := CoverTree.reject 2
def tree016_10 : CoverTree := CoverTree.reject 30
def tree016_11 : CoverTree := CoverTree.reject 108
def tree016_12 : CoverTree := CoverTree.accept
def tree016_13 : CoverTree := CoverTree.split [tree016_10,tree016_11,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_14 : CoverTree := CoverTree.reject 88
def tree016_15 : CoverTree := CoverTree.split [tree016_14,tree016_12,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_16 : CoverTree := CoverTree.reject 72
def tree016_17 : CoverTree := CoverTree.split [tree016_16,tree016_12,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_18 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_13,tree016_15,tree016_17]
def tree016_19 : CoverTree := CoverTree.split [tree016_10,tree016_12,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_20 : CoverTree := CoverTree.reject 86
def tree016_21 : CoverTree := CoverTree.split [tree016_20,tree016_12,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_22 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_19,tree016_21,tree016_12]
def tree016_23 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_19,tree016_12,tree016_12]
def tree016_24 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_8,tree016_18,tree016_22,tree016_23]
def tree016_25 : CoverTree := CoverTree.split [tree016_4,tree016_4,tree016_4,tree016_5,tree016_6,tree016_24]
def tree016_26 : CoverTree := CoverTree.reject 65
def tree016_27 : CoverTree := CoverTree.reject 3
def tree016_28 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_12,tree016_12,tree016_12]
def tree016_29 : CoverTree := CoverTree.reject 71
def tree016_30 : CoverTree := CoverTree.split [tree016_29,tree016_12,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_31 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_28,tree016_28,tree016_30]
def tree016_32 : CoverTree := CoverTree.reject 12
def tree016_33 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_34 : CoverTree := CoverTree.reject 136
def tree016_35 : CoverTree := CoverTree.split [tree016_14,tree016_34,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_36 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_33,tree016_35,tree016_17]
def tree016_37 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_33,tree016_21,tree016_12]
def tree016_38 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_31,tree016_36,tree016_37,tree016_23]
def tree016_39 : CoverTree := CoverTree.reject 105
def tree016_40 : CoverTree := CoverTree.reject 91
def tree016_41 : CoverTree := CoverTree.split [tree016_10,tree016_39,tree016_40,tree016_12,tree016_12,tree016_12]
def tree016_42 : CoverTree := CoverTree.reject 106
def tree016_43 : CoverTree := CoverTree.reject 107
def tree016_44 : CoverTree := CoverTree.split [tree016_42,tree016_43,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_45 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_41,tree016_44,tree016_30]
def tree016_46 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_45,tree016_18,tree016_22,tree016_23]
def tree016_47 : CoverTree := CoverTree.split [tree016_4,tree016_4,tree016_4,tree016_26,tree016_38,tree016_46]
def tree016_48 : CoverTree := CoverTree.split [tree016_0,tree016_1,tree016_2,tree016_3,tree016_25,tree016_47]
def tree016_49 : CoverTree := CoverTree.reject 78
def tree016_50 : CoverTree := CoverTree.reject 189
def tree016_51 : CoverTree := CoverTree.reject 190
def tree016_52 : CoverTree := CoverTree.reject 202
def tree016_53 : CoverTree := CoverTree.reject 203
def tree016_54 : CoverTree := CoverTree.reject 267
def tree016_55 : CoverTree := CoverTree.reject 1
def tree016_56 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_12,tree016_12,tree016_12]
def tree016_57 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_54,tree016_56,tree016_56]
def tree016_58 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_56,tree016_56,tree016_56]
def tree016_59 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_52,tree016_53,tree016_57,tree016_58]
def tree016_60 : CoverTree := CoverTree.split [tree016_4,tree016_4,tree016_4,tree016_50,tree016_51,tree016_59]
def tree016_61 : CoverTree := CoverTree.reject 147
def tree016_62 : CoverTree := CoverTree.reject 148
def tree016_63 : CoverTree := CoverTree.reject 268
def tree016_64 : CoverTree := CoverTree.reject 8
def tree016_65 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_66 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_63,tree016_65,tree016_65]
def tree016_67 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_65,tree016_65,tree016_65]
def tree016_68 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_66,tree016_67,tree016_67,tree016_67]
def tree016_69 : CoverTree := CoverTree.split [tree016_4,tree016_4,tree016_4,tree016_61,tree016_62,tree016_68]
def tree016_70 : CoverTree := CoverTree.reject 109
def tree016_71 : CoverTree := CoverTree.reject 11
def tree016_72 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_71,tree016_71,tree016_71,tree016_23]
def tree016_73 : CoverTree := CoverTree.split [tree016_4,tree016_4,tree016_4,tree016_70,tree016_72,tree016_46]
def tree016_74 : CoverTree := CoverTree.reject 34
def tree016_75 : CoverTree := CoverTree.reject 137
def tree016_76 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_74,tree016_74,tree016_75,tree016_23]
def tree016_77 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_74,tree016_74,tree016_37,tree016_23]
def tree016_78 : CoverTree := CoverTree.split [tree016_4,tree016_4,tree016_4,tree016_76,tree016_77,tree016_46]
def tree016_79 : CoverTree := CoverTree.reject 204
def tree016_80 : CoverTree := CoverTree.reject 36
def tree016_81 : CoverTree := CoverTree.split [tree016_80,tree016_80,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_82 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_33,tree016_81,tree016_17]
def tree016_83 : CoverTree := CoverTree.split [tree016_9,tree016_9,tree016_9,tree016_33,tree016_81,tree016_12]
def tree016_84 : CoverTree := CoverTree.split [tree016_7,tree016_7,tree016_79,tree016_82,tree016_83,tree016_23]
def tree016_85 : CoverTree := CoverTree.split [tree016_4,tree016_4,tree016_4,tree016_84,tree016_38,tree016_46]
def tree016_86 : CoverTree := CoverTree.split [tree016_49,tree016_60,tree016_69,tree016_73,tree016_78,tree016_85]
def tree016_87 : CoverTree := CoverTree.reject 21
def tree016_88 : CoverTree := CoverTree.reject 29
def tree016_89 : CoverTree := CoverTree.reject 149
def tree016_90 : CoverTree := CoverTree.reject 150
def tree016_91 : CoverTree := CoverTree.reject 69
def tree016_92 : CoverTree := CoverTree.reject 61
def tree016_93 : CoverTree := CoverTree.reject 292
def tree016_94 : CoverTree := CoverTree.reject 205
def tree016_95 : CoverTree := CoverTree.reject 171
def tree016_96 : CoverTree := CoverTree.reject 5
def tree016_97 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_56,tree016_56,tree016_56,tree016_56]
def tree016_98 : CoverTree := CoverTree.reject 247
def tree016_99 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_98,tree016_12,tree016_12]
def tree016_100 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_99,tree016_56,tree016_56,tree016_56]
def tree016_101 : CoverTree := CoverTree.split [tree016_93,tree016_94,tree016_95,tree016_97,tree016_100,tree016_97]
def tree016_102 : CoverTree := CoverTree.split [tree016_88,tree016_89,tree016_90,tree016_91,tree016_92,tree016_101]
def tree016_103 : CoverTree := CoverTree.reject 26
def tree016_104 : CoverTree := CoverTree.reject 120
def tree016_105 : CoverTree := CoverTree.reject 121
def tree016_106 : CoverTree := CoverTree.reject 51
def tree016_107 : CoverTree := CoverTree.reject 93
def tree016_108 : CoverTree := CoverTree.reject 206
def tree016_109 : CoverTree := CoverTree.reject 158
def tree016_110 : CoverTree := CoverTree.reject 132
def tree016_111 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_65,tree016_65,tree016_65,tree016_65]
def tree016_112 : CoverTree := CoverTree.reject 248
def tree016_113 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_112,tree016_12,tree016_12,tree016_12]
def tree016_114 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_113,tree016_65,tree016_65,tree016_65]
def tree016_115 : CoverTree := CoverTree.split [tree016_107,tree016_108,tree016_109,tree016_110,tree016_111,tree016_114]
def tree016_116 : CoverTree := CoverTree.reject 293
def tree016_117 : CoverTree := CoverTree.reject 182
def tree016_118 : CoverTree := CoverTree.reject 119
def tree016_119 : CoverTree := CoverTree.reject 37
def tree016_120 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_118,tree016_119,tree016_12,tree016_12]
def tree016_121 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_40,tree016_12,tree016_12,tree016_12]
def tree016_122 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_120,tree016_121,tree016_65,tree016_65]
def tree016_123 : CoverTree := CoverTree.reject 50
def tree016_124 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_123,tree016_12,tree016_12,tree016_12]
def tree016_125 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_124,tree016_65,tree016_65,tree016_65]
def tree016_126 : CoverTree := CoverTree.reject 250
def tree016_127 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_126,tree016_65,tree016_65,tree016_65]
def tree016_128 : CoverTree := CoverTree.split [tree016_116,tree016_117,tree016_122,tree016_125,tree016_127,tree016_111]
def tree016_129 : CoverTree := CoverTree.split [tree016_103,tree016_104,tree016_105,tree016_106,tree016_115,tree016_128]
def tree016_130 : CoverTree := CoverTree.reject 27
def tree016_131 : CoverTree := CoverTree.reject 122
def tree016_132 : CoverTree := CoverTree.reject 92
def tree016_133 : CoverTree := CoverTree.reject 14
def tree016_134 : CoverTree := CoverTree.reject 228
def tree016_135 : CoverTree := CoverTree.reject 172
def tree016_136 : CoverTree := CoverTree.reject 111
def tree016_137 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_123,tree016_136,tree016_12,tree016_12]
def tree016_138 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_137,tree016_33,tree016_81,tree016_17]
def tree016_139 : CoverTree := CoverTree.reject 131
def tree016_140 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_139,tree016_12,tree016_12,tree016_12]
def tree016_141 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_140,tree016_33,tree016_81,tree016_12]
def tree016_142 : CoverTree := CoverTree.reject 41
def tree016_143 : CoverTree := CoverTree.split [tree016_142,tree016_12,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_144 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_143,tree016_19,tree016_12,tree016_12]
def tree016_145 : CoverTree := CoverTree.split [tree016_133,tree016_134,tree016_135,tree016_138,tree016_141,tree016_144]
def tree016_146 : CoverTree := CoverTree.reject 207
def tree016_147 : CoverTree := CoverTree.reject 140
def tree016_148 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_123,tree016_12,tree016_12,tree016_12]
def tree016_149 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_148,tree016_33,tree016_35,tree016_17]
def tree016_150 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_33,tree016_33,tree016_21,tree016_12]
def tree016_151 : CoverTree := CoverTree.split [tree016_107,tree016_146,tree016_147,tree016_149,tree016_150,tree016_144]
def tree016_152 : CoverTree := CoverTree.reject 294
def tree016_153 : CoverTree := CoverTree.reject 15
def tree016_154 : CoverTree := CoverTree.reject 116
def tree016_155 : CoverTree := CoverTree.reject 96
def tree016_156 : CoverTree := CoverTree.reject 66
def tree016_157 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_154,tree016_155,tree016_156,tree016_12]
def tree016_158 : CoverTree := CoverTree.reject 117
def tree016_159 : CoverTree := CoverTree.reject 97
def tree016_160 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_158,tree016_159,tree016_12,tree016_12]
def tree016_161 : CoverTree := CoverTree.reject 118
def tree016_162 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_161,tree016_12,tree016_12,tree016_12]
def tree016_163 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_164 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_157,tree016_160,tree016_162,tree016_163]
def tree016_165 : CoverTree := CoverTree.reject 144
def tree016_166 : CoverTree := CoverTree.split [tree016_142,tree016_165,tree016_118,tree016_119,tree016_12,tree016_12]
def tree016_167 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_166,tree016_41,tree016_44,tree016_30]
def tree016_168 : CoverTree := CoverTree.reject 145
def tree016_169 : CoverTree := CoverTree.split [tree016_142,tree016_168,tree016_123,tree016_12,tree016_12,tree016_12]
def tree016_170 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_169,tree016_13,tree016_15,tree016_17]
def tree016_171 : CoverTree := CoverTree.reject 146
def tree016_172 : CoverTree := CoverTree.split [tree016_142,tree016_171,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_173 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_172,tree016_19,tree016_21,tree016_12]
def tree016_174 : CoverTree := CoverTree.split [tree016_152,tree016_164,tree016_167,tree016_170,tree016_173,tree016_144]
def tree016_175 : CoverTree := CoverTree.split [tree016_130,tree016_131,tree016_132,tree016_145,tree016_151,tree016_174]
def tree016_176 : CoverTree := CoverTree.reject 123
def tree016_177 : CoverTree := CoverTree.reject 124
def tree016_178 : CoverTree := CoverTree.reject 0
def tree016_179 : CoverTree := CoverTree.reject 170
def tree016_180 : CoverTree := CoverTree.split [tree016_179,tree016_12,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_181 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_143,tree016_19,tree016_180,tree016_12]
def tree016_182 : CoverTree := CoverTree.split [tree016_178,tree016_178,tree016_178,tree016_178,tree016_178,tree016_181]
def tree016_183 : CoverTree := CoverTree.reject 229
def tree016_184 : CoverTree := CoverTree.reject 315
def tree016_185 : CoverTree := CoverTree.reject 316
def tree016_186 : CoverTree := CoverTree.reject 139
def tree016_187 : CoverTree := CoverTree.split [tree016_29,tree016_186,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_188 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_184,tree016_185,tree016_28,tree016_187]
def tree016_189 : CoverTree := CoverTree.reject 317
def tree016_190 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_189,tree016_33,tree016_81,tree016_17]
def tree016_191 : CoverTree := CoverTree.split [tree016_133,tree016_183,tree016_188,tree016_190,tree016_141,tree016_144]
def tree016_192 : CoverTree := CoverTree.reject 208
def tree016_193 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_119,tree016_12,tree016_12]
def tree016_194 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_193,tree016_28,tree016_28,tree016_30]
def tree016_195 : CoverTree := CoverTree.split [tree016_107,tree016_192,tree016_194,tree016_149,tree016_150,tree016_144]
def tree016_196 : CoverTree := CoverTree.reject 23
def tree016_197 : CoverTree := CoverTree.reject 24
def tree016_198 : CoverTree := CoverTree.reject 115
def tree016_199 : CoverTree := CoverTree.reject 95
def tree016_200 : CoverTree := CoverTree.reject 83
def tree016_201 : CoverTree := CoverTree.reject 101
def tree016_202 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_198,tree016_199,tree016_200,tree016_201]
def tree016_203 : CoverTree := CoverTree.reject 81
def tree016_204 : CoverTree := CoverTree.reject 73
def tree016_205 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_203,tree016_204,tree016_12,tree016_12]
def tree016_206 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_196,tree016_197,tree016_202,tree016_205]
def tree016_207 : CoverTree := CoverTree.split [tree016_206,tree016_164,tree016_167,tree016_170,tree016_173,tree016_144]
def tree016_208 : CoverTree := CoverTree.split [tree016_176,tree016_177,tree016_182,tree016_191,tree016_195,tree016_207]
def tree016_209 : CoverTree := CoverTree.reject 82
def tree016_210 : CoverTree := CoverTree.reject 90
def tree016_211 : CoverTree := CoverTree.reject 295
def tree016_212 : CoverTree := CoverTree.reject 183
def tree016_213 : CoverTree := CoverTree.reject 133
def tree016_214 : CoverTree := CoverTree.reject 4
def tree016_215 : CoverTree := CoverTree.reject 191
def tree016_216 : CoverTree := CoverTree.reject 192
def tree016_217 : CoverTree := CoverTree.reject 193
def tree016_218 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_215,tree016_216,tree016_217,tree016_12]
def tree016_219 : CoverTree := CoverTree.reject 194
def tree016_220 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_219,tree016_12,tree016_12,tree016_12]
def tree016_221 : CoverTree := CoverTree.reject 195
def tree016_222 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_221,tree016_12,tree016_12,tree016_12]
def tree016_223 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_224 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_218,tree016_220,tree016_222,tree016_223]
def tree016_225 : CoverTree := CoverTree.reject 178
def tree016_226 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_225,tree016_12,tree016_12,tree016_12]
def tree016_227 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_226,tree016_223,tree016_223,tree016_223]
def tree016_228 : CoverTree := CoverTree.split [tree016_210,tree016_211,tree016_212,tree016_213,tree016_224,tree016_227]
def tree016_229 : CoverTree := CoverTree.reject 40
def tree016_230 : CoverTree := CoverTree.reject 164
def tree016_231 : CoverTree := CoverTree.reject 6
def tree016_232 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_231,tree016_231,tree016_12]
def tree016_233 : CoverTree := CoverTree.reject 179
def tree016_234 : CoverTree := CoverTree.reject 166
def tree016_235 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_233,tree016_234,tree016_12,tree016_12]
def tree016_236 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_230,tree016_232,tree016_232,tree016_235]
def tree016_237 : CoverTree := CoverTree.reject 180
def tree016_238 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_119,tree016_237,tree016_12]
def tree016_239 : CoverTree := CoverTree.reject 181
def tree016_240 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_239,tree016_12,tree016_12]
def tree016_241 : CoverTree := CoverTree.reject 198
def tree016_242 : CoverTree := CoverTree.split [tree016_29,tree016_241,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_243 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_238,tree016_240,tree016_28,tree016_242]
def tree016_244 : CoverTree := CoverTree.reject 152
def tree016_245 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_123,tree016_244,tree016_12,tree016_12]
def tree016_246 : CoverTree := CoverTree.reject 168
def tree016_247 : CoverTree := CoverTree.reject 153
def tree016_248 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_246,tree016_247,tree016_12,tree016_12]
def tree016_249 : CoverTree := CoverTree.reject 199
def tree016_250 : CoverTree := CoverTree.split [tree016_16,tree016_249,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_251 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_245,tree016_248,tree016_81,tree016_250]
def tree016_252 : CoverTree := CoverTree.reject 156
def tree016_253 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_252,tree016_12,tree016_12,tree016_12]
def tree016_254 : CoverTree := CoverTree.reject 157
def tree016_255 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_254,tree016_12,tree016_12,tree016_12]
def tree016_256 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_253,tree016_255,tree016_81,tree016_12]
def tree016_257 : CoverTree := CoverTree.split [tree016_229,tree016_236,tree016_243,tree016_251,tree016_256,tree016_181]
def tree016_258 : CoverTree := CoverTree.reject 19
def tree016_259 : CoverTree := CoverTree.reject 249
def tree016_260 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_156,tree016_259]
def tree016_261 : CoverTree := CoverTree.reject 110
def tree016_262 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_261,tree016_12]
def tree016_263 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_12,tree016_12]
def tree016_264 : CoverTree := CoverTree.reject 130
def tree016_265 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_264,tree016_12,tree016_12,tree016_12]
def tree016_266 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_260,tree016_262,tree016_263,tree016_265]
def tree016_267 : CoverTree := CoverTree.reject 318
def tree016_268 : CoverTree := CoverTree.reject 103
def tree016_269 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_268,tree016_12,tree016_12]
def tree016_270 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_267,tree016_269,tree016_28,tree016_187]
def tree016_271 : CoverTree := CoverTree.split [tree016_133,tree016_266,tree016_270,tree016_138,tree016_141,tree016_144]
def tree016_272 : CoverTree := CoverTree.reject 255
def tree016_273 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_156,tree016_12]
def tree016_274 : CoverTree := CoverTree.split [tree016_96,tree016_96,tree016_273,tree016_263,tree016_263,tree016_163]
def tree016_275 : CoverTree := CoverTree.split [tree016_272,tree016_274,tree016_194,tree016_149,tree016_150,tree016_144]
def tree016_276 : CoverTree := CoverTree.split [tree016_209,tree016_228,tree016_257,tree016_271,tree016_275,tree016_207]
def tree016_277 : CoverTree := CoverTree.split [tree016_87,tree016_102,tree016_129,tree016_175,tree016_208,tree016_276]
def tree016_278 : CoverTree := CoverTree.reject 17
def tree016_279 : CoverTree := CoverTree.reject 129
def tree016_280 : CoverTree := CoverTree.reject 58
def tree016_281 : CoverTree := CoverTree.reject 52
def tree016_282 : CoverTree := CoverTree.reject 217
def tree016_283 : CoverTree := CoverTree.reject 159
def tree016_284 : CoverTree := CoverTree.reject 25
def tree016_285 : CoverTree := CoverTree.reject 319
def tree016_286 : CoverTree := CoverTree.reject 269
def tree016_287 : CoverTree := CoverTree.split [tree016_284,tree016_285,tree016_286,tree016_56,tree016_56,tree016_56]
def tree016_288 : CoverTree := CoverTree.reject 13
def tree016_289 : CoverTree := CoverTree.reject 45
def tree016_290 : CoverTree := CoverTree.reject 46
def tree016_291 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_288,tree016_289,tree016_290]
def tree016_292 : CoverTree := CoverTree.split [tree016_291,tree016_56,tree016_56,tree016_56,tree016_56,tree016_56]
def tree016_293 : CoverTree := CoverTree.reject 43
def tree016_294 : CoverTree := CoverTree.reject 44
def tree016_295 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_288,tree016_293,tree016_294]
def tree016_296 : CoverTree := CoverTree.reject 257
def tree016_297 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_296,tree016_12,tree016_12]
def tree016_298 : CoverTree := CoverTree.split [tree016_295,tree016_297,tree016_56,tree016_56,tree016_56,tree016_56]
def tree016_299 : CoverTree := CoverTree.split [tree016_107,tree016_282,tree016_283,tree016_287,tree016_292,tree016_298]
def tree016_300 : CoverTree := CoverTree.reject 296
def tree016_301 : CoverTree := CoverTree.reject 184
def tree016_302 : CoverTree := CoverTree.reject 22
def tree016_303 : CoverTree := CoverTree.reject 368
def tree016_304 : CoverTree := CoverTree.reject 320
def tree016_305 : CoverTree := CoverTree.reject 258
def tree016_306 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_305,tree016_12,tree016_12]
def tree016_307 : CoverTree := CoverTree.split [tree016_302,tree016_303,tree016_304,tree016_306,tree016_56,tree016_56]
def tree016_308 : CoverTree := CoverTree.reject 321
def tree016_309 : CoverTree := CoverTree.split [tree016_284,tree016_308,tree016_56,tree016_56,tree016_56,tree016_56]
def tree016_310 : CoverTree := CoverTree.reject 270
def tree016_311 : CoverTree := CoverTree.split [tree016_291,tree016_310,tree016_99,tree016_56,tree016_56,tree016_56]
def tree016_312 : CoverTree := CoverTree.split [tree016_295,tree016_56,tree016_56,tree016_56,tree016_56,tree016_56]
def tree016_313 : CoverTree := CoverTree.split [tree016_300,tree016_301,tree016_307,tree016_309,tree016_311,tree016_312]
def tree016_314 : CoverTree := CoverTree.split [tree016_88,tree016_279,tree016_280,tree016_281,tree016_299,tree016_313]
def tree016_315 : CoverTree := CoverTree.reject 98
def tree016_316 : CoverTree := CoverTree.reject 39
def tree016_317 : CoverTree := CoverTree.reject 230
def tree016_318 : CoverTree := CoverTree.reject 160
def tree016_319 : CoverTree := CoverTree.reject 125
def tree016_320 : CoverTree := CoverTree.reject 20
def tree016_321 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_320,tree016_288,tree016_289,tree016_290]
def tree016_322 : CoverTree := CoverTree.reject 60
def tree016_323 : CoverTree := CoverTree.reject 259
def tree016_324 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_322,tree016_323,tree016_12,tree016_12]
def tree016_325 : CoverTree := CoverTree.reject 271
def tree016_326 : CoverTree := CoverTree.split [tree016_321,tree016_324,tree016_325,tree016_65,tree016_65,tree016_65]
def tree016_327 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_320,tree016_288,tree016_293,tree016_294]
def tree016_328 : CoverTree := CoverTree.split [tree016_327,tree016_65,tree016_65,tree016_65,tree016_65,tree016_65]
def tree016_329 : CoverTree := CoverTree.split [tree016_133,tree016_317,tree016_318,tree016_319,tree016_326,tree016_328]
def tree016_330 : CoverTree := CoverTree.reject 209
def tree016_331 : CoverTree := CoverTree.reject 369
def tree016_332 : CoverTree := CoverTree.reject 260
def tree016_333 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_119,tree016_332,tree016_12]
def tree016_334 : CoverTree := CoverTree.reject 261
def tree016_335 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_334,tree016_12,tree016_12]
def tree016_336 : CoverTree := CoverTree.split [tree016_302,tree016_331,tree016_333,tree016_335,tree016_28,tree016_65]
def tree016_337 : CoverTree := CoverTree.reject 322
def tree016_338 : CoverTree := CoverTree.reject 262
def tree016_339 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_123,tree016_338,tree016_12,tree016_12]
def tree016_340 : CoverTree := CoverTree.split [tree016_284,tree016_337,tree016_339,tree016_65,tree016_65,tree016_65]
def tree016_341 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_322,tree016_12,tree016_12,tree016_12]
def tree016_342 : CoverTree := CoverTree.split [tree016_321,tree016_341,tree016_65,tree016_65,tree016_65,tree016_65]
def tree016_343 : CoverTree := CoverTree.reject 251
def tree016_344 : CoverTree := CoverTree.split [tree016_327,tree016_343,tree016_113,tree016_65,tree016_65,tree016_65]
def tree016_345 : CoverTree := CoverTree.split [tree016_107,tree016_330,tree016_336,tree016_340,tree016_342,tree016_344]
def tree016_346 : CoverTree := CoverTree.reject 48
def tree016_347 : CoverTree := CoverTree.reject 33
def tree016_348 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_198,tree016_199,tree016_200,tree016_201]
def tree016_349 : CoverTree := CoverTree.reject 323
def tree016_350 : CoverTree := CoverTree.split [tree016_346,tree016_347,tree016_196,tree016_197,tree016_348,tree016_349]
def tree016_351 : CoverTree := CoverTree.reject 32
def tree016_352 : CoverTree := CoverTree.reject 370
def tree016_353 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_154,tree016_155,tree016_156,tree016_12]
def tree016_354 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_158,tree016_159,tree016_12,tree016_12]
def tree016_355 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_161,tree016_12,tree016_12,tree016_12]
def tree016_356 : CoverTree := CoverTree.split [tree016_351,tree016_352,tree016_353,tree016_354,tree016_355,tree016_65]
def tree016_357 : CoverTree := CoverTree.reject 371
def tree016_358 : CoverTree := CoverTree.split [tree016_302,tree016_357,tree016_120,tree016_121,tree016_65,tree016_65]
def tree016_359 : CoverTree := CoverTree.reject 324
def tree016_360 : CoverTree := CoverTree.split [tree016_284,tree016_359,tree016_124,tree016_65,tree016_65,tree016_65]
def tree016_361 : CoverTree := CoverTree.split [tree016_350,tree016_356,tree016_358,tree016_360,tree016_342,tree016_328]
def tree016_362 : CoverTree := CoverTree.split [tree016_103,tree016_315,tree016_316,tree016_329,tree016_345,tree016_361]
def tree016_363 : CoverTree := CoverTree.reject 99
def tree016_364 : CoverTree := CoverTree.reject 113
def tree016_365 : CoverTree := CoverTree.reject 138
def tree016_366 : CoverTree := CoverTree.reject 104
def tree016_367 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_320,tree016_288,tree016_289,tree016_290]
def tree016_368 : CoverTree := CoverTree.reject 372
def tree016_369 : CoverTree := CoverTree.reject 272
def tree016_370 : CoverTree := CoverTree.split [tree016_367,tree016_368,tree016_369,tree016_255,tree016_81,tree016_12]
def tree016_371 : CoverTree := CoverTree.reject 76
def tree016_372 : CoverTree := CoverTree.reject 77
def tree016_373 : CoverTree := CoverTree.split [tree016_371,tree016_372,tree016_320,tree016_288,tree016_293,tree016_294]
def tree016_374 : CoverTree := CoverTree.reject 273
def tree016_375 : CoverTree := CoverTree.reject 263
def tree016_376 : CoverTree := CoverTree.split [tree016_142,tree016_375,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_377 : CoverTree := CoverTree.split [tree016_373,tree016_374,tree016_376,tree016_19,tree016_180,tree016_12]
def tree016_378 : CoverTree := CoverTree.split [tree016_229,tree016_364,tree016_365,tree016_366,tree016_370,tree016_377]
def tree016_379 : CoverTree := CoverTree.reject 231
def tree016_380 : CoverTree := CoverTree.reject 161
def tree016_381 : CoverTree := CoverTree.reject 68
def tree016_382 : CoverTree := CoverTree.reject 49
def tree016_383 : CoverTree := CoverTree.reject 264
def tree016_384 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_381,tree016_382,tree016_383,tree016_12]
def tree016_385 : CoverTree := CoverTree.split [tree016_284,tree016_384,tree016_137,tree016_33,tree016_81,tree016_17]
def tree016_386 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_322,tree016_12,tree016_12,tree016_12]
def tree016_387 : CoverTree := CoverTree.split [tree016_367,tree016_386,tree016_140,tree016_33,tree016_81,tree016_12]
def tree016_388 : CoverTree := CoverTree.reject 57
def tree016_389 : CoverTree := CoverTree.reject 201
def tree016_390 : CoverTree := CoverTree.split [tree016_388,tree016_389,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_391 : CoverTree := CoverTree.split [tree016_373,tree016_390,tree016_143,tree016_19,tree016_12,tree016_12]
def tree016_392 : CoverTree := CoverTree.split [tree016_133,tree016_379,tree016_380,tree016_385,tree016_387,tree016_391]
def tree016_393 : CoverTree := CoverTree.reject 127
def tree016_394 : CoverTree := CoverTree.reject 373
def tree016_395 : CoverTree := CoverTree.reject 265
def tree016_396 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_395,tree016_12]
def tree016_397 : CoverTree := CoverTree.split [tree016_351,tree016_393,tree016_394,tree016_396,tree016_263,tree016_163]
def tree016_398 : CoverTree := CoverTree.reject 53
def tree016_399 : CoverTree := CoverTree.reject 54
def tree016_400 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_398,tree016_399,tree016_12]
def tree016_401 : CoverTree := CoverTree.split [tree016_302,tree016_400,tree016_193,tree016_28,tree016_28,tree016_30]
def tree016_402 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_381,tree016_382,tree016_12,tree016_12]
def tree016_403 : CoverTree := CoverTree.split [tree016_284,tree016_402,tree016_148,tree016_33,tree016_35,tree016_17]
def tree016_404 : CoverTree := CoverTree.split [tree016_367,tree016_386,tree016_33,tree016_33,tree016_21,tree016_12]
def tree016_405 : CoverTree := CoverTree.reject 266
def tree016_406 : CoverTree := CoverTree.split [tree016_388,tree016_405,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_407 : CoverTree := CoverTree.split [tree016_373,tree016_406,tree016_143,tree016_19,tree016_12,tree016_12]
def tree016_408 : CoverTree := CoverTree.split [tree016_107,tree016_397,tree016_401,tree016_403,tree016_404,tree016_407]
def tree016_409 : CoverTree := CoverTree.split [tree016_346,tree016_347,tree016_196,tree016_197,tree016_202,tree016_205]
def tree016_410 : CoverTree := CoverTree.reject 142
def tree016_411 : CoverTree := CoverTree.reject 126
def tree016_412 : CoverTree := CoverTree.reject 79
def tree016_413 : CoverTree := CoverTree.split [tree016_153,tree016_153,tree016_410,tree016_411,tree016_412,tree016_12]
def tree016_414 : CoverTree := CoverTree.split [tree016_351,tree016_413,tree016_157,tree016_160,tree016_162,tree016_163]
def tree016_415 : CoverTree := CoverTree.reject 186
def tree016_416 : CoverTree := CoverTree.reject 143
def tree016_417 : CoverTree := CoverTree.split [tree016_388,tree016_415,tree016_416,tree016_398,tree016_399,tree016_12]
def tree016_418 : CoverTree := CoverTree.split [tree016_302,tree016_417,tree016_166,tree016_41,tree016_44,tree016_30]
def tree016_419 : CoverTree := CoverTree.reject 187
def tree016_420 : CoverTree := CoverTree.split [tree016_388,tree016_419,tree016_381,tree016_382,tree016_12,tree016_12]
def tree016_421 : CoverTree := CoverTree.split [tree016_284,tree016_420,tree016_169,tree016_13,tree016_15,tree016_17]
def tree016_422 : CoverTree := CoverTree.split [tree016_371,tree016_372,tree016_320,tree016_288,tree016_289,tree016_290]
def tree016_423 : CoverTree := CoverTree.reject 188
def tree016_424 : CoverTree := CoverTree.split [tree016_388,tree016_423,tree016_322,tree016_12,tree016_12,tree016_12]
def tree016_425 : CoverTree := CoverTree.split [tree016_422,tree016_424,tree016_172,tree016_19,tree016_21,tree016_12]
def tree016_426 : CoverTree := CoverTree.split [tree016_388,tree016_12,tree016_12,tree016_12,tree016_12,tree016_12]
def tree016_427 : CoverTree := CoverTree.split [tree016_373,tree016_426,tree016_143,tree016_19,tree016_12,tree016_12]
def tree016_428 : CoverTree := CoverTree.split [tree016_409,tree016_414,tree016_418,tree016_421,tree016_425,tree016_427]
def tree016_429 : CoverTree := CoverTree.split [tree016_130,tree016_363,tree016_378,tree016_392,tree016_408,tree016_428]
def tree016_430 : CoverTree := CoverTree.reject 100
def tree016_431 : CoverTree := CoverTree.reject 9
def tree016_432 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_320,tree016_288,tree016_293,tree016_294]
def tree016_433 : CoverTree := CoverTree.reject 196
def tree016_434 : CoverTree := CoverTree.reject 177
def tree016_435 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_433,tree016_434,tree016_12,tree016_12]
def tree016_436 : CoverTree := CoverTree.split [tree016_432,tree016_435,tree016_226,tree016_223,tree016_223,tree016_223]
def tree016_437 : CoverTree := CoverTree.split [tree016_431,tree016_431,tree016_431,tree016_431,tree016_431,tree016_436]
def tree016_438 : CoverTree := CoverTree.reject 197
def tree016_439 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_398,tree016_399,tree016_438]
def tree016_440 : CoverTree := CoverTree.split [tree016_302,tree016_439,tree016_238,tree016_240,tree016_28,tree016_242]
def tree016_441 : CoverTree := CoverTree.reject 167
def tree016_442 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_381,tree016_382,tree016_441,tree016_12]
def tree016_443 : CoverTree := CoverTree.split [tree016_284,tree016_442,tree016_245,tree016_248,tree016_81,tree016_250]
def tree016_444 : CoverTree := CoverTree.reject 154
def tree016_445 : CoverTree := CoverTree.reject 155
def tree016_446 : CoverTree := CoverTree.split [tree016_32,tree016_32,tree016_322,tree016_444,tree016_445,tree016_12]
def tree016_447 : CoverTree := CoverTree.split [tree016_367,tree016_446,tree016_253,tree016_255,tree016_81,tree016_12]
def tree016_448 : CoverTree := CoverTree.reject 200
def tree016_449 : CoverTree := CoverTree.reject 169
def tree016_450 : CoverTree := CoverTree.split [tree016_388,tree016_448,tree016_449,tree016_12,tree016_12,tree016_12]
def tree016_451 : CoverTree := CoverTree.split [tree016_373,tree016_450,tree016_143,tree016_19,tree016_180,tree016_12]
def tree016_452 : CoverTree := CoverTree.split [tree016_229,tree016_364,tree016_440,tree016_443,tree016_447,tree016_451]
def tree016_453 : CoverTree := CoverTree.reject 232
def tree016_454 : CoverTree := CoverTree.split [tree016_302,tree016_400,tree016_193,tree016_269,tree016_28,tree016_187]
def tree016_455 : CoverTree := CoverTree.split [tree016_284,tree016_402,tree016_137,tree016_33,tree016_81,tree016_17]
def tree016_456 : CoverTree := CoverTree.split [tree016_133,tree016_453,tree016_454,tree016_455,tree016_387,tree016_391]
def tree016_457 : CoverTree := CoverTree.split [tree016_351,tree016_393,tree016_273,tree016_263,tree016_263,tree016_163]
def tree016_458 : CoverTree := CoverTree.split [tree016_107,tree016_457,tree016_401,tree016_403,tree016_404,tree016_427]
def tree016_459 : CoverTree := CoverTree.split [tree016_430,tree016_437,tree016_452,tree016_456,tree016_458,tree016_428]
def tree016_460 : CoverTree := CoverTree.reject 74
def tree016_461 : CoverTree := CoverTree.reject 297
def tree016_462 : CoverTree := CoverTree.reject 173
def tree016_463 : CoverTree := CoverTree.reject 374
def tree016_464 : CoverTree := CoverTree.reject 222
def tree016_465 : CoverTree := CoverTree.reject 223
def tree016_466 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_123,tree016_464,tree016_465,tree016_12]
def tree016_467 : CoverTree := CoverTree.reject 224
def tree016_468 : CoverTree := CoverTree.reject 225
def tree016_469 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_467,tree016_468,tree016_12,tree016_12]
def tree016_470 : CoverTree := CoverTree.reject 226
def tree016_471 : CoverTree := CoverTree.reject 227
def tree016_472 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_470,tree016_471,tree016_12,tree016_12]
def tree016_473 : CoverTree := CoverTree.split [tree016_284,tree016_463,tree016_466,tree016_469,tree016_472,tree016_223]
def tree016_474 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_320,tree016_288,tree016_289,tree016_290]
def tree016_475 : CoverTree := CoverTree.reject 215
def tree016_476 : CoverTree := CoverTree.reject 216
def tree016_477 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_322,tree016_475,tree016_476,tree016_12]
def tree016_478 : CoverTree := CoverTree.split [tree016_474,tree016_477,tree016_218,tree016_220,tree016_222,tree016_223]
def tree016_479 : CoverTree := CoverTree.split [tree016_210,tree016_461,tree016_462,tree016_473,tree016_478,tree016_436]
def tree016_480 : CoverTree := CoverTree.reject 175
def tree016_481 : CoverTree := CoverTree.split [tree016_351,tree016_480,tree016_230,tree016_232,tree016_232,tree016_235]
def tree016_482 : CoverTree := CoverTree.split [tree016_229,tree016_481,tree016_440,tree016_443,tree016_447,tree016_451]
def tree016_483 : CoverTree := CoverTree.reject 134
def tree016_484 : CoverTree := CoverTree.split [tree016_351,tree016_483,tree016_260,tree016_262,tree016_263,tree016_265]
def tree016_485 : CoverTree := CoverTree.split [tree016_133,tree016_484,tree016_454,tree016_455,tree016_387,tree016_391]
def tree016_486 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_200,tree016_12]
def tree016_487 : CoverTree := CoverTree.split [tree016_346,tree016_347,tree016_196,tree016_197,tree016_486,tree016_205]
def tree016_488 : CoverTree := CoverTree.split [tree016_487,tree016_457,tree016_401,tree016_403,tree016_404,tree016_427]
def tree016_489 : CoverTree := CoverTree.split [tree016_460,tree016_479,tree016_482,tree016_485,tree016_488,tree016_428]
def tree016_490 : CoverTree := CoverTree.split [tree016_278,tree016_314,tree016_362,tree016_429,tree016_459,tree016_489]
def tree016_491 : CoverTree := CoverTree.reject 64
def tree016_492 : CoverTree := CoverTree.reject 38
def tree016_493 : CoverTree := CoverTree.reject 31
def tree016_494 : CoverTree := CoverTree.reject 28
def tree016_495 : CoverTree := CoverTree.reject 62
def tree016_496 : CoverTree := CoverTree.reject 55
def tree016_497 : CoverTree := CoverTree.split [tree016_491,tree016_492,tree016_493,tree016_494,tree016_495,tree016_496]
def tree016_498 : CoverTree := CoverTree.reject 80
def tree016_499 : CoverTree := CoverTree.reject 59
def tree016_500 : CoverTree := CoverTree.reject 233
def tree016_501 : CoverTree := CoverTree.reject 174
def tree016_502 : CoverTree := CoverTree.reject 244
def tree016_503 : CoverTree := CoverTree.reject 299
def tree016_504 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_136,tree016_503,tree016_12]
def tree016_505 : CoverTree := CoverTree.reject 274
def tree016_506 : CoverTree := CoverTree.split [tree016_284,tree016_502,tree016_504,tree016_505,tree016_56,tree016_56]
def tree016_507 : CoverTree := CoverTree.reject 300
def tree016_508 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_507,tree016_12,tree016_12]
def tree016_509 : CoverTree := CoverTree.reject 301
def tree016_510 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_509,tree016_12,tree016_12]
def tree016_511 : CoverTree := CoverTree.split [tree016_291,tree016_508,tree016_510,tree016_56,tree016_56,tree016_56]
def tree016_512 : CoverTree := CoverTree.reject 302
def tree016_513 : CoverTree := CoverTree.reject 303
def tree016_514 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_512,tree016_513,tree016_12]
def tree016_515 : CoverTree := CoverTree.reject 304
def tree016_516 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_515,tree016_12,tree016_12]
def tree016_517 : CoverTree := CoverTree.split [tree016_295,tree016_514,tree016_516,tree016_56,tree016_56,tree016_56]
def tree016_518 : CoverTree := CoverTree.split [tree016_133,tree016_500,tree016_501,tree016_506,tree016_511,tree016_517]
def tree016_519 : CoverTree := CoverTree.reject 237
def tree016_520 : CoverTree := CoverTree.reject 218
def tree016_521 : CoverTree := CoverTree.reject 162
def tree016_522 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_382,tree016_12,tree016_12]
def tree016_523 : CoverTree := CoverTree.split [tree016_284,tree016_522,tree016_56,tree016_56,tree016_56,tree016_56]
def tree016_524 : CoverTree := CoverTree.split [tree016_519,tree016_520,tree016_521,tree016_523,tree016_292,tree016_298]
def tree016_525 : CoverTree := CoverTree.reject 298
def tree016_526 : CoverTree := CoverTree.reject 375
def tree016_527 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_155,tree016_156,tree016_12]
def tree016_528 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_159,tree016_12,tree016_12]
def tree016_529 : CoverTree := CoverTree.split [tree016_351,tree016_526,tree016_527,tree016_528,tree016_56,tree016_56]
def tree016_530 : CoverTree := CoverTree.reject 376
def tree016_531 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_119,tree016_12,tree016_12]
def tree016_532 : CoverTree := CoverTree.split [tree016_302,tree016_530,tree016_531,tree016_306,tree016_56,tree016_56]
def tree016_533 : CoverTree := CoverTree.reject 325
def tree016_534 : CoverTree := CoverTree.split [tree016_284,tree016_533,tree016_56,tree016_56,tree016_56,tree016_56]
def tree016_535 : CoverTree := CoverTree.split [tree016_291,tree016_56,tree016_99,tree016_56,tree016_56,tree016_56]
def tree016_536 : CoverTree := CoverTree.split [tree016_525,tree016_529,tree016_532,tree016_534,tree016_535,tree016_312]
def tree016_537 : CoverTree := CoverTree.split [tree016_88,tree016_498,tree016_499,tree016_518,tree016_524,tree016_536]
def tree016_538 : CoverTree := CoverTree.reject 67
def tree016_539 : CoverTree := CoverTree.reject 287
def tree016_540 : CoverTree := CoverTree.reject 288
def tree016_541 : CoverTree := CoverTree.reject 245
def tree016_542 : CoverTree := CoverTree.split [tree016_351,tree016_480,tree016_230,tree016_539,tree016_540,tree016_541]
def tree016_543 : CoverTree := CoverTree.reject 141
def tree016_544 : CoverTree := CoverTree.reject 305
def tree016_545 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_381,tree016_382,tree016_441,tree016_544]
def tree016_546 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_123,tree016_244,tree016_12,tree016_12]
def tree016_547 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_246,tree016_247,tree016_12,tree016_12]
def tree016_548 : CoverTree := CoverTree.reject 306
def tree016_549 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_548,tree016_12,tree016_12,tree016_12]
def tree016_550 : CoverTree := CoverTree.reject 307
def tree016_551 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_550,tree016_12,tree016_12,tree016_12]
def tree016_552 : CoverTree := CoverTree.split [tree016_284,tree016_545,tree016_546,tree016_547,tree016_549,tree016_551]
def tree016_553 : CoverTree := CoverTree.reject 377
def tree016_554 : CoverTree := CoverTree.reject 275
def tree016_555 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_254,tree016_12,tree016_12,tree016_12]
def tree016_556 : CoverTree := CoverTree.split [tree016_321,tree016_553,tree016_554,tree016_555,tree016_65,tree016_65]
def tree016_557 : CoverTree := CoverTree.reject 308
def tree016_558 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_449,tree016_557,tree016_12,tree016_12]
def tree016_559 : CoverTree := CoverTree.split [tree016_327,tree016_558,tree016_65,tree016_65,tree016_65,tree016_65]
def tree016_560 : CoverTree := CoverTree.split [tree016_229,tree016_542,tree016_543,tree016_552,tree016_556,tree016_559]
def tree016_561 : CoverTree := CoverTree.reject 234
def tree016_562 : CoverTree := CoverTree.reject 378
def tree016_563 : CoverTree := CoverTree.split [tree016_302,tree016_562,tree016_193,tree016_269,tree016_28,tree016_65]
def tree016_564 : CoverTree := CoverTree.reject 326
def tree016_565 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_123,tree016_136,tree016_12,tree016_12]
def tree016_566 : CoverTree := CoverTree.reject 309
def tree016_567 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_566,tree016_12,tree016_12,tree016_12]
def tree016_568 : CoverTree := CoverTree.split [tree016_284,tree016_564,tree016_565,tree016_65,tree016_567,tree016_65]
def tree016_569 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_139,tree016_12,tree016_12,tree016_12]
def tree016_570 : CoverTree := CoverTree.split [tree016_321,tree016_324,tree016_569,tree016_65,tree016_65,tree016_65]
def tree016_571 : CoverTree := CoverTree.split [tree016_133,tree016_561,tree016_563,tree016_568,tree016_570,tree016_328]
def tree016_572 : CoverTree := CoverTree.reject 238
def tree016_573 : CoverTree := CoverTree.reject 210
def tree016_574 : CoverTree := CoverTree.split [tree016_302,tree016_400,tree016_333,tree016_335,tree016_28,tree016_65]
def tree016_575 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_381,tree016_382,tree016_12,tree016_12]
def tree016_576 : CoverTree := CoverTree.split [tree016_284,tree016_575,tree016_339,tree016_65,tree016_65,tree016_65]
def tree016_577 : CoverTree := CoverTree.split [tree016_327,tree016_65,tree016_113,tree016_65,tree016_65,tree016_65]
def tree016_578 : CoverTree := CoverTree.split [tree016_572,tree016_573,tree016_574,tree016_576,tree016_342,tree016_577]
def tree016_579 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_203,tree016_204,tree016_12,tree016_12]
def tree016_580 : CoverTree := CoverTree.split [tree016_346,tree016_347,tree016_196,tree016_197,tree016_348,tree016_579]
def tree016_581 : CoverTree := CoverTree.reject 379
def tree016_582 : CoverTree := CoverTree.split [tree016_351,tree016_581,tree016_353,tree016_354,tree016_355,tree016_65]
def tree016_583 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_416,tree016_398,tree016_399,tree016_12]
def tree016_584 : CoverTree := CoverTree.split [tree016_302,tree016_583,tree016_120,tree016_121,tree016_65,tree016_65]
def tree016_585 : CoverTree := CoverTree.split [tree016_284,tree016_575,tree016_124,tree016_65,tree016_65,tree016_65]
def tree016_586 : CoverTree := CoverTree.split [tree016_580,tree016_582,tree016_584,tree016_585,tree016_342,tree016_328]
def tree016_587 : CoverTree := CoverTree.split [tree016_103,tree016_538,tree016_560,tree016_571,tree016_578,tree016_586]
def tree016_588 : CoverTree := CoverTree.reject 16
def tree016_589 : CoverTree := CoverTree.reject 112
def tree016_590 : CoverTree := CoverTree.reject 380
def tree016_591 : CoverTree := CoverTree.reject 381
def tree016_592 : CoverTree := CoverTree.reject 276
def tree016_593 : CoverTree := CoverTree.split [tree016_474,tree016_590,tree016_591,tree016_592,tree016_222,tree016_223]
def tree016_594 : CoverTree := CoverTree.split [tree016_588,tree016_588,tree016_588,tree016_589,tree016_593,tree016_436]
def tree016_595 : CoverTree := CoverTree.reject 246
def tree016_596 : CoverTree := CoverTree.reject 382
def tree016_597 : CoverTree := CoverTree.reject 310
def tree016_598 : CoverTree := CoverTree.split [tree016_80,tree016_80,tree016_597,tree016_12,tree016_12,tree016_12]
def tree016_599 : CoverTree := CoverTree.split [tree016_284,tree016_596,tree016_245,tree016_248,tree016_598,tree016_250]
def tree016_600 : CoverTree := CoverTree.split [tree016_373,tree016_450,tree016_376,tree016_19,tree016_180,tree016_12]
def tree016_601 : CoverTree := CoverTree.split [tree016_229,tree016_595,tree016_440,tree016_599,tree016_447,tree016_600]
def tree016_602 : CoverTree := CoverTree.reject 311
def tree016_603 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_156,tree016_602]
def tree016_604 : CoverTree := CoverTree.split [tree016_351,tree016_483,tree016_603,tree016_262,tree016_263,tree016_265]
def tree016_605 : CoverTree := CoverTree.split [tree016_133,tree016_604,tree016_454,tree016_385,tree016_387,tree016_391]
def tree016_606 : CoverTree := CoverTree.reject 256
def tree016_607 : CoverTree := CoverTree.split [tree016_351,tree016_393,tree016_273,tree016_396,tree016_263,tree016_163]
def tree016_608 : CoverTree := CoverTree.split [tree016_606,tree016_607,tree016_401,tree016_403,tree016_404,tree016_407]
def tree016_609 : CoverTree := CoverTree.split [tree016_130,tree016_594,tree016_601,tree016_605,tree016_608,tree016_428]
def tree016_610 : CoverTree := CoverTree.reject 84
def tree016_611 : CoverTree := CoverTree.reject 290
def tree016_612 : CoverTree := CoverTree.split [tree016_284,tree016_611,tree016_466,tree016_469,tree016_472,tree016_223]
def tree016_613 : CoverTree := CoverTree.split [tree016_588,tree016_588,tree016_588,tree016_612,tree016_478,tree016_436]
def tree016_614 : CoverTree := CoverTree.reject 291
def tree016_615 : CoverTree := CoverTree.split [tree016_351,tree016_480,tree016_230,tree016_232,tree016_614,tree016_235]
def tree016_616 : CoverTree := CoverTree.split [tree016_229,tree016_615,tree016_440,tree016_443,tree016_447,tree016_451]
def tree016_617 : CoverTree := CoverTree.reject 312
def tree016_618 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_156,tree016_617]
def tree016_619 : CoverTree := CoverTree.split [tree016_351,tree016_483,tree016_618,tree016_262,tree016_263,tree016_265]
def tree016_620 : CoverTree := CoverTree.split [tree016_133,tree016_619,tree016_454,tree016_455,tree016_387,tree016_391]
def tree016_621 : CoverTree := CoverTree.split [tree016_610,tree016_613,tree016_616,tree016_620,tree016_488,tree016_428]
def tree016_622 : CoverTree := CoverTree.reject 185
def tree016_623 : CoverTree := CoverTree.reject 89
def tree016_624 : CoverTree := CoverTree.reject 42
def tree016_625 : CoverTree := CoverTree.reject 18
def tree016_626 : CoverTree := CoverTree.reject 235
def tree016_627 : CoverTree := CoverTree.reject 236
def tree016_628 : CoverTree := CoverTree.reject 94
def tree016_629 : CoverTree := CoverTree.reject 253
def tree016_630 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_628,tree016_628,tree016_629,tree016_12]
def tree016_631 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_628,tree016_628,tree016_12,tree016_12]
def tree016_632 : CoverTree := CoverTree.reject 254
def tree016_633 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_632,tree016_12,tree016_12,tree016_12]
def tree016_634 : CoverTree := CoverTree.split [tree016_474,tree016_626,tree016_627,tree016_630,tree016_631,tree016_633]
def tree016_635 : CoverTree := CoverTree.reject 281
def tree016_636 : CoverTree := CoverTree.reject 282
def tree016_637 : CoverTree := CoverTree.reject 283
def tree016_638 : CoverTree := CoverTree.reject 313
def tree016_639 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_635,tree016_636,tree016_637,tree016_638]
def tree016_640 : CoverTree := CoverTree.reject 284
def tree016_641 : CoverTree := CoverTree.reject 314
def tree016_642 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_640,tree016_641,tree016_12,tree016_12]
def tree016_643 : CoverTree := CoverTree.reject 285
def tree016_644 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_643,tree016_12,tree016_12,tree016_12]
def tree016_645 : CoverTree := CoverTree.split [tree016_432,tree016_639,tree016_642,tree016_644,tree016_223,tree016_223]
def tree016_646 : CoverTree := CoverTree.split [tree016_622,tree016_623,tree016_624,tree016_625,tree016_634,tree016_645]
def tree016_647 : CoverTree := CoverTree.reject 219
def tree016_648 : CoverTree := CoverTree.reject 211
def tree016_649 : CoverTree := CoverTree.reject 212
def tree016_650 : CoverTree := CoverTree.reject 213
def tree016_651 : CoverTree := CoverTree.reject 220
def tree016_652 : CoverTree := CoverTree.reject 214
def tree016_653 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_651,tree016_652,tree016_12,tree016_12]
def tree016_654 : CoverTree := CoverTree.split [tree016_351,tree016_647,tree016_648,tree016_649,tree016_650,tree016_653]
def tree016_655 : CoverTree := CoverTree.reject 239
def tree016_656 : CoverTree := CoverTree.reject 241
def tree016_657 : CoverTree := CoverTree.reject 242
def tree016_658 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_119,tree016_656,tree016_657]
def tree016_659 : CoverTree := CoverTree.reject 114
def tree016_660 : CoverTree := CoverTree.reject 243
def tree016_661 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_659,tree016_660,tree016_12]
def tree016_662 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_659,tree016_12,tree016_12]
def tree016_663 : CoverTree := CoverTree.split [tree016_302,tree016_655,tree016_658,tree016_661,tree016_662,tree016_223]
def tree016_664 : CoverTree := CoverTree.reject 383
def tree016_665 : CoverTree := CoverTree.split [tree016_284,tree016_664,tree016_466,tree016_469,tree016_472,tree016_223]
def tree016_666 : CoverTree := CoverTree.split [tree016_210,tree016_654,tree016_663,tree016_665,tree016_478,tree016_436]
def tree016_667 : CoverTree := CoverTree.split [tree016_646,tree016_666,tree016_482,tree016_485,tree016_488,tree016_428]
def tree016_668 : CoverTree := CoverTree.split [tree016_497,tree016_537,tree016_587,tree016_609,tree016_621,tree016_667]
def tree016_669 : CoverTree := CoverTree.reject 63
def tree016_670 : CoverTree := CoverTree.reject 56
def tree016_671 : CoverTree := CoverTree.split [tree016_491,tree016_492,tree016_493,tree016_494,tree016_669,tree016_670]
def tree016_672 : CoverTree := CoverTree.reject 277
def tree016_673 : CoverTree := CoverTree.reject 176
def tree016_674 : CoverTree := CoverTree.reject 135
def tree016_675 : CoverTree := CoverTree.reject 128
def tree016_676 : CoverTree := CoverTree.reject 347
def tree016_677 : CoverTree := CoverTree.reject 348
def tree016_678 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_434,tree016_676,tree016_677]
def tree016_679 : CoverTree := CoverTree.reject 349
def tree016_680 : CoverTree := CoverTree.reject 350
def tree016_681 : CoverTree := CoverTree.reject 351
def tree016_682 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_679,tree016_680,tree016_681]
def tree016_683 : CoverTree := CoverTree.split [tree016_295,tree016_678,tree016_682,tree016_56,tree016_56,tree016_56]
def tree016_684 : CoverTree := CoverTree.split [tree016_210,tree016_672,tree016_673,tree016_674,tree016_675,tree016_683]
def tree016_685 : CoverTree := CoverTree.reject 240
def tree016_686 : CoverTree := CoverTree.reject 163
def tree016_687 : CoverTree := CoverTree.reject 331
def tree016_688 : CoverTree := CoverTree.reject 352
def tree016_689 : CoverTree := CoverTree.reject 353
def tree016_690 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_244,tree016_688,tree016_689]
def tree016_691 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_247,tree016_12,tree016_12]
def tree016_692 : CoverTree := CoverTree.split [tree016_284,tree016_687,tree016_690,tree016_691,tree016_56,tree016_56]
def tree016_693 : CoverTree := CoverTree.reject 332
def tree016_694 : CoverTree := CoverTree.reject 354
def tree016_695 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_694,tree016_12,tree016_12]
def tree016_696 : CoverTree := CoverTree.split [tree016_291,tree016_693,tree016_695,tree016_56,tree016_56,tree016_56]
def tree016_697 : CoverTree := CoverTree.reject 355
def tree016_698 : CoverTree := CoverTree.reject 356
def tree016_699 : CoverTree := CoverTree.reject 357
def tree016_700 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_697,tree016_698,tree016_699]
def tree016_701 : CoverTree := CoverTree.reject 358
def tree016_702 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_701,tree016_12,tree016_12]
def tree016_703 : CoverTree := CoverTree.split [tree016_295,tree016_700,tree016_702,tree016_56,tree016_56,tree016_56]
def tree016_704 : CoverTree := CoverTree.split [tree016_229,tree016_685,tree016_686,tree016_692,tree016_696,tree016_703]
def tree016_705 : CoverTree := CoverTree.reject 333
def tree016_706 : CoverTree := CoverTree.reject 334
def tree016_707 : CoverTree := CoverTree.reject 286
def tree016_708 : CoverTree := CoverTree.reject 359
def tree016_709 : CoverTree := CoverTree.reject 360
def tree016_710 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_708,tree016_709,tree016_12]
def tree016_711 : CoverTree := CoverTree.split [tree016_351,tree016_483,tree016_705,tree016_706,tree016_707,tree016_710]
def tree016_712 : CoverTree := CoverTree.reject 335
def tree016_713 : CoverTree := CoverTree.reject 327
def tree016_714 : CoverTree := CoverTree.reject 361
def tree016_715 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_268,tree016_714,tree016_12]
def tree016_716 : CoverTree := CoverTree.split [tree016_302,tree016_712,tree016_713,tree016_715,tree016_56,tree016_56]
def tree016_717 : CoverTree := CoverTree.split [tree016_284,tree016_502,tree016_504,tree016_56,tree016_56,tree016_56]
def tree016_718 : CoverTree := CoverTree.split [tree016_133,tree016_711,tree016_716,tree016_717,tree016_511,tree016_517]
def tree016_719 : CoverTree := CoverTree.reject 336
def tree016_720 : CoverTree := CoverTree.reject 362
def tree016_721 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_258,tree016_720,tree016_12]
def tree016_722 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_258,tree016_12,tree016_12]
def tree016_723 : CoverTree := CoverTree.split [tree016_351,tree016_393,tree016_719,tree016_721,tree016_722,tree016_56]
def tree016_724 : CoverTree := CoverTree.reject 337
def tree016_725 : CoverTree := CoverTree.reject 363
def tree016_726 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_119,tree016_725,tree016_12]
def tree016_727 : CoverTree := CoverTree.reject 364
def tree016_728 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_727,tree016_12,tree016_12]
def tree016_729 : CoverTree := CoverTree.split [tree016_302,tree016_724,tree016_726,tree016_728,tree016_56,tree016_56]
def tree016_730 : CoverTree := CoverTree.split [tree016_519,tree016_723,tree016_729,tree016_523,tree016_292,tree016_298]
def tree016_731 : CoverTree := CoverTree.split [tree016_55,tree016_55,tree016_55,tree016_199,tree016_200,tree016_201]
def tree016_732 : CoverTree := CoverTree.reject 328
def tree016_733 : CoverTree := CoverTree.split [tree016_346,tree016_347,tree016_196,tree016_197,tree016_731,tree016_732]
def tree016_734 : CoverTree := CoverTree.reject 384
def tree016_735 : CoverTree := CoverTree.reject 385
def tree016_736 : CoverTree := CoverTree.split [tree016_351,tree016_734,tree016_735,tree016_528,tree016_56,tree016_56]
def tree016_737 : CoverTree := CoverTree.reject 386
def tree016_738 : CoverTree := CoverTree.split [tree016_302,tree016_737,tree016_531,tree016_306,tree016_56,tree016_56]
def tree016_739 : CoverTree := CoverTree.split [tree016_733,tree016_736,tree016_738,tree016_523,tree016_535,tree016_312]
def tree016_740 : CoverTree := CoverTree.split [tree016_88,tree016_684,tree016_704,tree016_718,tree016_730,tree016_739]
def tree016_741 : CoverTree := CoverTree.reject 278
def tree016_742 : CoverTree := CoverTree.reject 165
def tree016_743 : CoverTree := CoverTree.reject 338
def tree016_744 : CoverTree := CoverTree.reject 339
def tree016_745 : CoverTree := CoverTree.reject 329
def tree016_746 : CoverTree := CoverTree.reject 330
def tree016_747 : CoverTree := CoverTree.reject 252
def tree016_748 : CoverTree := CoverTree.split [tree016_284,tree016_743,tree016_744,tree016_745,tree016_746,tree016_747]
def tree016_749 : CoverTree := CoverTree.reject 340
def tree016_750 : CoverTree := CoverTree.reject 365
def tree016_751 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_219,tree016_750,tree016_12,tree016_12]
def tree016_752 : CoverTree := CoverTree.split [tree016_474,tree016_749,tree016_218,tree016_751,tree016_222,tree016_223]
def tree016_753 : CoverTree := CoverTree.reject 366
def tree016_754 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_433,tree016_434,tree016_12,tree016_753]
def tree016_755 : CoverTree := CoverTree.split [tree016_432,tree016_754,tree016_226,tree016_223,tree016_223,tree016_223]
def tree016_756 : CoverTree := CoverTree.split [tree016_210,tree016_741,tree016_742,tree016_748,tree016_752,tree016_755]
def tree016_757 : CoverTree := CoverTree.split [tree016_302,tree016_439,tree016_238,tree016_240,tree016_28,tree016_65]
def tree016_758 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_322,tree016_444,tree016_445,tree016_12]
def tree016_759 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_252,tree016_12,tree016_12,tree016_12]
def tree016_760 : CoverTree := CoverTree.split [tree016_321,tree016_758,tree016_759,tree016_555,tree016_65,tree016_65]
def tree016_761 : CoverTree := CoverTree.split [tree016_229,tree016_542,tree016_757,tree016_552,tree016_760,tree016_559]
def tree016_762 : CoverTree := CoverTree.reject 341
def tree016_763 : CoverTree := CoverTree.split [tree016_64,tree016_64,tree016_264,tree016_12,tree016_12,tree016_12]
def tree016_764 : CoverTree := CoverTree.split [tree016_351,tree016_483,tree016_762,tree016_262,tree016_263,tree016_763]
def tree016_765 : CoverTree := CoverTree.reject 387
def tree016_766 : CoverTree := CoverTree.split [tree016_302,tree016_765,tree016_193,tree016_269,tree016_28,tree016_65]
def tree016_767 : CoverTree := CoverTree.split [tree016_284,tree016_575,tree016_565,tree016_65,tree016_567,tree016_65]
def tree016_768 : CoverTree := CoverTree.split [tree016_133,tree016_764,tree016_766,tree016_767,tree016_570,tree016_328]
def tree016_769 : CoverTree := CoverTree.reject 367
def tree016_770 : CoverTree := CoverTree.split [tree016_27,tree016_27,tree016_27,tree016_258,tree016_769,tree016_12]
def tree016_771 : CoverTree := CoverTree.split [tree016_351,tree016_393,tree016_273,tree016_770,tree016_263,tree016_65]
def tree016_772 : CoverTree := CoverTree.split [tree016_572,tree016_771,tree016_574,tree016_576,tree016_342,tree016_577]
def tree016_773 : CoverTree := CoverTree.reject 388
def tree016_774 : CoverTree := CoverTree.split [tree016_351,tree016_773,tree016_353,tree016_354,tree016_355,tree016_65]
def tree016_775 : CoverTree := CoverTree.split [tree016_580,tree016_774,tree016_584,tree016_585,tree016_342,tree016_328]
def tree016_776 : CoverTree := CoverTree.split [tree016_103,tree016_756,tree016_761,tree016_768,tree016_772,tree016_775]
def tree016_777 : CoverTree := CoverTree.reject 279
def tree016_778 : CoverTree := CoverTree.reject 342
def tree016_779 : CoverTree := CoverTree.split [tree016_284,tree016_778,tree016_466,tree016_469,tree016_472,tree016_223]
def tree016_780 : CoverTree := CoverTree.split [tree016_210,tree016_777,tree016_663,tree016_779,tree016_478,tree016_436]
def tree016_781 : CoverTree := CoverTree.reject 343
def tree016_782 : CoverTree := CoverTree.split [tree016_351,tree016_480,tree016_230,tree016_232,tree016_781,tree016_235]
def tree016_783 : CoverTree := CoverTree.split [tree016_284,tree016_442,tree016_245,tree016_248,tree016_598,tree016_250]
def tree016_784 : CoverTree := CoverTree.split [tree016_229,tree016_782,tree016_440,tree016_783,tree016_447,tree016_600]
def tree016_785 : CoverTree := CoverTree.reject 344
def tree016_786 : CoverTree := CoverTree.split [tree016_346,tree016_347,tree016_196,tree016_197,tree016_785,tree016_205]
def tree016_787 : CoverTree := CoverTree.split [tree016_786,tree016_607,tree016_401,tree016_403,tree016_404,tree016_407]
def tree016_788 : CoverTree := CoverTree.split [tree016_130,tree016_780,tree016_784,tree016_605,tree016_787,tree016_428]
def tree016_789 : CoverTree := CoverTree.reject 345
def tree016_790 : CoverTree := CoverTree.split [tree016_474,tree016_626,tree016_627,tree016_789,tree016_631,tree016_633]
def tree016_791 : CoverTree := CoverTree.reject 102
def tree016_792 : CoverTree := CoverTree.split [tree016_622,tree016_623,tree016_624,tree016_625,tree016_790,tree016_791]
def tree016_793 : CoverTree := CoverTree.reject 280
def tree016_794 : CoverTree := CoverTree.reject 346
def tree016_795 : CoverTree := CoverTree.reject 289
def tree016_796 : CoverTree := CoverTree.split [tree016_302,tree016_655,tree016_658,tree016_794,tree016_795,tree016_223]
def tree016_797 : CoverTree := CoverTree.split [tree016_210,tree016_793,tree016_796,tree016_612,tree016_478,tree016_436]
def tree016_798 : CoverTree := CoverTree.split [tree016_792,tree016_797,tree016_616,tree016_620,tree016_488,tree016_428]
def tree016_799 : CoverTree := CoverTree.reject 221
def tree016_800 : CoverTree := CoverTree.split [tree016_214,tree016_214,tree016_381,tree016_382,tree016_799,tree016_12]
def tree016_801 : CoverTree := CoverTree.split [tree016_284,tree016_800,tree016_466,tree016_469,tree016_472,tree016_223]
def tree016_802 : CoverTree := CoverTree.split [tree016_210,tree016_654,tree016_663,tree016_801,tree016_478,tree016_436]
def tree016_803 : CoverTree := CoverTree.split [tree016_646,tree016_802,tree016_482,tree016_485,tree016_488,tree016_428]
def tree016_804 : CoverTree := CoverTree.split [tree016_671,tree016_740,tree016_776,tree016_788,tree016_798,tree016_803]
def tree016_805 : CoverTree := CoverTree.split [tree016_48,tree016_86,tree016_277,tree016_490,tree016_668,tree016_804]
def tree016 : CoverTree := tree016_805

end Snake9.Shared89
