import GraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88

def boxes049 : List Box := [
[(1,3),(1,5),(1,3),(1,5),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(1,1),(1,6)],
[(1,6),(1,2),(1,6),(1,6),(1,6),(1,3)],
[(1,6),(1,6),(1,5),(1,3),(1,5),(1,3)],
[(1,2),(1,6),(1,6),(1,6),(1,3),(1,6)],
[(1,6),(1,6),(1,2),(1,6),(1,6),(1,2)],
[(1,2),(1,6),(1,6),(1,2),(1,6),(1,6)],
[(1,5),(1,5),(1,2),(1,3),(1,6),(1,6)],
[(1,6),(1,3),(1,6),(1,6),(1,6),(1,2)],
[(1,6),(1,6),(1,5),(1,2),(1,5),(1,4)],
[(1,2),(1,4),(1,5),(1,5),(1,6),(1,6)],
[(1,3),(1,6),(1,6),(1,6),(1,2),(1,6)],
[(4,4),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,5),(1,5),(1,4),(1,2)],
[(1,2),(1,6),(1,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,2),(1,6),(1,2)],
[(1,6),(1,6),(1,1),(4,4),(1,6),(1,6)],
[(1,6),(1,6),(1,3),(1,2),(1,5),(1,5)],
[(1,6),(1,6),(4,4),(1,1),(1,6),(1,6)],
[(3,3),(1,1),(1,6),(1,6),(1,6),(1,6)],
[(1,4),(1,5),(1,2),(1,5),(1,6),(1,6)],
[(1,6),(1,1),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,1),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(3,3),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(4,4),(1,6)],
[(1,6),(3,3),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(4,4),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(4,4),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(2,2),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(4,4),(1,1)],
[(1,6),(1,1),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(2,2),(1,1),(1,6),(1,6),(1,6)],
[(1,2),(1,5),(1,5),(1,4),(1,6),(1,6)],
[(1,6),(1,6),(1,4),(1,5),(1,5),(1,2)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(4,4)],
[(4,4),(3,3),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(3,3),(1,6),(1,6)],
[(1,1),(3,3),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(3,3),(1,1)],
[(5,5),(1,1),(6,6),(1,6),(1,6),(1,6)],
[(6,6),(1,1),(6,6),(1,6),(1,6),(1,6)],
[(5,5),(1,1),(5,5),(1,6),(1,6),(1,6)],
[(6,6),(1,1),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(1,1),(1,6),(1,6)],
[(1,6),(1,1),(1,1),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(3,3)],
[(3,3),(3,3),(4,4),(1,6),(1,6),(1,6)],
[(4,4),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(4,4)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(5,5)],
[(1,1),(2,2),(1,6),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,6),(2,2),(1,1)],
[(4,4),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(5,5),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(3,3)],
[(3,3),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,1),(6,6),(3,3),(1,6),(1,6),(1,6)],
[(1,1),(6,6),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(3,3),(5,5)],
[(5,5),(3,3),(2,2),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(6,6),(1,1)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(4,4),(6,6),(1,1)],
[(3,3),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(1,1),(6,6),(4,4)],
[(4,4),(6,6),(1,1),(1,6),(1,6),(1,6)],
[(1,1),(1,1),(1,6),(1,6),(1,6),(1,6)],
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
[(1,1),(5,5),(3,3),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(4,4),(2,2)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(1,1)],
[(1,6),(1,6),(1,6),(3,3),(5,5),(2,2)],
[(1,6),(1,6),(1,6),(4,4),(4,4),(2,2)],
[(2,2),(4,4),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(4,4),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(5,5),(3,3),(1,6),(1,6),(1,6)],
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
[(1,6),(1,6),(3,3),(3,3),(4,4),(4,4)],
[(1,6),(1,6),(5,5),(4,4),(5,5),(2,2)],
[(2,2),(5,5),(4,4),(5,5),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(3,3),(5,5)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(4,4)],
[(1,6),(1,6),(3,3),(5,5),(4,4),(3,3)],
[(1,6),(1,6),(4,4),(3,3),(6,6),(2,2)],
[(3,3),(4,4),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(2,2),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(3,3)],
[(1,6),(1,6),(1,6),(3,3),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(4,4),(3,3),(2,2)],
[(1,6),(1,6),(1,6),(5,5),(3,3),(2,2)],
[(2,2),(3,3),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(3,3),(5,5),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(2,2),(1,6),(1,6),(1,6)],
[(3,3),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(1,1),(5,5),(6,6),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(3,3),(2,2),(6,6)],
[(1,6),(1,6),(3,3),(4,4),(3,3),(4,4)],
[(1,6),(1,6),(3,3),(4,4),(4,4),(3,3)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(4,4)],
[(1,6),(1,6),(3,3),(5,5),(2,2),(5,5)],
[(1,6),(1,6),(3,3),(5,5),(3,3),(3,3)],
[(1,6),(1,6),(3,3),(6,6),(5,5),(1,1)],
[(3,3),(3,3),(5,5),(3,3),(1,6),(1,6)],
[(4,4),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(4,4),(3,3),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(5,5),(2,2),(5,5),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(3,3),(1,6)],
[(1,6),(3,3),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(4,4)],
[(1,6),(1,6),(3,3),(3,3),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(4,4),(2,2),(5,5)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(3,3)],
[(2,2),(6,6),(3,3),(4,4),(1,6),(1,6)],
[(3,3),(2,2),(6,6),(3,3),(1,6),(1,6)],
[(3,3),(4,4),(4,4),(3,3),(1,6),(1,6)],
[(4,4),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(5,5),(2,2),(4,4),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(3,3),(2,2),(2,2),(1,6)],
[(1,6),(2,2),(2,2),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(6,6),(2,2),(4,4)],
[(1,6),(1,6),(2,2),(6,6),(3,3),(3,3)],
[(1,6),(1,6),(3,3),(2,2),(6,6),(3,3)],
[(3,3),(3,3),(6,6),(2,2),(1,6),(1,6)],
[(3,3),(6,6),(2,2),(3,3),(1,6),(1,6)],
[(4,4),(2,2),(6,6),(2,2),(1,6),(1,6)],
[(4,4),(4,4),(3,3),(3,3),(1,6),(1,6)],
[(5,5),(3,3),(3,3),(3,3),(1,6),(1,6)],
[(1,6),(1,6),(1,1),(1,1),(1,6),(1,6)],
[(1,6),(1,6),(1,6),(3,3),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(4,4),(2,2),(2,2)],
[(1,6),(1,6),(1,6),(5,5),(2,2),(2,2)],
[(2,2),(2,2),(3,3),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(4,4),(1,6),(1,6),(1,6)],
[(2,2),(2,2),(5,5),(1,6),(1,6),(1,6)],
[(1,6),(1,6),(2,2),(5,5),(3,3),(3,3)],
[(1,6),(1,6),(2,2),(5,5),(3,3),(4,4)],
[(1,6),(1,6),(2,2),(5,5),(3,3),(5,5)],
[(1,6),(1,6),(2,2),(5,5),(4,4),(3,3)],
[(1,6),(1,6),(2,2),(5,5),(5,5),(3,3)],
[(1,6),(1,6),(2,2),(6,6),(2,2),(3,3)],
[(1,6),(1,6),(3,3),(4,4),(6,6),(2,2)],
[(1,6),(1,6),(3,3),(6,6),(2,2),(2,2)],
[(1,6),(1,6),(4,4),(6,6),(2,2),(2,2)],
[(2,2),(2,2),(6,6),(3,3),(1,6),(1,6)],
[(2,2),(2,2),(6,6),(4,4),(1,6),(1,6)],
[(2,2),(6,6),(3,3),(3,3),(1,6),(1,6)],
[(2,2),(6,6),(4,4),(3,3),(1,6),(1,6)],
[(3,3),(2,2),(6,6),(2,2),(1,6),(1,6)],
[(3,3),(3,3),(5,5),(2,2),(1,6),(1,6)],
[(3,3),(4,4),(5,5),(2,2),(1,6),(1,6)],
[(3,3),(5,5),(5,5),(2,2),(1,6),(1,6)],
[(4,4),(3,3),(5,5),(2,2),(1,6),(1,6)],
[(5,5),(3,3),(5,5),(2,2),(1,6),(1,6)],
[(6,6),(2,2),(3,3),(3,3),(1,6),(1,6)],
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

def root049 : Nat := 3380

def tree049_0 : CoverTree := CoverTree.reject 67
def tree049_1 : CoverTree := CoverTree.reject 51
def tree049_2 : CoverTree := CoverTree.reject 37
def tree049_3 : CoverTree := CoverTree.reject 27
def tree049_4 : CoverTree := CoverTree.reject 14
def tree049_5 : CoverTree := CoverTree.reject 95
def tree049_6 : CoverTree := CoverTree.reject 77
def tree049_7 : CoverTree := CoverTree.reject 75
def tree049_8 : CoverTree := CoverTree.reject 6
def tree049_9 : CoverTree := CoverTree.reject 147
def tree049_10 : CoverTree := CoverTree.reject 1
def tree049_11 : CoverTree := CoverTree.reject 4
def tree049_12 : CoverTree := CoverTree.reject 29
def tree049_13 : CoverTree := CoverTree.reject 99
def tree049_14 : CoverTree := CoverTree.accept
def tree049_15 : CoverTree := CoverTree.split [tree049_12,tree049_13,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_16 : CoverTree := CoverTree.reject 78
def tree049_17 : CoverTree := CoverTree.split [tree049_16,tree049_14,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_18 : CoverTree := CoverTree.reject 63
def tree049_19 : CoverTree := CoverTree.split [tree049_18,tree049_14,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_20 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_15,tree049_17,tree049_19]
def tree049_21 : CoverTree := CoverTree.split [tree049_12,tree049_14,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_22 : CoverTree := CoverTree.reject 76
def tree049_23 : CoverTree := CoverTree.split [tree049_22,tree049_14,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_24 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_21,tree049_23,tree049_14]
def tree049_25 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_21,tree049_14,tree049_14]
def tree049_26 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_9,tree049_20,tree049_24,tree049_25]
def tree049_27 : CoverTree := CoverTree.split [tree049_4,tree049_4,tree049_5,tree049_6,tree049_7,tree049_26]
def tree049_28 : CoverTree := CoverTree.reject 57
def tree049_29 : CoverTree := CoverTree.reject 58
def tree049_30 : CoverTree := CoverTree.reject 3
def tree049_31 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_14,tree049_14,tree049_14]
def tree049_32 : CoverTree := CoverTree.reject 61
def tree049_33 : CoverTree := CoverTree.split [tree049_32,tree049_14,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_34 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_31,tree049_31,tree049_33]
def tree049_35 : CoverTree := CoverTree.reject 13
def tree049_36 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_37 : CoverTree := CoverTree.reject 130
def tree049_38 : CoverTree := CoverTree.split [tree049_16,tree049_37,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_39 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_36,tree049_38,tree049_19]
def tree049_40 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_36,tree049_23,tree049_14]
def tree049_41 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_34,tree049_39,tree049_40,tree049_25]
def tree049_42 : CoverTree := CoverTree.reject 96
def tree049_43 : CoverTree := CoverTree.reject 81
def tree049_44 : CoverTree := CoverTree.split [tree049_12,tree049_42,tree049_43,tree049_14,tree049_14,tree049_14]
def tree049_45 : CoverTree := CoverTree.reject 97
def tree049_46 : CoverTree := CoverTree.reject 98
def tree049_47 : CoverTree := CoverTree.split [tree049_45,tree049_46,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_48 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_44,tree049_47,tree049_33]
def tree049_49 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_48,tree049_20,tree049_24,tree049_25]
def tree049_50 : CoverTree := CoverTree.split [tree049_4,tree049_4,tree049_28,tree049_29,tree049_41,tree049_49]
def tree049_51 : CoverTree := CoverTree.split [tree049_0,tree049_1,tree049_2,tree049_3,tree049_27,tree049_50]
def tree049_52 : CoverTree := CoverTree.reject 68
def tree049_53 : CoverTree := CoverTree.reject 185
def tree049_54 : CoverTree := CoverTree.reject 186
def tree049_55 : CoverTree := CoverTree.reject 187
def tree049_56 : CoverTree := CoverTree.reject 197
def tree049_57 : CoverTree := CoverTree.reject 198
def tree049_58 : CoverTree := CoverTree.reject 264
def tree049_59 : CoverTree := CoverTree.reject 2
def tree049_60 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_14,tree049_14,tree049_14]
def tree049_61 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_58,tree049_60,tree049_60]
def tree049_62 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_60,tree049_60,tree049_60]
def tree049_63 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_56,tree049_57,tree049_61,tree049_62]
def tree049_64 : CoverTree := CoverTree.split [tree049_4,tree049_4,tree049_53,tree049_54,tree049_55,tree049_63]
def tree049_65 : CoverTree := CoverTree.reject 142
def tree049_66 : CoverTree := CoverTree.reject 143
def tree049_67 : CoverTree := CoverTree.reject 144
def tree049_68 : CoverTree := CoverTree.reject 265
def tree049_69 : CoverTree := CoverTree.reject 8
def tree049_70 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_71 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_68,tree049_70,tree049_70]
def tree049_72 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_70,tree049_70,tree049_70]
def tree049_73 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_71,tree049_72,tree049_72,tree049_72]
def tree049_74 : CoverTree := CoverTree.split [tree049_4,tree049_4,tree049_65,tree049_66,tree049_67,tree049_73]
def tree049_75 : CoverTree := CoverTree.reject 100
def tree049_76 : CoverTree := CoverTree.reject 101
def tree049_77 : CoverTree := CoverTree.reject 10
def tree049_78 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_77,tree049_77,tree049_77,tree049_25]
def tree049_79 : CoverTree := CoverTree.split [tree049_4,tree049_4,tree049_75,tree049_76,tree049_78,tree049_49]
def tree049_80 : CoverTree := CoverTree.reject 102
def tree049_81 : CoverTree := CoverTree.reject 32
def tree049_82 : CoverTree := CoverTree.reject 131
def tree049_83 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_81,tree049_81,tree049_82,tree049_25]
def tree049_84 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_81,tree049_81,tree049_40,tree049_25]
def tree049_85 : CoverTree := CoverTree.split [tree049_4,tree049_4,tree049_80,tree049_83,tree049_84,tree049_49]
def tree049_86 : CoverTree := CoverTree.reject 199
def tree049_87 : CoverTree := CoverTree.reject 166
def tree049_88 : CoverTree := CoverTree.reject 134
def tree049_89 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_88,tree049_14,tree049_14,tree049_14]
def tree049_90 : CoverTree := CoverTree.reject 33
def tree049_91 : CoverTree := CoverTree.split [tree049_90,tree049_90,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_92 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_89,tree049_91,tree049_14]
def tree049_93 : CoverTree := CoverTree.reject 154
def tree049_94 : CoverTree := CoverTree.split [tree049_93,tree049_14,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_95 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_21,tree049_94,tree049_14]
def tree049_96 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_86,tree049_87,tree049_92,tree049_95]
def tree049_97 : CoverTree := CoverTree.reject 200
def tree049_98 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_36,tree049_91,tree049_19]
def tree049_99 : CoverTree := CoverTree.split [tree049_10,tree049_11,tree049_11,tree049_36,tree049_91,tree049_14]
def tree049_100 : CoverTree := CoverTree.split [tree049_8,tree049_8,tree049_97,tree049_98,tree049_99,tree049_25]
def tree049_101 : CoverTree := CoverTree.split [tree049_4,tree049_4,tree049_96,tree049_100,tree049_41,tree049_49]
def tree049_102 : CoverTree := CoverTree.split [tree049_52,tree049_64,tree049_74,tree049_79,tree049_85,tree049_101]
def tree049_103 : CoverTree := CoverTree.reject 19
def tree049_104 : CoverTree := CoverTree.reject 31
def tree049_105 : CoverTree := CoverTree.reject 145
def tree049_106 : CoverTree := CoverTree.reject 146
def tree049_107 : CoverTree := CoverTree.reject 64
def tree049_108 : CoverTree := CoverTree.reject 56
def tree049_109 : CoverTree := CoverTree.reject 289
def tree049_110 : CoverTree := CoverTree.reject 201
def tree049_111 : CoverTree := CoverTree.reject 167
def tree049_112 : CoverTree := CoverTree.reject 11
def tree049_113 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_60,tree049_60,tree049_60,tree049_60]
def tree049_114 : CoverTree := CoverTree.reject 244
def tree049_115 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_114,tree049_14,tree049_14]
def tree049_116 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_115,tree049_60,tree049_60,tree049_60]
def tree049_117 : CoverTree := CoverTree.split [tree049_109,tree049_110,tree049_111,tree049_113,tree049_116,tree049_113]
def tree049_118 : CoverTree := CoverTree.split [tree049_104,tree049_105,tree049_106,tree049_107,tree049_108,tree049_117]
def tree049_119 : CoverTree := CoverTree.reject 25
def tree049_120 : CoverTree := CoverTree.reject 113
def tree049_121 : CoverTree := CoverTree.reject 114
def tree049_122 : CoverTree := CoverTree.reject 47
def tree049_123 : CoverTree := CoverTree.reject 83
def tree049_124 : CoverTree := CoverTree.reject 202
def tree049_125 : CoverTree := CoverTree.reject 155
def tree049_126 : CoverTree := CoverTree.reject 125
def tree049_127 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_70,tree049_70,tree049_70,tree049_70]
def tree049_128 : CoverTree := CoverTree.reject 245
def tree049_129 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_128,tree049_14,tree049_14,tree049_14]
def tree049_130 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_129,tree049_70,tree049_70,tree049_70]
def tree049_131 : CoverTree := CoverTree.split [tree049_123,tree049_124,tree049_125,tree049_126,tree049_127,tree049_130]
def tree049_132 : CoverTree := CoverTree.reject 290
def tree049_133 : CoverTree := CoverTree.reject 176
def tree049_134 : CoverTree := CoverTree.reject 112
def tree049_135 : CoverTree := CoverTree.reject 34
def tree049_136 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_134,tree049_135,tree049_14,tree049_14]
def tree049_137 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_43,tree049_14,tree049_14,tree049_14]
def tree049_138 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_136,tree049_137,tree049_70,tree049_70]
def tree049_139 : CoverTree := CoverTree.reject 46
def tree049_140 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_139,tree049_14,tree049_14,tree049_14]
def tree049_141 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_140,tree049_70,tree049_70,tree049_70]
def tree049_142 : CoverTree := CoverTree.reject 247
def tree049_143 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_142,tree049_70,tree049_70,tree049_70]
def tree049_144 : CoverTree := CoverTree.split [tree049_132,tree049_133,tree049_138,tree049_141,tree049_143,tree049_127]
def tree049_145 : CoverTree := CoverTree.split [tree049_119,tree049_120,tree049_121,tree049_122,tree049_131,tree049_144]
def tree049_146 : CoverTree := CoverTree.reject 26
def tree049_147 : CoverTree := CoverTree.reject 115
def tree049_148 : CoverTree := CoverTree.reject 82
def tree049_149 : CoverTree := CoverTree.reject 18
def tree049_150 : CoverTree := CoverTree.reject 225
def tree049_151 : CoverTree := CoverTree.reject 168
def tree049_152 : CoverTree := CoverTree.reject 104
def tree049_153 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_139,tree049_152,tree049_14,tree049_14]
def tree049_154 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_153,tree049_36,tree049_91,tree049_19]
def tree049_155 : CoverTree := CoverTree.reject 124
def tree049_156 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_155,tree049_14,tree049_14,tree049_14]
def tree049_157 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_156,tree049_36,tree049_91,tree049_14]
def tree049_158 : CoverTree := CoverTree.reject 38
def tree049_159 : CoverTree := CoverTree.split [tree049_158,tree049_14,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_160 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_159,tree049_21,tree049_14,tree049_14]
def tree049_161 : CoverTree := CoverTree.split [tree049_149,tree049_150,tree049_151,tree049_154,tree049_157,tree049_160]
def tree049_162 : CoverTree := CoverTree.reject 203
def tree049_163 : CoverTree := CoverTree.reject 136
def tree049_164 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_139,tree049_14,tree049_14,tree049_14]
def tree049_165 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_164,tree049_36,tree049_38,tree049_19]
def tree049_166 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_36,tree049_36,tree049_23,tree049_14]
def tree049_167 : CoverTree := CoverTree.split [tree049_123,tree049_162,tree049_163,tree049_165,tree049_166,tree049_160]
def tree049_168 : CoverTree := CoverTree.reject 291
def tree049_169 : CoverTree := CoverTree.reject 15
def tree049_170 : CoverTree := CoverTree.reject 109
def tree049_171 : CoverTree := CoverTree.reject 86
def tree049_172 : CoverTree := CoverTree.reject 59
def tree049_173 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_170,tree049_171,tree049_172,tree049_14]
def tree049_174 : CoverTree := CoverTree.reject 110
def tree049_175 : CoverTree := CoverTree.reject 87
def tree049_176 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_174,tree049_175,tree049_14,tree049_14]
def tree049_177 : CoverTree := CoverTree.reject 111
def tree049_178 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_177,tree049_14,tree049_14,tree049_14]
def tree049_179 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_180 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_173,tree049_176,tree049_178,tree049_179]
def tree049_181 : CoverTree := CoverTree.reject 139
def tree049_182 : CoverTree := CoverTree.split [tree049_158,tree049_181,tree049_134,tree049_135,tree049_14,tree049_14]
def tree049_183 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_182,tree049_44,tree049_47,tree049_33]
def tree049_184 : CoverTree := CoverTree.reject 140
def tree049_185 : CoverTree := CoverTree.split [tree049_158,tree049_184,tree049_139,tree049_14,tree049_14,tree049_14]
def tree049_186 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_185,tree049_15,tree049_17,tree049_19]
def tree049_187 : CoverTree := CoverTree.reject 141
def tree049_188 : CoverTree := CoverTree.split [tree049_158,tree049_187,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_189 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_188,tree049_21,tree049_23,tree049_14]
def tree049_190 : CoverTree := CoverTree.split [tree049_168,tree049_180,tree049_183,tree049_186,tree049_189,tree049_160]
def tree049_191 : CoverTree := CoverTree.split [tree049_146,tree049_147,tree049_148,tree049_161,tree049_167,tree049_190]
def tree049_192 : CoverTree := CoverTree.reject 116
def tree049_193 : CoverTree := CoverTree.reject 117
def tree049_194 : CoverTree := CoverTree.reject 0
def tree049_195 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_159,tree049_21,tree049_94,tree049_14]
def tree049_196 : CoverTree := CoverTree.split [tree049_194,tree049_194,tree049_194,tree049_194,tree049_194,tree049_195]
def tree049_197 : CoverTree := CoverTree.reject 226
def tree049_198 : CoverTree := CoverTree.reject 312
def tree049_199 : CoverTree := CoverTree.reject 313
def tree049_200 : CoverTree := CoverTree.reject 135
def tree049_201 : CoverTree := CoverTree.split [tree049_32,tree049_200,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_202 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_198,tree049_199,tree049_31,tree049_201]
def tree049_203 : CoverTree := CoverTree.reject 314
def tree049_204 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_203,tree049_36,tree049_91,tree049_19]
def tree049_205 : CoverTree := CoverTree.split [tree049_149,tree049_197,tree049_202,tree049_204,tree049_157,tree049_160]
def tree049_206 : CoverTree := CoverTree.reject 204
def tree049_207 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_135,tree049_14,tree049_14]
def tree049_208 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_207,tree049_31,tree049_31,tree049_33]
def tree049_209 : CoverTree := CoverTree.split [tree049_123,tree049_206,tree049_208,tree049_165,tree049_166,tree049_160]
def tree049_210 : CoverTree := CoverTree.reject 23
def tree049_211 : CoverTree := CoverTree.reject 24
def tree049_212 : CoverTree := CoverTree.reject 108
def tree049_213 : CoverTree := CoverTree.reject 85
def tree049_214 : CoverTree := CoverTree.reject 73
def tree049_215 : CoverTree := CoverTree.reject 91
def tree049_216 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_212,tree049_213,tree049_214,tree049_215]
def tree049_217 : CoverTree := CoverTree.reject 71
def tree049_218 : CoverTree := CoverTree.reject 65
def tree049_219 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_217,tree049_218,tree049_14,tree049_14]
def tree049_220 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_210,tree049_211,tree049_216,tree049_219]
def tree049_221 : CoverTree := CoverTree.split [tree049_220,tree049_180,tree049_183,tree049_186,tree049_189,tree049_160]
def tree049_222 : CoverTree := CoverTree.split [tree049_192,tree049_193,tree049_196,tree049_205,tree049_209,tree049_221]
def tree049_223 : CoverTree := CoverTree.reject 72
def tree049_224 : CoverTree := CoverTree.reject 80
def tree049_225 : CoverTree := CoverTree.reject 292
def tree049_226 : CoverTree := CoverTree.reject 177
def tree049_227 : CoverTree := CoverTree.reject 126
def tree049_228 : CoverTree := CoverTree.reject 5
def tree049_229 : CoverTree := CoverTree.reject 188
def tree049_230 : CoverTree := CoverTree.reject 189
def tree049_231 : CoverTree := CoverTree.reject 190
def tree049_232 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_229,tree049_230,tree049_231,tree049_14]
def tree049_233 : CoverTree := CoverTree.reject 191
def tree049_234 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_233,tree049_14,tree049_14,tree049_14]
def tree049_235 : CoverTree := CoverTree.reject 192
def tree049_236 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_235,tree049_14,tree049_14,tree049_14]
def tree049_237 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_238 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_232,tree049_234,tree049_236,tree049_237]
def tree049_239 : CoverTree := CoverTree.reject 174
def tree049_240 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_239,tree049_14,tree049_14,tree049_14]
def tree049_241 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_240,tree049_237,tree049_237,tree049_237]
def tree049_242 : CoverTree := CoverTree.split [tree049_224,tree049_225,tree049_226,tree049_227,tree049_238,tree049_241]
def tree049_243 : CoverTree := CoverTree.reject 43
def tree049_244 : CoverTree := CoverTree.reject 160
def tree049_245 : CoverTree := CoverTree.reject 9
def tree049_246 : CoverTree := CoverTree.reject 17
def tree049_247 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_246,tree049_14]
def tree049_248 : CoverTree := CoverTree.reject 175
def tree049_249 : CoverTree := CoverTree.reject 162
def tree049_250 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_248,tree049_249,tree049_14,tree049_14]
def tree049_251 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_244,tree049_247,tree049_247,tree049_250]
def tree049_252 : CoverTree := CoverTree.reject 132
def tree049_253 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_135,tree049_252,tree049_14]
def tree049_254 : CoverTree := CoverTree.reject 129
def tree049_255 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_254,tree049_14,tree049_14]
def tree049_256 : CoverTree := CoverTree.reject 163
def tree049_257 : CoverTree := CoverTree.split [tree049_32,tree049_256,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_258 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_253,tree049_255,tree049_31,tree049_257]
def tree049_259 : CoverTree := CoverTree.reject 149
def tree049_260 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_139,tree049_259,tree049_14,tree049_14]
def tree049_261 : CoverTree := CoverTree.reject 150
def tree049_262 : CoverTree := CoverTree.reject 133
def tree049_263 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_261,tree049_262,tree049_14,tree049_14]
def tree049_264 : CoverTree := CoverTree.reject 194
def tree049_265 : CoverTree := CoverTree.split [tree049_18,tree049_264,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_266 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_260,tree049_263,tree049_91,tree049_265]
def tree049_267 : CoverTree := CoverTree.reject 153
def tree049_268 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_267,tree049_14,tree049_14,tree049_14]
def tree049_269 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_268,tree049_89,tree049_91,tree049_14]
def tree049_270 : CoverTree := CoverTree.split [tree049_243,tree049_251,tree049_258,tree049_266,tree049_269,tree049_195]
def tree049_271 : CoverTree := CoverTree.reject 246
def tree049_272 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_172,tree049_271]
def tree049_273 : CoverTree := CoverTree.reject 103
def tree049_274 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_273,tree049_14]
def tree049_275 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_14,tree049_14]
def tree049_276 : CoverTree := CoverTree.reject 123
def tree049_277 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_276,tree049_14,tree049_14,tree049_14]
def tree049_278 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_272,tree049_274,tree049_275,tree049_277]
def tree049_279 : CoverTree := CoverTree.reject 315
def tree049_280 : CoverTree := CoverTree.reject 93
def tree049_281 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_280,tree049_14,tree049_14]
def tree049_282 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_279,tree049_281,tree049_31,tree049_201]
def tree049_283 : CoverTree := CoverTree.split [tree049_149,tree049_278,tree049_282,tree049_154,tree049_157,tree049_160]
def tree049_284 : CoverTree := CoverTree.reject 252
def tree049_285 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_172,tree049_14]
def tree049_286 : CoverTree := CoverTree.split [tree049_10,tree049_112,tree049_285,tree049_275,tree049_275,tree049_179]
def tree049_287 : CoverTree := CoverTree.split [tree049_284,tree049_286,tree049_208,tree049_165,tree049_166,tree049_160]
def tree049_288 : CoverTree := CoverTree.split [tree049_223,tree049_242,tree049_270,tree049_283,tree049_287,tree049_221]
def tree049_289 : CoverTree := CoverTree.split [tree049_103,tree049_118,tree049_145,tree049_191,tree049_222,tree049_288]
def tree049_290 : CoverTree := CoverTree.reject 12
def tree049_291 : CoverTree := CoverTree.reject 122
def tree049_292 : CoverTree := CoverTree.reject 53
def tree049_293 : CoverTree := CoverTree.reject 48
def tree049_294 : CoverTree := CoverTree.reject 214
def tree049_295 : CoverTree := CoverTree.reject 156
def tree049_296 : CoverTree := CoverTree.reject 316
def tree049_297 : CoverTree := CoverTree.reject 266
def tree049_298 : CoverTree := CoverTree.split [tree049_10,tree049_296,tree049_297,tree049_60,tree049_60,tree049_60]
def tree049_299 : CoverTree := CoverTree.split [tree049_10,tree049_60,tree049_60,tree049_60,tree049_60,tree049_60]
def tree049_300 : CoverTree := CoverTree.reject 254
def tree049_301 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_300,tree049_14,tree049_14]
def tree049_302 : CoverTree := CoverTree.split [tree049_10,tree049_301,tree049_60,tree049_60,tree049_60,tree049_60]
def tree049_303 : CoverTree := CoverTree.split [tree049_123,tree049_294,tree049_295,tree049_298,tree049_299,tree049_302]
def tree049_304 : CoverTree := CoverTree.reject 293
def tree049_305 : CoverTree := CoverTree.reject 178
def tree049_306 : CoverTree := CoverTree.reject 365
def tree049_307 : CoverTree := CoverTree.reject 317
def tree049_308 : CoverTree := CoverTree.reject 255
def tree049_309 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_308,tree049_14,tree049_14]
def tree049_310 : CoverTree := CoverTree.split [tree049_10,tree049_306,tree049_307,tree049_309,tree049_60,tree049_60]
def tree049_311 : CoverTree := CoverTree.reject 318
def tree049_312 : CoverTree := CoverTree.split [tree049_10,tree049_311,tree049_60,tree049_60,tree049_60,tree049_60]
def tree049_313 : CoverTree := CoverTree.reject 267
def tree049_314 : CoverTree := CoverTree.split [tree049_10,tree049_313,tree049_115,tree049_60,tree049_60,tree049_60]
def tree049_315 : CoverTree := CoverTree.split [tree049_304,tree049_305,tree049_310,tree049_312,tree049_314,tree049_299]
def tree049_316 : CoverTree := CoverTree.split [tree049_104,tree049_291,tree049_292,tree049_293,tree049_303,tree049_315]
def tree049_317 : CoverTree := CoverTree.reject 88
def tree049_318 : CoverTree := CoverTree.reject 35
def tree049_319 : CoverTree := CoverTree.reject 227
def tree049_320 : CoverTree := CoverTree.reject 157
def tree049_321 : CoverTree := CoverTree.reject 118
def tree049_322 : CoverTree := CoverTree.reject 55
def tree049_323 : CoverTree := CoverTree.reject 256
def tree049_324 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_322,tree049_323,tree049_14,tree049_14]
def tree049_325 : CoverTree := CoverTree.reject 268
def tree049_326 : CoverTree := CoverTree.split [tree049_10,tree049_324,tree049_325,tree049_70,tree049_70,tree049_70]
def tree049_327 : CoverTree := CoverTree.split [tree049_10,tree049_70,tree049_70,tree049_70,tree049_70,tree049_70]
def tree049_328 : CoverTree := CoverTree.split [tree049_149,tree049_319,tree049_320,tree049_321,tree049_326,tree049_327]
def tree049_329 : CoverTree := CoverTree.reject 205
def tree049_330 : CoverTree := CoverTree.reject 366
def tree049_331 : CoverTree := CoverTree.reject 257
def tree049_332 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_135,tree049_331,tree049_14]
def tree049_333 : CoverTree := CoverTree.reject 258
def tree049_334 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_333,tree049_14,tree049_14]
def tree049_335 : CoverTree := CoverTree.split [tree049_10,tree049_330,tree049_332,tree049_334,tree049_31,tree049_70]
def tree049_336 : CoverTree := CoverTree.reject 319
def tree049_337 : CoverTree := CoverTree.reject 259
def tree049_338 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_139,tree049_337,tree049_14,tree049_14]
def tree049_339 : CoverTree := CoverTree.split [tree049_10,tree049_336,tree049_338,tree049_70,tree049_70,tree049_70]
def tree049_340 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_322,tree049_14,tree049_14,tree049_14]
def tree049_341 : CoverTree := CoverTree.split [tree049_10,tree049_340,tree049_70,tree049_70,tree049_70,tree049_70]
def tree049_342 : CoverTree := CoverTree.reject 248
def tree049_343 : CoverTree := CoverTree.split [tree049_10,tree049_342,tree049_129,tree049_70,tree049_70,tree049_70]
def tree049_344 : CoverTree := CoverTree.split [tree049_123,tree049_329,tree049_335,tree049_339,tree049_341,tree049_343]
def tree049_345 : CoverTree := CoverTree.reject 28
def tree049_346 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_212,tree049_213,tree049_214,tree049_215]
def tree049_347 : CoverTree := CoverTree.reject 320
def tree049_348 : CoverTree := CoverTree.split [tree049_10,tree049_345,tree049_210,tree049_211,tree049_346,tree049_347]
def tree049_349 : CoverTree := CoverTree.reject 367
def tree049_350 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_170,tree049_171,tree049_172,tree049_14]
def tree049_351 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_174,tree049_175,tree049_14,tree049_14]
def tree049_352 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_177,tree049_14,tree049_14,tree049_14]
def tree049_353 : CoverTree := CoverTree.split [tree049_10,tree049_349,tree049_350,tree049_351,tree049_352,tree049_70]
def tree049_354 : CoverTree := CoverTree.reject 368
def tree049_355 : CoverTree := CoverTree.split [tree049_10,tree049_354,tree049_136,tree049_137,tree049_70,tree049_70]
def tree049_356 : CoverTree := CoverTree.reject 321
def tree049_357 : CoverTree := CoverTree.split [tree049_10,tree049_356,tree049_140,tree049_70,tree049_70,tree049_70]
def tree049_358 : CoverTree := CoverTree.split [tree049_348,tree049_353,tree049_355,tree049_357,tree049_341,tree049_327]
def tree049_359 : CoverTree := CoverTree.split [tree049_119,tree049_317,tree049_318,tree049_328,tree049_344,tree049_358]
def tree049_360 : CoverTree := CoverTree.reject 89
def tree049_361 : CoverTree := CoverTree.reject 106
def tree049_362 : CoverTree := CoverTree.reject 179
def tree049_363 : CoverTree := CoverTree.reject 94
def tree049_364 : CoverTree := CoverTree.reject 369
def tree049_365 : CoverTree := CoverTree.reject 269
def tree049_366 : CoverTree := CoverTree.split [tree049_10,tree049_364,tree049_365,tree049_89,tree049_91,tree049_14]
def tree049_367 : CoverTree := CoverTree.reject 270
def tree049_368 : CoverTree := CoverTree.reject 260
def tree049_369 : CoverTree := CoverTree.split [tree049_158,tree049_368,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_370 : CoverTree := CoverTree.split [tree049_10,tree049_367,tree049_369,tree049_21,tree049_94,tree049_14]
def tree049_371 : CoverTree := CoverTree.split [tree049_243,tree049_361,tree049_362,tree049_363,tree049_366,tree049_370]
def tree049_372 : CoverTree := CoverTree.reject 228
def tree049_373 : CoverTree := CoverTree.reject 158
def tree049_374 : CoverTree := CoverTree.reject 62
def tree049_375 : CoverTree := CoverTree.reject 45
def tree049_376 : CoverTree := CoverTree.reject 261
def tree049_377 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_374,tree049_375,tree049_376,tree049_14]
def tree049_378 : CoverTree := CoverTree.split [tree049_10,tree049_377,tree049_153,tree049_36,tree049_91,tree049_19]
def tree049_379 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_322,tree049_14,tree049_14,tree049_14]
def tree049_380 : CoverTree := CoverTree.split [tree049_10,tree049_379,tree049_156,tree049_36,tree049_91,tree049_14]
def tree049_381 : CoverTree := CoverTree.reject 52
def tree049_382 : CoverTree := CoverTree.reject 196
def tree049_383 : CoverTree := CoverTree.split [tree049_381,tree049_382,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_384 : CoverTree := CoverTree.split [tree049_10,tree049_383,tree049_159,tree049_21,tree049_14,tree049_14]
def tree049_385 : CoverTree := CoverTree.split [tree049_149,tree049_372,tree049_373,tree049_378,tree049_380,tree049_384]
def tree049_386 : CoverTree := CoverTree.reject 120
def tree049_387 : CoverTree := CoverTree.reject 370
def tree049_388 : CoverTree := CoverTree.reject 262
def tree049_389 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_388,tree049_14]
def tree049_390 : CoverTree := CoverTree.split [tree049_10,tree049_386,tree049_387,tree049_389,tree049_275,tree049_179]
def tree049_391 : CoverTree := CoverTree.reject 49
def tree049_392 : CoverTree := CoverTree.reject 50
def tree049_393 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_391,tree049_392,tree049_14]
def tree049_394 : CoverTree := CoverTree.split [tree049_10,tree049_393,tree049_207,tree049_31,tree049_31,tree049_33]
def tree049_395 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_374,tree049_375,tree049_14,tree049_14]
def tree049_396 : CoverTree := CoverTree.split [tree049_10,tree049_395,tree049_164,tree049_36,tree049_38,tree049_19]
def tree049_397 : CoverTree := CoverTree.split [tree049_10,tree049_379,tree049_36,tree049_36,tree049_23,tree049_14]
def tree049_398 : CoverTree := CoverTree.reject 263
def tree049_399 : CoverTree := CoverTree.split [tree049_381,tree049_398,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_400 : CoverTree := CoverTree.split [tree049_10,tree049_399,tree049_159,tree049_21,tree049_14,tree049_14]
def tree049_401 : CoverTree := CoverTree.split [tree049_123,tree049_390,tree049_394,tree049_396,tree049_397,tree049_400]
def tree049_402 : CoverTree := CoverTree.split [tree049_10,tree049_345,tree049_210,tree049_211,tree049_216,tree049_219]
def tree049_403 : CoverTree := CoverTree.reject 137
def tree049_404 : CoverTree := CoverTree.reject 119
def tree049_405 : CoverTree := CoverTree.reject 69
def tree049_406 : CoverTree := CoverTree.split [tree049_169,tree049_169,tree049_403,tree049_404,tree049_405,tree049_14]
def tree049_407 : CoverTree := CoverTree.split [tree049_10,tree049_406,tree049_173,tree049_176,tree049_178,tree049_179]
def tree049_408 : CoverTree := CoverTree.reject 182
def tree049_409 : CoverTree := CoverTree.reject 138
def tree049_410 : CoverTree := CoverTree.split [tree049_381,tree049_408,tree049_409,tree049_391,tree049_392,tree049_14]
def tree049_411 : CoverTree := CoverTree.split [tree049_10,tree049_410,tree049_182,tree049_44,tree049_47,tree049_33]
def tree049_412 : CoverTree := CoverTree.reject 183
def tree049_413 : CoverTree := CoverTree.split [tree049_381,tree049_412,tree049_374,tree049_375,tree049_14,tree049_14]
def tree049_414 : CoverTree := CoverTree.split [tree049_10,tree049_413,tree049_185,tree049_15,tree049_17,tree049_19]
def tree049_415 : CoverTree := CoverTree.reject 184
def tree049_416 : CoverTree := CoverTree.split [tree049_381,tree049_415,tree049_322,tree049_14,tree049_14,tree049_14]
def tree049_417 : CoverTree := CoverTree.split [tree049_10,tree049_416,tree049_188,tree049_21,tree049_23,tree049_14]
def tree049_418 : CoverTree := CoverTree.split [tree049_381,tree049_14,tree049_14,tree049_14,tree049_14,tree049_14]
def tree049_419 : CoverTree := CoverTree.split [tree049_10,tree049_418,tree049_159,tree049_21,tree049_14,tree049_14]
def tree049_420 : CoverTree := CoverTree.split [tree049_402,tree049_407,tree049_411,tree049_414,tree049_417,tree049_419]
def tree049_421 : CoverTree := CoverTree.split [tree049_146,tree049_360,tree049_371,tree049_385,tree049_401,tree049_420]
def tree049_422 : CoverTree := CoverTree.reject 90
def tree049_423 : CoverTree := CoverTree.reject 7
def tree049_424 : CoverTree := CoverTree.reject 20
def tree049_425 : CoverTree := CoverTree.reject 193
def tree049_426 : CoverTree := CoverTree.reject 173
def tree049_427 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_425,tree049_426,tree049_14,tree049_14]
def tree049_428 : CoverTree := CoverTree.split [tree049_10,tree049_427,tree049_240,tree049_237,tree049_237,tree049_237]
def tree049_429 : CoverTree := CoverTree.split [tree049_423,tree049_423,tree049_423,tree049_424,tree049_424,tree049_428]
def tree049_430 : CoverTree := CoverTree.reject 148
def tree049_431 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_391,tree049_392,tree049_430]
def tree049_432 : CoverTree := CoverTree.split [tree049_10,tree049_431,tree049_253,tree049_255,tree049_31,tree049_257]
def tree049_433 : CoverTree := CoverTree.reject 164
def tree049_434 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_374,tree049_375,tree049_433,tree049_14]
def tree049_435 : CoverTree := CoverTree.split [tree049_10,tree049_434,tree049_260,tree049_263,tree049_91,tree049_265]
def tree049_436 : CoverTree := CoverTree.reject 151
def tree049_437 : CoverTree := CoverTree.reject 152
def tree049_438 : CoverTree := CoverTree.split [tree049_35,tree049_35,tree049_322,tree049_436,tree049_437,tree049_14]
def tree049_439 : CoverTree := CoverTree.split [tree049_10,tree049_438,tree049_268,tree049_89,tree049_91,tree049_14]
def tree049_440 : CoverTree := CoverTree.reject 195
def tree049_441 : CoverTree := CoverTree.reject 165
def tree049_442 : CoverTree := CoverTree.split [tree049_381,tree049_440,tree049_441,tree049_14,tree049_14,tree049_14]
def tree049_443 : CoverTree := CoverTree.split [tree049_10,tree049_442,tree049_159,tree049_21,tree049_94,tree049_14]
def tree049_444 : CoverTree := CoverTree.split [tree049_243,tree049_361,tree049_432,tree049_435,tree049_439,tree049_443]
def tree049_445 : CoverTree := CoverTree.reject 229
def tree049_446 : CoverTree := CoverTree.split [tree049_10,tree049_393,tree049_207,tree049_281,tree049_31,tree049_201]
def tree049_447 : CoverTree := CoverTree.split [tree049_10,tree049_395,tree049_153,tree049_36,tree049_91,tree049_19]
def tree049_448 : CoverTree := CoverTree.split [tree049_149,tree049_445,tree049_446,tree049_447,tree049_380,tree049_384]
def tree049_449 : CoverTree := CoverTree.split [tree049_10,tree049_386,tree049_285,tree049_275,tree049_275,tree049_179]
def tree049_450 : CoverTree := CoverTree.split [tree049_123,tree049_449,tree049_394,tree049_396,tree049_397,tree049_419]
def tree049_451 : CoverTree := CoverTree.split [tree049_422,tree049_429,tree049_444,tree049_448,tree049_450,tree049_420]
def tree049_452 : CoverTree := CoverTree.reject 66
def tree049_453 : CoverTree := CoverTree.reject 294
def tree049_454 : CoverTree := CoverTree.reject 169
def tree049_455 : CoverTree := CoverTree.reject 371
def tree049_456 : CoverTree := CoverTree.reject 219
def tree049_457 : CoverTree := CoverTree.reject 220
def tree049_458 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_139,tree049_456,tree049_457,tree049_14]
def tree049_459 : CoverTree := CoverTree.reject 221
def tree049_460 : CoverTree := CoverTree.reject 222
def tree049_461 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_459,tree049_460,tree049_14,tree049_14]
def tree049_462 : CoverTree := CoverTree.reject 223
def tree049_463 : CoverTree := CoverTree.reject 224
def tree049_464 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_462,tree049_463,tree049_14,tree049_14]
def tree049_465 : CoverTree := CoverTree.split [tree049_10,tree049_455,tree049_458,tree049_461,tree049_464,tree049_237]
def tree049_466 : CoverTree := CoverTree.reject 212
def tree049_467 : CoverTree := CoverTree.reject 213
def tree049_468 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_322,tree049_466,tree049_467,tree049_14]
def tree049_469 : CoverTree := CoverTree.split [tree049_10,tree049_468,tree049_232,tree049_234,tree049_236,tree049_237]
def tree049_470 : CoverTree := CoverTree.split [tree049_224,tree049_453,tree049_454,tree049_465,tree049_469,tree049_428]
def tree049_471 : CoverTree := CoverTree.reject 171
def tree049_472 : CoverTree := CoverTree.split [tree049_10,tree049_471,tree049_244,tree049_247,tree049_247,tree049_250]
def tree049_473 : CoverTree := CoverTree.split [tree049_243,tree049_472,tree049_432,tree049_435,tree049_439,tree049_443]
def tree049_474 : CoverTree := CoverTree.reject 127
def tree049_475 : CoverTree := CoverTree.split [tree049_10,tree049_474,tree049_272,tree049_274,tree049_275,tree049_277]
def tree049_476 : CoverTree := CoverTree.split [tree049_149,tree049_475,tree049_446,tree049_447,tree049_380,tree049_384]
def tree049_477 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_214,tree049_14]
def tree049_478 : CoverTree := CoverTree.split [tree049_10,tree049_345,tree049_210,tree049_211,tree049_477,tree049_219]
def tree049_479 : CoverTree := CoverTree.split [tree049_478,tree049_449,tree049_394,tree049_396,tree049_397,tree049_419]
def tree049_480 : CoverTree := CoverTree.split [tree049_452,tree049_470,tree049_473,tree049_476,tree049_479,tree049_420]
def tree049_481 : CoverTree := CoverTree.split [tree049_290,tree049_316,tree049_359,tree049_421,tree049_451,tree049_480]
def tree049_482 : CoverTree := CoverTree.reject 44
def tree049_483 : CoverTree := CoverTree.reject 30
def tree049_484 : CoverTree := CoverTree.reject 21
def tree049_485 : CoverTree := CoverTree.reject 22
def tree049_486 : CoverTree := CoverTree.reject 41
def tree049_487 : CoverTree := CoverTree.reject 39
def tree049_488 : CoverTree := CoverTree.split [tree049_482,tree049_483,tree049_484,tree049_485,tree049_486,tree049_487]
def tree049_489 : CoverTree := CoverTree.reject 70
def tree049_490 : CoverTree := CoverTree.reject 54
def tree049_491 : CoverTree := CoverTree.reject 230
def tree049_492 : CoverTree := CoverTree.reject 170
def tree049_493 : CoverTree := CoverTree.reject 241
def tree049_494 : CoverTree := CoverTree.reject 296
def tree049_495 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_152,tree049_494,tree049_14]
def tree049_496 : CoverTree := CoverTree.reject 271
def tree049_497 : CoverTree := CoverTree.split [tree049_10,tree049_493,tree049_495,tree049_496,tree049_60,tree049_60]
def tree049_498 : CoverTree := CoverTree.reject 297
def tree049_499 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_498,tree049_14,tree049_14]
def tree049_500 : CoverTree := CoverTree.reject 298
def tree049_501 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_500,tree049_14,tree049_14]
def tree049_502 : CoverTree := CoverTree.split [tree049_10,tree049_499,tree049_501,tree049_60,tree049_60,tree049_60]
def tree049_503 : CoverTree := CoverTree.reject 299
def tree049_504 : CoverTree := CoverTree.reject 300
def tree049_505 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_503,tree049_504,tree049_14]
def tree049_506 : CoverTree := CoverTree.reject 301
def tree049_507 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_506,tree049_14,tree049_14]
def tree049_508 : CoverTree := CoverTree.split [tree049_10,tree049_505,tree049_507,tree049_60,tree049_60,tree049_60]
def tree049_509 : CoverTree := CoverTree.split [tree049_149,tree049_491,tree049_492,tree049_497,tree049_502,tree049_508]
def tree049_510 : CoverTree := CoverTree.reject 234
def tree049_511 : CoverTree := CoverTree.reject 215
def tree049_512 : CoverTree := CoverTree.reject 159
def tree049_513 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_375,tree049_14,tree049_14]
def tree049_514 : CoverTree := CoverTree.split [tree049_10,tree049_513,tree049_60,tree049_60,tree049_60,tree049_60]
def tree049_515 : CoverTree := CoverTree.split [tree049_510,tree049_511,tree049_512,tree049_514,tree049_299,tree049_302]
def tree049_516 : CoverTree := CoverTree.reject 295
def tree049_517 : CoverTree := CoverTree.reject 372
def tree049_518 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_171,tree049_172,tree049_14]
def tree049_519 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_175,tree049_14,tree049_14]
def tree049_520 : CoverTree := CoverTree.split [tree049_10,tree049_517,tree049_518,tree049_519,tree049_60,tree049_60]
def tree049_521 : CoverTree := CoverTree.reject 373
def tree049_522 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_135,tree049_14,tree049_14]
def tree049_523 : CoverTree := CoverTree.split [tree049_10,tree049_521,tree049_522,tree049_309,tree049_60,tree049_60]
def tree049_524 : CoverTree := CoverTree.reject 322
def tree049_525 : CoverTree := CoverTree.split [tree049_10,tree049_524,tree049_60,tree049_60,tree049_60,tree049_60]
def tree049_526 : CoverTree := CoverTree.split [tree049_10,tree049_60,tree049_115,tree049_60,tree049_60,tree049_60]
def tree049_527 : CoverTree := CoverTree.split [tree049_516,tree049_520,tree049_523,tree049_525,tree049_526,tree049_299]
def tree049_528 : CoverTree := CoverTree.split [tree049_104,tree049_489,tree049_490,tree049_509,tree049_515,tree049_527]
def tree049_529 : CoverTree := CoverTree.reject 60
def tree049_530 : CoverTree := CoverTree.reject 284
def tree049_531 : CoverTree := CoverTree.reject 285
def tree049_532 : CoverTree := CoverTree.reject 242
def tree049_533 : CoverTree := CoverTree.split [tree049_10,tree049_471,tree049_244,tree049_530,tree049_531,tree049_532]
def tree049_534 : CoverTree := CoverTree.reject 180
def tree049_535 : CoverTree := CoverTree.reject 302
def tree049_536 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_374,tree049_375,tree049_433,tree049_535]
def tree049_537 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_139,tree049_259,tree049_14,tree049_14]
def tree049_538 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_261,tree049_262,tree049_14,tree049_14]
def tree049_539 : CoverTree := CoverTree.reject 303
def tree049_540 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_539,tree049_14,tree049_14,tree049_14]
def tree049_541 : CoverTree := CoverTree.reject 304
def tree049_542 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_541,tree049_14,tree049_14,tree049_14]
def tree049_543 : CoverTree := CoverTree.split [tree049_10,tree049_536,tree049_537,tree049_538,tree049_540,tree049_542]
def tree049_544 : CoverTree := CoverTree.reject 374
def tree049_545 : CoverTree := CoverTree.reject 272
def tree049_546 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_88,tree049_14,tree049_14,tree049_14]
def tree049_547 : CoverTree := CoverTree.split [tree049_10,tree049_544,tree049_545,tree049_546,tree049_70,tree049_70]
def tree049_548 : CoverTree := CoverTree.reject 305
def tree049_549 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_441,tree049_548,tree049_14,tree049_14]
def tree049_550 : CoverTree := CoverTree.split [tree049_10,tree049_549,tree049_70,tree049_70,tree049_70,tree049_70]
def tree049_551 : CoverTree := CoverTree.split [tree049_243,tree049_533,tree049_534,tree049_543,tree049_547,tree049_550]
def tree049_552 : CoverTree := CoverTree.reject 231
def tree049_553 : CoverTree := CoverTree.reject 375
def tree049_554 : CoverTree := CoverTree.split [tree049_10,tree049_553,tree049_207,tree049_281,tree049_31,tree049_70]
def tree049_555 : CoverTree := CoverTree.reject 323
def tree049_556 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_139,tree049_152,tree049_14,tree049_14]
def tree049_557 : CoverTree := CoverTree.reject 306
def tree049_558 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_557,tree049_14,tree049_14,tree049_14]
def tree049_559 : CoverTree := CoverTree.split [tree049_10,tree049_555,tree049_556,tree049_70,tree049_558,tree049_70]
def tree049_560 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_155,tree049_14,tree049_14,tree049_14]
def tree049_561 : CoverTree := CoverTree.split [tree049_10,tree049_324,tree049_560,tree049_70,tree049_70,tree049_70]
def tree049_562 : CoverTree := CoverTree.split [tree049_149,tree049_552,tree049_554,tree049_559,tree049_561,tree049_327]
def tree049_563 : CoverTree := CoverTree.reject 235
def tree049_564 : CoverTree := CoverTree.reject 206
def tree049_565 : CoverTree := CoverTree.split [tree049_10,tree049_393,tree049_332,tree049_334,tree049_31,tree049_70]
def tree049_566 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_374,tree049_375,tree049_14,tree049_14]
def tree049_567 : CoverTree := CoverTree.split [tree049_10,tree049_566,tree049_338,tree049_70,tree049_70,tree049_70]
def tree049_568 : CoverTree := CoverTree.split [tree049_10,tree049_70,tree049_129,tree049_70,tree049_70,tree049_70]
def tree049_569 : CoverTree := CoverTree.split [tree049_563,tree049_564,tree049_565,tree049_567,tree049_341,tree049_568]
def tree049_570 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_217,tree049_218,tree049_14,tree049_14]
def tree049_571 : CoverTree := CoverTree.split [tree049_10,tree049_345,tree049_210,tree049_211,tree049_346,tree049_570]
def tree049_572 : CoverTree := CoverTree.reject 376
def tree049_573 : CoverTree := CoverTree.split [tree049_10,tree049_572,tree049_350,tree049_351,tree049_352,tree049_70]
def tree049_574 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_409,tree049_391,tree049_392,tree049_14]
def tree049_575 : CoverTree := CoverTree.split [tree049_10,tree049_574,tree049_136,tree049_137,tree049_70,tree049_70]
def tree049_576 : CoverTree := CoverTree.split [tree049_10,tree049_566,tree049_140,tree049_70,tree049_70,tree049_70]
def tree049_577 : CoverTree := CoverTree.split [tree049_571,tree049_573,tree049_575,tree049_576,tree049_341,tree049_327]
def tree049_578 : CoverTree := CoverTree.split [tree049_119,tree049_529,tree049_551,tree049_562,tree049_569,tree049_577]
def tree049_579 : CoverTree := CoverTree.reject 105
def tree049_580 : CoverTree := CoverTree.reject 377
def tree049_581 : CoverTree := CoverTree.reject 378
def tree049_582 : CoverTree := CoverTree.reject 273
def tree049_583 : CoverTree := CoverTree.split [tree049_10,tree049_580,tree049_581,tree049_582,tree049_236,tree049_237]
def tree049_584 : CoverTree := CoverTree.split [tree049_423,tree049_423,tree049_423,tree049_579,tree049_583,tree049_428]
def tree049_585 : CoverTree := CoverTree.reject 243
def tree049_586 : CoverTree := CoverTree.reject 379
def tree049_587 : CoverTree := CoverTree.reject 307
def tree049_588 : CoverTree := CoverTree.split [tree049_90,tree049_90,tree049_587,tree049_14,tree049_14,tree049_14]
def tree049_589 : CoverTree := CoverTree.split [tree049_10,tree049_586,tree049_260,tree049_263,tree049_588,tree049_265]
def tree049_590 : CoverTree := CoverTree.split [tree049_10,tree049_442,tree049_369,tree049_21,tree049_94,tree049_14]
def tree049_591 : CoverTree := CoverTree.split [tree049_243,tree049_585,tree049_432,tree049_589,tree049_439,tree049_590]
def tree049_592 : CoverTree := CoverTree.reject 308
def tree049_593 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_172,tree049_592]
def tree049_594 : CoverTree := CoverTree.split [tree049_10,tree049_474,tree049_593,tree049_274,tree049_275,tree049_277]
def tree049_595 : CoverTree := CoverTree.split [tree049_149,tree049_594,tree049_446,tree049_378,tree049_380,tree049_384]
def tree049_596 : CoverTree := CoverTree.reject 253
def tree049_597 : CoverTree := CoverTree.split [tree049_10,tree049_386,tree049_285,tree049_389,tree049_275,tree049_179]
def tree049_598 : CoverTree := CoverTree.split [tree049_596,tree049_597,tree049_394,tree049_396,tree049_397,tree049_400]
def tree049_599 : CoverTree := CoverTree.split [tree049_146,tree049_584,tree049_591,tree049_595,tree049_598,tree049_420]
def tree049_600 : CoverTree := CoverTree.reject 74
def tree049_601 : CoverTree := CoverTree.reject 287
def tree049_602 : CoverTree := CoverTree.split [tree049_10,tree049_601,tree049_458,tree049_461,tree049_464,tree049_237]
def tree049_603 : CoverTree := CoverTree.split [tree049_423,tree049_423,tree049_423,tree049_602,tree049_469,tree049_428]
def tree049_604 : CoverTree := CoverTree.reject 288
def tree049_605 : CoverTree := CoverTree.split [tree049_10,tree049_471,tree049_244,tree049_247,tree049_604,tree049_250]
def tree049_606 : CoverTree := CoverTree.split [tree049_243,tree049_605,tree049_432,tree049_435,tree049_439,tree049_443]
def tree049_607 : CoverTree := CoverTree.reject 309
def tree049_608 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_172,tree049_607]
def tree049_609 : CoverTree := CoverTree.split [tree049_10,tree049_474,tree049_608,tree049_274,tree049_275,tree049_277]
def tree049_610 : CoverTree := CoverTree.split [tree049_149,tree049_609,tree049_446,tree049_447,tree049_380,tree049_384]
def tree049_611 : CoverTree := CoverTree.split [tree049_600,tree049_603,tree049_606,tree049_610,tree049_479,tree049_420]
def tree049_612 : CoverTree := CoverTree.reject 181
def tree049_613 : CoverTree := CoverTree.reject 79
def tree049_614 : CoverTree := CoverTree.reject 36
def tree049_615 : CoverTree := CoverTree.reject 16
def tree049_616 : CoverTree := CoverTree.reject 232
def tree049_617 : CoverTree := CoverTree.reject 233
def tree049_618 : CoverTree := CoverTree.reject 84
def tree049_619 : CoverTree := CoverTree.reject 250
def tree049_620 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_618,tree049_618,tree049_619,tree049_14]
def tree049_621 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_618,tree049_618,tree049_14,tree049_14]
def tree049_622 : CoverTree := CoverTree.reject 251
def tree049_623 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_622,tree049_14,tree049_14,tree049_14]
def tree049_624 : CoverTree := CoverTree.split [tree049_10,tree049_616,tree049_617,tree049_620,tree049_621,tree049_623]
def tree049_625 : CoverTree := CoverTree.reject 278
def tree049_626 : CoverTree := CoverTree.reject 279
def tree049_627 : CoverTree := CoverTree.reject 280
def tree049_628 : CoverTree := CoverTree.reject 310
def tree049_629 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_625,tree049_626,tree049_627,tree049_628]
def tree049_630 : CoverTree := CoverTree.reject 281
def tree049_631 : CoverTree := CoverTree.reject 311
def tree049_632 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_630,tree049_631,tree049_14,tree049_14]
def tree049_633 : CoverTree := CoverTree.reject 282
def tree049_634 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_633,tree049_14,tree049_14,tree049_14]
def tree049_635 : CoverTree := CoverTree.split [tree049_10,tree049_629,tree049_632,tree049_634,tree049_237,tree049_237]
def tree049_636 : CoverTree := CoverTree.split [tree049_612,tree049_613,tree049_614,tree049_615,tree049_624,tree049_635]
def tree049_637 : CoverTree := CoverTree.reject 216
def tree049_638 : CoverTree := CoverTree.reject 208
def tree049_639 : CoverTree := CoverTree.reject 209
def tree049_640 : CoverTree := CoverTree.reject 210
def tree049_641 : CoverTree := CoverTree.reject 217
def tree049_642 : CoverTree := CoverTree.reject 211
def tree049_643 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_641,tree049_642,tree049_14,tree049_14]
def tree049_644 : CoverTree := CoverTree.split [tree049_10,tree049_637,tree049_638,tree049_639,tree049_640,tree049_643]
def tree049_645 : CoverTree := CoverTree.reject 236
def tree049_646 : CoverTree := CoverTree.reject 238
def tree049_647 : CoverTree := CoverTree.reject 239
def tree049_648 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_135,tree049_646,tree049_647]
def tree049_649 : CoverTree := CoverTree.reject 107
def tree049_650 : CoverTree := CoverTree.reject 240
def tree049_651 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_649,tree049_650,tree049_14]
def tree049_652 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_649,tree049_14,tree049_14]
def tree049_653 : CoverTree := CoverTree.split [tree049_10,tree049_645,tree049_648,tree049_651,tree049_652,tree049_237]
def tree049_654 : CoverTree := CoverTree.reject 380
def tree049_655 : CoverTree := CoverTree.split [tree049_10,tree049_654,tree049_458,tree049_461,tree049_464,tree049_237]
def tree049_656 : CoverTree := CoverTree.split [tree049_224,tree049_644,tree049_653,tree049_655,tree049_469,tree049_428]
def tree049_657 : CoverTree := CoverTree.split [tree049_636,tree049_656,tree049_473,tree049_476,tree049_479,tree049_420]
def tree049_658 : CoverTree := CoverTree.split [tree049_488,tree049_528,tree049_578,tree049_599,tree049_611,tree049_657]
def tree049_659 : CoverTree := CoverTree.reject 42
def tree049_660 : CoverTree := CoverTree.reject 40
def tree049_661 : CoverTree := CoverTree.split [tree049_482,tree049_483,tree049_484,tree049_485,tree049_659,tree049_660]
def tree049_662 : CoverTree := CoverTree.reject 274
def tree049_663 : CoverTree := CoverTree.reject 172
def tree049_664 : CoverTree := CoverTree.reject 128
def tree049_665 : CoverTree := CoverTree.reject 121
def tree049_666 : CoverTree := CoverTree.reject 344
def tree049_667 : CoverTree := CoverTree.reject 345
def tree049_668 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_426,tree049_666,tree049_667]
def tree049_669 : CoverTree := CoverTree.reject 346
def tree049_670 : CoverTree := CoverTree.reject 347
def tree049_671 : CoverTree := CoverTree.reject 348
def tree049_672 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_669,tree049_670,tree049_671]
def tree049_673 : CoverTree := CoverTree.split [tree049_10,tree049_668,tree049_672,tree049_60,tree049_60,tree049_60]
def tree049_674 : CoverTree := CoverTree.split [tree049_224,tree049_662,tree049_663,tree049_664,tree049_665,tree049_673]
def tree049_675 : CoverTree := CoverTree.reject 237
def tree049_676 : CoverTree := CoverTree.reject 207
def tree049_677 : CoverTree := CoverTree.reject 328
def tree049_678 : CoverTree := CoverTree.reject 349
def tree049_679 : CoverTree := CoverTree.reject 350
def tree049_680 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_259,tree049_678,tree049_679]
def tree049_681 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_262,tree049_14,tree049_14]
def tree049_682 : CoverTree := CoverTree.split [tree049_10,tree049_677,tree049_680,tree049_681,tree049_60,tree049_60]
def tree049_683 : CoverTree := CoverTree.reject 329
def tree049_684 : CoverTree := CoverTree.reject 351
def tree049_685 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_684,tree049_14,tree049_14]
def tree049_686 : CoverTree := CoverTree.split [tree049_10,tree049_683,tree049_685,tree049_60,tree049_60,tree049_60]
def tree049_687 : CoverTree := CoverTree.reject 352
def tree049_688 : CoverTree := CoverTree.reject 353
def tree049_689 : CoverTree := CoverTree.reject 354
def tree049_690 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_687,tree049_688,tree049_689]
def tree049_691 : CoverTree := CoverTree.reject 355
def tree049_692 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_691,tree049_14,tree049_14]
def tree049_693 : CoverTree := CoverTree.split [tree049_10,tree049_690,tree049_692,tree049_60,tree049_60,tree049_60]
def tree049_694 : CoverTree := CoverTree.split [tree049_243,tree049_675,tree049_676,tree049_682,tree049_686,tree049_693]
def tree049_695 : CoverTree := CoverTree.reject 330
def tree049_696 : CoverTree := CoverTree.reject 331
def tree049_697 : CoverTree := CoverTree.reject 283
def tree049_698 : CoverTree := CoverTree.reject 356
def tree049_699 : CoverTree := CoverTree.reject 357
def tree049_700 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_698,tree049_699,tree049_14]
def tree049_701 : CoverTree := CoverTree.split [tree049_10,tree049_474,tree049_695,tree049_696,tree049_697,tree049_700]
def tree049_702 : CoverTree := CoverTree.reject 332
def tree049_703 : CoverTree := CoverTree.reject 324
def tree049_704 : CoverTree := CoverTree.reject 358
def tree049_705 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_280,tree049_704,tree049_14]
def tree049_706 : CoverTree := CoverTree.split [tree049_10,tree049_702,tree049_703,tree049_705,tree049_60,tree049_60]
def tree049_707 : CoverTree := CoverTree.split [tree049_10,tree049_493,tree049_495,tree049_60,tree049_60,tree049_60]
def tree049_708 : CoverTree := CoverTree.split [tree049_149,tree049_701,tree049_706,tree049_707,tree049_502,tree049_508]
def tree049_709 : CoverTree := CoverTree.reject 333
def tree049_710 : CoverTree := CoverTree.reject 359
def tree049_711 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_245,tree049_710,tree049_14]
def tree049_712 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_245,tree049_14,tree049_14]
def tree049_713 : CoverTree := CoverTree.split [tree049_10,tree049_386,tree049_709,tree049_711,tree049_712,tree049_60]
def tree049_714 : CoverTree := CoverTree.reject 334
def tree049_715 : CoverTree := CoverTree.reject 360
def tree049_716 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_135,tree049_715,tree049_14]
def tree049_717 : CoverTree := CoverTree.reject 361
def tree049_718 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_717,tree049_14,tree049_14]
def tree049_719 : CoverTree := CoverTree.split [tree049_10,tree049_714,tree049_716,tree049_718,tree049_60,tree049_60]
def tree049_720 : CoverTree := CoverTree.split [tree049_510,tree049_713,tree049_719,tree049_514,tree049_299,tree049_302]
def tree049_721 : CoverTree := CoverTree.split [tree049_59,tree049_59,tree049_59,tree049_213,tree049_214,tree049_215]
def tree049_722 : CoverTree := CoverTree.reject 325
def tree049_723 : CoverTree := CoverTree.split [tree049_10,tree049_345,tree049_210,tree049_211,tree049_721,tree049_722]
def tree049_724 : CoverTree := CoverTree.reject 381
def tree049_725 : CoverTree := CoverTree.reject 382
def tree049_726 : CoverTree := CoverTree.split [tree049_10,tree049_724,tree049_725,tree049_519,tree049_60,tree049_60]
def tree049_727 : CoverTree := CoverTree.reject 383
def tree049_728 : CoverTree := CoverTree.split [tree049_10,tree049_727,tree049_522,tree049_309,tree049_60,tree049_60]
def tree049_729 : CoverTree := CoverTree.split [tree049_723,tree049_726,tree049_728,tree049_514,tree049_526,tree049_299]
def tree049_730 : CoverTree := CoverTree.split [tree049_104,tree049_674,tree049_694,tree049_708,tree049_720,tree049_729]
def tree049_731 : CoverTree := CoverTree.reject 275
def tree049_732 : CoverTree := CoverTree.reject 161
def tree049_733 : CoverTree := CoverTree.reject 335
def tree049_734 : CoverTree := CoverTree.reject 336
def tree049_735 : CoverTree := CoverTree.reject 326
def tree049_736 : CoverTree := CoverTree.reject 327
def tree049_737 : CoverTree := CoverTree.reject 249
def tree049_738 : CoverTree := CoverTree.split [tree049_10,tree049_733,tree049_734,tree049_735,tree049_736,tree049_737]
def tree049_739 : CoverTree := CoverTree.reject 337
def tree049_740 : CoverTree := CoverTree.reject 362
def tree049_741 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_233,tree049_740,tree049_14,tree049_14]
def tree049_742 : CoverTree := CoverTree.split [tree049_10,tree049_739,tree049_232,tree049_741,tree049_236,tree049_237]
def tree049_743 : CoverTree := CoverTree.reject 363
def tree049_744 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_425,tree049_426,tree049_14,tree049_743]
def tree049_745 : CoverTree := CoverTree.split [tree049_10,tree049_744,tree049_240,tree049_237,tree049_237,tree049_237]
def tree049_746 : CoverTree := CoverTree.split [tree049_224,tree049_731,tree049_732,tree049_738,tree049_742,tree049_745]
def tree049_747 : CoverTree := CoverTree.split [tree049_10,tree049_431,tree049_253,tree049_255,tree049_31,tree049_70]
def tree049_748 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_322,tree049_436,tree049_437,tree049_14]
def tree049_749 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_267,tree049_14,tree049_14,tree049_14]
def tree049_750 : CoverTree := CoverTree.split [tree049_10,tree049_748,tree049_749,tree049_546,tree049_70,tree049_70]
def tree049_751 : CoverTree := CoverTree.split [tree049_243,tree049_533,tree049_747,tree049_543,tree049_750,tree049_550]
def tree049_752 : CoverTree := CoverTree.reject 338
def tree049_753 : CoverTree := CoverTree.split [tree049_69,tree049_69,tree049_276,tree049_14,tree049_14,tree049_14]
def tree049_754 : CoverTree := CoverTree.split [tree049_10,tree049_474,tree049_752,tree049_274,tree049_275,tree049_753]
def tree049_755 : CoverTree := CoverTree.reject 384
def tree049_756 : CoverTree := CoverTree.split [tree049_10,tree049_755,tree049_207,tree049_281,tree049_31,tree049_70]
def tree049_757 : CoverTree := CoverTree.split [tree049_10,tree049_566,tree049_556,tree049_70,tree049_558,tree049_70]
def tree049_758 : CoverTree := CoverTree.split [tree049_149,tree049_754,tree049_756,tree049_757,tree049_561,tree049_327]
def tree049_759 : CoverTree := CoverTree.reject 364
def tree049_760 : CoverTree := CoverTree.split [tree049_30,tree049_30,tree049_30,tree049_245,tree049_759,tree049_14]
def tree049_761 : CoverTree := CoverTree.split [tree049_10,tree049_386,tree049_285,tree049_760,tree049_275,tree049_70]
def tree049_762 : CoverTree := CoverTree.split [tree049_563,tree049_761,tree049_565,tree049_567,tree049_341,tree049_568]
def tree049_763 : CoverTree := CoverTree.reject 385
def tree049_764 : CoverTree := CoverTree.split [tree049_10,tree049_763,tree049_350,tree049_351,tree049_352,tree049_70]
def tree049_765 : CoverTree := CoverTree.split [tree049_571,tree049_764,tree049_575,tree049_576,tree049_341,tree049_327]
def tree049_766 : CoverTree := CoverTree.split [tree049_119,tree049_746,tree049_751,tree049_758,tree049_762,tree049_765]
def tree049_767 : CoverTree := CoverTree.reject 276
def tree049_768 : CoverTree := CoverTree.reject 339
def tree049_769 : CoverTree := CoverTree.split [tree049_10,tree049_768,tree049_458,tree049_461,tree049_464,tree049_237]
def tree049_770 : CoverTree := CoverTree.split [tree049_224,tree049_767,tree049_653,tree049_769,tree049_469,tree049_428]
def tree049_771 : CoverTree := CoverTree.reject 340
def tree049_772 : CoverTree := CoverTree.split [tree049_10,tree049_471,tree049_244,tree049_247,tree049_771,tree049_250]
def tree049_773 : CoverTree := CoverTree.split [tree049_10,tree049_434,tree049_260,tree049_263,tree049_588,tree049_265]
def tree049_774 : CoverTree := CoverTree.split [tree049_243,tree049_772,tree049_432,tree049_773,tree049_439,tree049_590]
def tree049_775 : CoverTree := CoverTree.reject 341
def tree049_776 : CoverTree := CoverTree.split [tree049_10,tree049_345,tree049_210,tree049_211,tree049_775,tree049_219]
def tree049_777 : CoverTree := CoverTree.split [tree049_776,tree049_597,tree049_394,tree049_396,tree049_397,tree049_400]
def tree049_778 : CoverTree := CoverTree.split [tree049_146,tree049_770,tree049_774,tree049_595,tree049_777,tree049_420]
def tree049_779 : CoverTree := CoverTree.reject 342
def tree049_780 : CoverTree := CoverTree.split [tree049_10,tree049_616,tree049_617,tree049_779,tree049_621,tree049_623]
def tree049_781 : CoverTree := CoverTree.reject 92
def tree049_782 : CoverTree := CoverTree.split [tree049_612,tree049_613,tree049_614,tree049_615,tree049_780,tree049_781]
def tree049_783 : CoverTree := CoverTree.reject 277
def tree049_784 : CoverTree := CoverTree.reject 343
def tree049_785 : CoverTree := CoverTree.reject 286
def tree049_786 : CoverTree := CoverTree.split [tree049_10,tree049_645,tree049_648,tree049_784,tree049_785,tree049_237]
def tree049_787 : CoverTree := CoverTree.split [tree049_224,tree049_783,tree049_786,tree049_602,tree049_469,tree049_428]
def tree049_788 : CoverTree := CoverTree.split [tree049_782,tree049_787,tree049_606,tree049_610,tree049_479,tree049_420]
def tree049_789 : CoverTree := CoverTree.reject 218
def tree049_790 : CoverTree := CoverTree.split [tree049_228,tree049_228,tree049_374,tree049_375,tree049_789,tree049_14]
def tree049_791 : CoverTree := CoverTree.split [tree049_10,tree049_790,tree049_458,tree049_461,tree049_464,tree049_237]
def tree049_792 : CoverTree := CoverTree.split [tree049_224,tree049_644,tree049_653,tree049_791,tree049_469,tree049_428]
def tree049_793 : CoverTree := CoverTree.split [tree049_636,tree049_792,tree049_473,tree049_476,tree049_479,tree049_420]
def tree049_794 : CoverTree := CoverTree.split [tree049_661,tree049_730,tree049_766,tree049_778,tree049_788,tree049_793]
def tree049_795 : CoverTree := CoverTree.split [tree049_51,tree049_102,tree049_289,tree049_481,tree049_658,tree049_794]
def tree049 : CoverTree := tree049_795

end Snake9.Shared89
