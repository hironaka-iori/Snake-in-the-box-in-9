"""Place every archived 98-edge candidate and rebuild the best compatible rooted arms."""
from opposite import HERE,MS,roots
import sys
sys.path.insert(0,str(MS/"268-archived-94-arms"))
from placement import run

if __name__=="__main__":
    run(HERE,98,"placements.json",roots(),iterations=3000)
