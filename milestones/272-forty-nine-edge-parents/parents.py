"""List all 49-edge Q7 snakes containing a selected interval of a published optimal Q7 snake."""
from argparse import ArgumentParser
from collections import defaultdict, Counter
from pathlib import Path
import json,sys

HERE=Path(__file__).resolve().parent
R270=HERE.parent/"270-optimal-seven-dimensional-arms"
sys.path.insert(0,str(R270))
from all_primers import points,unrooted,paircheck,read,write,ordered,wordof

def grow(path):
    tip=path[-1]; occupied=set(path)
    for d in range(7):
        w=tip^(1<<d)
        if w not in occupied and all((v^w).bit_count()!=1 for v in path[:-1]):
            yield path+[w]

def generate(window):
    source=read(R270/"palani-q7.json")["paths"]
    originals={unrooted(r["q7_parent"]) for r in source.values()}
    windows={unrooted(points(bytes.fromhex(q)[i:i+window])) for q in originals for i in range(51-window)}
    layer=windows
    levels={window:len(layer)}
    for n in range(window+1,50):
        new=set()
        for w in layer:
            p=points(bytes.fromhex(w))
            for d in (p,p[::-1]):
                new.update(unrooted(child) for child in grow(d))
        layer=new
        levels[n]=len(layer)
    return dict(window=window,intervals=sorted(windows),counts=levels,parents=sorted(layer))

if __name__=="__main__":
    ap=ArgumentParser();ap.add_argument("--window",type=int,default=40);a=ap.parse_args()
    result=generate(a.window)
    write(HERE/("parents-window-"+str(a.window)+".json"),result)
    print(result["counts"],flush=True)
