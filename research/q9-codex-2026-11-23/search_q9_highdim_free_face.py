"""Hold an eight-dimensional donor fixed and let the other face vary freely."""
import argparse
import hashlib
import json
import random
from pathlib import Path
from retry_q9_six_cube_cycle_cuts import search
from verify_q9_center_avoidance import verify

def run(face,length,cap,phase):
    pool=face|set(range(256,512))
    s,w=search(face,phase,length,cap,allowed=pool)
    if w:
        verify(w);assert set(v for v in w if v<256)==face and len(w)>length
    return [s,w]

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('bank');ap.add_argument('num',type=int)
    a=ap.parse_args();whole=list(map(int,Path('q9_forest_ports_control.log').read_text().splitlines()[0].split()[1:]))
    control=run({v for v in whole if v<256},191,30000,set(whole));assert control[1]
    print(json.dumps(['control',*control]),flush=True)
    rows=Path(a.bank).read_text().splitlines();order=list(range(len(rows)));random.Random(984411).shuffle(order)
    for k in order[:a.num]:
        face=set(map(int,rows[k].split()[1:]))
        h=hashlib.sha256(bytes(sorted(face))).hexdigest()
        s,w=run(face,192,1000,face)
        print(json.dumps([k,len(face),h,s,w],separators=(',',':')),flush=True)
        if w:break
