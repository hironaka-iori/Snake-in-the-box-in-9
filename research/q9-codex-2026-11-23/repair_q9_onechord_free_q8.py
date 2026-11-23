"""Search Q9 paths by replacing a whole Q8 half of a one-chord parent."""
import json
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
from search_q9_free_record_slice import normalize
from retry_q9_six_cube_sites_cadical import search
from verify_q9_center_avoidance import verify
def work(job):
    row,axis,side,q,target=job
    fixed={v for v in q if v<256}
    domain=fixed|set(range(256,512))
    st,w=search(fixed,set(q),target,3500,domain)
    if w:
        verify(w); assert len(w)>=target+1 and {v for v in w if v<256}==fixed
    return row,axis,side,len(fixed),st,w
if __name__=="__main__":
    p=json.load(open("q9_explicit_q8_96_plus_94.json"))["vertices"]
    z=work((-1,8,0,normalize(p,8,0),191))
    assert z[4]=="FOUND";print(json.dumps(z),flush=True)
    seen=set();jobs=[]
    for i,l in enumerate(open("q9_all_verified_onechord_walks.txt")):
        p=list(map(int,l.split()))
        assert len(set(p))==len(p)==193
        assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
        assert sum((v^w).bit_count()==1 for j,w in enumerate(p) for v in p[:max(0,j-1)])==1
        for axis in range(9):
            for side in (0,1):
                q=normalize(p,axis,side);mask=sum(1<<v for v in q if v<256)
                if mask in seen:continue
                seen.add(mask);jobs.append((i,axis,side,q,192))
    import random;random.Random(42192).shuffle(jobs)
    print(json.dumps({"distinct_labelled_domains":len(jobs)}),flush=True)
    with ProcessPoolExecutor(2) as pool:
        for z in pool.map(work,jobs,chunksize=4):
            print(json.dumps(z,separators=(",",":")),flush=True)
            if z[-1]:break
