"""Choose unresolved intact 96-edge donors plus geometrically different 95-edge donors."""
import json,sys,gzip,random
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
from split_q9_long_donor_ports import cases,run,donors,path,norm
def targets96():
    states={}
    for f in ('q9_long_arm_anywhere_atleast192.jsonl','q9_bitterman_free_192.jsonl','q9_bitterman_trims96_free_192.jsonl','q9_free_new_q8_shapes_192.jsonl','q9_free_extra_193donors_192.jsonl','q9_long_arm_anywhere_deep1.jsonl','q9_long_arm_anywhere_deep2.jsonl'):
        for line in Path(f).read_text().splitlines():
            r=json.loads(line)
            if type(r) is not list or len(r)!=6 or not isinstance(r[0],str) or len(r[0])!=192:continue
            w=''.join(str(x) for x in bytes.fromhex(r[0]));w=min(norm(w),norm(w[::-1]))
            states.setdefault((w,r[1],r[2]),set()).add(r[3])
    return sorted({w for (w,e,g),s in states.items() if s=={'UNKNOWN'} and g==192})
def targets95(limit):
    words=donors(95);r=random.Random(551923);r.shuffle(words);buckets={}
    for w in words:
        p=path(w);v=set(p);inside=set(p[1:-1]);opt=[x for x in set(range(256))-v if all(x^1<<d not in inside for d in range(8))]
        edges=sum((x^y).bit_count()==1 for i,x in enumerate(opt) for y in opt[:i])
        buckets.setdefault((len(opt),edges),[]).append(w)
    ans=[];keys=sorted(buckets,reverse=True)
    while len(ans)<limit and any(buckets.values()):
        for k in keys:
            if buckets[k]:ans.append(buckets[k].pop())
            if len(ans)==limit:break
    return ans
if __name__=='__main__':
    size,limit,parts,workers=map(int,sys.argv[1:5]);out=sys.argv[5]
    words=(targets96() if size==96 else targets95(limit))[:limit]
    jobs=[(w,c,parts) for w in words for c in cases(path(w))]
    # Interleave donors to cover more choices early.
    random.Random(391426).shuffle(jobs)
    print('START',len(words),len(jobs),flush=True)
    with ProcessPoolExecutor(workers) as pool,gzip.open(out,'wt') as f:
        for i,r in enumerate(pool.map(run,jobs,chunksize=1)):
            f.write(json.dumps(r,separators=(',',':'))+'\n');f.flush()
            print(i,r['word'],r.get('bound','EMPTY'),flush=True)
    print('DONE',len(words),len(jobs),flush=True)
