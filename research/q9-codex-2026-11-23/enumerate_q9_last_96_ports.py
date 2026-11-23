"""Enumerate every port case for 96-edge shapes outstanding in the 726-shape library."""
import gzip,json,random,sys
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from split_q9_long_donor_ports import norm,path,cases,run
def state():
    data=defaultdict(lambda:defaultdict(set))
    for f in ['q9_long_arm_anywhere_atleast192.jsonl','q9_bitterman_free_192.jsonl','q9_bitterman_trims96_free_192.jsonl','q9_free_new_q8_shapes_192.jsonl','q9_free_extra_193donors_192.jsonl','q9_long_arm_anywhere_deep1.jsonl','q9_long_arm_anywhere_deep2.jsonl','q9_free55_mothers_192.jsonl']:
        for line in open(f):
            r=json.loads(line)
            if type(r) is not list or len(r)!=6 or type(r[0]) is not str or len(r[0])!=192:continue
            w=''.join(map(str,bytes.fromhex(r[0])));w=min(norm(w),norm(w[::-1]))
            data[w][r[1],r[2]].add(r[3])
    return data
def choices():
    s=state();hard={json.loads(l)['word'] for l in gzip.open('q9_hard96_port_duals.jsonl.gz','rt')}
    words=[w for w in Path('q8_catalogue_96_98.words').read_text().split() if len(w)==96]
    def check(w,k):return bool(s[w][k]&{'DUAL_EXCLUSION','EXHAUSTED','EMPTY_FACTOR'})
    return [w for w in words if w not in hard and not all(check(w,k) for k in [(0,192),(1,192),(0,193)])]
if __name__=='__main__':
    words=choices();jobs=[(w,c,10) for w in words for c in cases(path(w))];random.Random(725134).shuffle(jobs)
    print('START',len(words),len(jobs),flush=True)
    with ProcessPoolExecutor(int(sys.argv[1])) as pool,gzip.open(sys.argv[2],'wt') as f:
        for i,r in enumerate(pool.map(run,jobs,chunksize=1)):
            f.write(json.dumps(r,separators=(',',':'))+'\n');f.flush();print(i,r['word'],r.get('bound','EMPTY'),flush=True)
    print('DONE',len(words),len(jobs),flush=True)

