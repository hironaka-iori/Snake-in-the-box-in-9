"""Bounded enumeration of optimal Q8 snakes near a published seed.

Enumerates every completion of fixed prefixes unless the node limit is hit.
Canonical transitions quotient translation, coordinate permutations and reversal.
This is a discovery search, never a global classification.
"""
import json,time,argparse
from pathlib import Path
from check_snake import verify

N=256
MASK=[sum(1 << (v^(1<<k)) for k in range(8)) for v in range(N)]
def canonical(vertices):
    transitions=[(u^v).bit_length()-1 for u,v in zip(vertices,vertices[1:])]
    def norm(xs):
        renaming={}
        return tuple(renaming.setdefault(x,len(renaming)) for x in xs)
    return min(norm(transitions),norm(reversed(transitions)))

def enumerate_prefix(prefix,limit,accept):
    ban=sum(1<<v for v in prefix)
    for v in prefix[:-1]: ban |= MASK[v]
    nodes=0
    stopped=False
    completions=0
    trail=[]
    def dfs(head,blocked,remaining):
        nonlocal nodes,stopped,completions
        nodes+=1
        if nodes>limit:
            stopped=True;return
        if remaining==0:
            completions+=1
            accept(prefix+trail)
            return
        options=MASK[head]&~blocked
        while options:
            bit=options&-options;options-=bit
            nxt=bit.bit_length()-1
            trail.append(nxt)
            dfs(nxt,blocked|MASK[head]|bit,remaining-1)
            trail.pop()
            if stopped:return
    dfs(prefix[-1],ban,99-len(prefix))
    return {'nodes':nodes,'status':'UNKNOWN' if stopped else 'EXHAUSTED','completions':completions}

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--retain',type=int,default=50)
    ap.add_argument('--nodes',type=int,default=3000000)
    ap.add_argument('--seeds',type=int,default=30)
    args=ap.parse_args()
    first=json.loads(Path('outputs/snake8_witness.json').read_text())['vertex_sequence']
    catalog={canonical(first):first}
    queue=[first]
    reports=[]
    def accept(p):
        key=canonical(p)
        if key not in catalog:
            checked=verify(list(key),8)
            assert checked['edges']==98
            catalog[key]=checked['vertex_sequence']
            queue.append(checked['vertex_sequence'])
    start=time.monotonic()
    index=0
    while index<len(queue) and index<args.seeds:
        for rev in [False,True]:
            path=queue[index][::-1] if rev else queue[index]
            r=enumerate_prefix(path[:args.retain],args.nodes,accept)
            r.update(seed=index,reversed=rev)
            reports.append(r)
        index+=1
        print(json.dumps({'processed':index,'classes_found':len(queue),'nodes':sum(r['nodes'] for r in reports)}),flush=True)
    result={'dimension':8,'edges':98,'retained_vertices':args.retain,
            'node_limit_per_search':args.nodes,'classes_found':len(queue),
            'elapsed_seconds':time.monotonic()-start,'searches':reports,
            'vertices':queue,'scope':'Local prefix completions; no claim of a complete global census.'}
    Path(f'outputs/snake8_exploration_{args.retain}.json').write_text(json.dumps(result,indent=2))
