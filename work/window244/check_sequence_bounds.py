"""Independent exact DP for the two Stage-1 necessary-condition relaxations.

This is executable evidence only. No solver and no Stage-2 survey is run.
Values >=6 can be replaced by 4 (even) or 5 (odd): this preserves parity,
the neighbour-of-1 constraints, and the forbidden 222/223/322 tests, while
weakly decreasing cost. Endpoints therefore need only values 4 and 5.
"""
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244/sequence-bounds.json'

def run(forbidden):
    # State = last two alpha values and total cost parity; cost includes first endpoint.
    state={(0,e,e%2):e for e in (4,5)}
    rows=[]
    # After n internal vertices, close with a last endpoint of alpha 4 or 5.
    for n in range(511):
        best=[None,None]
        for (_,y,parity),cost in state.items():
            for e in (4,5):
                new=cost+e;p=new%2
                if best[p] is None or new<best[p]:best[p]=new
        vertices=n+2
        # E is four times the number of empty squares, so T+v must be even.
        t=best[vertices%2]
        e=18428-70*vertices-2*t
        rows.append(dict(edges=vertices-1,vertices=vertices,min_T=t,E=e,
                         relaxed_feasible=e>=0 and e%4==0))
        nxt={}
        for (x,y,parity),cost in state.items():
            for z in range(1,6):
                if (y==1 and z<4) or (z==1 and y<4):continue
                if (x,y,z) in forbidden:continue
                total=cost+z;key=(y,z,total%2)
                if total<nxt.get(key,10**9):nxt[key]=total
        state=nxt
    bound=max(r['edges'] for r in rows if r['relaxed_feasible'])
    return dict(maximum_relaxed_edges=bound,rows=rows)

result={'evidence':'EXECUTABLE_DP_ONLY','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
        'identity':'E + 2*T + 70*v = 18428; E >= 0 and E divisible by 4',
        'baseline':run({(2,2,2)}),
        'with_223_and_reverse':run({(2,2,2),(2,2,3),(3,2,2)})}
OUT.write_text(json.dumps(result,indent=2)+'\n')
for k in ['baseline','with_223_and_reverse']:
    print(k,result[k]['maximum_relaxed_edges'])
assert result['baseline']['maximum_relaxed_edges']==245
assert result['with_223_and_reverse']['maximum_relaxed_edges']==244
