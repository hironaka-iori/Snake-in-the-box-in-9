"""Independent verifier: adjacency matrix and anchored square census, no research imports."""
import argparse, hashlib, itertools, json, pathlib, subprocess, time
P = pathlib.Path(__file__).resolve().parents[1]
R = P.parents[1]

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(w):
    vs=w['path']; n=w['n']; S=set(vs)
    assert len(S)==len(vs)
    adjacency=[[sum(a!=b for a,b in zip(f'{x:0{n}b}',f'{y:0{n}b}'))==1 for y in vs] for x in vs]
    assert all(adjacency[i][j]==(abs(i-j)==1) for i in range(len(vs)) for j in range(len(vs)))
    empty_anchored=0; single=0; alph=[]
    pairs=list(itertools.combinations(range(n),2))
    for x in range(1<<n):
        for a,b in pairs:
            corners={x,x^(1<<a),x^(1<<b),x^(1<<a)^(1<<b)}
            count=len(S & corners)
            empty_anchored += count==0
            single += count==1 and x in S
    for x in vs:
        alph.append(sum(not(S & {x^(1<<a),x^(1<<b),x^(1<<a)^(1<<b)}) for a,b in pairs))
    assert empty_anchored==w['E'] and single==w['T'] and alph==w['alpha']
    shell=set(y for q in range(4) for y in range(1<<n) if (q^y).bit_count()==1)-set(range(4))
    return {'vertices':len(vs),'E':empty_anchored,'T':single,'touches_canonical_face':len(S&shell),
            'canonical_face_empty':not(S & set(range(4))), 'all_pairs_checked':len(vs)**2}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',required=True); args=ap.parse_args()
    start=time.monotonic(); records=[]
    for p in sorted((P/'runs').glob('*/*.json')):
        z=json.loads(p.read_text(encoding='utf-8'))
        w=z.get('result',{}).get('witness')
        if w:
            records.append({'file':str(p.relative_to(R)),'sha256':digest(p),'checked':verify(w)})
    cycle=json.loads((P/'runs/20261020-a/cycle_extract.json').read_text())['result']
    ds=cycle['edges'][0]['shape'][:]
    for e in cycle['edges'][:2]:
        labels=list(dict.fromkeys(ds[-7:])); ds.append(labels[e['append_label']])
    assert ds==[0,1,2,3,0,4,2,3,1]
    vs=[0]
    for d in ds: vs.append(vs[-1]^(1<<d))
    assert vs[-1]==16
    assert all((vs[i]^vs[j]).bit_count()!=1 for i in range(10) for j in range(i+2,10) if (i,j)!=(0,9))
    result={'status':'PASS','scope':'Independent computational verification, not a Lean proof',
            'git':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
            'checker_sha256':digest(pathlib.Path(__file__)),'seconds':time.monotonic()-start,
            'witnesses':records,'cycle':{'directions':ds,'vertices':vs,'unique_chord_indices':[0,9]}}
    # Earlier UNKNOWN receipts remain intact; a later verified witness resolves their feasibility.
    run=P/'runs/20261020-b'
    w=json.loads((run/'joint_cycle_03.json').read_text())['result']['witness']
    S=set(w['path']); av=dict(zip(w['path'],w['alpha'])); derived=[]
    for k in [1,2]:
        f=run/f'joint_cycle_{k:02}.input.json'; spec=json.loads(f.read_text())
        assert set(spec['selected'])<=S
        for v,a,b,lo,hi in spec['centres']:
            idx=w['path'].index(v)
            assert 0<idx<len(w['path'])-1
            assert {w['path'][idx-1]^v,w['path'][idx+1]^v}=={1<<a,1<<b}
            assert lo<=av[v]<=hi
        derived.append({'case':f'joint_cycle_{k:02}','status':'SAT_BY_LATER_WITNESS',
                        'input_sha256':digest(f),'witness_sha256':digest(run/'joint_cycle_03.json')})
    result['resolved_timeouts']=derived
    pathlib.Path(args.out).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
