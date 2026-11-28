"""Partition a remaining crossing-port case by its zero or one opposite-face neighbours."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from middles import HERE,N,check,read,rebuild,save
from returns import cases,decide,lower_formula,old_shapes


def partition(run,t,dep,tips,maj):
    vertical=set(t)|set(dep)
    allowed=(set(range(256))-set(run)-set(t))|vertical
    def around(v):
        return sorted(w for w in N[v][:8] if w in allowed)
    root=min(vertical,key=lambda v:(len(around(v)),v))
    ns=around(root)
    branches=[(str(v),[(v,True)]) for v in ns]
    # With no lower neighbour this lower vertex is itself a global endpoint.
    # A return at this site would isolate a single vertical edge.
    if root not in t and len(tips)<2 and ((root+256).bit_count()&1)==maj:
        branches.append(('empty',[(v,False) for v in ns]))
    return root,branches


def replay(run,t,dep,tips,maj,group,scratch,verifier):
    root,branches=partition(run,t,dep,tips,maj)
    assert root==group['port'] and group['expected']==[k for k,_ in branches]
    statuses=[]
    assert set(group['rows'])<=set(group['expected'])
    for tag,pins in branches:
        row=group['rows'].get(tag,{})
        status=row.get('status','open')
        statuses.append(status)
        if status=='excluded':
            f,x=lower_formula(run,t,dep,tips,maj,row['cycles'])
            for v,selected in pins:
                f.clauses.append([x[v] if selected else -x[v]])
            cnf=scratch/'child.cnf'
            assert f.save(cnf)==row['cnf_sha256']
            assert rebuild.masks.p.check_proof(cnf,HERE/'return-proofs'/row['proof'],verifier)==row['replay']
        if status=='witness':
            check(row['path'])
            assert len(row['path'])==193
    return 'witness' if 'witness' in statuses else 'excluded' if all(s=='excluded' for s in statuses) else 'open'


def main():
    ap=ArgumentParser()
    ap.add_argument('--seconds',type=int,default=8)
    ap.add_argument('--limit',type=int,default=120)
    args=ap.parse_args()
    geo=read(HERE/'geometry.json')
    old=old_shapes(geo)
    parents=read(HERE/'returns.json')
    direct=read(HERE/'full-192.json')
    lower=read(HERE/'full-191.json') if (HERE/'full-191.json').exists() else {}
    file=HERE/'neighbours.json'
    ledger=read(file) if file.exists() else {}
    steps=0
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        tools=rebuild.masks.compilers(scratch)
        for k,r in sorted(geo.items(),key=lambda e:-e[1]['archived_191_count']):
            if any(c['status']=='excluded' for c in lower.get(k,{}).values()):
                continue
            for maj in (0,1):
                if direct[k][str(maj)]['status']=='excluded':
                    continue
                for tag,run,t,dep,tips,rule in cases(r,old,maj):
                    par=parents.get(k,{}).get(tag,{})
                    if rule or par.get('status')!='open':
                        continue
                    port,branches=partition(run,t,dep,tips,maj)
                    group=ledger.setdefault(k,{}).setdefault(tag,dict(port=port,expected=[j for j,_ in branches],rows={}))
                    for j,pins in branches:
                        if group['rows'].get(j,{}).get('status') in ('excluded','witness'):
                            continue
                        row=decide(run,t,dep,tips,maj,scratch,tools,args.seconds,pins,par['cycles'])
                        group['rows'][j]=row
                        save(file,ledger)
                        steps+=1
                        print(r['archived_source'],tag,port,j,row['status'],flush=True)
                        if steps>=args.limit or row['status']=='witness':
                            return
    print('Port-neighbour branches run',steps)


if __name__=='__main__':
    main()
