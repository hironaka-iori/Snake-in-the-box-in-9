"""Choose target-192 searches that together cover all placements in the first donor."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE=Path(__file__).resolve().parent
PREV=next(HERE.parent.glob('280-*'))
sys.path.insert(0,str(PREV))
from interval import BANK, check, free_graph, rebuild, solve
from compact import compact
from prefix import BASE, compile_worker
from spectrum import shape


def save(file, data):
    pending=file.with_suffix('.pending')
    pending.write_bytes((json.dumps(data,separators=(',',':'))+'\n').encode())
    pending.replace(file)


def native(exe, core, scratch, budget):
    inp=scratch/'native.tsv'
    out=scratch/'result.tsv'
    inp.write_text('core\t'+','.join(map(str,core))+'\n')
    subprocess.run([str(exe),str(inp),str(out),'192',str(budget)],check=True)
    _,status,nodes,prunes,path=out.read_text().rstrip('\n').split('\t')
    row=dict(status=status,nodes=int(nodes),prunes=int(prunes),budget=budget)
    if status=='witness':
        p=list(map(int,path.split(',')))
        check(p)
        assert len(p)==193 and any(p[i:i+len(core)] in (core,core[::-1]) for i in range(len(p)-len(core)+1))
        row['path']=p
    return row


def decide(core,scratch,workers,tools,seconds,budget):
    check(core)
    row=dict(core=core,native={})
    for name,exe in workers.items():
        result=native(exe,core,scratch,budget)
        row['native'][name]=result
        if result['status']=='witness':
            row.update(status='witness',path=result['path'])
            return row
    if all(r['status']=='excluded' for r in row['native'].values()):
        return dict(**row,status='excluded',method='two independent native searches')
    cases={}
    for maj in (0,1):
        r=solve(core,192,maj,HERE,scratch,tools[0],seconds)
        compact(core,r,HERE,scratch,*tools)
        cases[str(maj)]=r
        if r['status']=='witness':
            row.update(status='witness',path=r['path'],cases=cases)
            return row
        if r['status']=='open':
            break
    return dict(**row,cases=cases,status='excluded' if len(cases)==2 and all(r['status']=='excluded' for r in cases.values()) else 'open',method='endpoint parity certificates')


def prefix_hits():
    return {shape(r['core']):r['core'] for r in json.loads((PREV/'decisions.json').read_bytes()).values()
            if len(r['cases'])==2 and all(v['status']=='excluded' for v in r['cases'].values())}


def starts_covered(donor,width,certs):
    starts=set()
    for n in {len(k) for k in certs}:
        if n>width:
            continue
        for i in range(len(donor)-n):
            if shape(donor[i:i+n+1]) in certs:
                starts.update(range(max(0,i+n-width),min(i,len(donor)-width-1)+1))
    return starts


def main():
    ap=ArgumentParser()
    ap.add_argument('width',type=int)
    ap.add_argument('--count',type=int,default=12)
    ap.add_argument('--seconds',type=int,default=4)
    ap.add_argument('--floor',type=int,default=0)
    ap.add_argument('--budget',type=int,default=28000)
    args=ap.parse_args()
    donor=json.loads(BANK.read_bytes())[0]['vertex_sequence']
    output=HERE/'windows.json'
    ledger=json.loads(output.read_bytes()) if output.exists() else {}
    known=prefix_hits()
    known.update({shape(r['core']):r['core'] for r in ledger.values() if r['status']=='excluded'})
    width=args.width
    candidates=[]
    for n in sorted({max(args.floor,v) for v in (width-15,width-9,width-5,width) if v<=width}):
        for i in range(len(donor)-n):
            core=donor[i:i+n+1]
            key=sha256(shape(core)).hexdigest()
            starts=set(range(max(0,i+n-width),min(i,len(donor)-width-1)+1))
            candidates.append((key,i,core,starts))
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        workers={name:compile_worker(BASE/(name+'.cs'),scratch) for name in ('Target','TargetReplay')}
        tools=rebuild.masks.compilers(scratch)
        for _ in range(args.count):
            rest=set(range(len(donor)-width))-starts_covered(donor,width,known)
            eligible=[t for t in candidates if t[0] not in ledger and t[3]&rest]
            if not rest or not eligible:
                break
            gain=max(len(t[3]&rest) for t in eligible)
            choices=[t for t in eligible if len(t[3]&rest)==gain]
            key,i,core,_=min(choices,key=lambda t:(len(free_graph(t[2])),t[1]))
            r=decide(core,scratch,workers,tools,args.seconds,args.budget)
            r.update(archive='191-0',offset=i,requested_width=width)
            ledger[key]=r
            save(output,ledger)
            print(i,len(core)-1,r['status'],r.get('method','construction'),'remaining before query',len(rest),flush=True)
            if r['status']=='witness':
                return
            if r['status']=='excluded':
                known[shape(core)]=core
    print('Covered',len(starts_covered(donor,width,known)),'of',len(donor)-width,'windows at',width)


if __name__=='__main__':
    main()
