"""Reconstruct anchors from original 192-step one-chord walks, then certify arbitrary lengths."""
import json,os,sys,argparse
from pathlib import Path
from collections import defaultdict
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'q9_junction_integer_audit'))
from verify import close,value
os.chdir(ROOT)
def rows(p):return [json.loads(x) for x in Path(p).read_text().splitlines()]
def fixed_cases(radius):
    ds=json.loads(Path('q9_onechord_62anchors.json').read_text())
    inputs={}
    for ent in ds['results']:
        name=ent['input']; row=ent['row']
        if name not in inputs:inputs[name]=[list(map(int,s.split())) for s in Path(name).read_text().splitlines()]
        p=inputs[name][row]
        assert len(p)==len(set(p))==193 and all(0<=v<512 for v in p)
        ch=[(i,j) for i in range(193) for j in range(i+2,193) if (p[i]^p[j]).bit_count()==1]
        assert len(ch)==1 and all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
        i,j=ch[0];image,=ent['images'];assert len(set(image))==62 and set(image)<=set(p)
        fixed=set(p)-set(image)-{v for k,v in enumerate(p) if min(abs(k-c) for c in (0,i,j,192))<=radius}
        yield name,row,fixed

def valid(p):
    return len(p)==len(set(p)) and all(type(v)==int and 0<=v<512 for v in p) and all(((p[i]^p[j]).bit_count()==1)==(j==i+1) for i in range(len(p)) for j in range(i+1,len(p)))
def main():
    par=argparse.ArgumentParser();par.add_argument('--radius',type=int,default=12);par.add_argument('--parts',type=int,default=8);par.add_argument('--run',action='store_true');par.add_argument('--limit',type=int,default=36);par.add_argument('--start',type=int,default=0);opts=par.parse_args()
    data=list(fixed_cases(opts.radius));assert len(data)==36 and len({(a,b) for a,b,_ in data})==36
    cand={r['row']:r for r in rows('q9_full_obstruction_release.jsonl') if r['radius']==12}
    ws=defaultdict(list)
    for r in rows('q9_full_obstruction_191.jsonl')+rows('q9_break_matched_191.jsonl'):
        if r['status']=='FOUND':
            p=r['witness'];assert valid(p)
            ws[r['row']].append(p)
    chosen=sorted(data,key=lambda row:(len(row[2]),cand[row[1]]['status']!='UNKNOWN',row[1]))
    dest=HERE/'certs'
    if opts.run:
        from search_q9_shell_dual import build
        dest.mkdir(exist_ok=True);os.environ['Q9_SHELL_PARTS']=str(opts.parts)
        for name,row,f in chosen[opts.start:opts.start+opts.limit]:
            for h in (2,0,1):
                file=dest/f'r{opts.radius}_row{row}_h{h}_p{opts.parts}.json'
                if file.exists():continue
                req,dom=close(f,set(),None,h);g,e=(193,0) if h==2 else (192,h)
                built=build(sorted(f),0,e,g,req,dom)
                if built is None:print(f'empty factor row={row} h={h}',flush=True);continue
                c=built[-1];n=value(c,req,dom,g,e);assert n==built[1]
                c.update(row=row,source=name,radius=opts.radius,signature=h,fixed=sorted(f),numerator=n)
                tmp=file.with_suffix('.partial');tmp.write_text(json.dumps(c,separators=(',',':')));tmp.replace(file)
                print(json.dumps({'row':row,'radius':opts.radius,'fixed':len(f),'signature':h,'parts':opts.parts,'numerator':n}),flush=True)
        return
    sums=defaultdict(dict)
    for file in sorted(dest.glob(f'r{opts.radius}_row*.json')):
        c=json.loads(file.read_text());row=c['row'];name,_,f=next(i for i in data if i[1]==row);h=c['signature']
        assert c['radius']==opts.radius and c['source']==name and set(c['fixed'])==f and h in range(3)
        req,dom=close(f,set(),None,h);g,e=(193,0) if h==2 else (192,h);n=value(c,req,dom,g,e);assert n==c['numerator'] and c['scale']>0
        vertices=n//c['scale'];vertices-=(vertices%2!=int(h!=2))
        upper=vertices-1
        for _,idx,ff in data:
            if ff==f and (h not in sums[idx] or upper<sums[idx][h][0]):sums[idx][h]=[upper,str(file.relative_to(HERE)),n,c['scale']]
    entries=[]
    for name,row,f in data:
        known=next((p for p in ws[row] if f<=set(p)),None)
        if opts.radius==12:assert cand[row]['fixed']==len(f)
        info=sums[row];UB=max(v[0] for v in info.values()) if len(info)==3 else None
        assert known is None or UB is None or len(known)-1<=UB
        entries.append(dict(row=row,fixed=sorted(f),witness=known,lower=None if known is None else len(known)-1,upper=UB,signatures=info))
    print(json.dumps(dict(radius=opts.radius,certified_rows=sum(r['upper'] is not None for r in entries),excluded192=sum(r['upper'] is not None and r['upper']<192 for r in entries),conditional_exact191=sum(r['lower']==r['upper']==191 for r in entries),entries=entries),separators=(',',':')))
if __name__=='__main__':main()
