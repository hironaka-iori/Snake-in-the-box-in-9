"""Persist and replay exact branch-search inputs, trace provenance and integer upper bounds."""
from audit import *
import gzip,subprocess,hashlib
from io import StringIO

def main():
    from search_q9_shell_dual import build
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--parts',type=int,default=8);ap.add_argument('--cap',type=int,default=15000);ap.add_argument('--radius',type=int,default=12);ap.add_argument('--control',action='store_true');ap.add_argument('--rows',nargs='*',type=int)
    o=ap.parse_args();binary=HERE/'factor'
    env={**os.environ,'Q9_PATH_MINIMUM':'1'};env.pop('Q9_AVOID_SHAPES',None);os.environ['Q9_SHELL_PARTS']=str(o.parts)
    target=o.radius;data=list(fixed_cases(target))
    recs={}
    for source,row,f in data:
        key=frozenset(f)
        if key not in recs:recs[key]=[row,source,[]]
        recs[key][2].append(row)
    ws={r['row']:r['witness'] for r in rows('q9_full_obstruction_191.jsonl') if r['status']=='FOUND' and r['radius']==10}
    for f,(row,src,same) in sorted(recs.items(),key=lambda a:(len(a[0]),a[1][0])):
        if o.rows and not set(same).intersection(o.rows):continue
        for h in ((2,) if o.control else (0,1,2)):
            g=(191 if o.control else 193) if h==2 else 192
            P,D=close(f,set(),None,h)
            if o.control:
                match=next((p for p in ws.values() if f<=set(p)),None)
                if match is None:continue
                P,D=close(set(match),set(),None,2)
            e=h%2 if h!=2 else 0
            built=build(sorted(f),0,e,g,P,D)
            if built is None:print(json.dumps(dict(row=row,signature=h,status='EMPTY_FACTORS')),flush=True);continue
            _,upper,const,out,c=built;assert value(c,P,D,g,e)==upper
            c.update(row=row,source=src,radius=target,signature=h,fixed=sorted(f),numerator=upper)
            if not o.control:
                d=HERE/'certs';d.mkdir(exist_ok=True);cp=d/f'r{target}_row{row}_h{h}_p{o.parts}.json'
                if not cp.exists():cp.write_text(json.dumps(c,separators=(',',':')))
            st='DUAL';nodes=0;w=None;name=None
            if upper>=(g+1)*10000:
                name=f'{"ctrl" if o.control else "branch"}_r{target}_row{row}_h{h}'+(f'_p{o.parts}' if o.parts!=8 else '')+'.gz'
                stream=StringIO();print(row,g+1,e,10000,const,upper,len(D),*sorted(D),len(out),file=stream)
                for scope,opts in out:
                    print(len(scope),*scope,len(opts),file=stream)
                    for a,b,y in opts:print(a,b,y,file=stream)
                payload=stream.getvalue().encode()
                with gzip.open(HERE/name,'wb') as fd:fd.write(payload)
                res=subprocess.run([str(binary),str(o.cap)],input=payload,env=env,stdout=subprocess.PIPE,check=True)
                i,st,nn,*path=res.stdout.decode().split();nodes=int(nn);assert int(i)==row
                if path:
                    w=list(map(int,path));assert valid(w) and len(w)>=g+1 and (len(w)-g-1)%2==0 and (h==2 or w[0].bit_count()%2==h) and set(f)<=set(w)
            print(json.dumps(dict(row=row,equivalent_rows=same,radius=target,signature=h,numerator=upper,parts=o.parts,goal=g,fixed=len(f),status=st,nodes=nodes,input=name,witness=w)),flush=True)
        if o.control:return
if __name__=='__main__':main()
