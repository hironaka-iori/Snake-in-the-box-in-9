from pathlib import Path
import json,sys
D=Path(__file__).resolve().parent
for arg in sys.argv[1:]:
    src=D/(arg+'.jsonl')
    rows=list(map(json.loads,src.read_text().splitlines()))
    for trim in ('full','left','right') if arg.startswith('target') else ('full',):
        with (D/(arg+'_'+trim+'.in')).open('w') as f:
            for z in rows:
                a,b=z['patches'];w=z['word'];l=a['at'];p=b['at']+a['L']-a['n'];n=a['L'];m=b['L']
                if trim=='left':
                    w=w[1:]
                    if l==0:n-=1
                    else:l-=1
                    p-=1
                if trim=='right':
                    w=w[:-1]
                    if p+m>len(w):m-=1
                assert 0<=l<l+n<=p<p+m<=len(w)
                print(w,''.join(map(str,z['groups'])),l,n,p,m,file=f)
