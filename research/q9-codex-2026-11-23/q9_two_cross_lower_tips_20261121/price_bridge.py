from check import *
from diffuse_run import target
def main():
    priors=[R/n for n in ['q9_three_cross_odd_20261121','q9_three_cross_same_repriced_20261121']]
    old=[{(r['i'],r['x']):r for l in (p/'manifest.jsonl').read_text().splitlines() if(r:=json.loads(l))} for p in priors]
    with (D/'repriced.jsonl').open('w') as out:
        for start in range(0,len(jobs),100):
            subset=jobs[start:start+100];cs=[];keys={};qt=[]
            with tempfile.TemporaryFile('w+') as f:
                for i,y in subset:
                    for d,p in enumerate(priors):
                        r=old[d][i,y%256];path=p/r['cert']
                        if path not in keys:
                            keys[path]=len(cs);c=json.load(gzip.open(path,'rt'));writecert(f,len(cs),c);cs.append(c)
                        qt.append((i,y,keys[path]))
                for i,y,j in qt:print('T',j,i,y,file=f)
                f.seek(0);proc=subprocess.Popen([str(D/'refine'),str(R/'q8_catalogue_96_98.words')],stdin=f,stdout=subprocess.PIPE,text=True);best={}
                for q,l in zip(qt,proc.stdout,strict=True):
                    j,i,y,val,fee,balance=map(int,l.split());assert (i,y,j)==q and fee==0
                    if (i,y) not in best or val<best[i,y][0]:best[i,y]=(val,j,balance)
                assert proc.wait()==0
            for i,y in subset:
                val,j,balance=best[i,y];c=dict(cs[j],end_weights=[0,0],balance_weight=balance);p=D/'certs'/f'd{i}_x{y}_port.json.gz'
                with gzip.open(p,'wt',compresslevel=4) as f:json.dump(c,f,separators=(',',':'))
                print(json.dumps(dict(rank=jobs.index((i,y)),i=i,x=y,isolated=y%256,tip_choice=y//256,threshold=target(i,y),bound=val,scale=c['scale'],cert=str(p.relative_to(D)))),file=out,flush=True)
if __name__=='__main__':main()
