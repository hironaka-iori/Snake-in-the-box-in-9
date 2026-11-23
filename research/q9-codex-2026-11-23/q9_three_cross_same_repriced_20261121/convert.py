from check import *
O=R/'q9_three_cross_odd_20261121'
def freeze():
    live=R/'q9_catalogue_three_cross';out=[];keys=set()
    for l in (live/'results.jsonl').read_text().splitlines():
        if not l.endswith('}'):continue
        q=json.loads(l);i,x=q['i'],q['x']
        if q.get('root',10**100)>=193*q.get('scale',1):continue
        r=json.loads((live/'cases'/f'd{i}_x{x}.json').read_text());c=r['cert'];a=words[i];path=D/'certs'/f'd{i}_x{x}_frozen.json.gz'
        assert r['word']==a and r['ports']==sorted((0,G[i][1],x)) and (i,x) in jobs and (i,x) not in keys and r['total_scaled']==q['root']
        if not path.exists():
            with gzip.open(path,'wt') as f:json.dump(c,f,separators=(',',':'))
        out.append(dict(rank=jobs.index((i,x)),i=i,x=x,cert=str(path.relative_to(D)),scale=c['scale'],bound=q['root'],source='published_even_root'));keys.add((i,x))
    (D/'snapshot.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in out));return keys
def main():
    keys=freeze();odd=[json.loads(l) for l in (O/'manifest.jsonl').read_text().splitlines()];req=[r for r in odd if (r['i'],r['x']) not in keys]
    certs=[json.load(gzip.open(O/r['cert'],'rt')) for r in req]
    with tempfile.TemporaryFile('w+') as inp,(D/'converted.jsonl').open('w') as out:
        for j,c in enumerate(certs):writecert(inp,j,c)
        for j,r in enumerate(req):print('T',j,r['i'],r['x'],file=inp)
        inp.seek(0);pr=subprocess.Popen([str(D/'refine'),str(R/'q8_catalogue_96_98.words')],stdin=inp,stdout=subprocess.PIPE,text=True)
        for j,(r,l) in enumerate(zip(req,pr.stdout,strict=True)):
            ix,i,x,val,fee,bal=map(int,l.split());assert (ix,i,x)==(j,r['i'],r['x'])
            c=dict(certs[j],end_weights=[0,0],balance_weight=bal);c['end_weights'][x.bit_count()%2]=fee
            p=D/'certs'/f'd{i}_x{x}_odd_repriced.json.gz'
            with gzip.open(p,'wt',compresslevel=4) as f:json.dump(c,f,separators=(',',':'))
            print(json.dumps(dict(rank=r['rank'],i=i,x=x,cert=str(p.relative_to(D)),scale=c['scale'],bound=val,source='odd_repriced')),file=out,flush=True)
        assert pr.wait()==0
if __name__=='__main__':main()
