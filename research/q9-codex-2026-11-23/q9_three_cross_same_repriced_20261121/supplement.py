from check import *
dlogs=['snapshot.jsonl','converted.jsonl','diffuse8.jsonl']
closed={(r['i'],r['x']) for r in loadrows(dlogs) if r['bound']<193*r['scale']}
live=R/'q9_catalogue_three_cross'
with (D/'supplement.jsonl').open('w') as out:
    for l in (live/'results.jsonl').read_text().splitlines():
        if not l.endswith('}'):continue
        r=json.loads(l);i,x=r['i'],r['x']
        if (i,x) in closed or r.get('root',10**30)>=r.get('scale',1)*193:continue
        q=json.loads((live/'cases'/f'd{i}_x{x}.json').read_text());c=q['cert'];assert q['total_scaled']==r['root'] and q['word']==words[i]
        p=D/'certs'/f'd{i}_x{x}_sup.json.gz'
        with gzip.open(p,'wt') as f:json.dump(c,f,separators=(',',':'))
        print(json.dumps(dict(rank=jobs.index((i,x)),i=i,x=x,cert=str(p.relative_to(D)),bound=r['root'],scale=c['scale'],source='later_even_root')),file=out)
