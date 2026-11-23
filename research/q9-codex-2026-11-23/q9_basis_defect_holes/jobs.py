from prep import *
primary=lambda r:any('q8_single_cross' in f or 'monotone_near' in f for f,i in r['refs'])
def job(x):
    return dict(seed=x['seed'],word=x['word'],chords=x['chords'],rm=x['rm'],points=[v for i,v in enumerate(path(x['word'])) if i not in x['rm']])
def save(mode,rows):
    (D/(mode+'.jobs')).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in rows));print(mode,len(rows))
def go():
    ep=[json.loads(l) for l in (D/'endpoints.jsonl').read_text().splitlines()];pr=[job(x) for x in ep if primary(x)];save('primary',pr)
    nex=[]; buckets={}
    for l in (D/'local.jsonl').open():
        x=json.loads(l)
        if primary(x):nex.append(job(x))
        else:
            key=len(x['chords']),len(x['rm'])
            if len(buckets.setdefault(key,[]))<20:buckets[key].append(job(x))
    save('neighbors',nex)
    rng=random.Random(815211);rng.shuffle(ep)
    for l in ep:
        if primary(l):continue
        k=len(l['chords']),len(l['rm']),'tips'
        if len(buckets.setdefault(k,[]))<24:buckets[k].append(job(l))
    save('registered',[r for v in buckets.values() for r in v])
    pos=[json.loads(l) for l in (D/'positive.jsonl').read_text().splitlines()]
    for x,l in zip(pos,(D/'positive.txt').read_text().splitlines()):x['points']=list(map(int,l.split()[1:]))
    save('controls',pos)
if __name__=='__main__':go()
