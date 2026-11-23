from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'graft.cpp').read_text().replace('if(local<perface)exercise(weakBins[port.approx],true);','').replace('if(k<2||k>5)continue;','if(k<2||k>4)continue;')
(r/'exact.cpp').write_text(s)
p=(r/'run.py').read_text().replace("rows=[list(map", "rows=[list(map").replace("(r/'grafts.pts').read_text()","(r/('exact.pts' if tag.startswith('exact') else 'grafts.pts')).read_text()")
p=p.replace('counts=Counter();scores=',"""done=set()
 if mode==5:done={json.loads(l)[0] for nm in ('first','all') for f in [r/(nm+'.jsonl')] if f.exists() for l in f.read_text().splitlines()}
 if mode==6:done={json.loads(l)[0] for nm in ('exact','exactrest') for f in [r/(nm+'.jsonl')] if f.exists() for l in f.read_text().splitlines()}
 ix=[i for i in ix if i not in done]
 counts=Counter();scores=""")
(r/'run.py').write_text(p)

