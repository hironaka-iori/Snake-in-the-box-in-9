from run import *
cs=[json.loads(l) for l in (D/'controls.jobs').read_text().splitlines()]
ans=[]
for c in cs:
 line='points '+' '.join(map(str,c['points']))+'\n'
 s=subprocess.run([str(D/'direct'),'191','1700000'],input=line,text=True,capture_output=True,check=True).stdout
 w=verify(next(s for s in s.splitlines() if s.startswith('FOUND ')),c['points'],191)
 ans.append(dict(index=c['index'],removed=c['rm'],found_edges=len(w['path'])-1,witness=w))
(D/'direct_controls.json').write_text(json.dumps(ans))
print([r['found_edges'] for r in ans])
