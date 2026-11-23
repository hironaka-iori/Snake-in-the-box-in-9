import json
from prep import D
def build():
 rows=[json.loads(l) for l in (D/'primary.jobs').read_text().splitlines()]
 selected=sorted((r for r in rows if not any(z['seed']==r['seed'] and set(z['rm'])<set(r['rm']) for z in rows)),key=lambda r:(-len(r['rm']),r['seed'],r['rm']))
 a=''.join(json.dumps(r,separators=(',',':'))+'\n' for r in selected)
 b=''.join('points '+' '.join(map(str,r['points']))+'\n' for r in selected)
 for name,s in [('minimal.jobs',a),('minimal.txt',b)]:
    p=D/name
    if p.exists():assert p.read_text()==s
    else:p.write_text(s)
if __name__=='__main__':build()
