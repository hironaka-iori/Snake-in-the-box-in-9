from pathlib import Path
import itertools
import json
import subprocess
from verify_q9_excused_edge import word, vertices, chords, key
def canon(w):
    return ''.join(map(str,key(w)))
def run():
    directory=Path('q9_excused_frontier')
    directory.mkdir(exist_ok=True)
    entry=Path('q9_excused_orders_baseline.vertices')
    known={canon(word(list(map(int,row.split())))) for row in entry.read_text().splitlines()}
    assert len(known)==858
    frontier=set()
    for source in Path.cwd().glob('q9_excused_orders_*.words'):
        for w in source.read_text().splitlines():
            if len(w)==192:frontier.add(canon(w))
    frontier-=known
    for depth in range(10):
        assert all(len(chords(vertices(w)))==1 for w in frontier)
        if not frontier:break
        prefix=directory/f'round{depth}'
        prefix.with_suffix('.in').write_text('\n'.join(sorted(frontier))+'\n')
        known.update(frontier)
        base=prefix.with_suffix('.vertices')
        base.write_text(''.join(' '.join(map(str,vertices(w)))+'\n' for w in sorted(known)))
        new=set()
        for radius in (0,1):
            path=directory/f'round{depth}_radius{radius}.words'
            log=path.with_suffix('.log')
            with prefix.with_suffix('.in').open() as source,log.open('w') as dest:
                subprocess.run(['/tmp/q9-excused-orders-21',str(radius),'100000',str(base),str(path)],stdin=source,stdout=dest,check=True)
            for row in log.read_text().splitlines():
                if row.startswith('FOUND'):
                    p=list(map(int,row.split()[1:]));assert not chords(p)
                    (directory/'witness192.json').write_text(json.dumps(p));return
            new.update(map(canon,path.read_text().splitlines()))
        assert not new&known
        print(json.dumps(dict(round=depth,input=len(frontier),known=len(known),novel=len(new))),flush=True)
        frontier=new
if __name__=='__main__':run()
