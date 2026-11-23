"""Verify fresh eight-cube donors, then test both endpoint colors for a 192-edge lift."""
import json, os, sys
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
from search_q9_punctured_q8 import run
from verify_q9_record_facet_profile import canonical

def bank():
    old=set(Path("q8_catalogue_96_98.words").read_text().split())
    result={}
    for file in sorted(Path('.').glob('q8_four_piece_new_mothers*.log')):
        for line in file.read_text().splitlines():
            if not line.startswith(('NEW ','FOUND ')):continue
            p=list(map(int,line.split()[3:]))
            assert len(p)==len(set(p)) and len(p)>=97 and all(0<=v<256 for v in p)
            assert all(((v^p[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j in range(i+1,len(p)))
            w=canonical([(v^z).bit_length()-1 for v,z in zip(p,p[1:])])
            if w not in old:result[w]=p
    return result

def test(t):
    w,p,ep,g=t
    z=run(((),ep,g,p))
    return [w,*z[1:]]

if __name__=="__main__":
    assert os.environ['Q9_FREE_BOTTOM']=='1' and os.environ['Q9_PATH_MINIMUM']=='1'
    assert Path(os.environ['Q9_SHELL_SOLVER']).is_file()
    banked=bank(); previous=set()
    for file in sys.argv[1:]:
        for line in Path(file).read_text().splitlines():
            row=json.loads(line);previous.add(tuple(row[:3]))
    jobs=[(w,p,e,g) for w,p in banked.items() for e,g in [(0,192),(1,192),(0,191)] if (w,e,g) not in previous]
    with ProcessPoolExecutor(2) as pool:
        for row in pool.map(test,jobs):
            print(json.dumps(row,separators=(',',':')),flush=True)

