"""Check all record-file Q9 paths, all 96-edge single-facet windows, and five shape witnesses."""
import argparse
import csv
import io
import json
import zipfile
from pathlib import Path
from verify_q9_96_donor_coverage import canonical,check

def verify(p):
    check(len(p)==len(set(p)) and all(type(v) is int and 0<=v<512 for v in p),'bad Q9 vertices')
    seen=set()
    for i,v in enumerate(p):
        earlier={v^(1<<d) for d in range(9)}&seen
        check(earlier==({p[i-1]} if i else set()),'chord or missing edge')
        seen.add(v)
    return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))

def test(p,j,bank):
    t=verify(p);check(len(set(t[j:j+96]))==8 and j+96<len(p),'incorrect facet')
    shape=canonical(t[j:j+96]);check(shape in bank,'uncatalogued 96-window')
    return shape

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--archive',type=Path)
    ap.add_argument('--write-examples',type=Path)
    a=ap.parse_args()
    bank=set(Path('q8_catalogue_96_98.words').read_text().split())
    if not a.archive:
        examples=json.loads(Path('q9_96_donor_five_191_witnesses.json').read_text())
        check(len({r['shape'] for r in examples})==len(examples)==5,'repeated shape')
        for r in examples:check(len(r['vertices'])==192 and r['shape']==test(r['vertices'],r['start'],bank),'incorrect witness')
        print('5 distinct catalogue shapes each attain 191 edges')
        return
    examples={}
    with zipfile.ZipFile(a.archive) as z:
        for length,member in [(191,'record_snakes.csv'),(190,'snakes_dim9_190.csv')]:
            num=windows=carriers=0;shapes=set()
            for row,r in enumerate(csv.DictReader(io.TextIOWrapper(z.open(member)))):
                if int(r['n'])!=9 or int(r['length'])!=length:continue
                num+=1;p=list(map(int,r['vertices'].split()));t=verify(p)
                check(t==''.join(r['actions'].split()) and len(t)==length,'input word disagreement')
                found=False
                for j in range(len(t)-95):
                    sub=t[j:j+96]
                    if len(set(sub))>8:continue
                    w=test(p,j,bank);windows+=1;shapes.add(w);found=True
                    if length==191 and w not in examples:examples[w]=dict(shape=w,start=j,vertices=p,source_row=row)
                carriers+=int(found)
            print(json.dumps(dict(length=length,rows=num,windows=windows,paths_with_window=carriers,distinct_donor_shapes=len(shapes))))
    if a.write_examples:a.write_examples.write_text(json.dumps(list(examples.values()),separators=(',',':'))+'\n')
if __name__=='__main__':main()
