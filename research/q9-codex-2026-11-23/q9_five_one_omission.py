"""Search for 192 edges with exactly one omitted point in a proven 191-optimum donor."""
import json,random,sys
from pathlib import Path
from q9_intact_bank_search import word_path, verify, search

def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    witness=json.loads(Path("q9_rigid_five_witnesses.json").read_text())
    verified=json.loads(Path("q9_record_donor_optima.json").read_text())
    work=[]
    for key,row in witness.items():
        idx=int(key);word=bank[idx];path=row["vertices"]
        assert verified[key]["conditional_optimum"]==191 and verify(path)
        a=word_path(word)
        for pos,x in enumerate(a):work.append((idx,a,pos,x,path))
    random.Random(96972).shuffle(work)
    for idx,a,pos,x,path in work:
        near=set(path)-{x}
        res=search(a,192,int(sys.argv[1]),near,(),False,omit=(x,),forbid=(x,))
        print(json.dumps(dict(index=idx,omitted_index=pos,omitted_vertex=x,branches=res)),flush=True)
        if any(r["status"]=="FOUND" for r in res):return
if __name__=="__main__":main()
