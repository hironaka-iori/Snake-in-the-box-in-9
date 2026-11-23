from anywhere import *
from runs import bad
def main(n,count):
    bank=corpus(n);ct=Counter()
    with (D/f'near{n}.jsonl').open('w') as f:
        for err,nm,ix,w in bank[:count]:
            for upper in (2,3):
                st,c,p,used=unrestricted(w,25000,defect_cap=upper);row=dict(src=nm,i=ix,input_score=len(bad(vertices(w))),upper=upper,status=st,c=c)
                if p:
                    problems=bad(p);assert len(set(p))==len(p) and len(problems)<=upper
                    row.update(source_word=''.join(map(str,w)),word=''.join(map(str,word(p))),defects=problems,used=used)
                print(json.dumps(row,separators=(',',':')),file=f,flush=True);ct[(upper,st)]+=1
                if p:break
    print(ct)
if __name__=='__main__':main(*map(int,sys.argv[1:]))
