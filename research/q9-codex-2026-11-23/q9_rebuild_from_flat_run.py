from q9_intact_bank_search import *
import random

def flat_piece(word):
    starts=[]
    for direction in range(9):
        start=0
        for end in [i for i,c in enumerate(word) if c==str(direction)]+[len(word)]:
            starts.append((end-start,start,end,direction))
            start=end+1
    return max(starts)

def main():
    radius,pin_count,budget=map(int,sys.argv[1:4])
    ws=Path("q9_far189_spring_20261121/comparison191.words").read_text().split()
    for idx,w in enumerate(ws):
        p=word_path(w);assert verify(p)
        _,left,right,axis=flat_piece(w)
        a=p[left+radius:right+1-radius]
        assert a and len({(v>>axis)&1 for v in a})==1
        occupied=set(p)
        outside=occupied-set(a)
        candidates=[]
        for tip in (p[0],p[-1]):
            for d in range(9):
                y=tip^(1<<d)
                if y in occupied:continue
                clashes={y^(1<<i) for i in range(9)}&occupied-{tip}
                if clashes.intersection(a):continue
                candidates.append((len(clashes),y,tuple(sorted(clashes))))
        random.Random(8013+idx+radius+pin_count).shuffle(candidates)
        if not candidates:continue
        _,extra,clashes=min(candidates,key=lambda z:z[0])
        hint=occupied.difference(clashes)|{extra}
        stable=sorted(v for v in outside if all((u^v).bit_count()>=3 for u in (*clashes,extra)))
        selected=random.Random(idx+37693).sample(stable,min(pin_count,len(stable)))
        rr=search(a,192,budget,hint,selected,False)
        print(json.dumps(dict(i=idx,axis=axis,mandatory=len(a),pins=len(selected),near_chords=len(clashes),results=rr)),flush=True)
        if any(r["status"]=="FOUND" for r in rr):return
if __name__=="__main__":main()
