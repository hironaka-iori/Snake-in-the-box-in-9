"""Complete the eight-cube paths containing one of the five full 94-edge intervals."""
from collections import Counter
from functools import lru_cache
from catalogue import HERE, read, label, identifier, write
from growth import bank

def unrooted(path):
    a=label(path)[0]
    b=label(path[::-1])[0]
    return min(a,b)

def extensions(path):
    used=set(path)
    for r in (path,path[::-1]):
        for i in range(8):
            w=r[-1]^(1<<i)
            if w not in used and all((w^v).bit_count()!=1 for v in r[:-1]):
                yield unrooted(r+[w])

def main():
    inp=read(HERE/"parents.json")["parents"]
    seeds={identifier(unrooted(r["parent"])):unrooted(r["parent"]) for r in inp.values() if r["from_191"]}
    assert len(seeds)==5
    paths=dict(seeds)
    links={}
    for n in range(94,99):
        for k,r in list(paths.items()):
            if len(r)!=n+1:
                continue
            links[k]=[]
            for q in extensions(r):
                assert n<98
                bank.check_path(q,8)
                h=identifier(q)
                paths[h]=q
                if h not in links[k]:
                    links[k].append(h)
    hist=Counter(len(p)-1 for p in paths.values())
    write(HERE/"windows.json",dict(seeds=sorted(seeds),paths=paths,successors=links,by_length=hist))
    print(sorted(hist.items()),[len(links[k]) for k in seeds])

if __name__=="__main__":
    main()
