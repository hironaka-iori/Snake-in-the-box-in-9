"""Exhaust all eleven-step constraints missed by overlapping ten-step geometry."""
import json

from q9_window_geometry import canonical


def induced(word):
    vertex=0
    vertices=[0]
    for d in word:
        vertex^=1<<d
        if vertex in vertices or any((x^vertex).bit_count()==1 for x in vertices[:-1]):
            return False
        vertices.append(vertex)
    return True


def base_words(word=(), length=9):
    if len(word)==length:
        yield word
        return
    for d in range(min(9,1+len(set(word)))):
        extended=(*word,d)
        if induced(extended):
            yield from base_words(extended,length)


def catalogue():
    evidence={}
    for first in base_words():
        for a in range(min(9,1+len(set(first)))):
            ten=(*first,a)
            if not induced(ten):
                continue
            for b in range(min(9,1+len(set(ten)))):
                eleven=(*ten,b)
                if not induced(eleven[1:]):
                    continue
                key=tuple(canonical(eleven[i:i+9]) for i in range(3))
                evidence[key]=evidence.get(key,False) or induced(eleven)
    return sorted(k for k,v in evidence.items() if not v),len(evidence)


if __name__=="__main__":
    bad,total=catalogue()
    print(json.dumps(dict(nine_step_shapes=sum(1 for _ in base_words()),
                          adjacent_tens=total,forbidden_triples=bad)))
