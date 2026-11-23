"""Encode the exact singleton-plus-twice-empty square identity of an induced path."""
from itertools import combinations, product

from pysat.formula import IDPool


def squares(dim):
    for a,b in combinations(range(dim),2):
        x,y=1<<a,1<<b
        for v in range(1<<dim):
            if not v&(x|y):
                yield v,v^x,v^y,v^x^y


def add_popcount(f,pool,columns):
    """Return little-endian bits for the sum of weighted Boolean inputs."""
    def xor(a,b,s):
        f.extend([[-a,-b,-s],[a,b,-s],[a,-b,s],[-a,b,s]])
    def add_bits(i,items):
        a,b,*optional=items
        partial,carry=pool.id(),pool.id()
        xor(a,b,partial)
        if optional:
            c=optional[0]
            total=pool.id()
            xor(partial,c,total)
            for x,y in combinations((a,b,c),2):
                f.extend([[-x,-y,carry],[x,y,-carry]])
        else:
            total=partial
            f.extend([[-a,-b,carry],[-carry,a],[-carry,b]])
        columns[i].append(total)
        if i+1==len(columns):
            columns.append([])
        columns[i+1].append(carry)
    for i,group in enumerate(columns):
        while len(group)>1:
            size=min(3,len(group))
            add_bits(i,[group.pop() for _ in range(size)])
    return [group[0] if group else None for group in columns]


def add_square_identity(f,dim,vertices):
    pool=IDPool(start_from=max(f.nv,1<<dim)+1)
    columns=[[],[]]
    square_count=0
    for face in squares(dim):
        square_count+=1
        selection=[v+1 for v in face]
        single,empty=pool.id(),pool.id()
        for bits in product((False,True),repeat=4):
            guard=[-x if on else x for x,on in zip(selection,bits)]
            k=sum(bits)
            f.extend([[*guard,single if k==1 else -single],
                      [*guard,empty if k==0 else -empty]])
        columns[0].append(single)
        columns[1].append(empty)
    # Incidences: 36*n = 2*#squares - 2*N0 - N1 + N3, and N3=n-2.
    target=2*square_count-(dim*(dim-1)//2-1)*vertices-2
    predicted=add_popcount(f,pool,columns)
    if target<0 or target>>len(predicted):
        f.append([])
        return
    for i,bit in enumerate(predicted):
        if bit is not None:
            f.append([bit if target>>i&1 else -bit])
        elif target>>i&1:
            f.append([])
