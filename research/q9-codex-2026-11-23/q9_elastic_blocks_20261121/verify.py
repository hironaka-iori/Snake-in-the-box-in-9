import itertools
import pathlib
import sys

base = pathlib.Path(__file__).resolve().parent
def check(path):
    return (all(0 <= x < 512 for x in path) and len(set(path)) == len(path)
            and all(((x ^ y).bit_count() == 1) == (j == i + 1)
                    for (i, x), (j, y) in itertools.combinations(enumerate(path), 2)))
def labels(word):
    path = [0]
    for ch in word:
        path.append(path[-1] ^ (1 << int(ch)))
    return path
def undoable_example():
    word = (base.parent / 'q9_four_piece_191_classes.txt').read_text().splitlines()[0]
    path = labels(word)
    assert len(path) == 192 and check(path)
    cuts = [0, 38, 77, 115, 153, len(path)]
    result = []
    for k, (lo, hi) in enumerate(zip(cuts, cuts[1:])):
        block = path[lo:hi]
        a, b = [(1, 8), (0, 0), (3, 7), (2, 4), (4, 8)][k]
        for v in block[::-1] if k in (0, 3) else block:
            if ((v >> a) ^ (v >> b)) & 1:
                v ^= (1 << a) | (1 << b)
            result.append(v ^ (93*k))
    assert not check(result)
    return result
if __name__ == '__main__':
    if sys.argv[1] == 'plant':
        print(*undoable_example())
    elif sys.argv[1]=='missing':
        p=labels((base.parent/'q9_four_piece_191_classes.txt').read_text().splitlines()[0])
        del p[77]
        print(*p)
    else:
        parents=[labels(w) for w in (base.parent/'q9_four_piece_191_classes.txt').read_text().splitlines()]
        bank=[list(map(int,line.split())) for line in (base/'parents191.vertices').read_text().splitlines()]
        assert len(parents)==len(bank)==131 and parents==bank and all(len(p)==192 and check(p) for p in parents)
        print('Verified original transition words against clean 191-edge inputs',len(bank))
        rows = [list(map(int, line.split())) for line in (base.parent / 'q9_onechord_expanded_800.txt').read_text().splitlines()]
        for p in rows:
            assert len(p) == len(set(p)) == 193 and all(0<=x<512 for x in p)
            assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
            assert sum((p[i]^p[j]).bit_count()==1 for i in range(193) for j in range(i+2,193))==1
        print('Verified one-chord inputs', len(rows))
        for file in sys.argv[2:]:
            witnesses = 0
            for line in pathlib.Path(file).read_text().splitlines():
                if line.startswith('PATH '):
                    p=list(map(int,line.split()[1:]))
                    witnesses += 1
                    assert check(p)
                    print('Verified induced witness',len(p)-1,file)
            assert witnesses==1
