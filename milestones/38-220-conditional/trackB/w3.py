"""3-cube census weight c(x) = sum_{3-cubes Q containing x} floor(12/|Q cap S|)  (milestone 22):
sum_x c(x) <= 12 * 5376 = 64512 for any vertex set.  Needed mean for v vertices: 64512/v."""
import itertools
def c_of(x, S):
    tot = 0
    for t in itertools.combinations(range(9), 3):
        cube = [x ^ sum(1 << t[j] for j in range(3) if r >> j & 1) for r in range(8)]
        k = sum(1 for u in cube if u in S)
        tot += 12 // k
    return tot
if __name__ == '__main__':
    import json, sys, os
    bank = json.load(open(os.path.join(os.path.dirname(__file__), '..', '..', '..', 'work', 'bank9.json')))
    vals = []
    for sn in bank[:20]:
        seq = sn['vertex_sequence']; S = set(seq)
        vals += [c_of(x, S) for x in seq]
    print('real mean c', sum(vals) / len(vals), 'needed at v=222', 64512 / 222, 'min', min(vals))
