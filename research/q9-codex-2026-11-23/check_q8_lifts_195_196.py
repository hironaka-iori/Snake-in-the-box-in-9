"""Enumerate single-crossing lifts of contiguous subpaths of one Q8 witness.
Usage: python3 check_q8_lifts.py /path/to/snake8_witness.json
"""
import itertools
import json
import sys

path = json.load(open(sys.argv[1]))["vertex_sequence"]
assert len(path) == len(set(path)) == 99
assert all(0 <= x < 256 for x in path)
for i, x in enumerate(path):
    for j in range(i + 1, len(path)):
        assert ((x ^ path[j]).bit_count() == 1) == (j == i + 1)

def oriented_arms(length):
    for s in range(len(path) - length):
        arm = path[s:s + length + 1]
        for order in (arm, arm[::-1]):
            yield [v ^ order[0] for v in order[1:]]

pairs = [(98, 93), (97, 94), (96, 95), (98, 94), (97, 95), (96, 96),
         (98, 95), (97, 96), (98, 96), (97, 97), (98, 97), (98, 98)]
arms = {k: list(oriented_arms(k)) for k in range(93, 99)}
masks = {k: [sum(1 << v for v in arm) for arm in group] for k, group in arms.items()}
best = dict.fromkeys(pairs, 99)
for perm in itertools.permutations(range(8)):
    image_bits = [0] * 256
    image = [0] * 256
    for v in range(1, 256):
        low = v & -v
        image[v] = image[v ^ low] | (1 << perm[low.bit_length() - 1])
        image_bits[v] = 1 << image[v]
    transforms = {k: [sum(image_bits[v] for v in arm) for arm in group]
                  for k, group in arms.items()}
    for a, b in pairs:
        best[a, b] = min(best[a, b], min((x & y).bit_count()
                          for x in masks[a] for y in transforms[b]))
for (a, b), chords in best.items():
    print(a + b + 1, a, b, chords)
