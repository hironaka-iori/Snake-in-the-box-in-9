"""Replay integer facet-donor bounds from JSONL. Only Python's standard library is used."""
import argparse
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path


def require(test, message):
    if not test:
        raise ValueError(message)


def colour(vertex):
    return vertex.bit_count() & 1


def sign(vertex):
    return 1 - 2 * colour(vertex)


def directions(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def donor(word):
    require(isinstance(word, str) and len(word) >= 2 and set(word) <= set('01234567'),
            'word must describe at least two Q8 steps')
    path = [0]
    for char in word:
        path.append(path[-1] ^ (1 << int(char)))
    check_path(path)
    return path


def check_path(path):
    require(len(path) == len(set(path)) and all(type(v) is int and 0 <= v < 512 for v in path),
            'repeated or invalid vertex')
    position = {v: i for i, v in enumerate(path)}
    for i, v in enumerate(path):
        actual = {position[v ^ bit] for bit in directions(511) if v ^ bit in position}
        expected = {j for j in (i-1, i+1) if 0 <= j < len(path)}
        require(actual == expected, 'path is not induced or has a missing edge')


@lru_cache(None)
def linear_forests(dimension):
    """Index masks in a full Q3/Q4. An entry encodes its chosen vertices and their signatures."""
    size = 1 << dimension
    adjacency = [sum(1 << (x ^ bit) for bit in directions(size-1)) for x in range(size)]
    table = [None] * (1 << size)
    for mask in range(len(table)):
        codes = []
        tips = 0
        for bit in directions(mask):
            x = bit.bit_length()-1
            neighbours = adjacency[x] & mask
            if neighbours.bit_count() > 2:
                break
            if neighbours.bit_count() <= 1:
                tips |= bit
            signature = sum(x ^ (y.bit_length()-1) for y in directions(neighbours))
            codes.append(size*x + signature)
        else:
            # In a graph of degree at most two, a component has a cycle iff it has no tip.
            reached = tips
            front = tips
            while front:
                nxt = 0
                for bit in directions(front):
                    nxt |= adjacency[bit.bit_length()-1]
                front = nxt & mask & ~reached
                reached |= front
            if reached == mask:
                table[mask] = tuple(codes)
    return table


def face_maximum(cell, must, scores, dimension):
    forest = linear_forests(dimension)
    free = cell ^ must
    sub = free
    best = None
    while True:
        codes = forest[must | sub]
        if codes is not None:
            value = 0
            for code in codes:
                price = scores[code]
                if price is None:
                    break
                value += price
            else:
                if best is None or best < value:
                    best = value
        if not sub:
            break
        sub = (sub - 1) & free
    require(best is not None, 'face has no compatible linear forest')
    return best


def replay(c, witness=None):
    if witness is None:
        witness = c.get('witness')
    word, majority, scale = c['word'], c['majority'], c['scale']
    require(type(majority) is int and majority in (0, 1), 'bad endpoint colour')
    require(type(scale) is int and scale > 0, 'bad scale')
    masks, fees = c['axes'], c['fees']
    require(isinstance(masks, list) and all(type(m) is int and 0 < m < 512
            and m.bit_count() in (3, 4) for m in masks) and len(set(masks)) == len(masks),
            'axes must be distinct Q3/Q4 direction masks')
    require(isinstance(fees, list) and len(fees) == 3 and all(type(v) is int for v in fees),
            'expected three integer fees')
    require(type(c['bound_scaled']) is int, 'noninteger bound')
    path = donor(word)
    inside = set(path[1:-1])
    ends = {path[0], path[-1]}
    blocked = inside | {v ^ bit for v in inside for bit in directions(511)}
    residual = (set(range(512)) - blocked) | ends
    prices = {}
    require(isinstance(c['weights'], list), 'expected a list of weights')
    for row in c['weights']:
        require(isinstance(row, list) and len(row) == 4 and all(type(x) is int for x in row),
                'bad price entry')
        m, v, z, price = row
        require(m in masks and v in residual and z >= 0 and z & ~m == 0 and
                (m, v, z) not in prices, 'unknown or duplicate price key')
        prices[m, v, z] = price

    base = len(inside)*scale + 2*fees[majority] + (1-2*majority-sum(map(sign, inside)))*fees[2]
    total = base
    compatibility = {m: {} for m in masks}
    picked = None
    if witness is not None:
        check_path(witness)
        picked = set(witness) - inside
        require(ends <= picked <= residual and inside <= set(witness), 'witness misses donor or leaves domain')
        require(colour(witness[0]) == colour(witness[-1]) == majority, 'witness endpoint colour mismatch')
    witness_sum = base
    for v in residual:
        available = sum(bit for bit in directions(511) if v ^ bit in residual)
        options = list(directions(available))
        if v in ends:
            options.append(0)
        else:
            options.extend(a | b for a, b in combinations(directions(available), 2))
        best = None if v in ends else 0
        for m in masks:
            compatibility[m][v] = {z & m for z in options}
        true_sig = None
        if picked is not None and v in picked:
            true_sig = sum(bit for bit in directions(available) if v ^ bit in picked)
            require(true_sig in options, 'witness has bad residual degree')
        for z in options:
            is_endpoint = z.bit_count() + int(v in ends) == 1
            score = scale - sign(v)*fees[2] - (fees[colour(v)] if is_endpoint else 0)
            score += sum(prices.get((m, v, z & m), 0) for m in masks)
            if best is None or best < score:
                best = score
            if true_sig == z:
                witness_sum += score
        require(best is not None, 'mandatory node has no option')
        total += best
    for m, v, z in prices:
        require(z in compatibility[m][v], 'price names an unrealizable local signature')

    for m in masks:
        dim = m.bit_count()
        size = 1 << dim
        axes = list(directions(m))
        embed = [sum(bit for i, bit in enumerate(axes) if x >> i & 1) for x in range(size)]
        cells = {v & ~m for v in residual}
        for base_vertex in cells:
            cell = must = 0
            scores = [None] * (size*size)
            any_price = False
            for i, offset in enumerate(embed):
                v = base_vertex | offset
                if v not in residual:
                    continue
                cell |= 1 << i
                if v in ends:
                    must |= 1 << i
                for local, z in enumerate(embed):
                    if z in compatibility[m][v]:
                        fee = prices.get((m, v, z), 0)
                        scores[size*i + local] = -fee
                        any_price |= fee != 0
                if picked is not None and v in picked:
                    z = sum(bit for bit in axes if v ^ bit in picked)
                    witness_sum -= prices.get((m, v, z), 0)
            # Empty is permitted and attains zero in a fee-free unpinned cell.
            if any_price or must:
                total += face_maximum(cell, must, scores, dim)
    if picked is not None:
        require(witness_sum == len(witness)*scale and witness_sum <= total,
                'dual terms did not cancel on the positive witness')
    require(total == c['bound_scaled'], f'bound mismatch: got {total}, stored {c["bound_scaled"]}')
    return total


def self_test():
    # Interior 1 and its nine neighbours leave 504 residual vertices after reinserting 0 and 3.
    # Their parity sum is -6. Both endpoints have a residual incident direction.
    for majority, witness in [(0, [384,256,0,1,3,7,15]), (1, [256,0,1,3,7])]:
        c = dict(word='01', majority=majority, scale=10, axes=[7,15], fees=[0,0,1],
                 weights=[[7,0,z,11] for z in (0,2,4)]+[[15,0,z,-9] for z in (0,2,4,8)],
                 bound_scaled=5050+(1-2*majority)+7)
        replay(c, witness)
        try:
            replay(dict(c, bound_scaled=c['bound_scaled']+1))
        except ValueError as e:
            require('bound mismatch' in str(e), 'unexpected negative-control result')
        else:
            raise ValueError('altered certificate was accepted')
    for k in (3,4):
        forests = linear_forests(k)
        require(forests[15] is None and forests[7] is not None and forests[1] is not None,
                'forest control failed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='*', type=Path)
    parser.add_argument('--bank', type=Path, default=Path(__file__).with_name('q8_catalogue_96_98.words'))
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if not args.files and not args.self_test:
        parser.error('provide JSONL files or --self-test')
    if args.self_test:
        self_test()
        print(json.dumps({'self_test':'passed'}), flush=True)
    bank = None
    errors = 0
    for file in args.files:
        with file.open() as source:
            for line_no, line in enumerate(source, 1):
                try:
                    c = json.loads(line)
                    require(isinstance(c, dict), 'record is not an object')
                    if 'bound_scaled' not in c and 'status' in c:
                        raise ValueError(f'no certificate from generator: {c["status"]}')
                    if 'index' in c:
                        if bank is None:
                            bank = args.bank.read_text().split()
                        i = c['index']
                        require(type(i) is int and 0 <= i < len(bank) and bank[i] == c['word'],
                                'word and catalogue index do not match')
                    bound = replay(c)
                    result = dict(file=str(file), line=line_no, index=c.get('index'),
                                  majority=c['majority'], bound_scaled=bound, scale=c['scale'],
                                  max_vertices=bound//c['scale'], excludes_192=bound < 193*c['scale'])
                    if c.get('witness') is not None:
                        result['witness_edges'] = len(c['witness']) - 1
                    print(json.dumps(result), flush=True)
                except (KeyError, TypeError, ValueError) as err:
                    errors += 1
                    print(json.dumps(dict(file=str(file), line=line_no, verified=False, error=str(err))), flush=True)
    if errors:
        raise SystemExit(f'{errors} certificate record(s) did not verify')


if __name__ == '__main__':
    main()
