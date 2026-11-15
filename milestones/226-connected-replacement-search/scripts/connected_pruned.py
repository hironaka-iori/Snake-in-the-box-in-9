"""Bounded two-path enumeration with second-domain pruning at every first prefix.

No constraint solver is used. A checkpoint contains every outstanding DFS
prefix; the first complete path stays pending until its second search finishes.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
import os
import re
import time


H = Path(__file__).resolve().parents[1]
ORIGINAL_WORKER_SHA256 = '7c1c1dc41c4b7c73ef0038b417f9a09d7068c5b474217ccf272ad2c4b4e4c74a'
N = [{v ^ (1 << k) for k in range(9)} for v in range(512)]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')
    os.replace(temporary, path)


def crossing_count(path):
    return sum((u ^ v) == 256 for u, v in zip(path, path[1:]))


def induced(path):
    return len(path) == len(set(path)) and all(
        ((u ^ path[j]).bit_count() == 1) == (j == i + 1)
        for i, u in enumerate(path) for j in range(i + 1, len(path)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--width', type=int, required=True)
    parser.add_argument('--id', type=int, required=True)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--seconds', type=float, required=True)
    parser.add_argument('--first-part', type=int, choices=[0, 1], default=0,
                        help='Original interval to enumerate first.')
    parser.add_argument('--first-crossings', type=int,
                        help='Restrict crossings of the first-enumerated interval; exhaustion is allocation-only.')
    parser.add_argument('--resume', type=Path,
                        help='Prior checkpoint; a fresh tag preserves prior outputs.')
    args = parser.parse_args()
    require(34 <= args.width <= 43, 'Width must be between 34 and 43.')
    require(re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]*', args.tag) is not None,
            'Tag must be a plain filename component.')
    require(math.isfinite(args.seconds) and args.seconds > 0,
            'Seconds must be positive and finite.')
    source = H / 'data' / f'regions{args.width}.json'
    raw = json.loads(source.read_bytes())
    matches = [row for row in raw['contexts'] if row['id'] == args.id]
    require(len(matches) == 1, 'Context ID is absent or duplicated.')
    row = matches[0]
    require(row['status'] == 'PENDING' and len(row['parts']) == 2,
            'Choose a context with two prepared domains, without inherited/static exclusion.')
    seed = raw['seed']
    width = args.width
    endpoint = raw['endpoint']
    require(raw['width'] == width and endpoint == 24, 'Wrong prepared family.')
    require(len(seed) == 192 and induced(seed), 'Seed is not an induced 191-edge path.')
    require(seed[0] == 0 and seed[-1] == 88 and crossing_count(seed) == 4,
            'Seed endpoints or four-crossing normalization differ.')
    (a, b), (c, d) = row['intervals']
    require(0 <= a < b < c < d < len(seed) and b - a == d - c == width,
            'Replacement intervals are incompatible.')
    domains = [set(part['allowed']) for part in row['parts']]
    anchors = [tuple(part['anchors']) for part in row['parts']]
    for part, interval, pair, domain in zip(row['parts'], row['intervals'], anchors, domains):
        i, j = interval
        require(pair == (seed[i], seed[j]) and set(pair) <= domain,
                'Anchors do not match the seed or domain.')
        require(all(isinstance(v, int) and 0 <= v < 512 for v in domain),
                'Domain contains an invalid cube vertex.')
        require(part['target_vertices'] == width + 1, 'Wrong target path size.')
    fixed_crossings = sum((u ^ v) == 256 for i, (u, v) in enumerate(zip(seed, seed[1:]))
                          if not (a <= i < b or c <= i < d))
    budget = row['replacement_crossings']
    require(budget == 4 - fixed_crossings and budget >= 0, 'Wrong crossing budget.')
    allocation = None
    if args.first_crossings is not None:
        require(0 <= args.first_crossings <= min(width, budget), 'Invalid fixed crossing count.')
        allocation = [None, None]
        allocation[args.first_part] = args.first_crossings
        allocation[1 - args.first_part] = budget - args.first_crossings
    order = [args.first_part, 1 - args.first_part]
    domains = [domains[i] for i in order]
    anchors = [anchors[i] for i in order]
    zero_face_restricted = args.first_crossings == 0
    if zero_face_restricted:
        face = anchors[0][0] & 256
        domains[0] = {v for v in domains[0] if (v & 256) == face}
    original_worker = H / 'scripts' / 'connected_pairs.py'
    require(sha(original_worker) == ORIGINAL_WORKER_SHA256, 'Original worker provenance differs.')
    pins = {'source': str(source), 'source_sha256': sha(source),
            'script_sha256': sha(__file__), 'width': width, 'context_id': args.id,
            'first_part': args.first_part, 'crossing_allocation': allocation,
            'worker': 'connected_pruned', 'original_worker_sha256': ORIGINAL_WORKER_SHA256,
            'zero_crossing_first_face_restriction': zero_face_restricted}
    for path, digest in raw['pins'].items():
        require(sha(path) == digest, 'A prepared input dependency has changed: ' + path)

    counts = {'first_prefixes_processed': 0, 'first_complete_paths': 0,
              'second_prefixes_processed': 0, 'second_searches_exhausted': 0,
              'pruned_prefixes': 0,
              'second_domain_prefix_prunes': {'ANCHOR_REMOVED': 0, 'DISCONNECTED': 0,
                                               'SIZE': 0, 'COLOUR': 0}}
    state = {'phase': 'first', 'first_frontier': [[anchors[0][0]]],
             'second_frontier': []}
    prior_seconds = 0.0
    resume_pin = None
    if args.resume is not None:
        previous = json.loads(args.resume.read_bytes())
        require(previous['pins'] == pins, 'Checkpoint input or script pins differ.')
        require(previous['status'] in ['RUNNING', 'TIME_LIMIT', 'INTERRUPTED'],
                'Only an unfinished checkpoint can be resumed.')
        state = previous['state']
        counts = previous['counts']
        prior_seconds = previous['cumulative_seconds']
        resume_pin = {'path': str(args.resume.resolve()), 'sha256': sha(args.resume)}
        require(state['phase'] in ['first', 'second'], 'Invalid checkpoint phase.')
        require(bool(state['first_frontier']), 'An unfinished checkpoint has no first frontier.')
        for part_index, key in [(0, 'first_frontier'), (1, 'second_frontier')]:
            for prefix in state[key]:
                require(1 <= len(prefix) <= width + 1 and prefix[0] == anchors[part_index][0]
                        and set(prefix) <= domains[part_index] and induced(prefix),
                        'Malformed checkpoint prefix.')
        if state['phase'] == 'second':
            first = state['first_frontier'][-1]
            require(len(first) == width + 1 and first[-1] == anchors[0][1],
                    'Second phase lacks a complete pending first path.')

    output = H / 'data' / args.tag
    output.mkdir(exist_ok=False)
    started = time.monotonic()
    deadline = started + args.seconds
    last_save = started
    witness = None
    status = 'RUNNING'
    error = None
    second_cache_key = None
    second_domain = None

    def save():
        elapsed = time.monotonic() - started
        record = {'status': status, 'pins': pins, 'resume': resume_pin,
                  'intervals': row['intervals'], 'replacement_crossings': budget,
                  'first_part': args.first_part, 'crossing_allocation': allocation,
                  'counts': counts, 'seconds': elapsed,
                  'cumulative_seconds': prior_seconds + elapsed,
                  'witness': witness, 'error': error,
                  'exclusion': status == 'EXHAUSTED',
                  'whole_context_excluded': status == 'EXHAUSTED' and allocation is None,
                  'exhaustion_scope': 'whole prepared context' if allocation is None else 'specified crossing allocation only',
                  'scope': 'One prepared pair of equal-width replacements, retained outside indices, '
                           'endpoint24 appended and exactly four coordinate8 crossings. '
                           'An explicit crossing_allocation restricts the enumerated family. '
                           'Native DFS exhaustion only; no Lean traversal certificate.'}
        write_json(output / 'checkpoint.json', dict(record, state=state))
        write_json(output / 'result.json', dict(record,
                   checkpoint_sha256=sha(output / 'checkpoint.json'),
                   pending_first_prefixes=len(state['first_frontier']),
                   pending_second_prefixes=len(state['second_frontier'])))

    def second_domain_failure(first_prefix):
        # A full first path can only remove additional vertices from this domain.
        blocked = set(first_prefix)
        for z in first_prefix:
            blocked.update(N[z])
        available = domains[1] - blocked
        u, v = anchors[1]
        if u not in available or v not in available:
            return 'ANCHOR_REMOVED'
        component = {u}
        queue = [u]
        while queue:
            z = queue.pop()
            new = (N[z] & available) - component
            component.update(new)
            queue.extend(new)
        if v not in component:
            return 'DISCONNECTED'
        if len(component) < width + 1:
            return 'SIZE'
        required_even = (width + 2) // 2 if u.bit_count() % 2 == 0 else (width + 1) // 2
        even = sum(z.bit_count() % 2 == 0 for z in component)
        if even < required_even or len(component) - even < width + 1 - required_even:
            return 'COLOUR'
        return None

    def expand(prefix, domain, target, first_phase, first_crossings=0):
        """Return None for a necessary-condition failure, or every next prefix."""
        current = prefix[-1]
        remaining = width - len(prefix) + 1
        distance = (current ^ target).bit_count()
        if remaining < 0 or distance > remaining or (remaining - distance) % 2:
            return None
        used_crossings = crossing_count(prefix)
        parity_to_target = ((current ^ target) >> 8) & 1
        if first_phase:
            left = budget - used_crossings
            second_parity = ((anchors[1][0] ^ anchors[1][1]) >> 8) & 1
            if not any(0 <= left - n <= width and (left - n) % 2 == second_parity
                       and (args.first_crossings is None or used_crossings + n == args.first_crossings)
                       for n in range(parity_to_target, remaining + 1, 2)):
                return None
        else:
            left = budget - first_crossings - used_crossings
            if not (0 <= left <= remaining and left % 2 == parity_to_target):
                return None
        if current == target:
            return [] if remaining == 0 else None
        if remaining == 0 or target not in domain or current not in domain:
            return None
        # The final anchor cannot touch any earlier nonconsecutive path vertex.
        if any(target in N[z] for z in prefix[:-1]):
            return None
        if target in N[current] and remaining != 1:
            return None
        forbidden = set(prefix[:-1])
        for z in prefix[:-1]:
            forbidden.update(N[z])
        available = (domain - forbidden) | {current}
        if target not in available:
            return None
        component = {current}
        queue = [current]
        while queue:
            z = queue.pop()
            new = (N[z] & available) - component
            component.update(new)
            queue.extend(new)
        required_even = (remaining + 2) // 2 if current.bit_count() % 2 == 0 else (remaining + 1) // 2
        even = sum(z.bit_count() % 2 == 0 for z in component)
        if target not in component or len(component) < remaining + 1:
            return None
        if even < required_even or len(component) - even < remaining + 1 - required_even:
            return None
        next_vertices = (N[current] & available) - set(prefix)
        if remaining == 1:
            next_vertices &= {target}
        else:
            next_vertices.discard(target)
        return [prefix + [v] for v in sorted(next_vertices, reverse=True)]

    save()
    try:
        while state['first_frontier']:
            now = time.monotonic()
            if now >= deadline:
                status = 'TIME_LIMIT'
                break
            if now - last_save >= 5:
                save()
                last_save = time.monotonic()
            if state['phase'] == 'first':
                first = state['first_frontier'][-1]
                failure = second_domain_failure(first)
                if failure is not None:
                    counts['second_domain_prefix_prunes'][failure] += 1
                    children = None
                else:
                    children = expand(first, domains[0], anchors[0][1], True)
                counts['first_prefixes_processed'] += 1
                if children is not None and len(first) == width + 1:
                    counts['first_complete_paths'] += 1
                    # Do not remove this first path until its second frontier is exhausted.
                    state = dict(state, phase='second', second_frontier=[[anchors[1][0]]])
                else:
                    if children is None:
                        counts['pruned_prefixes'] += 1
                    state = dict(state, first_frontier=state['first_frontier'][:-1] + (children or []))
            else:
                first = state['first_frontier'][-1]
                key = tuple(first)
                if key != second_cache_key:
                    blocked = set(first)
                    for z in first:
                        blocked.update(N[z])
                    second_domain = domains[1] - blocked
                    second_cache_key = key
                if not state['second_frontier']:
                    counts['second_searches_exhausted'] += 1
                    state = dict(state, phase='first', first_frontier=state['first_frontier'][:-1],
                                 second_frontier=[])
                    continue
                second = state['second_frontier'][-1]
                if not set(anchors[1]) <= second_domain:
                    children = None
                else:
                    children = expand(second, second_domain, anchors[1][1], False, crossing_count(first))
                counts['second_prefixes_processed'] += 1
                if children is not None and len(second) == width + 1:
                    routes = [None, None]
                    routes[order[0]] = first
                    routes[order[1]] = second
                    route_a, route_b = routes
                    path = seed[:a] + route_a + seed[b + 1:c] + route_b + seed[d + 1:] + [endpoint]
                    require(len(path) == 193 and induced(path), 'Candidate failed the full pairwise witness audit.')
                    require(path[0] == 0 and path[-1] == 24 and crossing_count(path) == 4,
                            'Candidate failed endpoint or crossing audit.')
                    require(route_a[0] == seed[a] and route_a[-1] == seed[b]
                            and route_b[0] == seed[c] and route_b[-1] == seed[d],
                            'Candidate anchors differ.')
                    require(allocation is None or [crossing_count(route) for route in routes] == allocation,
                            'Candidate violates the selected crossing allocation.')
                    witness = {'path': path, 'replacements': routes,
                               'edges': 192, 'vertices': 193, 'crossings': 4,
                               'pairwise_induced_check': True}
                    status = 'WITNESS'
                    break
                if children is None:
                    counts['pruned_prefixes'] += 1
                state = dict(state, second_frontier=state['second_frontier'][:-1] + (children or []))
        else:
            status = 'EXHAUSTED'
    except KeyboardInterrupt:
        status = 'INTERRUPTED'
    except Exception as exc:
        status = 'ERROR'
        error = {'type': type(exc).__name__, 'message': str(exc)}
        raise
    finally:
        save()
    print(json.dumps({'status': status, 'result': str(output / 'result.json'),
                      'checkpoint': str(output / 'checkpoint.json'), 'counts': counts}), flush=True)


if __name__ == '__main__':
    main()
