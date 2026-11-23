"""Replay unresolved alternating-corner cases after reversing their orientation."""
import json
from pathlib import Path
from pysat.solvers import Gluecard4
import search_q9_flexible_corners as search


def main():
    search.Minicard = Gluecard4
    for source in ["q9_flexible_endpoint_relative_192.jsonl", "q9_flexible_corners_full_192.jsonl"]:
        for line in Path(source).read_text().splitlines():
            status, key, first, count, _ = json.loads(line)
            if status != "UNKNOWN":
                continue
            original = bytes.fromhex(key)
            n = len(original)
            free_end = "endpoint" in source
            if free_end:
                active = range(first,n,2)
            else:
                active = [i for i in range(first,n-1,2) if original[i-1] != original[i+1]]
            assert len(active)==count
            ids = [n-1-i for i in active]
            # Translating the two free bits always normalizes the new first color.
            st,w = search.solve(original[::-1], [], ids,192,10000,free_end)
            print(json.dumps([st,key,first,w,source]),flush=True)
            if w:return


if __name__ == '__main__':
    main()
