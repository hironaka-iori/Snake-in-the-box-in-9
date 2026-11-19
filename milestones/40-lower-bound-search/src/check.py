#!/usr/bin/env python3
"""Independent snake checker: reads lines with vertex lists, validates each.
Usage: check.py N file  (lines 'BEST ... : v0 v1 ...' or plain integers)."""
import sys
def check(n, seq):
    if len(set(seq)) != len(seq): return "repeat"
    if any(not 0 <= x < 2**n for x in seq): return "range"
    for i in range(len(seq)):
        for j in range(i+1, len(seq)):
            adj = bin(seq[i] ^ seq[j]).count("1") == 1
            if adj != (j == i+1): return f"bad pair {i},{j}"
    return None
if __name__ == "__main__":
  n = int(sys.argv[1])
  for line in open(sys.argv[2]):
      if not line.startswith("BEST") and not line[:1].isdigit(): continue
      if ":" in line: line = line.split(":", 1)[1]
      seq = [int(t) for t in line.split()]
      if not seq: continue
      err = check(n, seq)
      print(f"edges={len(seq)-1} {'OK' if err is None else 'FAIL '+err}")
