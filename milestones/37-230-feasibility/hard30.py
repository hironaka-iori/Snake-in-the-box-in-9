import json, sys, corner7
d = json.loads(sys.argv[1]); T = int(sys.argv[2]); tl = float(sys.argv[3])
st, wit, sec = corner7.test(d, T, tl)
r = dict(dirs=d, T=T, result=st, witness=wit, seconds=sec, tl=tl)
open('data/corner7_levels.jsonl', 'a').write(json.dumps(r) + '\n'); print(r)
