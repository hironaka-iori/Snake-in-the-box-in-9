import json, sys
sys.path.insert(0,'/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/ana')
from fiber_cp import solve, verify
from bank_words import decompose
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
i=int(sys.argv[1]); mode=sys.argv[2]; secs=float(sys.argv[3])
word, segs, n = decompose(bank[i])
if mode=='hint': r=solve(word,seconds=secs,workers=4,hint=segs)
else: r=solve(word,seconds=secs,workers=4,target=193)
print(i,mode,'outer len',len(word),{k:v for k,v in r.items() if k!='path'},'path_len',len(r.get('path',[])),'verified',verify(r['path']) if 'path' in r else None,flush=True)
