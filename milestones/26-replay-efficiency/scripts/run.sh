# run.sh TAG SEG CP GROUP CHUNK MERGE(0/1) FORCE NAME MOD   (EXTRA env passes to gen)
S=${STUDY:-/tmp/replay-study}
H=$(dirname "$(readlink -f "$0")")
cd $S && D=oleanstudy/$1_$9 && rm -rf $D && NOPACK=$NOPACK EXTRA="--force-lemmas $7" python3 $H/gen.py $D $2 $3 $4 $8 > $D.gen.json || exit 1
W=$(python3 -c "import json;print(json.load(open('$D.gen.json'))['wbits'])")
[ "$5" != 0 ] && python3 $H/packproof.py $D/LocalWindowUnsat/$9 $W $5
[ "$6" = 1 ] && python3 $H/merge.py $D $9
python3 $H/build.py $D $9 > $D.build.txt 2>&1; tail -1 $D.build.txt | grep -q '^{' || { echo "BUILD FAILED $1 $9"; grep -v '^  |' $D.build.txt | tail -5; }
python3 - $D $1 $9 $2 $3 $5 $6 <<'PY'
import json, sys, os
D, tag, mod, seg, cp, chunk, merge = sys.argv[1:]
g = json.load(open(D + '.gen.json'))
r = [json.loads(l) for l in open(D + '.build.txt') if l.startswith('{')]
chk = [x for x in r if x['module'].startswith('Check') or (merge == '1')]
tot = sum(x['olean'] for x in r)
rec = dict(tag=tag, window=mod, hints=g['hints'], lemmas=g['lemmas'], seg=int(seg), cp=int(cp), chunk=int(chunk), merged=merge == '1',
           segments=g['segments'], checkpoints=g['checkpoints'], modules=len(r), olean=tot, bph=round(tot / g['hints'], 3),
           kernel_cpu=round(sum(x['cpu'] for x in chk), 2), ms_per_hint=round(1000 * sum(x['cpu'] for x in chk) / g['hints'], 4),
           all_cpu=round(sum(x['cpu'] for x in r), 2), rss=max(x['rss_gb'] for x in r))
print(json.dumps(rec)); open(''+os.environ.get('STUDY','/tmp/replay-study')+'/results.jsonl', 'a').write(json.dumps(rec) + '\n')
PY
rm -rf $D/_olean
