from pathlib import Path
import collections,hashlib,json,subprocess,datetime
H=Path(__file__).resolve().parents[1];R=H.parents[1]
bankpath=R/'work/bank9.json';raw=bankpath.read_bytes();bank=json.loads(raw)
rows=[];spans=collections.Counter()
for seed,row in enumerate(bank):
    p=row['vertex_sequence']
    for end in [0,191]:
        for k in range(9):
            w=p[end]^(1<<k)
            blocked=[i for i,v in enumerate(p) if i!=end and (w==v or (w^v).bit_count()==1)]
            assert blocked
            possible=0 not in blocked and 191 not in blocked
            span=max(blocked)-min(blocked)+2 if possible else None
            if possible:spans[span]+=1
            rows.append(dict(seed=seed,endpoint=end,direction=k,extension_vertex=w,blocking_indices=blocked,
                possible_with_fixed_endpoints=possible,minimum_block_edges=span))
out=dict(status='COMPLETE',bank_sha256=hashlib.sha256(raw).hexdigest(),rows=rows,
    impossible_with_fixed_endpoints=sum(not r['possible_with_fixed_endpoints'] for r in rows),
    minimum_span_counts=dict(sorted(spans.items())),minimum_span=min(spans),
    explanation='Every original collision or chord with the proposed extension vertex must be removed. A fixed-endpoint contiguous replacement must contain all these positions strictly in its interior. The interval span is necessary, not sufficient.')
target=H/'data/blocker-spans.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
assert hashlib.sha256((R/'milestones/192-moving-ports/data/bank9-input.json').read_bytes()).hexdigest()==out['bank_sha256']
(H/'data/bank9-input.json').write_bytes(raw)
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
diff=subprocess.check_output(git+['diff','b2f85574241bd8d9aca499440b9bc0f3b4c0def0..origin/research/unconditional-241'],cwd=R)
(H/'data/contributor-update.diff').write_bytes(diff)
(H/'data/resume.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    previous_turn='Pause honoured; research resumes from saved completed census. No research progress during pause.',
    goal_status='active',main_head=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),
    contributor_head=subprocess.check_output(git+['rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip(),
    contributor_report='2639 of 3118 production modules at 2026-11-12 01:25 UTC; 746 of 748 replay migrations. Not independently rebuilt or merged.',
    resource_note='A regions2 startup attempt stopped before search at 1042739200 free bytes, below the unchanged 1GiB gate.'),indent=2)+'\n')
