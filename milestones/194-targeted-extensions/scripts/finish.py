from pathlib import Path
import collections,datetime,hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def read(name):return json.loads((H/'data'/name).read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def key(q):return tuple(q[k] for k in ['length','seed','endpoint','direction','start','end'])
audit=[]
def checked_retries(filename,dimension,bankfile):
    result=read(filename);assert result['status'] in ['COMPLETE','TIME_LIMIT','LONGER_WITNESS_FOUND']
    source=H/'data'/result['arguments']['source'];prior=json.loads(source.read_text())
    assert sha(source)==result['source_sha256']
    raw=(H/'data'/bankfile).read_bytes();digest=hashlib.sha256(raw).hexdigest()
    assert digest==prior['bank_sha256']
    if 'bank_sha256' in result:assert result['bank_sha256']==digest
    bank=json.loads(raw);out={};N=[{v^(1<<k) for k in range(dimension)} for v in range(1<<dimension)]
    for index,entry in enumerate(result['results']):
        q=entry['query'];p=bank[q['seed']]['vertex_sequence'];i=q['start'];j=q['end'];u=p[i];v=p[j]
        w=p[q['endpoint']]^(1<<q['direction']);retained=p[:i+1]+p[j:]
        assert all(z!=w and z not in N[w] for z in retained if z!=p[q['endpoint']])
        forbidden=set(retained)|N[w]|{w}
        for z in retained:
            if z not in [u,v]:forbidden|=N[z]
        allowed=sorted((set(range(1<<dimension))-forbidden)|{u,v})
        source_entry=entry
        if 'reused_query' in entry:
            earlier=entry['reused_query'];assert 0<=earlier<index
            source_entry=result['results'][earlier];assert 'reused_query' not in source_entry
            assert entry['status']==source_entry['status']
        assert source_entry['allowed']==allowed and source_entry['anchors']==[u,v]
        assert source_entry['target_vertices']==q['length']+1
        assert sha(source_entry['model'])==source_entry['model_sha256']
        assert key(q) not in out;out[key(q)]=entry['status']
    assert result['completed_queries']==len(result['results'])
    audit.append(dict(result=filename,bank_sha256=digest,queries=len(out),unique_models=result['unique_models'],reconstructed_regions_match=True,initial_models_match=True))
    return out

q9map=checked_retries('retry36-42.json',9,'bank9-input.json')
q9map.update(checked_retries('retry43-45.json',9,'bank9-input.json'))
lower=checked_retries('lower-retry28-32.json',7,'lower-input.json')
lower.update(checked_retries('lower-retry33-48.json',7,'lower-input.json'))
def coverage(files,retries,initial):
    rows=[]
    for filename in files:
        data=read(filename);assert data['status'] in ['COMPLETE','TIME_LIMIT']
        assert not data['witness']
        for row in data['completed_rows']:
            queries=[r['query'] for r in data['unknown'] if r['query']['length']==row['length']]
            assert len(queries)==row['unknown']
            assert sum(row['rejections'].values())+row['unknown']==row['queries']
            resolved=sum(retries.get(key(q))=='INFEASIBLE' for q in queries)
            rows.append(dict(length=row['length'],queries=row['queries'],native_excluded=sum(row['rejections'].values()),
                originally_unknown=row['unknown'],solver_excluded=resolved,remaining=row['unknown']-resolved))
    frontier=initial
    for row in rows:
        if row['length']!=frontier+1 or row['remaining']:break
        frontier=row['length']
    return frontier,rows
K,q9rows=coverage(['target34-64.json','target43-64-fast.json'],q9map,33)
L,lowrows=coverage(['lower48-to49.json','lower33-48.json'],lower,1)
aligned=read('aligned-lower49.json');upper=aligned['best']['block_length'];assert upper==43
accepted=[]
for module in ['Pruning194']+read('lower-proof-order.json'):
    record=read(module+'-audit.json');assert record['status']=='PASS' and record['exit_code']==0 and record['stop_reason'] is None
    for field,digest in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(record[field])==record[digest]
    for path,digest in record['dependencies'].items():assert sha(path)==digest
    accepted.append(dict(module=module,reports=len(record['axioms']),receipt_sha256=sha(H/'data'/(module+'-audit.json'))))
summary=dict(round=194,status='PROGRESS',goal_status='active',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    q9_single_replacement_excluded_through=K,q9_coverage=q9rows,lower_single_replacement_excluded_through=L,
    lower_improvement_block=upper,lower_minimum_block_interval=[L+1,upper],lower_coverage=lowrows,
    accepted_modules=accepted,numerical_scope='Native enumeration and solver exclusions; no full Lean contradiction certificate for numerical cutoffs.',
    distinction='The Q9 cutoff applies to one replacement immediately followed by one endpoint addition. Only round193 supplies closure under arbitrary finite sequences, through33 edges.')
(H/'data/completion.json').write_text(json.dumps(summary,indent=2)+'\n')
(H/'data/input-audit.json').write_text(json.dumps(dict(retries=audit,first_retry_bank_provenance='The first retry did not record its loaded bank hash. Every queried region, anchor pair, target size, cache reuse and saved model was reconstructed against the source-pinned bank and matched. Later retry code pins the bank directly.',dynamic_models='Initial model files plus recorded dynamic cycle cuts determine the final queried models.'),indent=2)+'\n')
(H/'data/review.json').write_text(json.dumps(dict(reviewer='exchange191_review',mode='Read-only mathematical and source review; no computations or edits',findings=['No unsound exclusion identified in strict blocker intervals, restored anchors, DFS masks, block bounds or solver cycle cuts.','COMPLETE means all queries visited; remaining UNKNOWN cases must be counted.','The interrupted active query is outside the unknown list and must remain unresolved.','Cache key (u,v,length,allowed) is sufficient for reusing exclusions.','First retry bank provenance required reconstruction; completed in input-audit.json.','Initial solver files require the recorded dynamic cycle cuts when reproducing later iterations.']),indent=2)+'\n')

note=f'''# Round 194: targeted extensions and a lower-dimensional comparison

Every single length-preserving contiguous replacement of at most {K} edges in the131 saved191-edge Q9 snakes, followed immediately by one endpoint addition, is computationally excluded. This is distinct from round193's closure under arbitrarily many moves of at most33 edges. It does not exclude sequences of larger replacements.

The main comparison is in Q7. The specific48-edge lift of the optimal26-edge Q6 middle is globally suboptimal because a50-edge Q7 snake is known. Nevertheless, one replacement followed by endpoint addition cannot improve it to49 when the block has at most {L} edges. An explicit aligned subpath of the known50-edge snake gives a49-edge construction using a43-edge replacement. Thus the minimum block length for this operation lies in [{L+1},43]. Its exact value remains unresolved. Both the old48-edge and new49-edge paths, and their retained positions, have now passed Lean checks. The numerical lower cutoff remains native.

## Search and pruning argument

For a specified candidate new endpoint w, remove every original blocker inside the replacement interval. The new interior avoids retained vertices, neighbours of retained nonanchors, w and all neighbours of w. The two anchors are restored only after verifying that all original blockers, except the endpoint to which w attaches, lie strictly inside the interval.

A nonanchor vertex with at most one available neighbour cannot belong to a simple path between the anchors: each internal path vertex has two distinct neighbours on that path. Repeating the deletion preserves all possible routes. The anchors must remain connected, and their graph distance cannot exceed the required length. Component size and bipartite colour counts give further necessary bounds.

For equal-coloured entry and exit, with t edges-pairs, the route uses t+1 vertices of the starting colour and t of the other. Its edge bound is twice the smaller of the available starting-colour count minus one and the other-colour count. For opposite colours it is twice the smaller colour count minus one. These arithmetic implications pass Lean under their count premises.

The allowed graph can also be decomposed into biconnected blocks, with bridges treated as blocks. Only the blocks on the terminal-to-terminal route can be used: entering an attached branch and leaving it repeats its cut vertex. If a used block's entry and exit are adjacent, inducedness forces their edge directly; any longer local route has that edge as a chord. Sum the local colour bounds, using one for adjacent entry/exit. Lean checks the single-attachment contradiction and the adjacent-anchor implication. The graph decomposition algorithm and its complete transfer remain written/native evidence.

Unresolved queries were converted to exact selected-vertex count and induced-degree models, with fixed anchors, colour counts and all contained square exclusions. The initial relaxation permits disconnected longer cycles. Every observed such cycle gives a valid exclusion of selecting all its vertices together. Initial models and subsequent cycle cuts are both retained. No solver INFEASIBLE result is presented as a Lean contradiction certificate.

## Evidence and limits

The baseline covered lengths34--42. Its512 unresolved queries at36--42 were all excluded by373 distinct solver models in13.297 seconds. A further reduced-node scan visited lengths43--51; the solver revisit of43--45 advances the complete cutoff to {K}. Later unknowns, unvisited queries and the globally interrupted active query remain unresolved. Completion.json records coverage by length.

The lower-dimensional scan excluded lengths2--27 directly and28--32 after171 solver retries. The next solver pass advances the complete lower cutoff to {L}. Of576 isometric placements of known49-edge subpaths with the desired48-edge tail anchors, the best displayed placement changes the block from position0 to43. Its coordinate map and translation are saved with the full vertices. This576-placement search does not classify all49-edge snakes.

The demonstrated lower-dimensional obstruction is compatible with suboptimality. Therefore the Q9 local exclusions do not support an optimality claim for191. The next constructive route is to reroute the231 shortened189-edge states from round193 before regrowth, beginning with the11 classes that already permit one endpoint addition. That operation has not yet been examined.

The two manuscripts are updated in place, preserving the authors and local hyperlink settings. Archived235 retains its pending independent-rebuild qualification;233/234 remain conditional. The contributor head at the opening fetch was aeab10ecbab6480a11f927e590b664bd7f0b4f5f, unchanged from round193. Whole-manuscript consistency review remains scheduled for round200. The goal remains active.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
(H/'README.md').write_text(f'''# Round 194: targeted endpoint extensions

One contiguous replacement of at most {K} edges followed by one endpoint addition is computationally excluded for all131 saved Q9 snakes. This is a one-operation result, distinct from round193's repeated-move closure through33 edges.

A known suboptimal48-edge Q7 lift resists the same operation through {L} edges, yet an explicit43-edge replacement produces49. Both paths and their retained coordinates pass Lean. This comparison shows why local obstructions cannot establish global optimality.

Read [the argument](MATHEMATICAL_NOTE.md), [coverage](data/completion.json), [input audit](data/input-audit.json), [aligned49-edge path](data/aligned-lower49.json), and [handoff](../../handoff/CURRENT_STATUS.md). Numerical exclusions remain native. Solver models are packaged in data/solver-models.zip; extract it into this milestone folder before replaying recorded model paths. Local raw models are also retained.
''',encoding='utf-8',newline='\n')

main=rf'''
\subsection{{Targeted extensions and a lower-dimensional obstruction}}
\label{{sec:target194}}
The necessary blocker interval allows the search to fix a proposed new
endpoint before enumerating replacements. Every old collision or chord
with that endpoint must lie strictly inside the replaced block. The
replacement interior then avoids the retained vertices, the neighbours
of retained non-anchors, and the new endpoint and its neighbours.

\begin{{proposition}}[Pruning a replacement region]
Let $G$ be the allowed graph and $u,v$ its distinct required anchors.
Deleting a vertex other than $u,v$ with degree at most one preserves
every simple $u$--$v$ path. The same holds after any finite sequence
of these deletions. A remaining route must lie in the component of
$u$ containing $v$, and its length is at least their graph distance.
\end{{proposition}}
\begin{{proof}}
Each internal vertex of a simple path has two distinct path neighbours.
It cannot be the first deleted path vertex. Induction gives the
repeated-deletion assertion. Connectivity and distance follow from
the route itself.
\end{{proof}}
The nonterminal deletion implication passes Lean for the actual
injective path representation.

Suppose a surviving region contains $N_0,N_1$ vertices of the two
cube colours. An induced route of length $\ell$ between opposite
colours satisfies
\[
\ell\le2\min(N_0,N_1)-1.
\]
If both endpoints have colour $c$, then
\[
\ell\le2\min(N_c-1,N_{{1-c}}).
\]
These follow by alternating the vertex colours along the route;
their arithmetic implications pass Lean under the count premises.

Decompose the surviving graph into maximal biconnected blocks,
treating each bridge as a block. Only blocks on the unique route
between the anchors in the block-cut tree can be used. A detour into
an attached branch would revisit its attachment vertex. Apply the
colour bound within each used block and add the resulting edge bounds.
If a block's entry and exit are adjacent, its bound is one: a longer
induced route would have their edge as a chord. The single-attachment
contradiction and the adjacent-anchor statement pass Lean. The
decomposition computation and its complete transfer remain outside
the checked proof.

\paragraph{{Current nine-dimensional cutoff.}}
All single length-preserving replacements of blocks of at most {K}
edges, followed immediately by one endpoint addition, are now
computationally excluded for every saved 191-edge snake. The search
combines complete enumeration, the preceding necessary bounds, and
selected-vertex solver models. The latter impose the required size,
the two anchor degrees, degree two at every other selected vertex,
colour counts and square exclusions. Longer disconnected cycles are
excluded as they appear. Infeasibility therefore excludes the desired
path, although these numerical solver results have no Lean contradiction
certificates. Later incomplete ranges retain their unresolved queries.

This cutoff concerns one replacement immediately followed by growth.
It does not extend the repeated-move closure beyond 33 edges: a larger
replacement could reach a new 191-edge class before further changes.

\paragraph{{A suboptimal lower-dimensional example.}}
The 48-edge $Q_7$ lift obtained from the displayed optimal 26-edge
$Q_6$ middle is globally suboptimal, because a 50-edge $Q_7$ snake is
known. Nevertheless, the same replacement-and-addition operation
cannot improve this particular lift to 49 edges using a block of
at most {L} edges, by complete native enumeration and solver exclusions.

An explicit alignment of a 49-edge subpath of the displayed 50-edge
snake gives an improvement using a 43-edge replacement. It replaces
the block from position 0 to position 43 of the old path, retains
positions 43--48 and the old initial anchor, and adds one new initial
vertex. Both the old 48-edge path and the resulting 49-edge path,
together with these retained positions, pass Lean checks.
The minimum block length for this operation therefore lies in
\[
{L+1}\le k_{{\min}}\le43.
\]
The lower inequality remains a native computational exclusion; the
exact minimum is unresolved. The displayed construction was selected
from 576 aligned placements of known subpaths, without classifying
all 49-edge snakes.

This example demonstrates a substantial local obstruction in a path
that is known to be suboptimal. Accordingly, the $Q_9$ exclusions
provide search restrictions without evidence of global optimality.
The next construction route is to reroute the shorter 189-edge states
before endpoint regrowth. Records and proof receipts are retained
in~\cite{{target194archive}}.

'''
short=rf'''
\paragraph{{Targeted growth and the lower-dimensional comparison.}}
Fixing the proposed new endpoint allows the search to remove its
blocking vertices first. Repeatedly delete non-anchor vertices with
at most one available neighbour; an internal path vertex needs two
distinct path neighbours. Reject disconnected anchors or insufficient
colour counts. Attached graph branches cannot be used without
revisiting their attachment vertex. If a required section has adjacent
entry and exit vertices, inducedness forces their edge directly.
The key implications pass Lean; finite coverage remains native.

These bounds and selected-vertex solver models exclude every single
replacement of at most {K} edges immediately followed by one endpoint
addition, for all saved 191-edge snakes. This is a one-operation
cutoff. The earlier repeated-move closure still extends only through
33 edges.

A lower-dimensional comparison prevents interpreting these exclusions
as optimality. The known suboptimal 48-edge $Q_7$ lift cannot improve
to 49 by this operation with a block of at most {L} edges, yet an
explicit 43-edge replacement succeeds. Both paths and their retained
positions are checked in Lean; the numerical lower cutoff is native.
Thus the required block size in this example lies between {L+1} and 43.
Large local obstructions can coexist with a better global construction.
The next $Q_9$ search will allow rerouting of the shorter 189-edge
states before endpoint regrowth.

'''
edits=[]
for name,addition,marker in [('snake9_research.tex',main,'\\section{Construction experiments and their scope}'),('snake9_frontier_explanation.tex',short,'\\textbf{7. What is proved, and what remains.}')]:
    p=D/name;mirror=R/'paper'/name;assert p.read_bytes()==mirror.read_bytes();before=p.read_text(encoding='utf-8')
    assert 'sec:target194' not in before and before.count(marker)==1
    after=before.replace(marker,addition+marker,1)
    if name=='snake9_research.tex':
        bib=r'''\bibitem{target194archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Targeted extensions and lower-dimensional local obstructions}. Research record 194, 12 November 2026. Region enumerations, solver models, coverage records and checked path constructions:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/194-targeted-extensions}.

'''
        after=after.replace('\\end{thebibliography}',bib+'\\end{thebibliography}',1)
    else:after=after.replace('Research state after round 193','Research state after round 194').replace('research records 175--193','research records 175--194')
    assert before.split('\\begin{document}')[0].replace('round 193','round 194')==after.split('\\begin{document}')[0]
    p.write_text(after,encoding='utf-8',newline='\n');mirror.write_bytes(p.read_bytes());edits.append(dict(path=str(p),mirror=str(mirror),sha256=sha(p)))
(H/'data/manuscript-edits.json').write_text(json.dumps(edits,indent=2)+'\n')
status=f'''# Round 194 complete; goal active

Read milestones/194-targeted-extensions/MATHEMATICAL_NOTE.md and data/completion.json. The previous turn was progress and the active goal remains unresolved.

Q9: every single length-preserving contiguous replacement of at most {K} edges followed immediately by one endpoint addition is computationally excluded for all 131 saved 191-edge snakes. This is NOT arbitrary repeated-move closure. Only round193 has such closure through33 edges. No longer Q9 snake or global numerical bound follows.

The initial baseline visited34--42; all512 unresolved queries through42 were excluded by373 distinct solver models. The later scan visited43--51 with many UNKNOWN cases; a bounded retry of43--45 yields the complete cutoff {K}. Read per-length coverage, rather than interpreting COMPLETE as infeasibility. Globally interrupted active queries are outside the unknown list and remain unresolved. Raw solver files are local and also packaged in data/solver-models.zip for publication; extract into the milestone folder for replay. Initial models require any recorded dynamic cycle cuts.

Q7 comparison: the48-edge lift from the fixed optimal26-edge Q6 middle is known suboptimal. Its one-replacement-plus-addition minimum lies in [{L+1},43]. Exclusion through{L} is native. An aligned known49-edge subpath gives the43-edge construction. Both actual48- and49-edge paths and retained positions are checked in Lean. This is direct evidence that strong local rigidity does not imply optimality.

Pruning194 checks degree-one deletion, adjacent-anchor length1, colour-count arithmetic and the single-attachment obstruction. LowerData194/LowerRows194/LowerWitness194 check the two concrete Q7 paths. Native numerical coverage and complete graph-decomposition transfer remain outside Lean. Two initial failed pruning source snapshots are preserved; accepted modules pass without admitted statements.

Next constructive route: reroute the231 shorter189-edge states from round193 before endpoint growth, beginning with the11 classes permitting one endpoint addition. Those changed shorter states fall outside the established191-edge closure. This route has not yet been attempted. Do not repeat completed targeted exclusions.

Inherited dimensional findings: fixed26-edge Q6 middle maximum48; shorter24-edge middle supports50. Fixed50-edge Q7 middle range89--97; fixed98-edge Q8 middle targeting192 remains unresolved. Fixed95-to97 middle replacements require at least8 omissions computationally; whole191-to192 replacements require at least5 omissions/6 additions. Preserve their distinct scopes.

Archived235 independent rebuild remains pending;233/234 conditional; round18793/98 batches and11904/12424 clauses checked; critical contradiction and actual-snake transfer pending. Contributor branch was unchanged at aeab10ecbab6480a11f927e590b664bd7f0b4f5f on initial fetch. Whole-source review next at200.

Preserve unrelated edits, currently .gitignore. Edit existing D:/Codex/2026-10-13/new-chat/outputs manuscripts and mirror E:/Snake-in-a-box/paper. Authors and hypersetup remain unchanged. Keep one heavy worker and the existing memory/time guards. All research worker handles are terminal at publication.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(status,encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Continue the active construction goal from round194. Inspect the current worktree and remote state before continuing.\n\n'+status,encoding='utf-8',newline='\n')
p=R/'README.md';before=p.read_text(encoding='utf-8');assert before.startswith('# Current result after round 193')
p.write_text(f'''# Current result after round 194

A single contiguous replacement of at most {K} edges followed by one endpoint addition is computationally excluded for every saved191-edge Q9 snake. Repeated-move closure remains established natively only through33 edges.

The lower-dimensional comparison is decisive for interpretation: a known suboptimal48-edge Q7 lift resists this operation through{L} edges, yet a43-edge replacement gives49. Both concrete paths and retained positions pass Lean. Strong local obstruction therefore does not establish global optimality.

Read [round194](milestones/194-targeted-extensions/README.md), [the argument](milestones/194-targeted-extensions/MATHEMATICAL_NOTE.md), [handoff](handoff/CURRENT_STATUS.md), [paper](paper/snake9_research.tex), and [frontier explanation](paper/snake9_frontier_explanation.tex). The goal remains active; no new Q9 record or global numerical bound was obtained.

## Earlier checkpoints

'''+before,encoding='utf-8',newline='\n')
print(json.dumps(dict(q9_cutoff=K,lower_cutoff=L,lower_upper=upper,modules=len(accepted),reports=sum(x['reports'] for x in accepted)),indent=2))
