"""Assemble round193 evidence and update the existing manuscript sources."""
from pathlib import Path
import collections,datetime,hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def read(name):return json.loads((H/'data'/name).read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
original=read('reroutings.json');small=read('regions2.json');mid=read('regions6-24.json');large=read('regions25-36.json')
assert original['status']==small['status']==mid['status']=='COMPLETE'
assert large['status'] in ['COMPLETE','TIME_LIMIT']
counts={int(k):v['valid_moves'] for k,v in original['summary'].items()}
groups=collections.defaultdict(list)
for dataset in [small,mid,large]:
    assert not dataset['new_classes'] and not dataset['growth']
    assert dataset['bank_sha256']==original['bank_sha256']
    for row in dataset['completed_rows']:groups[row['length']].append(row)
for length,rows in groups.items():
    if len(rows)==131:
        assert {r['seed'] for r in rows}==set(range(131))
        assert all(r['blocks_complete']==192-length for r in rows)
        counts[length]=sum(r['valid_moves'] for r in rows)
assert set(counts)==set(range(2,max(counts)+1))
K=max(counts);total=sum(counts.values())
assert all(r['rare_crossing_moves']==0 for d in [small,mid,large] for r in d['completed_rows'])
loss=read('shorten2-blocks4-24.json');regrowth=read('regrowth.json')
assert loss['status']==regrowth['status']=='COMPLETE'
assert len(loss['completed_rows'])==21*131 and len(loss['new_classes'])==231
assert regrowth['maxima']=={'0':220,'1':11} and not regrowth['new_191_classes'] and not regrowth['longer']
proofs=[]
for module in ['BlockReplacement193','EndpointBlockers193']:
    q=read(module+'-audit.json');assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    for field,digest in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(q[field])==q[digest]
    for p,d in q['dependencies'].items():assert sha(p)==d
    proofs.append(dict(module=module,reports=len(q['axioms']),receipt_sha256=sha(H/'data'/(module+'-audit.json'))))
partial=large.get('current_incomplete')
summary=dict(round=193,status='PROGRESS',goal_status='active',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    complete_block_lengths=[2,K],valid_moves_by_length=counts,total_moves=total,
    new_191_classes=0,endpoint_extensions=0,rare_crossing_moves=0,partial_larger_search=partial,
    shortening=dict(complete_lengths=[4,24],loss_edges=2,classes_189=231,maximum_growth_counts=regrowth['maxima']),
    accepted_modules=proofs,scope='General replacement and closure implications pass Lean. Numerical bank closure and all finite enumerations remain native; no new global bound or longer snake.')
(H/'data/completion.json').write_text(json.dumps(summary,indent=2)+'\n')
(H/'data/review.json').write_text(json.dumps(dict(
    reviewer='exchange191_review',mode='Read-only mathematical review; no edits or computation',
    conclusions=['Retained-neighbour mask is necessary and sufficient for an induced replacement with fixed anchors; apply only to internal vertices.',
    'Boundary blocks preserve the global endpoints and require no extra exterior segment.',
    'Closure under symmetry-invariant moves on every representative implies closure under every finite sequence.',
    'Endpoint extension must be checked for every representative; reversal swaps the two ends.'],
    limitations=['Native census is not a Lean proof of the finite bank closure.','The move family must include every block position and every permitted induced replacement.']),indent=2)+'\n')
note=rf'''# Round 193: contiguous replacements and closure of the saved bank

The construction search still has no snake longer than 191 edges. This round establishes a restricted computational barrier: every length-preserving replacement of a contiguous block of at most {K} edges in any of the 131 saved snakes stays in the same bank up to cube isometry and path reversal. Blocks of one edge have no alternative. There are {total} valid moves for lengths 2--{K}; the counts include repeated outcomes. None changes the crossing positions of a coordinate used exactly twice. Every bank representative has both endpoints blocked.

## Replacement criterion

Let P=(p_0,...,p_L) be induced, 0<=i<j<=L, and retain C={{p_0,...,p_i}} union {{p_j,...,p_L}}. Let R be an induced path between u=p_i and v=p_j, with interior I. The concatenation is induced exactly when

I intersects neither C nor the neighbours of any vertex in C minus {{u,v}}.

Every collision repeats a retained vertex, and every forbidden edge is a chord. Conversely, pairs within the replacement are controlled by its inducedness, retained pairs keep their original relationships, and the displayed condition handles all remaining pairs. The anchors are excluded from the neighbourhood mask because their intended replacement edges must remain. Boundary blocks i=0 and j=L satisfy the same argument. The replacement's length has the same parity as j-i; the total length is L-(j-i)+length(R).

The Lean construction checks the sufficient direction for a replacement of unchanged length, including boundary blocks. The exact set criterion and variable-length version are written mathematical deductions; the native programs also check each accepted entire path independently.

## Why repeating short moves cannot help

Take the union of the saved bank's cube-isometry and reversal classes. The move rule is invariant under these symmetries. Complete enumeration from every representative shows that one allowed move stays in this union. Induction on the number of moves gives the same conclusion for any finite sequence. Both-endpoint nonextendibility is preserved by the same symmetries. Thus a finite sequence of these length-preserving moves cannot unlock a one-edge extension.

Lean checks the general finite-chain and nonextension implications with explicit closure and blocked-family hypotheses. The numerical closure premise for the 131 representatives remains native. This is not a classification of all 191-edge snakes and gives no global upper bound. A successful construction through this move family must use a block longer than {K} edges, or a different operation.

## Enumerations and completeness

The original 3--5-edge census first enumerates induced routes between each pair of endpoints and filters against the retained path. The longer search enumerates directly in the region freed by a deletion. At each step it rejects retained vertices, neighbours of retained non-anchors, repeats and chords to earlier replacement vertices. Distance and parity provide necessary pruning. Every legal next cube neighbour is considered; a target is accepted only at the specified depth. Canonical transition sequences use first-occurrence coordinate relabelling and the minimum of forward and reversed order. This is exact for translations, coordinate permutations and reversal, including unused coordinates.

The 6--24-edge sweep completed in {mid['seconds']:.3f} seconds. The 25--36 sweep stopped with status {large['status']} after {large['seconds']:.3f} seconds. Complete coverage ends at {K}; any later completed seed rows and the current partial row are retained separately and do not establish full coverage of that longer block length. The earlier 3--5-edge census is retained unchanged.

## Shortening before endpoint growth

All replacements of a 4--24-edge block by a path shorter by two edges were enumerated. Their 189-edge outcomes form 231 symmetry classes. Complete endpoint growth, allowing either end at every step, finds no extension for 220 classes and exactly one extra edge at most for the other 11. No class can reach even 191 edges using endpoint additions alone. The computation does not exclude internal reroutings of these shorter paths before regrowth.

## Focusing the next search

Fix a candidate new endpoint w adjacent to an old endpoint. Every original nonattachment vertex equal or adjacent to w must be removed. If their smallest and largest indices are lo and hi, a contiguous replacement from i to j must satisfy i<lo<=hi<j, hence j-i>=hi-lo+2. An original blocking global endpoint would make the fixed-endpoint operation impossible. The current bank has no such endpoint blocker, and the recorded minimum necessary spans range from 2 to 190. These are only necessary conditions.

Lean checks that every old blocker lies in the changed interior under the actual agreement and separation premises, together with the span inequality. The next useful search is to impose these blocker requirements before enumerating larger replacements. This directly targets a 192-edge extension. Another open operation is to reroute a 189-edge shortened state before trying endpoint growth. Neither operation has been searched in this round.

## Verification and inherited state

Two new Lean modules pass, with five theorem dependency reports, no admitted statements and no native decision oracle. The unchanged guards require 1GiB free at startup, 768MiB reserve, at most 256MiB per Lean process, 60 seconds per check and one heavy research worker. One small census startup stopped below the threshold, then was retried after memory recovered. Generic proof checks do not certify native enumeration completeness.

The contributor branch was fetched at aeab10ecbab6480a11f927e590b664bd7f0b4f5f. Its report states 2639/3118 production modules and 746/748 replay migrations. The diff is archived; these additions were neither merged nor independently rebuilt. Archived 235, conditional 233/234, and pending graph-to-snake obligations retain their earlier qualifications. Full manuscript consistency review remains scheduled for round 200.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8')
(H/'README.md').write_text(f'''# Round 193: block replacements

Complete length-preserving block enumeration through {K} edges leaves the 131 saved 191-edge symmetry classes closed. No finite sequence of these moves can unlock endpoint growth, conditional on the native closure census; the general implication passes Lean. All two-edge shortenings inside 4--24-edge blocks produce 231 shorter classes, none capable of regrowing to 191 by endpoint additions alone.

Read [the argument](MATHEMATICAL_NOTE.md), [completion](data/completion.json), [longer blocks](data/regions25-36.json), [shortening](data/shorten2-blocks4-24.json), [regrowth](data/regrowth.json), and [blocker spans](data/blocker-spans.json). The two accepted proof receipts are under data. No improved numerical bound or longer snake follows.
''',encoding='utf-8')

main_add=rf'''
\subsection{{Contiguous replacements and repeated local moves}}
\label{{sec:block193}}
Let $P=(p_0,\ldots,p_L)$ be an induced path and replace the subpath
from $u=p_i$ to $v=p_j$ by another induced path with the same endpoints.
Write $C=\{{p_0,\ldots,p_i\}}\cup\{{p_j,\ldots,p_L\}}$ for the retained
vertices and $I$ for the replacement's internal vertices.

\begin{{proposition}}[Criterion for a contiguous replacement]
The concatenated path is induced if and only if
\[
I\cap\left(C\cup\bigcup_{{z\in C\setminus\{{u,v\}}}}N(z)\right)=\varnothing.
\]
Here $N(z)$ denotes the neighbours of $z$ in the cube.
\end{{proposition}}
\begin{{proof}}
A collision repeats a retained vertex, and an edge from the replacement
interior to a retained non-anchor is a chord. These prove necessity.
For sufficiency, the replacement's inducedness controls its internal
pairs and contacts with the two anchors. Retained pairs keep their
original relationships. The displayed condition excludes every remaining
collision or chord. If a block has one edge, its adjacent anchors
permit only that edge as an induced replacement. The same argument
applies at either global endpoint, with the absent exterior segment omitted.
\end{{proof}}
The new length is $L-(j-i)+\ell$, where $\ell$ is the replacement length.
Cube bipartiteness forces $\ell\equiv j-i\pmod 2$. In particular,
preserving both global endpoints permits only even changes in length.
The sufficient replacement criterion at unchanged length passes Lean;
the variable-length set statement above is a written deduction.

\begin{{proposition}}[Closure under repeated replacements]
Suppose a collection of path symmetry classes is closed under an allowed
replacement rule invariant under those symmetries. If every class has
blocked endpoints, no finite sequence of allowed replacements starting
in the collection can produce a path admitting an endpoint extension.
\end{{proposition}}
\begin{{proof}}
Induction on the number of replacements keeps the path in the collection.
Cube isometries preserve endpoint extendibility, and path reversal
interchanges the two endpoints. The final path therefore has blocked endpoints.
\end{{proof}}
The general induction and nonextension implication pass Lean with
explicit closure and blocked-family premises.

\paragraph{{The complete finite census.}}
For each of the 131 saved 191-edge snakes, all induced replacements
of every contiguous block of 2--{K} edges by a path of the same length
were enumerated. Every valid result belongs to an existing saved
symmetry class; there are {total:,} valid moves, with repeated outcomes
counted separately. No move changes the crossing positions of a
coordinate used exactly twice. Blocks of one edge have no alternative.
The complete bank is therefore computationally closed under these moves.
Since all its endpoints are blocked, the proposition excludes any
finite sequence of such moves followed by one endpoint extension.
This numerical closure premise has no complete Lean enumeration certificate.
It supplies a restriction on this move family, with no global upper bound.

The search over 25--36-edge blocks reached complete coverage through
{K} edges before its stopping condition. Later partial results do not
extend the complete range. The search enumerates every legal next
neighbour in the region freed by the deletion, pruning only repetitions,
chords, forbidden retained contacts, and impossible distance or parity.
Every accepted entire path is also checked directly.

\paragraph{{Shortening and subsequent growth.}}
Every replacement of a 4--24-edge block by a path shorter by two edges
was also enumerated. The resulting 189-edge paths form 231 symmetry
classes. Among these, 220 admit no endpoint addition and 11 admit at
most one. All choices of endpoint at each growth step are covered.
Thus endpoint additions alone cannot recover even 191 edges from
these states. Internal reroutings of the shortened paths remain open.

\paragraph{{Necessary locations for a useful replacement.}}
For a proposed extension vertex $w$, every original nonattachment
vertex equal or adjacent to $w$ must be removed. If their smallest
and largest indices are $r$ and $s$, replacing the block from $i$ to
$j$ requires
\[
i<r\le s<j,\qquad j-i\ge s-r+2.
\]
Indeed, each retained blocker would still violate distinctness or
create a chord with $w$. The interior requirement and the span
inequality pass Lean under explicit agreement and separation premises.
This condition can restrict the larger-block search before enumeration;
it does not ensure that a replacement exists. The next construction
search can impose all these blocker requirements and target a
192-edge path directly. Evidence and remaining scopes are recorded
in~\cite{{block193archive}}.

'''
short_add=rf'''
\paragraph{{Larger contiguous replacements.}}
The completed census now replaces every block of 2--{K} edges in each
of the 131 saved 191-edge snakes by every induced route of the same
length between its endpoints. Every valid result remains in an
existing symmetry class. This gives a stronger consequence than a
single failed move: any finite sequence of these replacements stays
in the bank and therefore cannot unlock an endpoint extension.
The general induction passes Lean; the numerical bank-closure premise
remains a native computation.

The replacement criterion is direct. Its internal vertices must avoid
all retained vertices and all neighbours of retained vertices other
than the two anchors. Its own inducedness controls contacts with the
anchors. This excludes every possible repeat or chord, including for
blocks touching a global endpoint. Lean checks the sufficient criterion
for replacements of unchanged length.

Shortening a block by two edges was also examined for all block
lengths 4--24. The resulting 189-edge paths form 231 symmetry classes:
220 allow no endpoint addition and 11 allow only one. None regrows to
191 through endpoint additions alone. Rerouting a shortened path
before regrowth remains open.

The next search can focus on the old vertices that block a proposed
new endpoint. Every such vertex must lie inside the replaced block.
If their first and last indices are $r,s$, the block needs at least
$s-r+2$ edges. This necessary condition and its underlying retained-vertex
argument pass Lean. It directs larger replacements towards the
192-edge target; it does not prove their existence. Complete native
coverage currently ends at {K} edges, and no global bound has changed.

'''
edited=[]
for name,addition,marker in [
    ('snake9_research.tex',main_add,'\\section{Construction experiments and their scope}'),
    ('snake9_frontier_explanation.tex',short_add,'\\textbf{7. What is proved, and what remains.}')]:
    path=D/name;mirror=R/'paper'/name
    assert path.read_bytes()==mirror.read_bytes()
    before=path.read_text(encoding='utf-8');assert '\\label{sec:block193}' not in before and '\\paragraph{Larger contiguous replacements.}' not in before
    assert before.count(marker)==1
    after=before.replace(marker,addition+marker,1)
    if name=='snake9_research.tex':
        bib=rf'''\bibitem{{block193archive}}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{{Contiguous replacements and closure of the saved snake bank}}. Research record 193, 12 November 2026. Complete and partial block enumerations, shorter-path regrowth, blocker spans and proof receipts:
\url{{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/193-block-reroutings}}.

'''
        after=after.replace('\\end{thebibliography}',bib+'\\end{thebibliography}',1)
    else:
        after=after.replace('Research state after round 192','Research state after round 193')
        after=after.replace('research records 175--192','research records 175--193')
        after=after.replace('Round 192 adds endpoint corrections','Round 193 adds the contiguous-replacement criterion and the general closure argument, with the finite census described above. Round 192 adds endpoint corrections')
    assert before.split('\\begin{document}')[0].replace('round 192','round 193')==after.split('\\begin{document}')[0]
    (H/'data'/(name+'.before.txt')).write_text(before,encoding='utf-8')
    path.write_text(after,encoding='utf-8',newline='\n');mirror.write_bytes(path.read_bytes())
    edited.append(dict(path=str(path),mirror=str(mirror),sha256=sha(path)))
(H/'data/manuscript-edits.json').write_text(json.dumps(edited,indent=2)+'\n')

status=f'''# Round 193 complete; goal active

The explicit resumption supersedes the preceding pause. Read milestones/193-block-reroutings/MATHEMATICAL_NOTE.md and data/completion.json.

All length-preserving contiguous replacements of 2--{K} edges over all 131 saved 191-edge snakes were enumerated. There are {total} valid moves, counting repeated outcomes; every result belongs to an existing bank class and no two-crossing positions change. One-edge blocks have no alternative. Since all bank endpoints are blocked, any finite sequence of these moves cannot unlock endpoint extension. This conclusion has a native closure premise; Lean checks only the general finite-chain implication and the sufficient unchanged-length replacement criterion.

All two-edge shortenings inside 4--24-edge blocks yield 231 symmetry classes of 189-edge paths. Complete endpoint growth finds 220 with no extension and 11 with maximum one added edge. No shorter state recovers 191 by endpoint growth alone. Do not confuse these 231 shorter classes with new 191-edge classes.

The larger sweep was {large['status']}; complete all-bank coverage ends at {K}. The partial row is in data/regions25-36.json. Do not claim full exclusion beyond the completed range. No longer snake or global numerical bound was obtained.

Two Lean modules pass, five dependency reports. EndpointBlockers193 proves that old blockers of a proposed extension must lie in the changed interior; their first/last indices r,s force block length at least s-r+2. The 2358 candidate blocker lists are saved. Numerical enumeration completeness remains outside Lean.

Next: search larger blocks targeted to a specified extension vertex, requiring all its old blockers to be removed and all replacement vertices to avoid the new endpoint's forbidden contacts. Alternatively reroute the 189-edge shortened states before endpoint regrowth. Neither has been attempted here. Do not repeat the completed unchanged-length scans.

The dimensional route remains: the displayed optimal 26-edge Q6 middle lifts to at most 48 in its fixed-middle problem, while the shorter 24-edge middle supports 50. The fixed 50-edge Q7 middle has range 89--97; the fixed 98-edge Q8 middle targeting 192 is unresolved. Fixed 95-to-97 middle replacements need at least 8 omissions computationally; the whole 191-to-192 model needs at least 5 omissions/6 additions. These have different scopes.

Round 192's concrete square-substitution plus extension exclusion for normalized bank25 remains Lean-checked. Its full 131-bank census is native. The 147 rooted closures do not enumerate all simultaneous subsets.

Contributor branch at aeab10ecbab6480a11f927e590b664bd7f0b4f5f reports 2639/3118 production modules and 746/748 replay migrations; fetched diff saved, not merged or independently rebuilt. Archived 235 independent rebuild remains pending; 233/234 conditional; round 187 coverage 93/98 batches and 11904/12424 clauses; critical contradiction and actual-snake transfer pending. Whole-source review next at 200.

Preserve unrelated .gitignore and milestones/50-three-count-return/excess-screen/data/critical-family.json modifications. Editor originals are the two existing D:/Codex/2026-10-13/new-chat/outputs TeX files, mirrored in E:/Snake-in-a-box/paper. Authors and hyperlink settings preserved. Keep one heavy worker and the existing memory/time guards. All research sessions are terminal at publication.
'''
(R/'handoff/CURRENT_STATUS.md').write_text(status,encoding='utf-8')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Continue the active construction goal from round193. Inspect current repository and remote state before proceeding.\n\n'+status,encoding='utf-8')
readme=R/'README.md';old=readme.read_text(encoding='utf-8')
assert old.startswith('# Current result after round 192')
readme.write_text(f'''# Current result after round 193

The 131 saved 191-edge snakes are computationally closed under all length-preserving contiguous replacements of at most {K} edges. Thus repeating these moves cannot unlock an endpoint extension. Lean checks the general closure argument and the sufficient replacement criterion; the finite bank census remains native. No longer snake or improved global numerical bound was found.

All two-edge shortenings inside 4--24-edge blocks produce 231 shorter symmetry classes. Of these, 220 allow no endpoint addition and 11 allow only one. Rerouting shorter states before regrowth and targeted larger replacements remain open.

Read [round193](milestones/193-block-reroutings/README.md), [the argument](milestones/193-block-reroutings/MATHEMATICAL_NOTE.md), [handoff](handoff/CURRENT_STATUS.md), [paper](paper/snake9_research.tex), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8')
print(json.dumps(dict(complete_through=K,moves=total,partial=partial,proofs=proofs),indent=2))
