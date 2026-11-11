from pathlib import Path
import collections,hashlib,json,sys
R=Path('E:/Snake-in-a-box');H=R/'milestones/191-coloured-replacements';D=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
sys.path.insert(0,str(R/'work/solver_packages'));import ortools
sys.path.insert(0,str(H/'scripts'));from native_resources import snapshot
rows=json.loads((R/'milestones/189-middle-replacements/data/replacement-contexts.json').read_text())['rows']
colours=collections.Counter(tuple(sum(v.bit_count()%2==i for v in row['allowed']) for i in range(2)) for row in rows if row['middle_edges']==95)
assert colours=={(81,81):84}
old=json.loads((R/'milestones/188-dimensional-constructions/data/lift7to8-fixed50-allow-singletons.json').read_text());new=json.loads((H/'data/optimal-middle-7-target0.json').read_text());assert old['middle']==new['middle'] and old['status']=='INFEASIBLE' and old['singleton_outer_paths_allowed']
pins=[R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json',R/'milestones/188-dimensional-constructions/data/lift7to8-fixed50-allow-singletons.json',R/'milestones/189-middle-replacements/data/replacement-contexts.json']
(H/'data/input-audit.json').write_text(json.dumps({'ortools_version':ortools.__version__,'python_version':sys.version,'sources':{str(p):sha(p) for p in pins},'current_script_sha256':{p.name:sha(p) for p in (H/'scripts').glob('*.py')},'common95_allowed_colour_counts':[{'counts':list(k),'contexts':v} for k,v in colours.items()],'fixed50_same_middle_as_inherited_exclusion':True,'native_resource_snapshot_after_research':snapshot()},indent=2)+'\n')
(H/'MATHEMATICAL_NOTE.md').write_bytes((D/'round191_note.md').read_bytes())
(H/'README.md').write_text('''# Round 191: attachment balance and dimensional lifts

The research round is complete. Pause after publication, as requested.

The displayed optimal26-edge Q6 middle gives a maximum48-edge two-crossing lift, confirmed by complete native enumeration; the known50-edge lift uses a shorter24-edge middle. This supports optimizing compatible components together.

The common95-edge path now requires at least8 omissions and10 additions for a fixed-port97-edge replacement according to the new solver exclusions. The corresponding Lean contradiction certificates are pending. Two accepted Lean modules check attachment-count and alternating-colour arguments. No Q9 record or global bound changes.

Read [the mathematical note](MATHEMATICAL_NOTE.md), [completion record](data/completion.json), and [handoff](../../handoff/CURRENT_STATUS.md). Models and numerical outcomes are in data/, accepted sources in lean/, proof objects in build/, and accepted/failed proof receipts in logs/.
''',encoding='utf-8',newline='\n')
handoff=(D/'round191_handoff.md').read_text();(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n');(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Research pauses after round191 publication. Resume only upon a new user instruction.\n\n'+handoff,encoding='utf-8',newline='\n')
p=R/'README.md';old=p.read_text();assert not old.startswith('# Current result after round 191')
p.write_text('''# Current result after round 191

The round is complete; research pauses after publication. A fixed optimal26-edge Q6 middle lifts to at most48 edges, while a shorter24-edge middle supports the known50-edge construction. The48 result has both solver and complete native enumeration evidence. This identifies compatibility of the components as the next construction focus.

For the common95-edge path with fixed endpoints, at most7 omissions is computationally excluded, so a97-edge replacement needs at least8 omissions/10 additions. Lean checks finite attachment balance and alternating-colour counts; the numerical exclusions have no Lean contradiction certificate. No longer Q9 snake or new global bound was obtained.

Read [round191](milestones/191-coloured-replacements/README.md), [the argument](milestones/191-coloured-replacements/MATHEMATICAL_NOTE.md), [handoff](handoff/CURRENT_STATUS.md), [paper](paper/snake9_research.tex), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
(H/'scripts/save_notes.py').write_bytes(Path(__file__).read_bytes())
print('SAVED notes, handoff, input audit and README')
