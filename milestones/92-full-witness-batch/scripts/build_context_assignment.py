"""Materialize the count-independent selector and exact saved class/root payload."""
from pathlib import Path
import ast,gzip,hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
REPO=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
planpath=HERE/'data/context-assignment-plan.json'
assert sha(planpath)=='832d2c1761c16281425b3a6a86842de5e2b41d3f1626751eea6460b99f27aab7'
plan=json.loads(planpath.read_text())
assert plan['status']=='PASS_BOUNDED_CONTEXT_ASSIGNMENT_PLAN'
for rel,pin in plan['input_sha256'].items():assert sha(REPO/rel)==pin,rel
context=HERE/'lean/BatchContextData.lean'
assert sha(context)=='9bc39b24e6473247d29bbf46d8759cdeb86aae1250533be40dcb8bc87e393394'
source=context.read_text()
assert 'open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88' not in source
keys=ast.literal_eval(re.search(r'def recordedClassKeyLists[^=]*:=\s*(\[.*?\])\s*\n\s*def recordedClassKeys',source,re.S).group(1))
roots=ast.literal_eval(re.search(r'def recordedClassRoots[^=]*:=\s*(\[[^\n]*\])',source).group(1))
payloadpath=REPO/'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz'
payload=json.loads(gzip.decompress(payloadpath.read_bytes()))
blocks=payload['blocks'];savedroots=payload['roots']
assert len(blocks)==791 and len(savedroots)==127
assert len(dict(blocks))==791
assert roots==savedroots==plan['roots_by_class']
assert keys==[[tuple(p) for p in pairs] for cls,pairs in plan['per_class_context_keys']]
mapping={75*di+q:cls for cls,pairs in enumerate(keys) for di,q in pairs}
assert mapping==dict(blocks)
defaults=plan['default_class_by_direction'];overrides=plan['history_overrides']
assert len(defaults)==505
assert [(x['direction'],x['history'],x['class_id']) for x in overrides]==[(177,43,85),(177,70,85),(180,68,89)]
def natlist(xs):return '['+','.join(map(str,xs))+']'
def pairlist(xs):return '['+','.join(f'({a},{b})' for a,b in xs)+']'
override_source=''
for item in overrides:
    override_source+=f"  if di = {item['direction']} ∧ q = {item['history']} then {item['class_id']} else\n"
text='''import BatchContextData

set_option maxRecDepth 100000

namespace Snake9.Batch92

def defaultClasses : List Nat := '''+natlist(defaults)+'''

def chosenClass (di q : Nat) : Nat :=
'''+override_source+'''  defaultClasses.getD di 0

/-- Exact ordered block/class pairs from the saved milestone87 payload. -/
def savedBlockClasses : List (Nat × Nat) := '''+pairlist(blocks)+'''

def savedRoots : List Nat := '''+natlist(savedroots)+'''

/-- Missing blocks have no class; class zero is not used as a missing default. -/
def savedBlockClass (block : Nat) : Option Nat :=
  (savedBlockClasses.find? fun item => item.1 == block).map Prod.snd

def savedRootForBlock (block : Nat) : Option Nat :=
  (savedBlockClass block).bind fun cls => savedRoots[cls]?

end Snake9.Batch92
'''
out=HERE/'lean/ContextAssignmentData.lean';out.write_text(text,encoding='utf-8')
record=dict(status='GENERATED_NOT_LEAN_CHECKED',plan_sha256=sha(planpath),payload_sha256=sha(payloadpath),batch_context_source_sha256=sha(context),source_sha256=sha(out),defaults=505,overrides=3,blocks=791,roots=127,count_codes_enumerated=0,input_sha256=plan['input_sha256'])
(HERE/'data/ContextAssignment-build.json').write_text(json.dumps(record,indent=2)+'\n')
print('ContextAssignmentData generated; 505 defaults, 3 overrides, 791 blocks, 127 roots. No compiler run.')

# This module deliberately imports no prior snake proof environment.
lite='''import Mathlib.Data.List.Range

set_option maxRecDepth 100000

namespace Snake9.ContextLite92

def sourceShapeIds : List Nat := '''+natlist(plan['source_shape_ids'])+'''
def compatibilityIds : List Nat := '''+natlist(plan['recorded_compatible'])+'''
def defaultClasses : List Nat := '''+natlist(defaults)+'''
def recordedClassKeyLists : List (List (Nat × Nat)) := ['''+','.join(pairlist(xs) for xs in keys)+''']
def recordedClassRoots : List Nat := '''+natlist(roots)+'''
def recordedClassKeys (cls : Nat) : List (Nat × Nat) := recordedClassKeyLists.getD cls []
def recordedClassRoot (cls : Nat) : Nat := recordedClassRoots.getD cls 0

def chosenClass (di q : Nat) : Nat :=
'''+override_source+'''  defaultClasses.getD di 0

def savedBlockClasses : List (Nat × Nat) := '''+pairlist(blocks)+'''
def savedRoots : List Nat := '''+natlist(savedroots)+'''
def savedBlockClass (block : Nat) : Option Nat :=
  (savedBlockClasses.find? fun item => item.1 == block).map Prod.snd
def savedRootForBlock (block : Nat) : Option Nat :=
  (savedBlockClass block).bind fun cls => savedRoots[cls]?

def sourceCompatibleB (di q : Nat) : Bool :=
  q == 0 || compatibilityIds.getD q 0 == sourceShapeIds.getD di 0

def Assigned (di q : Nat) : Prop :=
  let cls := chosenClass di q
  cls < 127 ∧ (di,q) ∈ recordedClassKeys cls ∧
    savedBlockClass (75*di+q) = some cls ∧
    savedRootForBlock (75*di+q) = some (recordedClassRoot cls)

instance (di q : Nat) : Decidable (Assigned di q) := by
  unfold Assigned
  infer_instance

def assignmentAt (di q : Nat) : Bool :=
  if sourceCompatibleB di q then decide (Assigned di q) else true

def rowAt (di sid q compatible : Nat) : Bool :=
  if q == 0 || compatible == sid then decide (Assigned di q) else true

/-- Indexed iteration supplies both numeric compatibility values directly.
No per-pair source/history list lookup is evaluated in this finite check. -/
def fastCheck : Bool :=
  sourceShapeIds.zipIdx.all fun source =>
    compatibilityIds.zipIdx.all fun history =>
      rowAt source.2 source.1 history.2 history.1

end Snake9.ContextLite92
'''
liteout=HERE/'lean/ContextAssignmentLiteData.lean';liteout.write_text(lite,encoding='utf-8')
literecord=dict(status='GENERATED_NOT_LEAN_CHECKED',source_sha256=sha(liteout),original_build_sha256=sha(HERE/'data/ContextAssignment-build.json'),plan_sha256=sha(planpath),payload_sha256=sha(payloadpath),batch_context_source_sha256=sha(context),direction_entries=505,history_entries=75,positions=37875,count_codes_enumerated=0,scope='Literal-only assignment predicates with directly indexed source/history rows; equality to the original predicates must be proved separately.')
(HERE/'data/ContextAssignmentLite-build.json').write_text(json.dumps(literecord,indent=2)+'\n')
print('ContextAssignmentLiteData generated with indexed source/history rows. No compiler run.')

# Each bounded Boolean computation is a separate kernel-checked module.
chunks=[]
for index,start in enumerate(range(0,505,20)):
    count=min(20,505-start)
    name=f'ContextAssignmentLiteChunk{index:02}'
    chunktext=f'''import ContextAssignmentLiteCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.ContextLite92
theorem chunk_{index:02} : chunkCheck {start} {count} = true := by decide +kernel
#print axioms chunk_{index:02}
end Snake9.ContextLite92
'''
    chunkpath=HERE/'lean'/f'{name}.lean';chunkpath.write_text(chunktext,encoding='utf-8')
    accepted=sum(1 for di in range(start,start+count) for q in range(75)
        if q==0 or plan['recorded_compatible'][q]==plan['source_shape_ids'][di])
    chunks.append(dict(module=name,index=index,start=start,count=count,positions=count*75,
        compatible_contexts=accepted,source_sha256=sha(chunkpath)))
assembly='\n'.join('import '+c['module'] for c in chunks)+'''

namespace Snake9.ContextLite92
theorem prefix_0 : prefixCheck 0 = true := rfl
'''
for c in chunks:
    start=c['start'];count=c['count'];end=start+count;index=c['index']
    assembly+=f'''
theorem prefix_{end} : prefixCheck {end} = true := by
  calc
    prefixCheck {end} = (prefixCheck {start} && chunkCheck {start} {count}) :=
      prefix_add {start} {count}
    _ = true := by rw [prefix_{start},chunk_{index:02}]; rfl
'''
assembly+='''
theorem fast_checked : fastCheck = true := by
  rw [← prefix_full]
  exact prefix_505

theorem assignmentAt_true (di q : Nat) (hd : di < 505) (hq : q < 75) :
    assignmentAt di q = true := assignmentAt_of_fast fast_checked di q hd hq

#print axioms fast_checked
#print axioms assignmentAt_true
end Snake9.ContextLite92
'''
assemblypath=HERE/'lean/ContextAssignmentLiteChecks.lean'
assemblypath.write_text(assembly,encoding='utf-8')
chunkrecord=dict(status='GENERATED_NOT_LEAN_CHECKED',chunks=chunks,
    assembly_source_sha256=sha(assemblypath),lite_build_sha256=sha(HERE/'data/ContextAssignmentLite-build.json'),
    pilot='ContextAssignmentLiteChunk17',scope='Disjoint consecutive direction ranges cover exactly 0 through 504. Each chunk checks all 75 histories; the assembly uses a generic prefix concatenation identity.')
(HERE/'data/ContextAssignmentLite-chunks.json').write_text(json.dumps(chunkrecord,indent=2)+'\n')
print('Generated 26 bounded direction chunks and a non-enumerating concatenation assembly. Pilot: chunk17.')
