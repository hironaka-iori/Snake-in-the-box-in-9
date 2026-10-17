"""Instantiate generic family proofs for an untrusted recorded compact core.

Every geometry fact and descriptor/numbered-clause equality is rechecked by
Lean's kernel. Generated modules assert no geometric exclusion without the
separate Boolean refutation and subsequent arbitrary-window normalization.
"""
import itertools,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
HERE=ROOT/'work/window244';OUT=HERE/'generated'
def lst(xs):return '['+', '.join(map(str,xs))+']'
def litlist(xs):return '['+', '.join(f'({abs(x)}, {str(x>0).lower()})' for x in xs)+']'

def emit(shape,model_path=None,core_path=None,prefix=None):
    base=ROOT/f'milestones/07-window-223/data/window_223_{shape}_compact'
    model_path=pathlib.Path(model_path) if model_path else base.with_suffix('.json')
    core_path=pathlib.Path(core_path) if core_path else pathlib.Path(str(base)+'_core.json')
    data=json.loads(model_path.read_text());core=json.loads(core_path.read_text())
    assert data['compact'] and data['radius']>=2 and len(data['alpha_target'])==3 and all(k>=1 for k in data['alpha_target'])
    expected_window={'repeated':[0,1,3,7,6],'distinct':[0,1,3,7,15]}[shape]
    assert data['window']==expected_window
    prefix=prefix or 'W223'+shape.title();ns=prefix+'Geometry';variables=data['variables'];window=data['window'];centers=window[1:4]
    endverts=[int(n[3:]) for n in variables if n.startswith('end')]
    pairs={};corners={};directions={}
    for i,c in enumerate(centers,1):
        used=[(c^window[i-1]).bit_length()-1,(c^window[i+1]).bit_length()-1]
        directions[c]=used
        pairs[c]=[(a,b) for a,b in itertools.combinations(range(9),2) if a not in used and b not in used]
        corners[c]=[c^(1<<a)^(1<<b) for a,b in pairs[c]]
    modules=[]
    head=f'namespace {ns}\nopen Snake9 Snake9.Window244 Snake9.SquareIncidence\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnoncomputable section\n'
    tail=f'end\nend {ns}\n'
    def write(name,text):
        p=OUT/(name+'.lean')
        if not p.exists() or p.read_text(encoding='utf-8')!=text:p.write_text(text,encoding='utf-8')
        modules.append(name)
    s='import WindowClauses\nimport WindowAlpha\nimport '+prefix+'Constraints\n'+head
    s+='def window : List Vertex := '+lst(window)+'\n'
    s+='def endpoints : List Vertex := '+lst(endverts)+'\n'
    for c in centers:
        s+=f'def corners{c} : List Vertex := {lst(corners[c])}\n'
        s+=f'def pairs{c} : List AxisPair := ['+', '.join(f'⟨({a},{b}),by decide⟩' for a,b in pairs[c])+']\n'
    atoms=['.constant false']*(max(variables.values())+1)
    for name,ident in variables.items():
        if name.startswith('x'):a=f'.selected {name[1:]}'
        elif name.startswith('end'):a=f'.endpoint {name[3:]}'
        elif name.startswith('prefix'):
            i,j=map(int,name[6:].split('_'));a=f'.endpointThreshold (endpoints.take {i+1}) {j}'
        elif name.startswith('missing'):
            c,i,j=map(int,name[7:].split('_'));a=f'.missingThreshold (corners{c}.take {i}) {j}'
        else:raise ValueError(name)
        atoms[ident]=a
    s+='def descriptors : Array Atom := #[\n'+',\n'.join(atoms)+']\n'
    s+='def decode (i : Nat) : Atom := descriptors[i]?.getD (.constant false)\n'
    s+='structure Context {m : Nat} (p : Snake m) : Prop where\n  nontrivial : 0 < m\n  selected : ∀ v ∈ window, InPath p v\n'
    for c,k in zip(centers,data['alpha_target']):s+=f'  missing{c} : missingCount p corners{c} = {k}\n'
    s+='theorem context_of_alpha {m : Nat} (p : Snake m) (hm : 0 < m)\n  (hw : ∀ v ∈ window, InPath p v)\n'
    for c,k in zip(centers,data['alpha_target']):s+=f'  (i{c} : Fin (m+1)) (hv{c} : p.vertex i{c} = {c}) (ha{c} : localAlpha p i{c} = {k})\n'
    s+='  : Context p where\n  nontrivial := hm\n  selected := hw\n'
    for idx,c in enumerate(centers,1):
        a,b=directions[c]
        s+=f'  missing{c} := by\n'
        s+=f'    have hleft : InPath p (flip {a} (p.vertex i{c})) := by\n      rw [hv{c}]\n      exact hw {window[idx-1]} (by decide)\n'
        s+=f'    have hright : InPath p (flip {b} (p.vertex i{c})) := by\n      rw [hv{c}]\n      exact hw {window[idx+1]} (by decide)\n'
        s+=f'    have hh := localAlpha_corner_list p i{c} {a} {b} hleft hright (by decide) pairs{c} (by decide) (by decide)\n'
        s+=f'    have he : pairs{c}.map (fun ab => flip ab.val.2 (flip ab.val.1 (p.vertex i{c}))) = corners{c} := by\n      rw [hv{c}]\n      decide\n'
        s+=f'    rw [he] at hh\n    exact hh.symm.trans ha{c}\n'
    s+='#print axioms context_of_alpha\n'
    write(ns+'Data',s+tail)
    simp='LocalRup.clause,LocalRup.value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false'

    def simplified(c):
        if any(x is True for x in c):return None
        c=list(dict.fromkeys(x for x in c if x is not False))
        if any(-x in c for x in c):return None
        return c
    def neg(x):return not x if isinstance(x,bool) else -x
    def countvar(c,i,j):
        if j==0:return True
        if i==0:return False
        return variables[f'missing{c}_{i}_{j}']
    def family(clause,reason):
        tag=reason[0];extra=''
        if tag=='window_selected':return f'selected_clause p {reason[1]} (h.selected _ (by decide))',extra
        if tag=='degree_at_most_two':
            v,a,b,c=[-x-1 for x in clause]
            return f'degree_family p {v} {a} {b} {c} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',extra
        if tag=='interior_positive_degree':
            v=reason[1];neighbours=[x-1 for x in clause[1:]]
            return f'positive_degree_family p h.nontrivial {v} {lst(neighbours)} (by decide)',extra
        if tag=='endpoint_selected':return f'endpoint_selected_family p {reason[1]}',extra
        if tag=='degree_one_implies_endpoint':
            v=reason[1];others=[x-1 for x in clause[2:]];excluded=next(v^(1<<k) for k in range(9) if v^(1<<k) not in others)
            return f'degree_one_endpoint_family p {v} {excluded} {lst(others)} (by decide)',extra
        if tag=='endpoint_degree_at_most_one':return f'endpoint_degree_family p {reason[1]} {-clause[1]-1} {-clause[2]-1} (by decide) (by decide) (by decide)',extra
        if tag.startswith('counter_'):
            i=reason[1];v=endverts[i];projection={'counter_current':'.1','counter_carry_one':'.2.1','counter_carry_two':'.2.2.1','counter_increment':'.2.2.2.1','counter_overflow':'.2.2.2.2'}[tag]
            return f'(endpoint_counter_family p (endpoints.take {i}) {v} (by decide)){projection}',extra
        if tag=='missing_counter':
            c,i,j=reason[1:];v=corners[c][i-1];s=variables[f'missing{c}_{i}_{j}'];a=countvar(c,i-1,j);b=-(v+1);cc=countvar(c,i-1,j-1)
            options=[[neg(a),s],[neg(b),neg(cc),s],[-s,a,b],[-s,a,cc]]
            which=next(k for k,o in enumerate(options) if simplified(o)==clause)
            projection=['.1','.2.1','.2.2.1','.2.2.2'][which]
            return f'(missing_counter_family p (corners{c}.take {i-1}) {v} {j} (by decide)){projection}',extra
        if tag in ['missing_exact_lower','missing_exact_upper']:
            c,k=reason[1:];projection='.1' if tag.endswith('lower') else '.2'
            return f'(missing_exact_family p corners{c} {k} h.missing{c}){projection}',extra
        if tag=='cycle':
            vs=reason[1]
            extra=f'    have hd : ∀ v ∈ ({lst(vs)} : List Vertex), ∃ a ∈ ({lst(vs)} : List Vertex), ∃ b ∈ ({lst(vs)} : List Vertex), a ≠ b ∧ Adj v a ∧ Adj v b := by\n'
            extra+='      intro v hv\n      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv\n      rcases hv with '+' | '.join('rfl' for _ in vs)+'\n'
            for v in vs:
                a,b=[w for w in vs if (v^w).bit_count()==1]
                extra+=f'      · exact ⟨{a},by decide,{b},by decide,by decide,by decide,by decide⟩\n'
            return f'cycle_family p {lst(vs)} (by decide) hd',extra
        raise ValueError(reason)
    for block,start in enumerate(range(0,len(core['clauses']),32)):
        split=shape=='distinct' or block>=8
        parts=[]
        if split:
            for offset in range(start,min(start+32,len(core['clauses'])),8):
                s='import '+modules[0]+'\n'+head
                for i in range(offset,min(offset+8,start+32,len(core['clauses']))):
                    clause=core['clauses'][i];proof,extra=family(clause,core['reasons'][i]);raw=litlist(clause)
                    s+=f'theorem clause{i+1} {{m : Nat}} (p : Snake m) (h : Context p) : LocalRup.clause (assignment p decode) {raw} = true := by\n'
                    s+=extra+f'    have hs := {proof}\n    refine numbered_of_family p decode {raw} _ ?_ hs\n    decide\n'
                    s+=f'#print axioms clause{i+1}\n'
                name=ns+f'Block{block:03d}Part{(offset-start)//8}'
                write(name,s+tail);parts.append(name)
        s=''.join('import '+n+'\n' for n in (parts or [modules[0]]))+head
        s+=f'theorem block{block} {{m : Nat}} (p : Snake m) (h : Context p) : {prefix}.Block{block} (assignment p decode) where\n'
        for i in range(start,min(start+32,len(core['clauses']))):
            clause=core['clauses'][i];proof,extra=family(clause,core['reasons'][i]);raw=litlist(clause)
            if split:
                s+=f'  clause{i+1} := by simpa only [{simp}] using clause{i+1} p h\n'
                continue
            s+=f'  clause{i+1} := by\n'+extra+f'    have hs := {proof}\n'
            s+=f'    have hh : LocalRup.clause (assignment p decode) {raw} = true := by\n      refine numbered_of_family p decode {raw} _ ?_ hs\n      decide\n'
            s+=f'    simpa only [{simp}] using hh\n'
        s+=f'#print axioms block{block}\n';write(ns+f'Block{block:03d}',s+tail)
    s=''.join('import '+name+'\n' for name in modules[1:])+head
    s+=f'theorem constraints {{m : Nat}} (p : Snake m) (h : Context p) : {prefix}.Constraints (assignment p decode) where\n'
    for b in range((len(core['clauses'])+31)//32):s+=f'  block{b} := block{b} p h\n'
    s+='#print axioms constraints\n';write(ns,s+tail)
    return modules

if __name__=='__main__':
    for shape in ['repeated','distinct']:print(shape,len(emit(shape)))
