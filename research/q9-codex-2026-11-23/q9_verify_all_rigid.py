"""Check the union of each initial tree and its open-leaf continuations against identical prefix assignments."""
import json
from collections import Counter
from pathlib import Path
from q9_resume_rigid_leaves import replay,open_nodes,D,OUT
from q9_check_rigid_tables import check
from q9_rigid_facet_ports import word_path
from q9_verify_record_donor_optima import verify as old_verify
def main():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    original=old_verify()
    done={i for i,obj in original.items() if obj["conditional_optimum"]==191};assert len(done)==5
    output={};incomplete=[];total=Counter()
    for i,w in enumerate(bank):
        a=word_path(w);assert len(set(a))==len(a)
        if any(x not in a and all((x^y).bit_count()!=1 for y in a[1:-1]) for x in range(256)):continue
        if str(i) in done:
            output[i]=dict(upper_edges=191,witness_edges=191,previous=True);continue
        assert len(a)==97 and a[0]==0
        needed={((a[0],),0),((a[-1],),0),((a[0],a[-1]),0),((a[0],a[-1]),1)}
        stats=Counter();missing=[]
        for line in (D/f"donor{i}.jsonl").read_text().splitlines():
            r=json.loads(line);ports=tuple(r["ports"]);m=r["majority"];needed.remove((ports,m))
            assert r["word"]==w
            name="d%d_m%d_p%s"%(i,m,"-".join(map(str,ports)));tag=D/name
            states,_=check(r,tag,[]);stats["table_options"]+=states
            def visit(tree,pins,level,label):
                if not tree.is_file():
                    missing.append(label);return
                ass=tree.with_suffix(".pins") if level else None
                if ass is not None:
                    assert len(set(v for v,b in pins))==len(pins)
                    assert [tuple(map(int,l.split())) for l in ass.read_text().splitlines()]==pins
                counts=replay(tag,tree,ass);assert counts["witnesses"]==0
                stats["trees"]+=1
                for k in ("nodes","splits","bound_leaves","invalid_full"):stats[k]+=counts[k]
                if not counts["open"]:return
                children=list(open_nodes(tree));assert len(children)==counts["open"]
                for j,sub in enumerate(children):
                    assert sub
                    childname=label+("_leaf" if level==0 else "_")+str(j)
                    childtree=(OUT if level==0 else OUT/"next")/(childname+".tree")
                    visit(childtree,pins+sub,level+1,childname)
            visit(tag.with_suffix(".tree"),[],0,name)
        assert not needed
        output[i]=dict(upper_edges=None if missing else 191,missing=missing,stats=dict(stats));total+=stats
        incomplete.extend(missing)
    assert len(output)==41
    print(json.dumps(dict(catalogue=len(bank),rigid=len(output),closed=sum(r["upper_edges"]==191 for r in output.values()),
                          missing=incomplete,stats_new36=dict(total),records=output),indent=2))
if __name__=="__main__":main()
