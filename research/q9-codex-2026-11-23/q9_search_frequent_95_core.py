"""Search the free upper Q8 over the frequent 95-edge core, allowing all its possible crossings."""
from q9_one_hole_port_prices import *
from q9_rigid_ports_tree import export
import subprocess
def run():
    bank=Path("q8_catalogue_96_98.words").read_text().split()
    arm=word_path(bank[472])
    low=set(arm[1:])
    fixed=set(arm[2:-1])
    assert {x for x in set(range(256))-low if not neighbors[x]&fixed}=={0,33}
    assert neighbors[0]&low==neighbors[33]&low=={1}
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
    dest=Path("q9_frequent_95_core");dest.mkdir(exist_ok=True)
    rows=[]
    for extra,ports,ends,delta,F in layouts(arm,0):
        if extra:continue
        assert F==low
        majority=(1-(sum(1-2*(v.bit_count()%2) for v in F)-delta))//2
        tag=dest/("p"+"-".join(map(str,ports))+"_m"+str(majority))
        if tag.with_suffix(".json").exists():
            r=json.loads(tag.with_suffix(".json").read_text())
        else:
            const,scale,tables,cert=build(arm,ports,low,ends,delta,axes[:int(sys.argv[1])])
            num=len(low)*scale+const+sum(t[0][2] for _,t in tables)
            assert num==len(low)*scale+integer_bound(cert,low,set(ports),ends,delta)
            r=dict(word=bank[472],lower_vertices=sorted(low),ports=ports,majority=majority,upper_endpoint_counts=ends,upper_delta=delta,total_scaled=num,cert=cert)
            tag.with_suffix(".json").write_text(json.dumps(r,separators=(",",":")))
        export(r,tag.with_suffix(".tables"))
        print(tag,r["total_scaled"]/r["cert"]["scale"],flush=True)
        rows.append((r["total_scaled"],tag))
    for _,tag in sorted(rows):
        rr=subprocess.run(["q9_facet_priced_tree_20261121/tree",str(tag),str(tag.with_suffix(".tree")),"193",sys.argv[2]],capture_output=True,check=True,text=True)
        print(tag,rr.stdout.strip(),flush=True)
        rr=subprocess.run(["q9_facet_priced_tree_20261121/replay",str(tag.with_suffix(".tables")),str(tag.with_suffix(".tree")),"193"],capture_output=True,check=True,text=True)
        print(tag,rr.stdout.strip(),flush=True)
if __name__=="__main__":run()
