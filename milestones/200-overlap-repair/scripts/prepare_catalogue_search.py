from pathlib import Path
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/coupled_search.py').read_text()
changes={
 "choices=[0,1],":"",
 "placement=R/'milestones/199-parent-diversity/data/all-isometries-published50.json';c=json.loads(placement.read_bytes())['rows'][0]['minimum_examples'][a.case]":"placement=H/'data/low-overlap-maps.json';c=json.loads(placement.read_bytes())['rows'][a.case]",
 "assert all(h(h(v))==v for v in range(128))":"involution=all(h(h(v))==v for v in range(128))",
 "seeds=[p,[h(v) for v in p]];assert len(set(seeds[0])&set(seeds[1]))==2":"seeds=[p,[h(v) for v in p]];assert len(set(seeds[0])&set(seeds[1]))==c['intersection_count']",
 "m.add(omissions[0]<=omissions[1])":"if involution:m.add(omissions[0]<=omissions[1])",
 "Omission-order reduction uses the checked-in-script involution exchanging seeds.":"Omission-order reduction is imposed only when the placing map is an involution; inverse-pair reduction is handled in the catalogue runner."
}
for a,b in changes.items():assert a in s,a;s=s.replace(a,b)
target=H/'scripts/coupled_catalogue.py';assert not target.exists();target.write_text(s,encoding='utf-8',newline='\n');print('PREPARED_CATALOGUE_MODEL')
