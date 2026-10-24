"""Reuse the checked ordinary-core generator for two three-position exclusions."""
from pathlib import Path
import importlib.util,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
path=ROOT/'milestones/38-four-position-obstruction/scripts/certify.py'
spec=importlib.util.spec_from_file_location('ordinary_certify',path)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
module.HERE=HERE
BaseEncoding=module.TaggedEncoding
for d in ['data','logs','lean','certificates','build']:(HERE/d).mkdir(exist_ok=True)
for i,caps in [(401,[3,21,4,21,21,21,3]),(402,[3,21,21,21,21,4,3])]:
 source='only-3' if i==401 else 'sixth-boundary'
 cuts=json.loads((HERE/f'data/{source}.json').read_text())['cycle_cuts']
 assert cuts and all(module.gen.is_cycle_set(c) for c in cuts)
 class CutEncoding(BaseEncoding):
  def __init__(self,*args,**kwargs):
   super().__init__(*args,**kwargs)
   for cc in cuts:
    assert set(cc)<=set(self.ball)
    self.add([-self.var[v] for v in cc],('cut',))
 module.TaggedEncoding=CutEncoding
 module.build(i,dict(dirs=[0,1,2,3,4,2,0,3],bounds=[(0,k) for k in caps]))
 meta=HERE/f'data/cycle{i}.json';row=json.loads(meta.read_text())
 row.update(cycle_cut_source=source,cycle_cuts=cuts)
 meta.write_text(json.dumps(row,indent=2)+'\n')
