"""Resolve the three-count sum and retain exact local controls."""
from pathlib import Path
import importlib.util,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('baseprobe',ROOT/'milestones/40-intervening-counts/scripts/probe.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE;p.DIRS=[0,1,2,3,4,0]
if __name__=='__main__':
 for cap in [12,13]:p.solve(f'triple-sum-{cap}',[21]*5,seconds=45,joint=([1,4,5],cap))
 p.solve('three-fours',[4,21,21,4,4],seconds=8)
