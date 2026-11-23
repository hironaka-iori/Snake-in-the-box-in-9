"""Recheck previously undecided section projections; validate reconstructed Q9 witnesses."""
import gzip
import json
import sys
from search_q9_unordered_projection import project,solve

def main():
    budget=int(sys.argv[1]);inputs=sys.argv[2:]
    with gzip.open('q9_high_section_surgery_20261120/sections.gz','rt') as stream:
        sources=[list(map(int,line.split()))[3:] for line in stream]
    for f in inputs:
        for i,d,status,_ in map(json.loads,open(f)):
            if status!='UNKNOWN':continue
            state,w=solve(project(sources[i],d),192,budget,True)
            print(json.dumps([i,d,state,w],separators=(',',':')),flush=True)
            if w:return
if __name__=='__main__':main()
