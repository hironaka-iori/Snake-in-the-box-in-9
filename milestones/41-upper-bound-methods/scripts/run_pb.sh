#!/bin/bash
for d in '[0,1,2,3,4,0,1,5]' '[0,1,2,3,4,1,2,5]' '[0,1,2,3,4,5,2,4]'; do
  timeout 1000 python3 pb_share.py "$d" 60 900 2>/dev/null >> ../data/pb_share60.jsonl
done
