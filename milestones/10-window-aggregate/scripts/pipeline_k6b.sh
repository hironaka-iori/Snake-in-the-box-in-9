#!/bin/bash
cd "$(dirname "$0")"; D=../data
python3 minimize_fast.py --L 7 --k 6 --K 5 --radius 3 --avoid $D/avoid_k6.json --tag _cheap > $D/minimize_L7k6_cheap.log 2>&1 || exit 1
python3 certify_direction.py --set $D/minimal_L7_k6_K5_r3_cheap.json --workers 4 --out $D/direction_certificates_k6.json > $D/certify_direction_k6b.log 2>&1 || exit 1
python3 refine_fast.py --L 7 --k 6 --K 5 --radius 3 --index $D/direction_certificates_k6.json --out $D/direction_bound_L7_k6.json > $D/direction_bound_L7_k6.log 2>&1 || exit 1
echo PIPELINE_B_DONE
