# probe.sh DIR NAME CNF BUDGET : cadical 2.1.3 --unsat, LRAT to file, -t BUDGET (proof file kept)
d=$1; n=$2; f=$3; t=$4
python3 /home/user/b229/meas.py "solve_$n" $d/timing.jsonl -- sh -c "cadical --unsat --lrat --binary=false -t $t $f $d/probe/$n.lrat > $d/probe/$n.log 2>&1"
st=$(grep '^s ' $d/probe/$n.log | head -1); [ -z "$st" ] && st="s UNKNOWN"
echo "$n $st $(du -m $d/probe/$n.lrat | cut -f1)MB-proof"
