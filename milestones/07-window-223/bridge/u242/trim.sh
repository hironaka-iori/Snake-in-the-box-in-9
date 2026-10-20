#!/bin/bash
cd /tmp/claude-0/-home-user-Snake-in-the-box-in-9/f9d17ed0-2ed6-5b33-9fe8-21ba7f2d6530/scratchpad/u242/data
for t in $@; do s=$(date +%s); nice -n 10 /home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/.build/drat-trim $t.cnf $t.drup -L $t.lrat -t 3000 > $t.trim.log 2>&1; echo "$t $(grep -c . $t.lrat) lines $(( $(date +%s)-s )) s $(grep '^s ' $t.trim.log)"; done
