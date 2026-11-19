#!/bin/bash
# Wang-Landau density of states, run after predA on the same core.
while [ ! -f logs/predA/DONE ]; do sleep 30; done
out=logs/predB; mkdir -p $out
bin/wl 5 13 120 1 > $out/wl5.txt 2> $out/wl5.err
bin/wl 6 26 900 1 > $out/wl6.txt 2> $out/wl6.err
bin/wl 7 50 1800 1 > $out/wl7.txt 2> $out/wl7.err
bin/wl 8 98 2400 1 > $out/wl8.txt 2> $out/wl8.err
bin/wl 9 191 2400 1 > $out/wl9.txt 2> $out/wl9.err
echo DONE > $out/DONE
