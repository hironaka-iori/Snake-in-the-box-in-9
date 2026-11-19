#!/bin/bash
out=logs/predB
bin/wl 8 98 2400 1 > $out/wl8.txt 2> $out/wl8.err
bin/wl 9 191 2400 1 > $out/wl9.txt 2> $out/wl9.err
echo DONE > $out/DONE
