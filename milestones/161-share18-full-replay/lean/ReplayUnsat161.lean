import CheckpointConsequence160
import ReplaySteps161_0000
import ReplaySteps161_0001
import ReplaySteps161_0002
import ReplaySteps161_0003
import ReplaySteps161_0004
import ReplaySteps161_0005
import ReplaySteps161_0006
import ReplaySteps161_0007
import ReplaySteps161_0008
import ReplaySteps161_0009
import ReplaySteps161_0010
import ReplaySteps161_0011
import ReplaySteps161_0012
import ReplaySteps161_0013
import ReplaySteps161_0014
import ReplaySteps161_0015
import ReplaySteps161_0016
import ReplaySteps161_0017
import ReplaySteps161_0018
import ReplaySteps161_0019
import ReplaySteps161_0020
import ReplaySteps161_0021
import ReplaySteps161_0022
import ReplaySteps161_0023
import ReplaySteps161_0024
import ReplaySteps161_0025
import ReplaySteps161_0026
import ReplaySteps161_0027
import ReplaySteps161_0028
import ReplaySteps161_0029
import ReplaySteps161_0030
import ReplaySteps161_0031
import ReplaySteps161_0032
import ReplaySteps161_0033
import ReplaySteps161_0034
import ReplaySteps161_0035
import ReplaySteps161_0036
import ReplaySteps161_0037
import ReplaySteps161_0038
import ReplaySteps161_0039
import ReplaySteps161_0040
import ReplaySteps161_0041
import ReplaySteps161_0042
import ReplaySteps161_0043
import ReplaySteps161_0044
import ReplaySteps161_0045
import ReplaySteps161_0046
import ReplaySteps161_0047
import ReplaySteps161_0048
import ReplaySteps161_0049
import ReplaySteps161_0050
import ReplaySteps161_0051
import ReplaySteps161_0052
import ReplaySteps161_0053
import ReplaySteps161_0054
import ReplaySteps161_0055
import ReplaySteps161_0056
import ReplaySteps161_0057
import ReplaySteps161_0058
import ReplaySteps161_0059
import ReplaySteps161_0060
import ReplaySteps161_0061
import ReplaySteps161_0062
import ReplaySteps161_0063
import ReplaySteps161_0064
import ReplaySteps161_0065
import ReplaySteps161_0066
import ReplaySteps161_0067
import ReplaySteps161_0068
import ReplaySteps161_0069
import ReplaySteps161_0070
import ReplaySteps161_0071
import ReplaySteps161_0072
import ReplaySteps161_0073
import ReplaySteps161_0074
import ReplaySteps161_0075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue unsat_of_raw)
theorem unsat : Snake9.LocalWindow.Unsat Snake9.LocalWindow.ShareWindow144.cnf := by
  apply unsat_of_raw
  intro τ h
  have h0 : TreeTrue τ start0 := Snake9.Checkpoint160.afterPrefix_true τ h
  have h32 : TreeTrue τ start32 := steps0 τ h0
  have h64 : TreeTrue τ start64 := steps1 τ h32
  have h96 : TreeTrue τ start96 := steps2 τ h64
  have h128 : TreeTrue τ start128 := steps3 τ h96
  have h160 : TreeTrue τ start160 := steps4 τ h128
  have h192 : TreeTrue τ start192 := steps5 τ h160
  have h224 : TreeTrue τ start224 := steps6 τ h192
  have h256 : TreeTrue τ start256 := steps7 τ h224
  have h288 : TreeTrue τ start288 := steps8 τ h256
  have h320 : TreeTrue τ start320 := steps9 τ h288
  have h352 : TreeTrue τ start352 := steps10 τ h320
  have h384 : TreeTrue τ start384 := steps11 τ h352
  have h416 : TreeTrue τ start416 := steps12 τ h384
  have h448 : TreeTrue τ start448 := steps13 τ h416
  have h480 : TreeTrue τ start480 := steps14 τ h448
  have h512 : TreeTrue τ start512 := steps15 τ h480
  have h544 : TreeTrue τ start544 := steps16 τ h512
  have h576 : TreeTrue τ start576 := steps17 τ h544
  have h608 : TreeTrue τ start608 := steps18 τ h576
  have h640 : TreeTrue τ start640 := steps19 τ h608
  have h672 : TreeTrue τ start672 := steps20 τ h640
  have h704 : TreeTrue τ start704 := steps21 τ h672
  have h736 : TreeTrue τ start736 := steps22 τ h704
  have h768 : TreeTrue τ start768 := steps23 τ h736
  have h800 : TreeTrue τ start800 := steps24 τ h768
  have h832 : TreeTrue τ start832 := steps25 τ h800
  have h864 : TreeTrue τ start864 := steps26 τ h832
  have h896 : TreeTrue τ start896 := steps27 τ h864
  have h928 : TreeTrue τ start928 := steps28 τ h896
  have h960 : TreeTrue τ start960 := steps29 τ h928
  have h992 : TreeTrue τ start992 := steps30 τ h960
  have h1024 : TreeTrue τ start1024 := steps31 τ h992
  have h1056 : TreeTrue τ start1056 := steps32 τ h1024
  have h1088 : TreeTrue τ start1088 := steps33 τ h1056
  have h1120 : TreeTrue τ start1120 := steps34 τ h1088
  have h1152 : TreeTrue τ start1152 := steps35 τ h1120
  have h1184 : TreeTrue τ start1184 := steps36 τ h1152
  have h1216 : TreeTrue τ start1216 := steps37 τ h1184
  have h1248 : TreeTrue τ start1248 := steps38 τ h1216
  have h1280 : TreeTrue τ start1280 := steps39 τ h1248
  have h1312 : TreeTrue τ start1312 := steps40 τ h1280
  have h1344 : TreeTrue τ start1344 := steps41 τ h1312
  have h1376 : TreeTrue τ start1376 := steps42 τ h1344
  have h1408 : TreeTrue τ start1408 := steps43 τ h1376
  have h1440 : TreeTrue τ start1440 := steps44 τ h1408
  have h1472 : TreeTrue τ start1472 := steps45 τ h1440
  have h1504 : TreeTrue τ start1504 := steps46 τ h1472
  have h1536 : TreeTrue τ start1536 := steps47 τ h1504
  have h1568 : TreeTrue τ start1568 := steps48 τ h1536
  have h1600 : TreeTrue τ start1600 := steps49 τ h1568
  have h1632 : TreeTrue τ start1632 := steps50 τ h1600
  have h1664 : TreeTrue τ start1664 := steps51 τ h1632
  have h1696 : TreeTrue τ start1696 := steps52 τ h1664
  have h1728 : TreeTrue τ start1728 := steps53 τ h1696
  have h1760 : TreeTrue τ start1760 := steps54 τ h1728
  have h1792 : TreeTrue τ start1792 := steps55 τ h1760
  have h1824 : TreeTrue τ start1824 := steps56 τ h1792
  have h1856 : TreeTrue τ start1856 := steps57 τ h1824
  have h1888 : TreeTrue τ start1888 := steps58 τ h1856
  have h1920 : TreeTrue τ start1920 := steps59 τ h1888
  have h1952 : TreeTrue τ start1952 := steps60 τ h1920
  have h1984 : TreeTrue τ start1984 := steps61 τ h1952
  have h2016 : TreeTrue τ start2016 := steps62 τ h1984
  have h2048 : TreeTrue τ start2048 := steps63 τ h2016
  have h2080 : TreeTrue τ start2080 := steps64 τ h2048
  have h2112 : TreeTrue τ start2112 := steps65 τ h2080
  have h2144 : TreeTrue τ start2144 := steps66 τ h2112
  have h2176 : TreeTrue τ start2176 := steps67 τ h2144
  have h2208 : TreeTrue τ start2208 := steps68 τ h2176
  have h2240 : TreeTrue τ start2240 := steps69 τ h2208
  have h2272 : TreeTrue τ start2272 := steps70 τ h2240
  have h2304 : TreeTrue τ start2304 := steps71 τ h2272
  have h2336 : TreeTrue τ start2336 := steps72 τ h2304
  have h2368 : TreeTrue τ start2368 := steps73 τ h2336
  have h2400 : TreeTrue τ start2400 := steps74 τ h2368
  exact steps75 τ h2400
#print axioms unsat
end Snake9.ReplayFull161
