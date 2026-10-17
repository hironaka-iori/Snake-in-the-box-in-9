import B112E091Inputs
namespace B112E091
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c919 : List Lit := [(75, true)]
theorem step919 (p : Nat → Bool) (h : Constraints p) : clause p c919 = true :=
  Snake9.LocalRup.prove_clause [c238, c237] c919 (by decide) p (sat_cons (step238 p h) (sat_cons (step237 p h) (sat_nil p)))
def c920 : List Lit := [(181, true), (71, true)]
theorem step920 (p : Nat → Bool) (h : Constraints p) : clause p c920 = true :=
  Snake9.LocalRup.prove_clause [c919, c239] c920 (by decide) p (sat_cons (step919 p h) (sat_cons (step239 p h) (sat_nil p)))
def c921 : List Lit := [(418, false)]
theorem step921 (p : Nat → Bool) (h : Constraints p) : clause p c921 = true :=
  Snake9.LocalRup.prove_clause [c569, c566] c921 (by decide) p (sat_cons (step569 p h) (sat_cons (step566 p h) (sat_nil p)))
def c922 : List Lit := [(314, false)]
theorem step922 (p : Nat → Bool) (h : Constraints p) : clause p c922 = true :=
  Snake9.LocalRup.prove_clause [c569, c568] c922 (by decide) p (sat_cons (step569 p h) (sat_cons (step568 p h) (sat_nil p)))
def c923 : List Lit := [(416, false)]
theorem step923 (p : Nat → Bool) (h : Constraints p) : clause p c923 = true :=
  Snake9.LocalRup.prove_clause [c921, c562] c923 (by decide) p (sat_cons (step921 p h) (sat_cons (step562 p h) (sat_nil p)))
def c924 : List Lit := [(364, false)]
theorem step924 (p : Nat → Bool) (h : Constraints p) : clause p c924 = true :=
  Snake9.LocalRup.prove_clause [c921, c565] c924 (by decide) p (sat_cons (step921 p h) (sat_cons (step565 p h) (sat_nil p)))
def c925 : List Lit := [(312, false)]
theorem step925 (p : Nat → Bool) (h : Constraints p) : clause p c925 = true :=
  Snake9.LocalRup.prove_clause [c922, c455] c925 (by decide) p (sat_cons (step922 p h) (sat_cons (step455 p h) (sat_nil p)))
def c926 : List Lit := [(262, false)]
theorem step926 (p : Nat → Bool) (h : Constraints p) : clause p c926 = true :=
  Snake9.LocalRup.prove_clause [c922, c458] c926 (by decide) p (sat_cons (step922 p h) (sat_cons (step458 p h) (sat_nil p)))
def c927 : List Lit := [(414, false)]
theorem step927 (p : Nat → Bool) (h : Constraints p) : clause p c927 = true :=
  Snake9.LocalRup.prove_clause [c923, c557] c927 (by decide) p (sat_cons (step923 p h) (sat_cons (step557 p h) (sat_nil p)))
def c928 : List Lit := [(388, false)]
theorem step928 (p : Nat → Bool) (h : Constraints p) : clause p c928 = true :=
  Snake9.LocalRup.prove_clause [c923, c560] c928 (by decide) p (sat_cons (step923 p h) (sat_cons (step560 p h) (sat_nil p)))
def c929 : List Lit := [(362, false)]
theorem step929 (p : Nat → Bool) (h : Constraints p) : clause p c929 = true :=
  Snake9.LocalRup.prove_clause [c924, c506] c929 (by decide) p (sat_cons (step924 p h) (sat_cons (step506 p h) (sat_nil p)))
def c930 : List Lit := [(338, false)]
theorem step930 (p : Nat → Bool) (h : Constraints p) : clause p c930 = true :=
  Snake9.LocalRup.prove_clause [c924, c509] c930 (by decide) p (sat_cons (step924 p h) (sat_cons (step509 p h) (sat_nil p)))
def c931 : List Lit := [(310, false)]
theorem step931 (p : Nat → Bool) (h : Constraints p) : clause p c931 = true :=
  Snake9.LocalRup.prove_clause [c925, c450] c931 (by decide) p (sat_cons (step925 p h) (sat_cons (step450 p h) (sat_nil p)))
def c932 : List Lit := [(286, false)]
theorem step932 (p : Nat → Bool) (h : Constraints p) : clause p c932 = true :=
  Snake9.LocalRup.prove_clause [c925, c453] c932 (by decide) p (sat_cons (step925 p h) (sat_cons (step453 p h) (sat_nil p)))
def c933 : List Lit := [(260, false)]
theorem step933 (p : Nat → Bool) (h : Constraints p) : clause p c933 = true :=
  Snake9.LocalRup.prove_clause [c926, c398] c933 (by decide) p (sat_cons (step926 p h) (sat_cons (step398 p h) (sat_nil p)))
def c934 : List Lit := [(236, false)]
theorem step934 (p : Nat → Bool) (h : Constraints p) : clause p c934 = true :=
  Snake9.LocalRup.prove_clause [c926, c401] c934 (by decide) p (sat_cons (step926 p h) (sat_cons (step401 p h) (sat_nil p)))
def c935 : List Lit := [(412, false)]
theorem step935 (p : Nat → Bool) (h : Constraints p) : clause p c935 = true :=
  Snake9.LocalRup.prove_clause [c927, c552] c935 (by decide) p (sat_cons (step927 p h) (sat_cons (step552 p h) (sat_nil p)))
def c936 : List Lit := [(400, false)]
theorem step936 (p : Nat → Bool) (h : Constraints p) : clause p c936 = true :=
  Snake9.LocalRup.prove_clause [c927, c555] c936 (by decide) p (sat_cons (step927 p h) (sat_cons (step555 p h) (sat_nil p)))
def c937 : List Lit := [(374, false)]
theorem step937 (p : Nat → Bool) (h : Constraints p) : clause p c937 = true :=
  Snake9.LocalRup.prove_clause [c928, c531] c937 (by decide) p (sat_cons (step928 p h) (sat_cons (step531 p h) (sat_nil p)))
def c938 : List Lit := [(360, false)]
theorem step938 (p : Nat → Bool) (h : Constraints p) : clause p c938 = true :=
  Snake9.LocalRup.prove_clause [c929, c501] c938 (by decide) p (sat_cons (step929 p h) (sat_cons (step501 p h) (sat_nil p)))
def c939 : List Lit := [(348, false)]
theorem step939 (p : Nat → Bool) (h : Constraints p) : clause p c939 = true :=
  Snake9.LocalRup.prove_clause [c929, c504] c939 (by decide) p (sat_cons (step929 p h) (sat_cons (step504 p h) (sat_nil p)))
def c940 : List Lit := [(324, false)]
theorem step940 (p : Nat → Bool) (h : Constraints p) : clause p c940 = true :=
  Snake9.LocalRup.prove_clause [c930, c480] c940 (by decide) p (sat_cons (step930 p h) (sat_cons (step480 p h) (sat_nil p)))
def c941 : List Lit := [(296, false)]
theorem step941 (p : Nat → Bool) (h : Constraints p) : clause p c941 = true :=
  Snake9.LocalRup.prove_clause [c931, c448] c941 (by decide) p (sat_cons (step931 p h) (sat_cons (step448 p h) (sat_nil p)))
def c942 : List Lit := [(272, false)]
theorem step942 (p : Nat → Bool) (h : Constraints p) : clause p c942 = true :=
  Snake9.LocalRup.prove_clause [c932, c421] c942 (by decide) p (sat_cons (step932 p h) (sat_cons (step421 p h) (sat_nil p)))
def c943 : List Lit := [(258, false)]
theorem step943 (p : Nat → Bool) (h : Constraints p) : clause p c943 = true :=
  Snake9.LocalRup.prove_clause [c933, c393] c943 (by decide) p (sat_cons (step933 p h) (sat_cons (step393 p h) (sat_nil p)))
def c944 : List Lit := [(246, false)]
theorem step944 (p : Nat → Bool) (h : Constraints p) : clause p c944 = true :=
  Snake9.LocalRup.prove_clause [c933, c396] c944 (by decide) p (sat_cons (step933 p h) (sat_cons (step396 p h) (sat_nil p)))
def c945 : List Lit := [(234, false)]
theorem step945 (p : Nat → Bool) (h : Constraints p) : clause p c945 = true :=
  Snake9.LocalRup.prove_clause [c934, c372] c945 (by decide) p (sat_cons (step934 p h) (sat_cons (step372 p h) (sat_nil p)))
def c946 : List Lit := [(404, false)]
theorem step946 (p : Nat → Bool) (h : Constraints p) : clause p c946 = true :=
  Snake9.LocalRup.prove_clause [c935, c550] c946 (by decide) p (sat_cons (step935 p h) (sat_cons (step550 p h) (sat_nil p)))
def c947 : List Lit := [(372, false)]
theorem step947 (p : Nat → Bool) (h : Constraints p) : clause p c947 = true :=
  Snake9.LocalRup.prove_clause [c937, c517] c947 (by decide) p (sat_cons (step937 p h) (sat_cons (step517 p h) (sat_nil p)))
def c948 : List Lit := [(358, false)]
theorem step948 (p : Nat → Bool) (h : Constraints p) : clause p c948 = true :=
  Snake9.LocalRup.prove_clause [c938, c497] c948 (by decide) p (sat_cons (step938 p h) (sat_cons (step497 p h) (sat_nil p)))
def c949 : List Lit := [(318, false)]
theorem step949 (p : Nat → Bool) (h : Constraints p) : clause p c949 = true :=
  Snake9.LocalRup.prove_clause [c940, c467] c949 (by decide) p (sat_cons (step940 p h) (sat_cons (step467 p h) (sat_nil p)))
def c950 : List Lit := [(294, false)]
theorem step950 (p : Nat → Bool) (h : Constraints p) : clause p c950 = true :=
  Snake9.LocalRup.prove_clause [c941, c433] c950 (by decide) p (sat_cons (step941 p h) (sat_cons (step433 p h) (sat_nil p)))
def c951 : List Lit := [(290, false)]
theorem step951 (p : Nat → Bool) (h : Constraints p) : clause p c951 = true :=
  Snake9.LocalRup.prove_clause [c941, c436] c951 (by decide) p (sat_cons (step941 p h) (sat_cons (step436 p h) (sat_nil p)))
def c952 : List Lit := [(266, false)]
theorem step952 (p : Nat → Bool) (h : Constraints p) : clause p c952 = true :=
  Snake9.LocalRup.prove_clause [c942, c411] c952 (by decide) p (sat_cons (step942 p h) (sat_cons (step411 p h) (sat_nil p)))
def c953 : List Lit := [(240, false)]
theorem step953 (p : Nat → Bool) (h : Constraints p) : clause p c953 = true :=
  Snake9.LocalRup.prove_clause [c944, c383] c953 (by decide) p (sat_cons (step944 p h) (sat_cons (step383 p h) (sat_nil p)))
def c954 : List Lit := [(232, false)]
theorem step954 (p : Nat → Bool) (h : Constraints p) : clause p c954 = true :=
  Snake9.LocalRup.prove_clause [c945, c368] c954 (by decide) p (sat_cons (step945 p h) (sat_cons (step368 p h) (sat_nil p)))
def c955 : List Lit := [(292, false)]
theorem step955 (p : Nat → Bool) (h : Constraints p) : clause p c955 = true :=
  Snake9.LocalRup.prove_clause [c950, c431] c955 (by decide) p (sat_cons (step950 p h) (sat_cons (step431 p h) (sat_nil p)))
def c956 : List Lit := [(228, false)]
theorem step956 (p : Nat → Bool) (h : Constraints p) : clause p c956 = true :=
  Snake9.LocalRup.prove_clause [c954, c366] c956 (by decide) p (sat_cons (step954 p h) (sat_cons (step366 p h) (sat_nil p)))
def c957 : List Lit := [(108, true), (110, true), (113, true), (114, true), (115, true), (116, true), (117, true), (120, true), (121, true), (124, true), (126, true), (129, true), (131, true), (133, true), (135, true), (136, true), (138, true), (141, true), (143, true), (146, true), (147, true), (148, true), (150, true), (151, true), (154, true), (155, true), (158, true), (159, true), (161, true), (163, true), (167, true), (168, true), (169, true), (171, true), (174, true), (176, true), (179, true), (181, true), (182, true), (184, true), (187, true), (189, true), (191, true), (193, true), (195, true), (197, true), (199, true), (202, true), (204, true), (206, true), (208, true), (209, true), (211, true)]
theorem step957 (p : Nat → Bool) (h : Constraints p) : clause p c957 = true :=
  Snake9.LocalRup.prove_clause [c301, c302, c303, c304, c305, c306, c307, c308, c309, c310, c311, c312, c313, c314, c315, c316, c317, c318, c319, c320, c321, c322, c323, c324, c325, c326, c327, c328, c329, c330, c331, c332, c333, c334, c335, c336, c337, c338, c339, c340, c341, c342, c343, c344, c345, c346, c347, c348, c349, c350, c351, c352, c570] c957 (by decide) p (sat_cons (step301 p h) (sat_cons (step302 p h) (sat_cons (step303 p h) (sat_cons (step304 p h) (sat_cons (step305 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step308 p h) (sat_cons (step309 p h) (sat_cons (step310 p h) (sat_cons (step311 p h) (sat_cons (step312 p h) (sat_cons (step313 p h) (sat_cons (step314 p h) (sat_cons (step315 p h) (sat_cons (step316 p h) (sat_cons (step317 p h) (sat_cons (step318 p h) (sat_cons (step319 p h) (sat_cons (step320 p h) (sat_cons (step321 p h) (sat_cons (step322 p h) (sat_cons (step323 p h) (sat_cons (step324 p h) (sat_cons (step325 p h) (sat_cons (step326 p h) (sat_cons (step327 p h) (sat_cons (step328 p h) (sat_cons (step329 p h) (sat_cons (step330 p h) (sat_cons (step331 p h) (sat_cons (step332 p h) (sat_cons (step333 p h) (sat_cons (step334 p h) (sat_cons (step335 p h) (sat_cons (step336 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step339 p h) (sat_cons (step340 p h) (sat_cons (step341 p h) (sat_cons (step342 p h) (sat_cons (step343 p h) (sat_cons (step344 p h) (sat_cons (step345 p h) (sat_cons (step346 p h) (sat_cons (step347 p h) (sat_cons (step348 p h) (sat_cons (step349 p h) (sat_cons (step350 p h) (sat_cons (step351 p h) (sat_cons (step352 p h) (sat_cons (step570 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c958 : List Lit := [(1337, true)]
theorem step958 (p : Nat → Bool) (h : Constraints p) : clause p c958 = true :=
  Snake9.LocalRup.prove_clause [c693, c698, c681, c685, c651, c673, c663, c665, c647, c670, c671, c660, c661, c120, c164, c644, c123, c114] c958 (by decide) p (sat_cons (step693 p h) (sat_cons (step698 p h) (sat_cons (step681 p h) (sat_cons (step685 p h) (sat_cons (step651 p h) (sat_cons (step673 p h) (sat_cons (step663 p h) (sat_cons (step665 p h) (sat_cons (step647 p h) (sat_cons (step670 p h) (sat_cons (step671 p h) (sat_cons (step660 p h) (sat_cons (step661 p h) (sat_cons (step120 p h) (sat_cons (step164 p h) (sat_cons (step644 p h) (sat_cons (step123 p h) (sat_cons (step114 p h) (sat_nil p)))))))))))))))))))
def c959 : List Lit := [(1288, true)]
theorem step959 (p : Nat → Bool) (h : Constraints p) : clause p c959 = true :=
  Snake9.LocalRup.prove_clause [c621, c626, c612, c584, c586, c597, c581, c582, c576, c579, c580, c7, c45, c42] c959 (by decide) p (sat_cons (step621 p h) (sat_cons (step626 p h) (sat_cons (step612 p h) (sat_cons (step584 p h) (sat_cons (step586 p h) (sat_cons (step597 p h) (sat_cons (step581 p h) (sat_cons (step582 p h) (sat_cons (step576 p h) (sat_cons (step579 p h) (sat_cons (step580 p h) (sat_cons (step7 p h) (sat_cons (step45 p h) (sat_cons (step42 p h) (sat_nil p)))))))))))))))
def c960 : List Lit := [(57, false), (62, false), (61, false)]
theorem step960 (p : Nat → Bool) (h : Constraints p) : clause p c960 = true :=
  Snake9.LocalRup.prove_clause [c210, c213] c960 (by decide) p (sat_cons (step210 p h) (sat_cons (step213 p h) (sat_nil p)))
def c961 : List Lit := [(1370, true)]
theorem step961 (p : Nat → Bool) (h : Constraints p) : clause p c961 = true :=
  Snake9.LocalRup.prove_clause [c747, c749, c744, c745, c960] c961 (by decide) p (sat_cons (step747 p h) (sat_cons (step749 p h) (sat_cons (step744 p h) (sat_cons (step745 p h) (sat_cons (step960 p h) (sat_nil p))))))
def c962 : List Lit := [(1373, true)]
theorem step962 (p : Nat → Bool) (h : Constraints p) : clause p c962 = true :=
  Snake9.LocalRup.prove_clause [c961, c752] c962 (by decide) p (sat_cons (step961 p h) (sat_cons (step752 p h) (sat_nil p)))
def c963 : List Lit := [(1399, true)]
theorem step963 (p : Nat → Bool) (h : Constraints p) : clause p c963 = true :=
  Snake9.LocalRup.prove_clause [c962, c778] c963 (by decide) p (sat_cons (step962 p h) (sat_cons (step778 p h) (sat_nil p)))
def c964 : List Lit := [(1330, true), (146, true)]
theorem step964 (p : Nat → Bool) (h : Constraints p) : clause p c964 = true :=
  Snake9.LocalRup.prove_clause [c681, c685, c673, c663, c665, c670, c671, c660, c661, c120, c164, c125] c964 (by decide) p (sat_cons (step681 p h) (sat_cons (step685 p h) (sat_cons (step673 p h) (sat_cons (step663 p h) (sat_cons (step665 p h) (sat_cons (step670 p h) (sat_cons (step671 p h) (sat_cons (step660 p h) (sat_cons (step661 p h) (sat_cons (step120 p h) (sat_cons (step164 p h) (sat_cons (step125 p h) (sat_nil p)))))))))))))
def c965 : List Lit := [(1324, true), (37, false), (1320, true), (155, true)]
theorem step965 (p : Nat → Bool) (h : Constraints p) : clause p c965 = true :=
  Snake9.LocalRup.prove_clause [c670, c671, c152, c161, c167, c170, c666, c660] c965 (by decide) p (sat_cons (step670 p h) (sat_cons (step671 p h) (sat_cons (step152 p h) (sat_cons (step161 p h) (sat_cons (step167 p h) (sat_cons (step170 p h) (sat_cons (step666 p h) (sat_cons (step660 p h) (sat_nil p)))))))))
def c966 : List Lit := [(1322, true), (42, false), (151, true), (62, false)]
theorem step966 (p : Nat → Bool) (h : Constraints p) : clause p c966 = true :=
  Snake9.LocalRup.prove_clause [c667, c668, c140, c150, c147] c966 (by decide) p (sat_cons (step667 p h) (sat_cons (step668 p h) (sat_cons (step140 p h) (sat_cons (step150 p h) (sat_cons (step147 p h) (sat_nil p))))))
def c967 : List Lit := [(1303, true), (1290, true), (313, true)]
theorem step967 (p : Nat → Bool) (h : Constraints p) : clause p c967 = true :=
  Snake9.LocalRup.prove_clause [c456, c399, c371, c367, c365, c362, c454, c451, c419, c409, c404, c639, c641, c636, c637, c82, c83, c84, c78, c580, c601, c581, c606, c584, c609, c628, c631, c613, c585, c587, c597, c583, c576, c44, c7] c967 (by decide) p (sat_cons (step456 p h) (sat_cons (step399 p h) (sat_cons (step371 p h) (sat_cons (step367 p h) (sat_cons (step365 p h) (sat_cons (step362 p h) (sat_cons (step454 p h) (sat_cons (step451 p h) (sat_cons (step419 p h) (sat_cons (step409 p h) (sat_cons (step404 p h) (sat_cons (step639 p h) (sat_cons (step641 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step82 p h) (sat_cons (step83 p h) (sat_cons (step84 p h) (sat_cons (step78 p h) (sat_cons (step580 p h) (sat_cons (step601 p h) (sat_cons (step581 p h) (sat_cons (step606 p h) (sat_cons (step584 p h) (sat_cons (step609 p h) (sat_cons (step628 p h) (sat_cons (step631 p h) (sat_cons (step613 p h) (sat_cons (step585 p h) (sat_cons (step587 p h) (sat_cons (step597 p h) (sat_cons (step583 p h) (sat_cons (step576 p h) (sat_cons (step44 p h) (sat_cons (step7 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c968 : List Lit := [(89, false), (82, false), (88, true), (41, false), (195, true)]
theorem step968 (p : Nat → Bool) (h : Constraints p) : clause p c968 = true :=
  Snake9.LocalRup.prove_clause [c344, c269, c254, c271] c968 (by decide) p (sat_cons (step344 p h) (sat_cons (step269 p h) (sat_cons (step254 p h) (sat_cons (step271 p h) (sat_nil p)))))
def c969 : List Lit := [(63, false), (1325, true), (50, false), (42, false)]
theorem step969 (p : Nat → Bool) (h : Constraints p) : clause p c969 = true :=
  Snake9.LocalRup.prove_clause [c171, c172, c672] c969 (by decide) p (sat_cons (step171 p h) (sat_cons (step172 p h) (sat_cons (step672 p h) (sat_nil p))))
def c970 : List Lit := [(63, true), (1382, true), (64, true), (171, true)]
theorem step970 (p : Nat → Bool) (h : Constraints p) : clause p c970 = true :=
  Snake9.LocalRup.prove_clause [c332, c227, c766, c223, c763] c970 (by decide) p (sat_cons (step332 p h) (sat_cons (step227 p h) (sat_cons (step766 p h) (sat_cons (step223 p h) (sat_cons (step763 p h) (sat_nil p))))))
def c971 : List Lit := [(89, true), (1453, true), (199, true)]
theorem step971 (p : Nat → Bool) (h : Constraints p) : clause p c971 = true :=
  Snake9.LocalRup.prove_clause [c861, c818, c811, c808, c809, c810, c817, c858, c845, c829, c830, c827, c277, c273] c971 (by decide) p (sat_cons (step861 p h) (sat_cons (step818 p h) (sat_cons (step811 p h) (sat_cons (step808 p h) (sat_cons (step809 p h) (sat_cons (step810 p h) (sat_cons (step817 p h) (sat_cons (step858 p h) (sat_cons (step845 p h) (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step827 p h) (sat_cons (step277 p h) (sat_cons (step273 p h) (sat_nil p)))))))))))))))
def c972 : List Lit := [(89, false), (195, true), (88, true), (41, false)]
theorem step972 (p : Nat → Bool) (h : Constraints p) : clause p c972 = true :=
  Snake9.LocalRup.prove_clause [c270, c968] c972 (by decide) p (sat_cons (step270 p h) (sat_cons (step968 p h) (sat_nil p)))
def c973 : List Lit := [(40, false), (50, false), (42, false), (1325, true)]
theorem step973 (p : Nat → Bool) (h : Constraints p) : clause p c973 = true :=
  Snake9.LocalRup.prove_clause [c164, c165, c672] c973 (by decide) p (sat_cons (step164 p h) (sat_cons (step165 p h) (sat_cons (step672 p h) (sat_nil p))))
def c974 : List Lit := [(1333, true), (37, false), (155, true), (1323, false), (1319, false)]
theorem step974 (p : Nat → Bool) (h : Constraints p) : clause p c974 = true :=
  Snake9.LocalRup.prove_clause [c678, c692, c688, c965, c679] c974 (by decide) p (sat_cons (step678 p h) (sat_cons (step692 p h) (sat_cons (step688 p h) (sat_cons (step965 p h) (sat_cons (step679 p h) (sat_nil p))))))
def c975 : List Lit := [(49, false), (37, false), (155, true), (41, false), (50, true)]
theorem step975 (p : Nat → Bool) (h : Constraints p) : clause p c975 = true :=
  Snake9.LocalRup.prove_clause [c119, c162] c975 (by decide) p (sat_cons (step119 p h) (sat_cons (step162 p h) (sat_nil p)))
def c976 : List Lit := [(100, true), (1439, false), (413, true), (1447, true)]
theorem step976 (p : Nat → Bool) (h : Constraints p) : clause p c976 = true :=
  Snake9.LocalRup.prove_clause [c349, c844, c841, c551, c549, c541, c540, c553, c538, c532, c834, c835, c840, c294, c847, c288, c829, c830, c827, c277, c273] c976 (by decide) p (sat_cons (step349 p h) (sat_cons (step844 p h) (sat_cons (step841 p h) (sat_cons (step551 p h) (sat_cons (step549 p h) (sat_cons (step541 p h) (sat_cons (step540 p h) (sat_cons (step553 p h) (sat_cons (step538 p h) (sat_cons (step532 p h) (sat_cons (step834 p h) (sat_cons (step835 p h) (sat_cons (step840 p h) (sat_cons (step294 p h) (sat_cons (step847 p h) (sat_cons (step288 p h) (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step827 p h) (sat_cons (step277 p h) (sat_cons (step273 p h) (sat_nil p))))))))))))))))))))))
def c977 : List Lit := [(91, false), (102, false), (100, false)]
theorem step977 (p : Nat → Bool) (h : Constraints p) : clause p c977 = true :=
  Snake9.LocalRup.prove_clause [c946, c286, c290, c294, c543, c540] c977 (by decide) p (sat_cons (step946 p h) (sat_cons (step286 p h) (sat_cons (step290 p h) (sat_cons (step294 p h) (sat_cons (step543 p h) (sat_cons (step540 p h) (sat_nil p)))))))
def c978 : List Lit := [(1439, false), (1454, true), (1414, false)]
theorem step978 (p : Nat → Bool) (h : Constraints p) : clause p c978 = true :=
  Snake9.LocalRup.prove_clause [c820, c859, c843, c838, c840, c842, c833, c834, c862, c821, c810, c807, c977] c978 (by decide) p (sat_cons (step820 p h) (sat_cons (step859 p h) (sat_cons (step843 p h) (sat_cons (step838 p h) (sat_cons (step840 p h) (sat_cons (step842 p h) (sat_cons (step833 p h) (sat_cons (step834 p h) (sat_cons (step862 p h) (sat_cons (step821 p h) (sat_cons (step810 p h) (sat_cons (step807 p h) (sat_cons (step977 p h) (sat_nil p))))))))))))))
def c979 : List Lit := [(96, false), (93, false), (91, false)]
theorem step979 (p : Nat → Bool) (h : Constraints p) : clause p c979 = true :=
  Snake9.LocalRup.prove_clause [c936, c273, c277, c283, c532, c533, c539, c536] c979 (by decide) p (sat_cons (step936 p h) (sat_cons (step273 p h) (sat_cons (step277 p h) (sat_cons (step283 p h) (sat_cons (step532 p h) (sat_cons (step533 p h) (sat_cons (step539 p h) (sat_cons (step536 p h) (sat_nil p)))))))))
def c980 : List Lit := [(1434, true), (91, false)]
theorem step980 (p : Nat → Bool) (h : Constraints p) : clause p c980 = true :=
  Snake9.LocalRup.prove_clause [c829, c830, c827, c979] c980 (by decide) p (sat_cons (step829 p h) (sat_cons (step830 p h) (sat_cons (step827 p h) (sat_cons (step979 p h) (sat_nil p)))))
def c981 : List Lit := [(91, false), (1446, true)]
theorem step981 (p : Nat → Bool) (h : Constraints p) : clause p c981 = true :=
  Snake9.LocalRup.prove_clause [c980, c846, c839, c833, c834, c977] c981 (by decide) p (sat_cons (step980 p h) (sat_cons (step846 p h) (sat_cons (step839 p h) (sat_cons (step833 p h) (sat_cons (step834 p h) (sat_cons (step977 p h) (sat_nil p)))))))
def c982 : List Lit := [(413, false), (1454, true), (81, true)]
theorem step982 (p : Nat → Bool) (h : Constraints p) : clause p c982 = true :=
  Snake9.LocalRup.prove_clause [c923, c921, c337, c800, c865, c801, c820, c859, c981, c807, c810, c825, c803, c822, c813, c805, c804, c556, c559, c564, c529, c505, c516, c500, c513, c496, c512, c493, c263, c492, c257, c246, c245] c982 (by decide) p (sat_cons (step923 p h) (sat_cons (step921 p h) (sat_cons (step337 p h) (sat_cons (step800 p h) (sat_cons (step865 p h) (sat_cons (step801 p h) (sat_cons (step820 p h) (sat_cons (step859 p h) (sat_cons (step981 p h) (sat_cons (step807 p h) (sat_cons (step810 p h) (sat_cons (step825 p h) (sat_cons (step803 p h) (sat_cons (step822 p h) (sat_cons (step813 p h) (sat_cons (step805 p h) (sat_cons (step804 p h) (sat_cons (step556 p h) (sat_cons (step559 p h) (sat_cons (step564 p h) (sat_cons (step529 p h) (sat_cons (step505 p h) (sat_cons (step516 p h) (sat_cons (step500 p h) (sat_cons (step513 p h) (sat_cons (step496 p h) (sat_cons (step512 p h) (sat_cons (step493 p h) (sat_cons (step263 p h) (sat_cons (step492 p h) (sat_cons (step257 p h) (sat_cons (step246 p h) (sat_cons (step245 p h) (sat_nil p))))))))))))))))))))))))))))))))))
end B112E091
