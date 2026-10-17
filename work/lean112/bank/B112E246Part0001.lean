import B112E246Part0000
namespace B112E246
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c435 : List Lit := [(70, false), (62, false), (69, false), (1393, false)]
theorem step435 (p : Nat → Bool) (h : Constraints p) : clause p c435 = true :=
  Snake9.LocalRup.prove_clause [c417, c293, c251, c369, c432, c250, c291, c434, c433, c295, c35, c32, c243, c248] c435 (by decide) p (sat_cons (step417 p h) (sat_cons (step293 p h) (sat_cons (step251 p h) (sat_cons (step369 p h) (sat_cons (step432 p h) (sat_cons (step250 p h) (sat_cons (step291 p h) (sat_cons (step434 p h) (sat_cons (step433 p h) (sat_cons (step295 p h) (sat_cons (step35 p h) (sat_cons (step32 p h) (sat_cons (step243 p h) (sat_cons (step248 p h) (sat_nil p)))))))))))))))
def c436 : List Lit := [(62, false), (1373, false), (69, false), (67, true)]
theorem step436 (p : Nat → Bool) (h : Constraints p) : clause p c436 = true :=
  Snake9.LocalRup.prove_clause [c385, c417, c134, c289, c282, c255, c257, c277, c435, c256, c258, c261, c280, c292, c288, c250, c434, c433, c294, c295, c79, c37, c247, c241, c242, c34] c436 (by decide) p (sat_cons (step385 p h) (sat_cons (step417 p h) (sat_cons (step134 p h) (sat_cons (step289 p h) (sat_cons (step282 p h) (sat_cons (step255 p h) (sat_cons (step257 p h) (sat_cons (step277 p h) (sat_cons (step435 p h) (sat_cons (step256 p h) (sat_cons (step258 p h) (sat_cons (step261 p h) (sat_cons (step280 p h) (sat_cons (step292 p h) (sat_cons (step288 p h) (sat_cons (step250 p h) (sat_cons (step434 p h) (sat_cons (step433 p h) (sat_cons (step294 p h) (sat_cons (step295 p h) (sat_cons (step79 p h) (sat_cons (step37 p h) (sat_cons (step247 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step34 p h) (sat_nil p)))))))))))))))))))))))))))
def c437 : List Lit := [(78, false), (1402, false)]
theorem step437 (p : Nat → Bool) (h : Constraints p) : clause p c437 = true :=
  Snake9.LocalRup.prove_clause [c415, c404, c405, c367, c390, c359, c365, c396, c203, c195, c193, c434, c433, c295, c360, c350, c69, c67, c305, c299, c310, c317] c437 (by decide) p (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step405 p h) (sat_cons (step367 p h) (sat_cons (step390 p h) (sat_cons (step359 p h) (sat_cons (step365 p h) (sat_cons (step396 p h) (sat_cons (step203 p h) (sat_cons (step195 p h) (sat_cons (step193 p h) (sat_cons (step434 p h) (sat_cons (step433 p h) (sat_cons (step295 p h) (sat_cons (step360 p h) (sat_cons (step350 p h) (sat_cons (step69 p h) (sat_cons (step67 p h) (sat_cons (step305 p h) (sat_cons (step299 p h) (sat_cons (step310 p h) (sat_cons (step317 p h) (sat_nil p)))))))))))))))))))))))
def c438 : List Lit := [(1402, false)]
theorem step438 (p : Nat → Bool) (h : Constraints p) : clause p c438 = true :=
  Snake9.LocalRup.prove_clause [c415, c404, c132, c137, c360, c434, c350, c437, c75, c91, c299, c305, c317, c310] c438 (by decide) p (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step132 p h) (sat_cons (step137 p h) (sat_cons (step360 p h) (sat_cons (step434 p h) (sat_cons (step350 p h) (sat_cons (step437 p h) (sat_cons (step75 p h) (sat_cons (step91 p h) (sat_cons (step299 p h) (sat_cons (step305 p h) (sat_cons (step317 p h) (sat_cons (step310 p h) (sat_nil p)))))))))))))))
def c439 : List Lit := [(1395, false)]
theorem step439 (p : Nat → Bool) (h : Constraints p) : clause p c439 = true :=
  Snake9.LocalRup.prove_clause [c438, c285] c439 (by decide) p (sat_cons (step438 p h) (sat_cons (step285 p h) (sat_nil p)))
def c440 : List Lit := [(1383, false)]
theorem step440 (p : Nat → Bool) (h : Constraints p) : clause p c440 = true :=
  Snake9.LocalRup.prove_clause [c439, c385, c282] c440 (by decide) p (sat_cons (step439 p h) (sat_cons (step385 p h) (sat_cons (step282 p h) (sat_nil p))))
def c441 : List Lit := [(61, false), (62, false), (82, false), (1371, true)]
theorem step441 (p : Nat → Bool) (h : Constraints p) : clause p c441 = true :=
  Snake9.LocalRup.prove_clause [c29, c34, c247, c241] c441 (by decide) p (sat_cons (step29 p h) (sat_cons (step34 p h) (sat_cons (step247 p h) (sat_cons (step241 p h) (sat_nil p)))))
def c442 : List Lit := [(62, false), (82, false), (1371, true)]
theorem step442 (p : Nat → Bool) (h : Constraints p) : clause p c442 = true :=
  Snake9.LocalRup.prove_clause [c245, c441, c242, c243, c247, c31] c442 (by decide) p (sat_cons (step245 p h) (sat_cons (step441 p h) (sat_cons (step242 p h) (sat_cons (step243 p h) (sat_cons (step247 p h) (sat_cons (step31 p h) (sat_nil p)))))))
def c443 : List Lit := [(83, false), (65, false), (60, false)]
theorem step443 (p : Nat → Bool) (h : Constraints p) : clause p c443 = true :=
  Snake9.LocalRup.prove_clause [c134, c79, c37] c443 (by decide) p (sat_cons (step134 p h) (sat_cons (step79 p h) (sat_cons (step37 p h) (sat_nil p))))
def c444 : List Lit := [(1373, false), (60, false), (62, true), (82, false), (1417, false)]
theorem step444 (p : Nat → Bool) (h : Constraints p) : clause p c444 = true :=
  Snake9.LocalRup.prove_clause [c133, c438, c385, c415, c390, c367, c404, c403, c257, c277, c77, c309, c288, c287, c280, c358, c260, c352, c443, c294, c411, c297, c193, c195, c203, c396, c365, c357, c350, c320, c317, c300, c310, c70, c305] c444 (by decide) p (sat_cons (step133 p h) (sat_cons (step438 p h) (sat_cons (step385 p h) (sat_cons (step415 p h) (sat_cons (step390 p h) (sat_cons (step367 p h) (sat_cons (step404 p h) (sat_cons (step403 p h) (sat_cons (step257 p h) (sat_cons (step277 p h) (sat_cons (step77 p h) (sat_cons (step309 p h) (sat_cons (step288 p h) (sat_cons (step287 p h) (sat_cons (step280 p h) (sat_cons (step358 p h) (sat_cons (step260 p h) (sat_cons (step352 p h) (sat_cons (step443 p h) (sat_cons (step294 p h) (sat_cons (step411 p h) (sat_cons (step297 p h) (sat_cons (step193 p h) (sat_cons (step195 p h) (sat_cons (step203 p h) (sat_cons (step396 p h) (sat_cons (step365 p h) (sat_cons (step357 p h) (sat_cons (step350 p h) (sat_cons (step320 p h) (sat_cons (step317 p h) (sat_cons (step300 p h) (sat_cons (step310 p h) (sat_cons (step70 p h) (sat_cons (step305 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c445 : List Lit := [(1423, false), (1412, false), (78, false), (82, false)]
theorem step445 (p : Nat → Bool) (h : Constraints p) : clause p c445 = true :=
  Snake9.LocalRup.prove_clause [c418, c404, c387, c367, c390, c297, c318, c322, c352, c300, c354, c67, c365, c193, c396, c195, c203] c445 (by decide) p (sat_cons (step418 p h) (sat_cons (step404 p h) (sat_cons (step387 p h) (sat_cons (step367 p h) (sat_cons (step390 p h) (sat_cons (step297 p h) (sat_cons (step318 p h) (sat_cons (step322 p h) (sat_cons (step352 p h) (sat_cons (step300 p h) (sat_cons (step354 p h) (sat_cons (step67 p h) (sat_cons (step365 p h) (sat_cons (step193 p h) (sat_cons (step396 p h) (sat_cons (step195 p h) (sat_cons (step203 p h) (sat_nil p))))))))))))))))))
def c446 : List Lit := [(1412, false), (90, true), (78, false), (82, false), (1417, false)]
theorem step446 (p : Nat → Bool) (h : Constraints p) : clause p c446 = true :=
  Snake9.LocalRup.prove_clause [c390, c404, c387, c367, c306, c310, c445, c311, c307, c69, c70, c193, c300, c195, c321, c203, c352, c396, c354, c365] c446 (by decide) p (sat_cons (step390 p h) (sat_cons (step404 p h) (sat_cons (step387 p h) (sat_cons (step367 p h) (sat_cons (step306 p h) (sat_cons (step310 p h) (sat_cons (step445 p h) (sat_cons (step311 p h) (sat_cons (step307 p h) (sat_cons (step69 p h) (sat_cons (step70 p h) (sat_cons (step193 p h) (sat_cons (step300 p h) (sat_cons (step195 p h) (sat_cons (step321 p h) (sat_cons (step203 p h) (sat_cons (step352 p h) (sat_cons (step396 p h) (sat_cons (step354 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))))))))))))
def c447 : List Lit := [(1414, false), (90, true), (78, false), (82, false), (1417, false)]
theorem step447 (p : Nat → Bool) (h : Constraints p) : clause p c447 = true :=
  Snake9.LocalRup.prove_clause [c415, c404, c367, c390, c446, c294, c402, c358, c352, c306, c310, c317, c318, c350, c311, c357, c307, c365, c69, c396, c193, c203, c195] c447 (by decide) p (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step367 p h) (sat_cons (step390 p h) (sat_cons (step446 p h) (sat_cons (step294 p h) (sat_cons (step402 p h) (sat_cons (step358 p h) (sat_cons (step352 p h) (sat_cons (step306 p h) (sat_cons (step310 p h) (sat_cons (step317 p h) (sat_cons (step318 p h) (sat_cons (step350 p h) (sat_cons (step311 p h) (sat_cons (step357 p h) (sat_cons (step307 p h) (sat_cons (step365 p h) (sat_cons (step69 p h) (sat_cons (step396 p h) (sat_cons (step193 p h) (sat_cons (step203 p h) (sat_cons (step195 p h) (sat_nil p))))))))))))))))))))))))
def c448 : List Lit := [(90, true), (78, false), (1417, false), (82, false)]
theorem step448 (p : Nat → Bool) (h : Constraints p) : clause p c448 = true :=
  Snake9.LocalRup.prove_clause [c367, c404, c390, c446, c294, c402, c447, c299, c70, c67, c307, c193, c311, c195, c315, c203, c350, c396, c357, c365] c448 (by decide) p (sat_cons (step367 p h) (sat_cons (step404 p h) (sat_cons (step390 p h) (sat_cons (step446 p h) (sat_cons (step294 p h) (sat_cons (step402 p h) (sat_cons (step447 p h) (sat_cons (step299 p h) (sat_cons (step70 p h) (sat_cons (step67 p h) (sat_cons (step307 p h) (sat_cons (step193 p h) (sat_cons (step311 p h) (sat_cons (step195 p h) (sat_cons (step315 p h) (sat_cons (step203 p h) (sat_cons (step350 p h) (sat_cons (step396 p h) (sat_cons (step357 p h) (sat_cons (step365 p h) (sat_nil p)))))))))))))))))))))
def c449 : List Lit := [(82, false), (1417, false), (1371, true)]
theorem step449 (p : Nat → Bool) (h : Constraints p) : clause p c449 = true :=
  Snake9.LocalRup.prove_clause [c133, c442, c77, c76, c448, c80, c241, c244, c247, c249, c444] c449 (by decide) p (sat_cons (step133 p h) (sat_cons (step442 p h) (sat_cons (step77 p h) (sat_cons (step76 p h) (sat_cons (step448 p h) (sat_cons (step80 p h) (sat_cons (step241 p h) (sat_cons (step244 p h) (sat_cons (step247 p h) (sat_cons (step249 p h) (sat_cons (step444 p h) (sat_nil p))))))))))))
def c450 : List Lit := [(1368, false), (62, true), (1417, false), (1371, true)]
theorem step450 (p : Nat → Bool) (h : Constraints p) : clause p c450 = true :=
  Snake9.LocalRup.prove_clause [c438, c385, c415, c404, c390, c367, c449, c309, c244, c247, c249, c403, c288, c257, c280, c277, c260, c287, c443, c358, c296, c352, c298, c408, c320, c193, c350, c195, c357, c203, c365, c396] c450 (by decide) p (sat_cons (step438 p h) (sat_cons (step385 p h) (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step390 p h) (sat_cons (step367 p h) (sat_cons (step449 p h) (sat_cons (step309 p h) (sat_cons (step244 p h) (sat_cons (step247 p h) (sat_cons (step249 p h) (sat_cons (step403 p h) (sat_cons (step288 p h) (sat_cons (step257 p h) (sat_cons (step280 p h) (sat_cons (step277 p h) (sat_cons (step260 p h) (sat_cons (step287 p h) (sat_cons (step443 p h) (sat_cons (step358 p h) (sat_cons (step296 p h) (sat_cons (step352 p h) (sat_cons (step298 p h) (sat_cons (step408 p h) (sat_cons (step320 p h) (sat_cons (step193 p h) (sat_cons (step350 p h) (sat_cons (step195 p h) (sat_cons (step357 p h) (sat_cons (step203 p h) (sat_cons (step365 p h) (sat_cons (step396 p h) (sat_nil p)))))))))))))))))))))))))))))))))
def c451 : List Lit := [(1455, true), (60, false), (90, false), (61, false), (62, true), (82, true), (1417, false)]
theorem step451 (p : Nat → Bool) (h : Constraints p) : clause p c451 = true :=
  Snake9.LocalRup.prove_clause [c389, c404, c132, c134, c137, c440, c439, c135, c126, c136, c403, c295, c297, c309, c348, c350, c423, c320, c317, c298, c300, c312, c310, c296, c74, c305, c79, c443, c90, c260, c421, c261, c424, c281, c23, c83, c26, c304, c85, c87, c266, c271, c263, c50, c51, c256] c451 (by decide) p (sat_cons (step389 p h) (sat_cons (step404 p h) (sat_cons (step132 p h) (sat_cons (step134 p h) (sat_cons (step137 p h) (sat_cons (step440 p h) (sat_cons (step439 p h) (sat_cons (step135 p h) (sat_cons (step126 p h) (sat_cons (step136 p h) (sat_cons (step403 p h) (sat_cons (step295 p h) (sat_cons (step297 p h) (sat_cons (step309 p h) (sat_cons (step348 p h) (sat_cons (step350 p h) (sat_cons (step423 p h) (sat_cons (step320 p h) (sat_cons (step317 p h) (sat_cons (step298 p h) (sat_cons (step300 p h) (sat_cons (step312 p h) (sat_cons (step310 p h) (sat_cons (step296 p h) (sat_cons (step74 p h) (sat_cons (step305 p h) (sat_cons (step79 p h) (sat_cons (step443 p h) (sat_cons (step90 p h) (sat_cons (step260 p h) (sat_cons (step421 p h) (sat_cons (step261 p h) (sat_cons (step424 p h) (sat_cons (step281 p h) (sat_cons (step23 p h) (sat_cons (step83 p h) (sat_cons (step26 p h) (sat_cons (step304 p h) (sat_cons (step85 p h) (sat_cons (step87 p h) (sat_cons (step266 p h) (sat_cons (step271 p h) (sat_cons (step263 p h) (sat_cons (step50 p h) (sat_cons (step51 p h) (sat_cons (step256 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))
def c452 : List Lit := [(1471, true), (1455, false), (1381, false), (90, false), (61, false), (82, true), (1417, false)]
theorem step452 (p : Nat → Bool) (h : Constraints p) : clause p c452 = true :=
  Snake9.LocalRup.prove_clause [c387, c404, c385, c132, c137, c135, c136, c130, c309, c354, c352, c324, c357, c284, c402, c280, c278, c296, c258, c298, c301, c321, c320, c74, c312, c310, c351, c305, c423, c90, c424, c83, c304, c85, c87, c266, c271, c263, c57, c50, c51, c256] c452 (by decide) p (sat_cons (step387 p h) (sat_cons (step404 p h) (sat_cons (step385 p h) (sat_cons (step132 p h) (sat_cons (step137 p h) (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step130 p h) (sat_cons (step309 p h) (sat_cons (step354 p h) (sat_cons (step352 p h) (sat_cons (step324 p h) (sat_cons (step357 p h) (sat_cons (step284 p h) (sat_cons (step402 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step296 p h) (sat_cons (step258 p h) (sat_cons (step298 p h) (sat_cons (step301 p h) (sat_cons (step321 p h) (sat_cons (step320 p h) (sat_cons (step74 p h) (sat_cons (step312 p h) (sat_cons (step310 p h) (sat_cons (step351 p h) (sat_cons (step305 p h) (sat_cons (step423 p h) (sat_cons (step90 p h) (sat_cons (step424 p h) (sat_cons (step83 p h) (sat_cons (step304 p h) (sat_cons (step85 p h) (sat_cons (step87 p h) (sat_cons (step266 p h) (sat_cons (step271 p h) (sat_cons (step263 p h) (sat_cons (step57 p h) (sat_cons (step50 p h) (sat_cons (step51 p h) (sat_cons (step256 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))
def c453 : List Lit := [(71, false), (1380, true), (61, false)]
theorem step453 (p : Nat → Bool) (h : Constraints p) : clause p c453 = true :=
  Snake9.LocalRup.prove_clause [c130, c57, c50, c51, c256] c453 (by decide) p (sat_cons (step130 p h) (sat_cons (step57 p h) (sat_cons (step50 p h) (sat_cons (step51 p h) (sat_cons (step256 p h) (sat_nil p))))))
def c454 : List Lit := [(1394, true), (1379, false), (1368, true)]
theorem step454 (p : Nat → Bool) (h : Constraints p) : clause p c454 = true :=
  Snake9.LocalRup.prove_clause [c385, c128, c257, c242, c241, c280, c278, c258, c260, c273, c453, c263, c264, c271, c266, c62, c40, c39] c454 (by decide) p (sat_cons (step385 p h) (sat_cons (step128 p h) (sat_cons (step257 p h) (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_cons (step280 p h) (sat_cons (step278 p h) (sat_cons (step258 p h) (sat_cons (step260 p h) (sat_cons (step273 p h) (sat_cons (step453 p h) (sat_cons (step263 p h) (sat_cons (step264 p h) (sat_cons (step271 p h) (sat_cons (step266 p h) (sat_cons (step62 p h) (sat_cons (step40 p h) (sat_cons (step39 p h) (sat_nil p)))))))))))))))))))
def c455 : List Lit := [(6, false), (4, true), (15, false), (1256, true), (64, false)]
theorem step455 (p : Nat → Bool) (h : Constraints p) : clause p c455 = true :=
  Snake9.LocalRup.prove_clause [c2, c3, c182, c177] c455 (by decide) p (sat_cons (step2 p h) (sat_cons (step3 p h) (sat_cons (step182 p h) (sat_cons (step177 p h) (sat_nil p)))))
def c456 : List Lit := [(60, false), (90, false), (1368, true), (62, true), (82, true), (1417, false)]
theorem step456 (p : Nat → Bool) (h : Constraints p) : clause p c456 = true :=
  Snake9.LocalRup.prove_clause [c367, c384, c391, c390, c415, c404, c134, c440, c439, c117, c127, c131, c242, c241, c403, c257, c451, c452, c365, c237, c396, c208, c203, c192, c195, c193, c194, c454, c284, c358, c352, c411, c79, c36, c443, c260, c261, c281, c453, c273, c263, c264, c271, c266, c455, c9, c38, c65, c64, c60] c456 (by decide) p (sat_cons (step367 p h) (sat_cons (step384 p h) (sat_cons (step391 p h) (sat_cons (step390 p h) (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step134 p h) (sat_cons (step440 p h) (sat_cons (step439 p h) (sat_cons (step117 p h) (sat_cons (step127 p h) (sat_cons (step131 p h) (sat_cons (step242 p h) (sat_cons (step241 p h) (sat_cons (step403 p h) (sat_cons (step257 p h) (sat_cons (step451 p h) (sat_cons (step452 p h) (sat_cons (step365 p h) (sat_cons (step237 p h) (sat_cons (step396 p h) (sat_cons (step208 p h) (sat_cons (step203 p h) (sat_cons (step192 p h) (sat_cons (step195 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step454 p h) (sat_cons (step284 p h) (sat_cons (step358 p h) (sat_cons (step352 p h) (sat_cons (step411 p h) (sat_cons (step79 p h) (sat_cons (step36 p h) (sat_cons (step443 p h) (sat_cons (step260 p h) (sat_cons (step261 p h) (sat_cons (step281 p h) (sat_cons (step453 p h) (sat_cons (step273 p h) (sat_cons (step263 p h) (sat_cons (step264 p h) (sat_cons (step271 p h) (sat_cons (step266 p h) (sat_cons (step455 p h) (sat_cons (step9 p h) (sat_cons (step38 p h) (sat_cons (step65 p h) (sat_cons (step64 p h) (sat_cons (step60 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))
def c457 : List Lit := [(1379, true), (61, false), (62, true)]
theorem step457 (p : Nat → Bool) (h : Constraints p) : clause p c457 = true :=
  Snake9.LocalRup.prove_clause [c129, c254, c255, c54, c49] c457 (by decide) p (sat_cons (step129 p h) (sat_cons (step254 p h) (sat_cons (step255 p h) (sat_cons (step54 p h) (sat_cons (step49 p h) (sat_nil p))))))
def c458 : List Lit := [(62, true), (1417, false), (1371, true)]
theorem step458 (p : Nat → Bool) (h : Constraints p) : clause p c458 = true :=
  Snake9.LocalRup.prove_clause [c438, c415, c404, c367, c390, c137, c449, c295, c297, c450, c242, c457, c454, c284, c288, c358, c249, c352, c246, c318, c456, c311, c306, c307, c310, c317, c321, c350, c300, c357, c365, c396, c203, c91, c68, c195, c193] c458 (by decide) p (sat_cons (step438 p h) (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step367 p h) (sat_cons (step390 p h) (sat_cons (step137 p h) (sat_cons (step449 p h) (sat_cons (step295 p h) (sat_cons (step297 p h) (sat_cons (step450 p h) (sat_cons (step242 p h) (sat_cons (step457 p h) (sat_cons (step454 p h) (sat_cons (step284 p h) (sat_cons (step288 p h) (sat_cons (step358 p h) (sat_cons (step249 p h) (sat_cons (step352 p h) (sat_cons (step246 p h) (sat_cons (step318 p h) (sat_cons (step456 p h) (sat_cons (step311 p h) (sat_cons (step306 p h) (sat_cons (step307 p h) (sat_cons (step310 p h) (sat_cons (step317 p h) (sat_cons (step321 p h) (sat_cons (step350 p h) (sat_cons (step300 p h) (sat_cons (step357 p h) (sat_cons (step365 p h) (sat_cons (step396 p h) (sat_cons (step203 p h) (sat_cons (step91 p h) (sat_cons (step68 p h) (sat_cons (step195 p h) (sat_cons (step193 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c459 : List Lit := [(1368, true), (62, false)]
theorem step459 (p : Nat → Bool) (h : Constraints p) : clause p c459 = true :=
  Snake9.LocalRup.prove_clause [c438, c430, c249, c288, c241, c242, c454, c33, c254] c459 (by decide) p (sat_cons (step438 p h) (sat_cons (step430 p h) (sat_cons (step249 p h) (sat_cons (step288 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step454 p h) (sat_cons (step33 p h) (sat_cons (step254 p h) (sat_nil p))))))))))
def c460 : List Lit := [(1379, false), (60, false), (1373, false), (82, true), (1417, false)]
theorem step460 (p : Nat → Bool) (h : Constraints p) : clause p c460 = true :=
  Snake9.LocalRup.prove_clause [c438, c385, c415, c404, c367, c390, c288, c280, c309, c257, c260, c277, c443, c287, c296, c358, c298, c352, c320, c408, c350, c193, c357, c195, c365, c203, c396] c460 (by decide) p (sat_cons (step438 p h) (sat_cons (step385 p h) (sat_cons (step415 p h) (sat_cons (step404 p h) (sat_cons (step367 p h) (sat_cons (step390 p h) (sat_cons (step288 p h) (sat_cons (step280 p h) (sat_cons (step309 p h) (sat_cons (step257 p h) (sat_cons (step260 p h) (sat_cons (step277 p h) (sat_cons (step443 p h) (sat_cons (step287 p h) (sat_cons (step296 p h) (sat_cons (step358 p h) (sat_cons (step298 p h) (sat_cons (step352 p h) (sat_cons (step320 p h) (sat_cons (step408 p h) (sat_cons (step350 p h) (sat_cons (step193 p h) (sat_cons (step357 p h) (sat_cons (step195 p h) (sat_cons (step365 p h) (sat_cons (step203 p h) (sat_cons (step396 p h) (sat_nil p))))))))))))))))))))))))))))
def c461 : List Lit := [(1417, false), (1371, true)]
theorem step461 (p : Nat → Bool) (h : Constraints p) : clause p c461 = true :=
  Snake9.LocalRup.prove_clause [c449, c458, c430, c249, c459, c247, c460, c254, c432, c28] c461 (by decide) p (sat_cons (step449 p h) (sat_cons (step458 p h) (sat_cons (step430 p h) (sat_cons (step249 p h) (sat_cons (step459 p h) (sat_cons (step247 p h) (sat_cons (step460 p h) (sat_cons (step254 p h) (sat_cons (step432 p h) (sat_cons (step28 p h) (sat_nil p)))))))))))
def c462 : List Lit := [(1379, true), (60, false), (1371, true)]
theorem step462 (p : Nat → Bool) (h : Constraints p) : clause p c462 = true :=
  Snake9.LocalRup.prove_clause [c254, c403, c432, c28] c462 (by decide) p (sat_cons (step254 p h) (sat_cons (step403 p h) (sat_cons (step432 p h) (sat_cons (step28 p h) (sat_nil p)))))
def c463 : List Lit := [(71, true), (1389, true), (65, false), (91, false)]
theorem step463 (p : Nat → Bool) (h : Constraints p) : clause p c463 = true :=
  Snake9.LocalRup.prove_clause [c131, c128, c273, c263, c264, c271, c266, c62, c60, c39, c66] c463 (by decide) p (sat_cons (step131 p h) (sat_cons (step128 p h) (sat_cons (step273 p h) (sat_cons (step263 p h) (sat_cons (step264 p h) (sat_cons (step271 p h) (sat_cons (step266 p h) (sat_cons (step62 p h) (sat_cons (step60 p h) (sat_cons (step39 p h) (sat_cons (step66 p h) (sat_nil p))))))))))))
def c464 : List Lit := [(1455, true), (1413, false), (79, false), (85, false)]
theorem step464 (p : Nat → Bool) (h : Constraints p) : clause p c464 = true :=
  Snake9.LocalRup.prove_clause [c389, c404, c142, c132, c348, c350, c423, c323, c334, c301, c107, c74, c72] c464 (by decide) p (sat_cons (step389 p h) (sat_cons (step404 p h) (sat_cons (step142 p h) (sat_cons (step132 p h) (sat_cons (step348 p h) (sat_cons (step350 p h) (sat_cons (step423 p h) (sat_cons (step323 p h) (sat_cons (step334 p h) (sat_cons (step301 p h) (sat_cons (step107 p h) (sat_cons (step74 p h) (sat_cons (step72 p h) (sat_nil p))))))))))))))
def c465 : List Lit := [(1427, true), (18, false), (1417, true)]
theorem step465 (p : Nat → Bool) (h : Constraints p) : clause p c465 = true :=
  Snake9.LocalRup.prove_clause [c136, c302, c86, c303, c84, c399, c323, c320, c422, c308, c305] c465 (by decide) p (sat_cons (step136 p h) (sat_cons (step302 p h) (sat_cons (step86 p h) (sat_cons (step303 p h) (sat_cons (step84 p h) (sat_cons (step399 p h) (sat_cons (step323 p h) (sat_cons (step320 p h) (sat_cons (step422 p h) (sat_cons (step308 p h) (sat_cons (step305 p h) (sat_nil p))))))))))))
def c466 : List Lit := [(1355, true), (79, false), (1456, true), (51, false), (1417, true)]
theorem step466 (p : Nat → Bool) (h : Constraints p) : clause p c466 = true :=
  Snake9.LocalRup.prove_clause [c135, c393, c383, c390, c142, c119, c382, c121, c122, c303, c83, c234, c396, c231, c203, c195, c193, c465, c351, c423, c334, c107, c71, c12, c209, c210, c379, c216, c230, c377, c227, c211, c219, c220, c14, c218, c16, c17] c466 (by decide) p (sat_cons (step135 p h) (sat_cons (step393 p h) (sat_cons (step383 p h) (sat_cons (step390 p h) (sat_cons (step142 p h) (sat_cons (step119 p h) (sat_cons (step382 p h) (sat_cons (step121 p h) (sat_cons (step122 p h) (sat_cons (step303 p h) (sat_cons (step83 p h) (sat_cons (step234 p h) (sat_cons (step396 p h) (sat_cons (step231 p h) (sat_cons (step203 p h) (sat_cons (step195 p h) (sat_cons (step193 p h) (sat_cons (step465 p h) (sat_cons (step351 p h) (sat_cons (step423 p h) (sat_cons (step334 p h) (sat_cons (step107 p h) (sat_cons (step71 p h) (sat_cons (step12 p h) (sat_cons (step209 p h) (sat_cons (step210 p h) (sat_cons (step379 p h) (sat_cons (step216 p h) (sat_cons (step230 p h) (sat_cons (step377 p h) (sat_cons (step227 p h) (sat_cons (step211 p h) (sat_cons (step219 p h) (sat_cons (step220 p h) (sat_cons (step14 p h) (sat_cons (step218 p h) (sat_cons (step16 p h) (sat_cons (step17 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))
def c467 : List Lit := [(79, false), (64, false), (62, true), (1401, false), (51, false), (1417, true)]
theorem step467 (p : Nat → Bool) (h : Constraints p) : clause p c467 = true :=
  Snake9.LocalRup.prove_clause [c135, c136, c415, c367, c404, c133, c358, c302, c86, c303, c84, c83, c399, c466, c365, c357, c350, c464, c320, c296, c308, c76, c306, c80] c467 (by decide) p (sat_cons (step135 p h) (sat_cons (step136 p h) (sat_cons (step415 p h) (sat_cons (step367 p h) (sat_cons (step404 p h) (sat_cons (step133 p h) (sat_cons (step358 p h) (sat_cons (step302 p h) (sat_cons (step86 p h) (sat_cons (step303 p h) (sat_cons (step84 p h) (sat_cons (step83 p h) (sat_cons (step399 p h) (sat_cons (step466 p h) (sat_cons (step365 p h) (sat_cons (step357 p h) (sat_cons (step350 p h) (sat_cons (step464 p h) (sat_cons (step320 p h) (sat_cons (step296 p h) (sat_cons (step308 p h) (sat_cons (step76 p h) (sat_cons (step306 p h) (sat_cons (step80 p h) (sat_nil p)))))))))))))))))))))))))
def c468 : List Lit := [(79, true), (71, false), (1389, true)]
theorem step468 (p : Nat → Bool) (h : Constraints p) : clause p c468 = true :=
  Snake9.LocalRup.prove_clause [c269, c265, c267, c271, c431, c262] c468 (by decide) p (sat_cons (step269 p h) (sat_cons (step265 p h) (sat_cons (step267 p h) (sat_cons (step271 p h) (sat_cons (step431 p h) (sat_cons (step262 p h) (sat_nil p)))))))
def c469 : List Lit := [(1368, false), (1374, true)]
theorem step469 (p : Nat → Bool) (h : Constraints p) : clause p c469 = true :=
  Snake9.LocalRup.prove_clause [c136, c135, c438, c124, c385, c130, c250, c461, c303, c83, c302, c85, c245, c244, c247, c249, c253, c288, c240, c280, c239, c258, c21, c462, c257, c260, c277, c278, c287, c463, c468, c57, c453, c81, c243, c436, c467] c469 (by decide) p (sat_cons (step136 p h) (sat_cons (step135 p h) (sat_cons (step438 p h) (sat_cons (step124 p h) (sat_cons (step385 p h) (sat_cons (step130 p h) (sat_cons (step250 p h) (sat_cons (step461 p h) (sat_cons (step303 p h) (sat_cons (step83 p h) (sat_cons (step302 p h) (sat_cons (step85 p h) (sat_cons (step245 p h) (sat_cons (step244 p h) (sat_cons (step247 p h) (sat_cons (step249 p h) (sat_cons (step253 p h) (sat_cons (step288 p h) (sat_cons (step240 p h) (sat_cons (step280 p h) (sat_cons (step239 p h) (sat_cons (step258 p h) (sat_cons (step21 p h) (sat_cons (step462 p h) (sat_cons (step257 p h) (sat_cons (step260 p h) (sat_cons (step277 p h) (sat_cons (step278 p h) (sat_cons (step287 p h) (sat_cons (step463 p h) (sat_cons (step468 p h) (sat_cons (step57 p h) (sat_cons (step453 p h) (sat_cons (step81 p h) (sat_cons (step243 p h) (sat_cons (step436 p h) (sat_cons (step467 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))
def c470 : List Lit := [(1374, true)]
theorem step470 (p : Nat → Bool) (h : Constraints p) : clause p c470 = true :=
  Snake9.TreeRup.prove_clause [c135, c438, c415, c389, c124, c375, c373, c137, c142, c139, c143, c140, c141, c250, c461, c303, c83, c469, c241, c242, c459, c457, c454, c284, c288, c358, c252, c349, c240, c342, c346, c239, c21, c467, c429, c82, c145, c146, c147, c153, c154, c397, c171, c151, c90, c167, c168, c150, c166, c160, c149, c164, c165, c398, c159, c88, c163, c162, c106, c107, c157, c158, c96, c108, c102, c100, c110, c99, c113, c103, c105] c470 (by decide) p (sat_cons (step135 p h) (sat_cons (step438 p h) (sat_cons (step415 p h) (sat_cons (step389 p h) (sat_cons (step124 p h) (sat_cons (step375 p h) (sat_cons (step373 p h) (sat_cons (step137 p h) (sat_cons (step142 p h) (sat_cons (step139 p h) (sat_cons (step143 p h) (sat_cons (step140 p h) (sat_cons (step141 p h) (sat_cons (step250 p h) (sat_cons (step461 p h) (sat_cons (step303 p h) (sat_cons (step83 p h) (sat_cons (step469 p h) (sat_cons (step241 p h) (sat_cons (step242 p h) (sat_cons (step459 p h) (sat_cons (step457 p h) (sat_cons (step454 p h) (sat_cons (step284 p h) (sat_cons (step288 p h) (sat_cons (step358 p h) (sat_cons (step252 p h) (sat_cons (step349 p h) (sat_cons (step240 p h) (sat_cons (step342 p h) (sat_cons (step346 p h) (sat_cons (step239 p h) (sat_cons (step21 p h) (sat_cons (step467 p h) (sat_cons (step429 p h) (sat_cons (step82 p h) (sat_cons (step145 p h) (sat_cons (step146 p h) (sat_cons (step147 p h) (sat_cons (step153 p h) (sat_cons (step154 p h) (sat_cons (step397 p h) (sat_cons (step171 p h) (sat_cons (step151 p h) (sat_cons (step90 p h) (sat_cons (step167 p h) (sat_cons (step168 p h) (sat_cons (step150 p h) (sat_cons (step166 p h) (sat_cons (step160 p h) (sat_cons (step149 p h) (sat_cons (step164 p h) (sat_cons (step165 p h) (sat_cons (step398 p h) (sat_cons (step159 p h) (sat_cons (step88 p h) (sat_cons (step163 p h) (sat_cons (step162 p h) (sat_cons (step106 p h) (sat_cons (step107 p h) (sat_cons (step157 p h) (sat_cons (step158 p h) (sat_cons (step96 p h) (sat_cons (step108 p h) (sat_cons (step102 p h) (sat_cons (step100 p h) (sat_cons (step110 p h) (sat_cons (step99 p h) (sat_cons (step113 p h) (sat_cons (step103 p h) (sat_cons (step105 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c471 : List Lit := [(1401, true)]
theorem step471 (p : Nat → Bool) (h : Constraints p) : clause p c471 = true :=
  Snake9.LocalRup.prove_clause [c470, c386, c290] c471 (by decide) p (sat_cons (step470 p h) (sat_cons (step386 p h) (sat_cons (step290 p h) (sat_nil p))))
def c472 : List Lit := [(1393, false)]
theorem step472 (p : Nat → Bool) (h : Constraints p) : clause p c472 = true :=
  Snake9.LocalRup.prove_clause [c470, c438, c291] c472 (by decide) p (sat_cons (step470 p h) (sat_cons (step438 p h) (sat_cons (step291 p h) (sat_nil p))))
def c473 : List Lit := [(1389, false)]
theorem step473 (p : Nat → Bool) (h : Constraints p) : clause p c473 = true :=
  Snake9.LocalRup.prove_clause [c472, c276] c473 (by decide) p (sat_cons (step472 p h) (sat_cons (step276 p h) (sat_nil p)))
def c474 : List Lit := [(1381, false)]
theorem step474 (p : Nat → Bool) (h : Constraints p) : clause p c474 = true :=
  Snake9.LocalRup.prove_clause [c472, c385, c277] c474 (by decide) p (sat_cons (step472 p h) (sat_cons (step385 p h) (sat_cons (step277 p h) (sat_nil p))))
def c475 : List Lit := [(1385, false)]
theorem step475 (p : Nat → Bool) (h : Constraints p) : clause p c475 = true :=
  Snake9.LocalRup.prove_clause [c473, c273] c475 (by decide) p (sat_cons (step473 p h) (sat_cons (step273 p h) (sat_nil p)))
def c476 : List Lit := [(1379, false)]
theorem step476 (p : Nat → Bool) (h : Constraints p) : clause p c476 = true :=
  Snake9.LocalRup.prove_clause [c474, c257] c476 (by decide) p (sat_cons (step474 p h) (sat_cons (step257 p h) (sat_nil p)))
def c477 : List Lit := [(65, true)]
theorem step477 (p : Nat → Bool) (h : Constraints p) : clause p c477 = true :=
  Snake9.LocalRup.prove_clause [c474, c259] c477 (by decide) p (sat_cons (step474 p h) (sat_cons (step259 p h) (sat_nil p)))
def c478 : List Lit := [(70, true)]
theorem step478 (p : Nat → Bool) (h : Constraints p) : clause p c478 = true :=
  Snake9.LocalRup.prove_clause [c476, c254] c478 (by decide) p (sat_cons (step476 p h) (sat_cons (step254 p h) (sat_nil p)))
def c479 : List Lit := [(67, true)]
theorem step479 (p : Nat → Bool) (h : Constraints p) : clause p c479 = true :=
  Snake9.LocalRup.prove_clause [c476, c255] c479 (by decide) p (sat_cons (step476 p h) (sat_cons (step255 p h) (sat_nil p)))
def c480 : List Lit := [(71, false)]
theorem step480 (p : Nat → Bool) (h : Constraints p) : clause p c480 = true :=
  Snake9.LocalRup.prove_clause [c130, c479, c478, c57, c52] c480 (by decide) p (sat_cons (step130 p h) (sat_cons (step479 p h) (sat_cons (step478 p h) (sat_cons (step57 p h) (sat_cons (step52 p h) (sat_nil p))))))
def c481 : List Lit := [(1384, true)]
theorem step481 (p : Nat → Bool) (h : Constraints p) : clause p c481 = true :=
  Snake9.LocalRup.prove_clause [c480, c263] c481 (by decide) p (sat_cons (step480 p h) (sat_cons (step263 p h) (sat_nil p)))
def c482 : List Lit := [(73, true)]
theorem step482 (p : Nat → Bool) (h : Constraints p) : clause p c482 = true :=
  Snake9.LocalRup.prove_clause [c480, c475, c264] c482 (by decide) p (sat_cons (step480 p h) (sat_cons (step475 p h) (sat_cons (step264 p h) (sat_nil p))))
def c483 : List Lit := [(91, false)]
theorem step483 (p : Nat → Bool) (h : Constraints p) : clause p c483 = true :=
  Snake9.LocalRup.prove_clause [c480, c473, c477, c463] c483 (by decide) p (sat_cons (step480 p h) (sat_cons (step473 p h) (sat_cons (step477 p h) (sat_cons (step463 p h) (sat_nil p)))))
def c484 : List Lit := [(1386, false)]
theorem step484 (p : Nat → Bool) (h : Constraints p) : clause p c484 = true :=
  Snake9.LocalRup.prove_clause [c481, c473, c271] c484 (by decide) p (sat_cons (step481 p h) (sat_cons (step473 p h) (sat_cons (step271 p h) (sat_nil p))))
def c485 : List Lit := [(88, false)]
theorem step485 (p : Nat → Bool) (h : Constraints p) : clause p c485 = true :=
  Snake9.LocalRup.prove_clause [c483, c136, c85] c485 (by decide) p (sat_cons (step483 p h) (sat_cons (step136 p h) (sat_cons (step85 p h) (sat_nil p))))
def c486 : List Lit := [(76, true)]
theorem step486 (p : Nat → Bool) (h : Constraints p) : clause p c486 = true :=
  Snake9.LocalRup.prove_clause [c484, c266] c486 (by decide) p (sat_cons (step484 p h) (sat_cons (step266 p h) (sat_nil p)))
def c487 : List Lit := [(74, false)]
theorem step487 (p : Nat → Bool) (h : Constraints p) : clause p c487 = true :=
  Snake9.LocalRup.prove_clause [c486, c477, c482, c62] c487 (by decide) p (sat_cons (step486 p h) (sat_cons (step477 p h) (sat_cons (step482 p h) (sat_cons (step62 p h) (sat_nil p)))))
def c488 : List Lit := [(72, true)]
theorem step488 (p : Nat → Bool) (h : Constraints p) : clause p c488 = true :=
  Snake9.LocalRup.prove_clause [c487, c131, c482, c61] c488 (by decide) p (sat_cons (step487 p h) (sat_cons (step131 p h) (sat_cons (step482 p h) (sat_cons (step61 p h) (sat_nil p)))))
def c489 : List Lit := [(13, false)]
theorem step489 (p : Nat → Bool) (h : Constraints p) : clause p c489 = true :=
  Snake9.LocalRup.prove_clause [c488, c482, c479, c58] c489 (by decide) p (sat_cons (step488 p h) (sat_cons (step482 p h) (sat_cons (step479 p h) (sat_cons (step58 p h) (sat_nil p)))))
def c490 : List Lit := [(1270, true)]
theorem step490 (p : Nat → Bool) (h : Constraints p) : clause p c490 = true :=
  Snake9.LocalRup.prove_clause [c489, c196] c490 (by decide) p (sat_cons (step489 p h) (sat_cons (step196 p h) (sat_nil p)))
def c491 : List Lit := [(1282, true)]
theorem step491 (p : Nat → Bool) (h : Constraints p) : clause p c491 = true :=
  Snake9.LocalRup.prove_clause [c490, c390, c203] c491 (by decide) p (sat_cons (step490 p h) (sat_cons (step390 p h) (sat_cons (step203 p h) (sat_nil p))))
def c492 : List Lit := [(1355, true)]
theorem step492 (p : Nat → Bool) (h : Constraints p) : clause p c492 = true :=
  Snake9.LocalRup.prove_clause [c491, c396] c492 (by decide) p (sat_cons (step491 p h) (sat_cons (step396 p h) (sat_nil p)))
def c493 : List Lit := [(1471, false)]
theorem step493 (p : Nat → Bool) (h : Constraints p) : clause p c493 = true :=
  Snake9.LocalRup.prove_clause [c492, c367, c365] c493 (by decide) p (sat_cons (step492 p h) (sat_cons (step367 p h) (sat_cons (step365 p h) (sat_nil p))))
def c494 : List Lit := [(1455, false)]
theorem step494 (p : Nat → Bool) (h : Constraints p) : clause p c494 = true :=
  Snake9.LocalRup.prove_clause [c493, c471, c357] c494 (by decide) p (sat_cons (step493 p h) (sat_cons (step471 p h) (sat_cons (step357 p h) (sat_nil p))))
def c495 : List Lit := [(1427, false)]
theorem step495 (p : Nat → Bool) (h : Constraints p) : clause p c495 = true :=
  Snake9.LocalRup.prove_clause [c494, c404, c350] c495 (by decide) p (sat_cons (step494 p h) (sat_cons (step404 p h) (sat_cons (step350 p h) (sat_nil p))))
def c496 : List Lit := [(1423, false)]
theorem step496 (p : Nat → Bool) (h : Constraints p) : clause p c496 = true :=
  Snake9.LocalRup.prove_clause [c495, c315] c496 (by decide) p (sat_cons (step495 p h) (sat_cons (step315 p h) (sat_nil p)))
def c497 : List Lit := [(85, false)]
theorem step497 (p : Nat → Bool) (h : Constraints p) : clause p c497 = true :=
  Snake9.LocalRup.prove_clause [c488, c479, c478, c129, c47, c46, c53] c497 (by decide) p (sat_cons (step488 p h) (sat_cons (step479 p h) (sat_cons (step478 p h) (sat_cons (step129 p h) (sat_cons (step47 p h) (sat_cons (step46 p h) (sat_cons (step53 p h) (sat_nil p))))))))
def c498 : List Lit := [(86, false)]
theorem step498 (p : Nat → Bool) (h : Constraints p) : clause p c498 = true :=
  Snake9.LocalRup.prove_clause [c497, c135, c83] c498 (by decide) p (sat_cons (step497 p h) (sat_cons (step135 p h) (sat_cons (step83 p h) (sat_nil p))))
end B112E246
