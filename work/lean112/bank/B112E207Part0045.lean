import B112E207Part0044
namespace B112E207
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c4227 : List Lit := [(46, true), (47, true), (162, true), (45, false), (52, true), (48, true), (68, true)]
theorem step4227 (p : Nat → Bool) (h : Constraints p) : clause p c4227 = true :=
  Snake9.LocalRup.prove_clause [c4067, c207] c4227 (by decide) p (sat_cons (step4067 p h) (sat_cons (step207 p h) (sat_nil p)))
def c4228 : List Lit := [(46, true), (8, true), (2, false)]
theorem step4228 (p : Nat → Bool) (h : Constraints p) : clause p c4228 = true :=
  Snake9.LocalRup.prove_clause [c4067, c9] c4228 (by decide) p (sat_cons (step4067 p h) (sat_cons (step9 p h) (sat_nil p)))
def c4229 : List Lit := [(1516, false), (1534, true)]
theorem step4229 (p : Nat → Bool) (h : Constraints p) : clause p c4229 = true :=
  Snake9.LocalRup.prove_clause [c4139, c1114] c4229 (by decide) p (sat_cons (step4139 p h) (sat_cons (step1114 p h) (sat_nil p)))
def c4230 : List Lit := [(1515, false), (1534, true), (1596, true), (54, false), (63, true), (1642, false)]
theorem step4230 (p : Nat → Bool) (h : Constraints p) : clause p c4230 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3020] c4230 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3020 p h) (sat_nil p)))
def c4231 : List Lit := [(1425, true), (57, false)]
theorem step4231 (p : Nat → Bool) (h : Constraints p) : clause p c4231 = true :=
  Snake9.LocalRup.prove_clause [c4135, c1763] c4231 (by decide) p (sat_cons (step4135 p h) (sat_cons (step1763 p h) (sat_nil p)))
def c4232 : List Lit := [(1421, false), (1426, true)]
theorem step4232 (p : Nat → Bool) (h : Constraints p) : clause p c4232 = true :=
  Snake9.LocalRup.prove_clause [c4137, c930] c4232 (by decide) p (sat_cons (step4137 p h) (sat_cons (step930 p h) (sat_nil p)))
def c4233 : List Lit := [(243, true), (1426, true), (54, true), (57, true)]
theorem step4233 (p : Nat → Bool) (h : Constraints p) : clause p c4233 = true :=
  Snake9.LocalRup.prove_clause [c4135, c1802] c4233 (by decide) p (sat_cons (step4135 p h) (sat_cons (step1802 p h) (sat_nil p)))
def c4234 : List Lit := [(1515, false), (1533, true)]
theorem step4234 (p : Nat → Bool) (h : Constraints p) : clause p c4234 = true :=
  Snake9.LocalRup.prove_clause [c4139, c1113] c4234 (by decide) p (sat_cons (step4139 p h) (sat_cons (step1113 p h) (sat_nil p)))
def c4235 : List Lit := [(1532, true), (1514, false)]
theorem step4235 (p : Nat → Bool) (h : Constraints p) : clause p c4235 = true :=
  Snake9.LocalRup.prove_clause [c4139, c1112] c4235 (by decide) p (sat_cons (step4139 p h) (sat_cons (step1112 p h) (sat_nil p)))
def c4236 : List Lit := [(1420, false), (1425, true)]
theorem step4236 (p : Nat → Bool) (h : Constraints p) : clause p c4236 = true :=
  Snake9.LocalRup.prove_clause [c4137, c929] c4236 (by decide) p (sat_cons (step4137 p h) (sat_cons (step929 p h) (sat_nil p)))
def c4237 : List Lit := [(1454, true), (1446, false)]
theorem step4237 (p : Nat → Bool) (h : Constraints p) : clause p c4237 = true :=
  Snake9.LocalRup.prove_clause [c4138, c985] c4237 (by decide) p (sat_cons (step4138 p h) (sat_cons (step985 p h) (sat_nil p)))
def c4238 : List Lit := [(48, true), (1494, false), (57, true), (58, true), (1534, true), (5, true), (1489, false)]
theorem step4238 (p : Nat → Bool) (h : Constraints p) : clause p c4238 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2816] c4238 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2816 p h) (sat_nil p)))
def c4239 : List Lit := [(371, false), (48, true), (58, true), (1534, true), (5, true), (57, true), (1494, false)]
theorem step4239 (p : Nat → Bool) (h : Constraints p) : clause p c4239 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3012] c4239 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3012 p h) (sat_nil p)))
def c4240 : List Lit := [(48, true), (1533, true), (58, true), (5, true), (57, true), (1513, false), (1494, false)]
theorem step4240 (p : Nat → Bool) (h : Constraints p) : clause p c4240 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3013] c4240 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3013 p h) (sat_nil p)))
def c4241 : List Lit := [(123, true), (1426, true), (5, true), (57, true)]
theorem step4241 (p : Nat → Bool) (h : Constraints p) : clause p c4241 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2162] c4241 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2162 p h) (sat_nil p)))
def c4242 : List Lit := [(85, true), (48, true), (1542, false), (68, true), (57, false), (72, true), (52, false), (45, false), (58, true)]
theorem step4242 (p : Nat → Bool) (h : Constraints p) : clause p c4242 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2844] c4242 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2844 p h) (sat_nil p)))
def c4243 : List Lit := [(85, true), (48, false), (58, true), (20, true), (72, true), (53, true), (1542, false), (45, false), (52, true), (57, true)]
theorem step4243 (p : Nat → Bool) (h : Constraints p) : clause p c4243 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2984] c4243 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2984 p h) (sat_nil p)))
def c4244 : List Lit := [(54, true), (85, true), (53, true), (1494, false), (5, false), (72, true), (1542, false), (58, true)]
theorem step4244 (p : Nat → Bool) (h : Constraints p) : clause p c4244 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2822] c4244 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2822 p h) (sat_nil p)))
def c4245 : List Lit := [(69, true), (1545, false), (243, true), (57, true), (1513, false), (91, true), (90, false), (2, true), (93, false), (92, false), (277, true), (86, true), (52, true), (72, false)]
theorem step4245 (p : Nat → Bool) (h : Constraints p) : clause p c4245 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2157] c4245 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2157 p h) (sat_nil p)))
def c4246 : List Lit := [(2, false), (119, true), (58, false)]
theorem step4246 (p : Nat → Bool) (h : Constraints p) : clause p c4246 = true :=
  Snake9.LocalRup.prove_clause [c4067, c2218] c4246 (by decide) p (sat_cons (step4067 p h) (sat_cons (step2218 p h) (sat_nil p)))
def c4247 : List Lit := [(54, true), (48, true), (57, true), (72, true), (52, false), (90, true), (1542, false), (45, false), (58, true)]
theorem step4247 (p : Nat → Bool) (h : Constraints p) : clause p c4247 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2821] c4247 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2821 p h) (sat_nil p)))
def c4248 : List Lit := [(54, false), (48, true), (52, false), (90, true), (72, true), (57, false), (58, true), (45, false), (1542, false)]
theorem step4248 (p : Nat → Bool) (h : Constraints p) : clause p c4248 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2835] c4248 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2835 p h) (sat_nil p)))
def c4249 : List Lit := [(54, false), (1494, false), (72, true), (90, true), (58, true), (5, false), (1542, false), (53, true)]
theorem step4249 (p : Nat → Bool) (h : Constraints p) : clause p c4249 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2804] c4249 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2804 p h) (sat_nil p)))
def c4250 : List Lit := [(54, false), (1494, false), (63, true), (53, false), (5, false), (72, true), (58, true), (90, true)]
theorem step4250 (p : Nat → Bool) (h : Constraints p) : clause p c4250 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2810] c4250 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2810 p h) (sat_nil p)))
def c4251 : List Lit := [(1547, false), (48, true), (1643, false), (5, false), (54, false), (53, true), (1494, false), (1499, false), (1542, false), (72, false), (58, true), (52, true)]
theorem step4251 (p : Nat → Bool) (h : Constraints p) : clause p c4251 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2994] c4251 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2994 p h) (sat_nil p)))
def c4252 : List Lit := [(53, false), (46, true), (52, true), (54, false), (90, true), (1494, false), (48, true), (1544, false), (72, false), (57, true), (58, true), (1643, false), (45, false), (5, false)]
theorem step4252 (p : Nat → Bool) (h : Constraints p) : clause p c4252 = true :=
  Snake9.LocalRup.prove_clause [c4139, c3009] c4252 (by decide) p (sat_cons (step4139 p h) (sat_cons (step3009 p h) (sat_nil p)))
def c4253 : List Lit := [(1542, false), (52, true), (57, true), (58, true), (72, true), (45, true), (177, true)]
theorem step4253 (p : Nat → Bool) (h : Constraints p) : clause p c4253 = true :=
  Snake9.LocalRup.prove_clause [c4149, c4135, c2898] c4253 (by decide) p (sat_cons (step4149 p h) (sat_cons (step4135 p h) (sat_cons (step2898 p h) (sat_nil p))))
def c4254 : List Lit := [(68, true), (1514, false), (52, true), (1542, false), (57, false), (45, true), (58, true), (72, true)]
theorem step4254 (p : Nat → Bool) (h : Constraints p) : clause p c4254 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2906] c4254 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2906 p h) (sat_nil p)))
def c4255 : List Lit := [(48, true), (54, true), (57, true), (1489, false), (1504, true), (1533, true), (58, true)]
theorem step4255 (p : Nat → Bool) (h : Constraints p) : clause p c4255 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2820] c4255 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2820 p h) (sat_nil p)))
def c4256 : List Lit := [(48, true), (1542, false), (58, true), (54, true), (72, true), (57, false), (53, true), (68, true), (1643, false), (90, true), (45, false), (52, false)]
theorem step4256 (p : Nat → Bool) (h : Constraints p) : clause p c4256 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2840] c4256 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2840 p h) (sat_nil p)))
def c4257 : List Lit := [(3, false), (1643, false), (72, false), (90, true), (63, true), (57, false), (1514, false), (1542, false)]
theorem step4257 (p : Nat → Bool) (h : Constraints p) : clause p c4257 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3087] c4257 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3087 p h) (sat_nil p)))
def c4258 : List Lit := [(48, true), (1643, false), (52, true), (57, false), (1454, false), (72, true), (1542, false), (58, true), (45, true)]
theorem step4258 (p : Nat → Bool) (h : Constraints p) : clause p c4258 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2904] c4258 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2904 p h) (sat_nil p)))
def c4259 : List Lit := [(1643, false), (1542, false), (72, true), (1454, false), (1514, false)]
theorem step4259 (p : Nat → Bool) (h : Constraints p) : clause p c4259 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2539] c4259 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2539 p h) (sat_nil p)))
def c4260 : List Lit := [(48, true), (1542, false), (72, true), (1643, false), (1454, false), (58, true), (1487, false), (1493, false)]
theorem step4260 (p : Nat → Bool) (h : Constraints p) : clause p c4260 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2836] c4260 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2836 p h) (sat_nil p)))
def c4261 : List Lit := [(54, true), (68, true), (1643, false), (1544, false), (63, true), (1513, false), (1533, true), (72, true), (57, false), (58, true)]
theorem step4261 (p : Nat → Bool) (h : Constraints p) : clause p c4261 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2839] c4261 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2839 p h) (sat_nil p)))
def c4262 : List Lit := [(1494, false), (5, false), (53, true), (1643, false), (1542, false), (58, true), (72, true)]
theorem step4262 (p : Nat → Bool) (h : Constraints p) : clause p c4262 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2803] c4262 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2803 p h) (sat_nil p)))
def c4263 : List Lit := [(1514, false), (63, true), (57, false), (58, true), (72, true), (68, true), (90, false)]
theorem step4263 (p : Nat → Bool) (h : Constraints p) : clause p c4263 = true :=
  Snake9.LocalRup.prove_clause [c4135, c2843] c4263 (by decide) p (sat_cons (step4135 p h) (sat_cons (step2843 p h) (sat_nil p)))
def c4264 : List Lit := [(60, false), (243, true), (1514, false), (1542, false), (1495, false), (63, true), (57, true), (1643, false), (72, true), (45, true)]
theorem step4264 (p : Nat → Bool) (h : Constraints p) : clause p c4264 = true :=
  Snake9.LocalRup.prove_clause [c4149, c4135, c2913] c4264 (by decide) p (sat_cons (step4149 p h) (sat_cons (step4135 p h) (sat_cons (step2913 p h) (sat_nil p))))
def c4265 : List Lit := [(1542, false), (1514, false), (1454, false), (90, true), (72, true)]
theorem step4265 (p : Nat → Bool) (h : Constraints p) : clause p c4265 = true :=
  Snake9.LocalRup.prove_clause [c4139, c2698] c4265 (by decide) p (sat_cons (step4139 p h) (sat_cons (step2698 p h) (sat_nil p)))
def c4266 : List Lit := [(54, true), (1534, true), (66, false), (1454, false), (72, true), (68, true), (1643, false), (57, false), (1514, false), (58, true)]
theorem step4266 (p : Nat → Bool) (h : Constraints p) : clause p c4266 = true :=
  Snake9.LocalRup.prove_clause [c4136, c2668] c4266 (by decide) p (sat_cons (step4136 p h) (sat_cons (step2668 p h) (sat_nil p)))
def c4267 : List Lit := [(54, true), (66, false), (57, false), (68, true), (58, true), (1585, true), (1426, true), (72, true)]
theorem step4267 (p : Nat → Bool) (h : Constraints p) : clause p c4267 = true :=
  Snake9.LocalRup.prove_clause [c4136, c2520] c4267 (by decide) p (sat_cons (step4136 p h) (sat_cons (step2520 p h) (sat_nil p)))
def c4268 : List Lit := [(69, false), (119, true), (2, false), (86, false)]
theorem step4268 (p : Nat → Bool) (h : Constraints p) : clause p c4268 = true :=
  Snake9.LocalRup.prove_clause [c4067, c2209] c4268 (by decide) p (sat_cons (step4067 p h) (sat_cons (step2209 p h) (sat_nil p)))
def c4269 : List Lit := [(48, true), (1493, false), (1454, false), (1542, false), (90, true), (53, true), (72, true), (58, true), (57, false)]
theorem step4269 (p : Nat → Bool) (h : Constraints p) : clause p c4269 = true :=
  Snake9.LocalRup.prove_clause [c4139, c3045] c4269 (by decide) p (sat_cons (step4139 p h) (sat_cons (step3045 p h) (sat_nil p)))
def c4270 : List Lit := [(48, true), (1494, false), (1542, false), (72, true), (1643, false), (53, true), (58, true), (57, true)]
theorem step4270 (p : Nat → Bool) (h : Constraints p) : clause p c4270 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3217] c4270 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3217 p h) (sat_nil p)))
def c4271 : List Lit := [(3, false), (48, true), (57, true), (90, true), (58, true), (52, true), (53, true), (72, true), (1542, false)]
theorem step4271 (p : Nat → Bool) (h : Constraints p) : clause p c4271 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3236] c4271 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3236 p h) (sat_nil p)))
def c4272 : List Lit := [(48, true), (1426, true), (1454, false), (53, true), (1542, false), (1494, false), (57, true), (58, true), (52, true), (90, false), (72, true)]
theorem step4272 (p : Nat → Bool) (h : Constraints p) : clause p c4272 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3239] c4272 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3239 p h) (sat_nil p)))
def c4273 : List Lit := [(1446, false), (54, false), (1514, false), (1534, true), (63, true), (53, false), (72, true)]
theorem step4273 (p : Nat → Bool) (h : Constraints p) : clause p c4273 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3243] c4273 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3243 p h) (sat_nil p)))
def c4274 : List Lit := [(1446, false), (54, false), (1499, false), (48, true), (1542, false), (90, false), (1513, false), (53, false), (63, true), (72, true), (57, true), (58, true), (1494, false)]
theorem step4274 (p : Nat → Bool) (h : Constraints p) : clause p c4274 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3244] c4274 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3244 p h) (sat_nil p)))
def c4275 : List Lit := [(63, true), (48, true), (90, true), (72, true), (54, false), (57, false), (52, true), (58, true), (1542, false)]
theorem step4275 (p : Nat → Bool) (h : Constraints p) : clause p c4275 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3248] c4275 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3248 p h) (sat_nil p)))
def c4276 : List Lit := [(54, false), (1455, false), (90, false), (1542, false), (72, true), (57, false), (52, true), (58, true), (45, false), (48, true)]
theorem step4276 (p : Nat → Bool) (h : Constraints p) : clause p c4276 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3255] c4276 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3255 p h) (sat_nil p)))
def c4277 : List Lit := [(54, false), (2, false), (1425, true), (58, false), (72, true), (1542, false), (1662, true)]
theorem step4277 (p : Nat → Bool) (h : Constraints p) : clause p c4277 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3555] c4277 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3555 p h) (sat_nil p)))
def c4278 : List Lit := [(2, false), (1542, false), (1514, false), (58, false), (72, true), (90, true)]
theorem step4278 (p : Nat → Bool) (h : Constraints p) : clause p c4278 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3602] c4278 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3602 p h) (sat_nil p)))
def c4279 : List Lit := [(2, false), (1542, false), (72, true), (1514, false), (1643, false), (58, false)]
theorem step4279 (p : Nat → Bool) (h : Constraints p) : clause p c4279 = true :=
  Snake9.LocalRup.prove_clause [c4137, c3603] c4279 (by decide) p (sat_cons (step4137 p h) (sat_cons (step3603 p h) (sat_nil p)))
def c4280 : List Lit := [(1542, false), (3, true), (57, false), (58, false), (52, true), (45, true), (1643, false), (2, false)]
theorem step4280 (p : Nat → Bool) (h : Constraints p) : clause p c4280 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3611] c4280 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3611 p h) (sat_nil p)))
def c4281 : List Lit := [(48, true), (1643, false), (72, true), (1454, false), (58, true), (52, false), (57, true), (1542, false), (45, false)]
theorem step4281 (p : Nat → Bool) (h : Constraints p) : clause p c4281 = true :=
  Snake9.LocalRup.prove_clause [c4139, c3684] c4281 (by decide) p (sat_cons (step4139 p h) (sat_cons (step3684 p h) (sat_nil p)))
def c4282 : List Lit := [(66, false), (1542, false), (52, false), (90, true), (48, true), (57, true), (72, true), (1454, false), (58, true), (45, false)]
theorem step4282 (p : Nat → Bool) (h : Constraints p) : clause p c4282 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3685] c4282 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3685 p h) (sat_nil p)))
def c4283 : List Lit := [(5, true), (48, true), (58, true), (1534, true), (1489, false), (52, true), (57, true)]
theorem step4283 (p : Nat → Bool) (h : Constraints p) : clause p c4283 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3707] c4283 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3707 p h) (sat_nil p)))
def c4284 : List Lit := [(1599, false), (5, false), (1643, false), (53, true), (63, true), (72, true), (57, true), (52, true), (58, true), (48, true)]
theorem step4284 (p : Nat → Bool) (h : Constraints p) : clause p c4284 = true :=
  Snake9.LocalRup.prove_clause [c4137, c3735] c4284 (by decide) p (sat_cons (step4137 p h) (sat_cons (step3735 p h) (sat_nil p)))
def c4285 : List Lit := [(48, false), (1454, false), (58, true), (90, true), (72, true), (57, true), (45, false)]
theorem step4285 (p : Nat → Bool) (h : Constraints p) : clause p c4285 = true :=
  Snake9.LocalRup.prove_clause [c4139, c3757] c4285 (by decide) p (sat_cons (step4139 p h) (sat_cons (step3757 p h) (sat_nil p)))
def c4286 : List Lit := [(48, true), (1569, false), (1542, false), (1643, false), (1664, true), (72, true), (57, true), (52, true), (58, true)]
theorem step4286 (p : Nat → Bool) (h : Constraints p) : clause p c4286 = true :=
  Snake9.LocalRup.prove_clause [c4139, c3762] c4286 (by decide) p (sat_cons (step4139 p h) (sat_cons (step3762 p h) (sat_nil p)))
def c4287 : List Lit := [(95, true), (48, true), (63, true), (86, true), (5, false), (90, false), (72, true), (1664, true), (57, true), (52, true), (58, true)]
theorem step4287 (p : Nat → Bool) (h : Constraints p) : clause p c4287 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3765] c4287 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3765 p h) (sat_nil p)))
def c4288 : List Lit := [(5, true), (46, true), (90, false), (72, true), (63, true), (52, true), (57, true), (58, true), (15, true), (45, false), (2, false)]
theorem step4288 (p : Nat → Bool) (h : Constraints p) : clause p c4288 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3767] c4288 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3767 p h) (sat_nil p)))
def c4289 : List Lit := [(58, true), (45, false), (170, true), (1493, false), (48, true), (72, true), (1542, false), (52, true), (1642, false), (1643, false), (57, false)]
theorem step4289 (p : Nat → Bool) (h : Constraints p) : clause p c4289 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3797] c4289 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3797 p h) (sat_nil p)))
def c4290 : List Lit := [(1446, false), (54, false), (1534, true), (1454, false), (2, false), (1542, false), (72, true), (58, false), (1514, false)]
theorem step4290 (p : Nat → Bool) (h : Constraints p) : clause p c4290 = true :=
  Snake9.LocalRup.prove_clause [c4135, c3841] c4290 (by decide) p (sat_cons (step4135 p h) (sat_cons (step3841 p h) (sat_nil p)))
end B112E207
