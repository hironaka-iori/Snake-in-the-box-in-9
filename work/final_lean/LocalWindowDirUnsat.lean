import LocalWindowDirSat
import LocalWindowUnsat.D012A11
import LocalWindowUnsat.D012A12
import LocalWindowUnsat.D012A13
import LocalWindowUnsat.D0120A122
import LocalWindowUnsat.D0120A123
import LocalWindowUnsat.D0120A132
import LocalWindowUnsat.D0120A133
import LocalWindowUnsat.D0120A141
import LocalWindowUnsat.D0120A142
import LocalWindowUnsat.D0120A143
import LocalWindowUnsat.D0120A144
import LocalWindowUnsat.D0120A145
import LocalWindowUnsat.D0120A151
import LocalWindowUnsat.D0120A152
import LocalWindowUnsat.D0120A153
import LocalWindowUnsat.D0120A154
import LocalWindowUnsat.D0120A161
import LocalWindowUnsat.D0120A162
import LocalWindowUnsat.D0120A222
import LocalWindowUnsat.D0120A223
import LocalWindowUnsat.D0120A224
import LocalWindowUnsat.D0120A225
import LocalWindowUnsat.D0120A232
import LocalWindowUnsat.D0120A233
import LocalWindowUnsat.D0120A234
import LocalWindowUnsat.D0120A235
import LocalWindowUnsat.D0120A242
import LocalWindowUnsat.D0120A243
import LocalWindowUnsat.D0120A244
import LocalWindowUnsat.D0120A252
import LocalWindowUnsat.D0120A253
import LocalWindowUnsat.D0120A323
import LocalWindowUnsat.D0120A324
import LocalWindowUnsat.D0120A325
import LocalWindowUnsat.D0120A333
import LocalWindowUnsat.D0120A334
import LocalWindowUnsat.D0120A343
import LocalWindowUnsat.D0120A414
import LocalWindowUnsat.D0120A415
import LocalWindowUnsat.D0120A424
import LocalWindowUnsat.D0120A515
import LocalWindowUnsat.D0120A516
import LocalWindowUnsat.D0123A122
import LocalWindowUnsat.D0123A123
import LocalWindowUnsat.D0123A132
import LocalWindowUnsat.D0123A133
import LocalWindowUnsat.D0123A141
import LocalWindowUnsat.D0123A142
import LocalWindowUnsat.D0123A143
import LocalWindowUnsat.D0123A144
import LocalWindowUnsat.D0123A145
import LocalWindowUnsat.D0123A151
import LocalWindowUnsat.D0123A222
import LocalWindowUnsat.D0123A223
import LocalWindowUnsat.D0123A224
import LocalWindowUnsat.D0123A232
import LocalWindowUnsat.D0123A323
import LocalWindowUnsat.D0123A414
import LocalWindowUnsat.D0123A415
import LocalWindowUnsat.D01203A3351
import LocalWindowUnsat.D01203A3442
import LocalWindowUnsat.D01203A3443
import LocalWindowUnsat.D01203A4251
import LocalWindowUnsat.D01203A4342
import LocalWindowUnsat.D01203A4343
import LocalWindowUnsat.D01203A4351
import LocalWindowUnsat.D01203A4432
import LocalWindowUnsat.D01203A4522
import LocalWindowUnsat.D01203A5242
import LocalWindowUnsat.D01203A5251
import LocalWindowUnsat.D01203A5332
import LocalWindowUnsat.D01203A5351
import LocalWindowUnsat.D01203A6152
import LocalWindowUnsat.D01203A6251
import LocalWindowUnsat.D01203A6332
import LocalWindowUnsat.D01230A1522
import LocalWindowUnsat.D01230A1523
import LocalWindowUnsat.D01230A1524
import LocalWindowUnsat.D01230A1532
import LocalWindowUnsat.D01230A1533
import LocalWindowUnsat.D01230A2252
import LocalWindowUnsat.D01230A2253
import LocalWindowUnsat.D01230A2254
import LocalWindowUnsat.D01230A2332
import LocalWindowUnsat.D01230A2333
import LocalWindowUnsat.D01230A2334
import LocalWindowUnsat.D01230A2335
import LocalWindowUnsat.D01230A2342
import LocalWindowUnsat.D01230A2423
import LocalWindowUnsat.D01230A2424
import LocalWindowUnsat.D01230A2515
import LocalWindowUnsat.D01230A2516
import LocalWindowUnsat.D01230A3243
import LocalWindowUnsat.D01230A3324
import LocalWindowUnsat.D01230A3325
import LocalWindowUnsat.D01230A3326
import LocalWindowUnsat.D01234A1522
import LocalWindowUnsat.D01234A1523
import LocalWindowUnsat.D01234A1524
import LocalWindowUnsat.D01234A1525
import LocalWindowUnsat.D01234A1526
import LocalWindowUnsat.D01234A1532
import LocalWindowUnsat.D01234A1533
import LocalWindowUnsat.D01234A1534
import LocalWindowUnsat.D01234A2252
import LocalWindowUnsat.D01234A2253
import LocalWindowUnsat.D01234A2254
import LocalWindowUnsat.D01234A2332
import LocalWindowUnsat.D01234A2333
import LocalWindowUnsat.D01234A2334
import LocalWindowUnsat.D01234A2335
import LocalWindowUnsat.D01234A2342
import LocalWindowUnsat.D01234A2343
import LocalWindowUnsat.D01234A2344
import LocalWindowUnsat.D01234A2423
import LocalWindowUnsat.D01234A2424
import LocalWindowUnsat.D01234A2425
import LocalWindowUnsat.D01234A2426
import LocalWindowUnsat.D01234A2433
import LocalWindowUnsat.D01234A2434
import LocalWindowUnsat.D01234A2435
import LocalWindowUnsat.D01234A2442
import LocalWindowUnsat.D01234A2443
import LocalWindowUnsat.D01234A2515
import LocalWindowUnsat.D01234A2516
import LocalWindowUnsat.D01234A2523
import LocalWindowUnsat.D01234A2524
import LocalWindowUnsat.D01234A3243
import LocalWindowUnsat.D01234A3244
import LocalWindowUnsat.D01234A3253
import LocalWindowUnsat.D01234A3324
import LocalWindowUnsat.D01234A3325
import LocalWindowUnsat.D01234A3333
import LocalWindowUnsat.D01234A3334
import LocalWindowUnsat.D01234A3343
import LocalWindowUnsat.D01234A3344
import LocalWindowUnsat.D01234A3424
import LocalWindowUnsat.D01234A3434
import LocalWindowUnsat.D01234A3515
import LocalWindowUnsat.D01234A3516
import LocalWindowUnsat.D01234A3524
import LocalWindowUnsat.D01234A4234
import LocalWindowUnsat.D01234A4244
import LocalWindowUnsat.D01234A4325
import LocalWindowUnsat.D01234A4334

/-!
# The 145 direction-window refutations

Combines the kernel-checked LRAT refutations `LocalWindowUnsat.D*` (generated by
`milestones/10-window-aggregate/scripts/run_direction_replays.py`, not committed) with the
`sat` theorems into `AllRefuted239`, the premise of `upper_239_of_refuted`.
-/

namespace Snake9.LocalWindow

theorem allUnsat239 : AllUnsat239 :=
  ⟨D012A11.unsat,
   D012A12.unsat,
   D012A13.unsat,
   D0120A122.unsat,
   D0120A123.unsat,
   D0120A132.unsat,
   D0120A133.unsat,
   D0120A141.unsat,
   D0120A142.unsat,
   D0120A143.unsat,
   D0120A144.unsat,
   D0120A145.unsat,
   D0120A151.unsat,
   D0120A152.unsat,
   D0120A153.unsat,
   D0120A154.unsat,
   D0120A161.unsat,
   D0120A162.unsat,
   D0120A222.unsat,
   D0120A223.unsat,
   D0120A224.unsat,
   D0120A225.unsat,
   D0120A232.unsat,
   D0120A233.unsat,
   D0120A234.unsat,
   D0120A235.unsat,
   D0120A242.unsat,
   D0120A243.unsat,
   D0120A244.unsat,
   D0120A252.unsat,
   D0120A253.unsat,
   D0120A323.unsat,
   D0120A324.unsat,
   D0120A325.unsat,
   D0120A333.unsat,
   D0120A334.unsat,
   D0120A343.unsat,
   D0120A414.unsat,
   D0120A415.unsat,
   D0120A424.unsat,
   D0120A515.unsat,
   D0120A516.unsat,
   D0123A122.unsat,
   D0123A123.unsat,
   D0123A132.unsat,
   D0123A133.unsat,
   D0123A141.unsat,
   D0123A142.unsat,
   D0123A143.unsat,
   D0123A144.unsat,
   D0123A145.unsat,
   D0123A151.unsat,
   D0123A222.unsat,
   D0123A223.unsat,
   D0123A224.unsat,
   D0123A232.unsat,
   D0123A323.unsat,
   D0123A414.unsat,
   D0123A415.unsat,
   D01203A3351.unsat,
   D01203A3442.unsat,
   D01203A3443.unsat,
   D01203A4251.unsat,
   D01203A4342.unsat,
   D01203A4343.unsat,
   D01203A4351.unsat,
   D01203A4432.unsat,
   D01203A4522.unsat,
   D01203A5242.unsat,
   D01203A5251.unsat,
   D01203A5332.unsat,
   D01203A5351.unsat,
   D01203A6152.unsat,
   D01203A6251.unsat,
   D01203A6332.unsat,
   D01230A1522.unsat,
   D01230A1523.unsat,
   D01230A1524.unsat,
   D01230A1532.unsat,
   D01230A1533.unsat,
   D01230A2252.unsat,
   D01230A2253.unsat,
   D01230A2254.unsat,
   D01230A2332.unsat,
   D01230A2333.unsat,
   D01230A2334.unsat,
   D01230A2335.unsat,
   D01230A2342.unsat,
   D01230A2423.unsat,
   D01230A2424.unsat,
   D01230A2515.unsat,
   D01230A2516.unsat,
   D01230A3243.unsat,
   D01230A3324.unsat,
   D01230A3325.unsat,
   D01230A3326.unsat,
   D01234A1522.unsat,
   D01234A1523.unsat,
   D01234A1524.unsat,
   D01234A1525.unsat,
   D01234A1526.unsat,
   D01234A1532.unsat,
   D01234A1533.unsat,
   D01234A1534.unsat,
   D01234A2252.unsat,
   D01234A2253.unsat,
   D01234A2254.unsat,
   D01234A2332.unsat,
   D01234A2333.unsat,
   D01234A2334.unsat,
   D01234A2335.unsat,
   D01234A2342.unsat,
   D01234A2343.unsat,
   D01234A2344.unsat,
   D01234A2423.unsat,
   D01234A2424.unsat,
   D01234A2425.unsat,
   D01234A2426.unsat,
   D01234A2433.unsat,
   D01234A2434.unsat,
   D01234A2435.unsat,
   D01234A2442.unsat,
   D01234A2443.unsat,
   D01234A2515.unsat,
   D01234A2516.unsat,
   D01234A2523.unsat,
   D01234A2524.unsat,
   D01234A3243.unsat,
   D01234A3244.unsat,
   D01234A3253.unsat,
   D01234A3324.unsat,
   D01234A3325.unsat,
   D01234A3333.unsat,
   D01234A3334.unsat,
   D01234A3343.unsat,
   D01234A3344.unsat,
   D01234A3424.unsat,
   D01234A3434.unsat,
   D01234A3515.unsat,
   D01234A3516.unsat,
   D01234A3524.unsat,
   D01234A4234.unsat,
   D01234A4244.unsat,
   D01234A4325.unsat,
   D01234A4334.unsat⟩

theorem allRefuted239 : AllRefuted239 := allRefuted239_of_unsat allUnsat239

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefuted239
