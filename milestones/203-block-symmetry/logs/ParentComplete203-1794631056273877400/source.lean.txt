import ParentRows203_0
import ParentRows203_1
import ParentRows203_2
import ParentRows203_3
import ParentRows203_4
import ParentRows203_5
import ParentRows203_6
import ParentRows203_7
import ParentRows203_8
import ParentRows203_9
import ParentRows203_10
import ParentRows203_11
import ParentRows203_12
import ParentRows203_13
import ParentRows203_14
import ParentRows203_15
import ParentRows203_16
import ParentRows203_17
import ParentRows203_18
import ParentRows203_19
import ParentRows203_20
import ParentRows203_21
import ParentRows203_22
import ParentRows203_23
import ParentRows203_24
import ParentRows203_25
import ParentRows203_26
import ParentRows203_27
import ParentRows203_28
import ParentRows203_29
import ParentRows203_30
import ParentRows203_31
import ParentRows203_32
import ParentRows203_33
import ParentRows203_34
import ParentRows203_35
import ParentRows203_36
import ParentRows203_37
import ParentRows203_38
import ParentRows203_39
import ParentRows203_40
import ParentRows203_41
import ParentRows203_42
import ParentRows203_43
import ParentRows203_44
import ParentRows203_45
import ParentRows203_46
import ParentRows203_47
import ParentRows203_48
import ParentRows203_49
import ParentRows203_50
namespace ParentComplete203
open ParentData203
theorem allPairs (i j : Fin 51) : pairProperty i.val j.val := by
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · have h := ParentRows203_0.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h0] using h
  by_cases h1 : i.val = 1
  · have h := ParentRows203_1.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h1] using h
  by_cases h2 : i.val = 2
  · have h := ParentRows203_2.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h2] using h
  by_cases h3 : i.val = 3
  · have h := ParentRows203_3.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h3] using h
  by_cases h4 : i.val = 4
  · have h := ParentRows203_4.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h4] using h
  by_cases h5 : i.val = 5
  · have h := ParentRows203_5.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h5] using h
  by_cases h6 : i.val = 6
  · have h := ParentRows203_6.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h6] using h
  by_cases h7 : i.val = 7
  · have h := ParentRows203_7.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h7] using h
  by_cases h8 : i.val = 8
  · have h := ParentRows203_8.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h8] using h
  by_cases h9 : i.val = 9
  · have h := ParentRows203_9.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h9] using h
  by_cases h10 : i.val = 10
  · have h := ParentRows203_10.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h10] using h
  by_cases h11 : i.val = 11
  · have h := ParentRows203_11.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h11] using h
  by_cases h12 : i.val = 12
  · have h := ParentRows203_12.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h12] using h
  by_cases h13 : i.val = 13
  · have h := ParentRows203_13.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h13] using h
  by_cases h14 : i.val = 14
  · have h := ParentRows203_14.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h14] using h
  by_cases h15 : i.val = 15
  · have h := ParentRows203_15.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h15] using h
  by_cases h16 : i.val = 16
  · have h := ParentRows203_16.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h16] using h
  by_cases h17 : i.val = 17
  · have h := ParentRows203_17.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h17] using h
  by_cases h18 : i.val = 18
  · have h := ParentRows203_18.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h18] using h
  by_cases h19 : i.val = 19
  · have h := ParentRows203_19.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h19] using h
  by_cases h20 : i.val = 20
  · have h := ParentRows203_20.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h20] using h
  by_cases h21 : i.val = 21
  · have h := ParentRows203_21.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h21] using h
  by_cases h22 : i.val = 22
  · have h := ParentRows203_22.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h22] using h
  by_cases h23 : i.val = 23
  · have h := ParentRows203_23.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h23] using h
  by_cases h24 : i.val = 24
  · have h := ParentRows203_24.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h24] using h
  by_cases h25 : i.val = 25
  · have h := ParentRows203_25.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h25] using h
  by_cases h26 : i.val = 26
  · have h := ParentRows203_26.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h26] using h
  by_cases h27 : i.val = 27
  · have h := ParentRows203_27.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h27] using h
  by_cases h28 : i.val = 28
  · have h := ParentRows203_28.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h28] using h
  by_cases h29 : i.val = 29
  · have h := ParentRows203_29.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h29] using h
  by_cases h30 : i.val = 30
  · have h := ParentRows203_30.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h30] using h
  by_cases h31 : i.val = 31
  · have h := ParentRows203_31.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h31] using h
  by_cases h32 : i.val = 32
  · have h := ParentRows203_32.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h32] using h
  by_cases h33 : i.val = 33
  · have h := ParentRows203_33.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h33] using h
  by_cases h34 : i.val = 34
  · have h := ParentRows203_34.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h34] using h
  by_cases h35 : i.val = 35
  · have h := ParentRows203_35.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h35] using h
  by_cases h36 : i.val = 36
  · have h := ParentRows203_36.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h36] using h
  by_cases h37 : i.val = 37
  · have h := ParentRows203_37.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h37] using h
  by_cases h38 : i.val = 38
  · have h := ParentRows203_38.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h38] using h
  by_cases h39 : i.val = 39
  · have h := ParentRows203_39.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h39] using h
  by_cases h40 : i.val = 40
  · have h := ParentRows203_40.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h40] using h
  by_cases h41 : i.val = 41
  · have h := ParentRows203_41.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h41] using h
  by_cases h42 : i.val = 42
  · have h := ParentRows203_42.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h42] using h
  by_cases h43 : i.val = 43
  · have h := ParentRows203_43.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h43] using h
  by_cases h44 : i.val = 44
  · have h := ParentRows203_44.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h44] using h
  by_cases h45 : i.val = 45
  · have h := ParentRows203_45.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h45] using h
  by_cases h46 : i.val = 46
  · have h := ParentRows203_46.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h46] using h
  by_cases h47 : i.val = 47
  · have h := ParentRows203_47.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h47] using h
  by_cases h48 : i.val = 48
  · have h := ParentRows203_48.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h48] using h
  by_cases h49 : i.val = 49
  · have h := ParentRows203_49.rows ⟨0,by omega⟩ j (by omega)
    simpa only [Fin.val_mk,Nat.zero_add,h49] using h
  have h50 : i.val=50 := by omega
  have h := ParentRows203_50.rows ⟨0,by omega⟩ j (by omega)
  simpa only [Fin.val_mk,Nat.zero_add,h50] using h
#print axioms allPairs
end ParentComplete203
