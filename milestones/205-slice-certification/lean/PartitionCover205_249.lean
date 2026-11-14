import FiniteDomain205
namespace PartitionCover205_249
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[1]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[1]
def r5 : Array Nat := #[1]
def r6 : Array Nat := #[1]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[1]
def r9 : Array Nat := #[1]
def r10 : Array Nat := #[1]
def r11 : Array Nat := #[1]
def r12 : Array Nat := #[1]
def r13 : Array Nat := #[1]
def r14 : Array Nat := #[1]
def r15 : Array Nat := #[1]
def r16 : Array Nat := #[1]
def r17 : Array Nat := #[1]
def r18 : Array Nat := #[1]
def r19 : Array Nat := #[1]
def r20 : Array Nat := #[1]
def r21 : Array Nat := #[1]
def r22 : Array Nat := #[1]
def r23 : Array Nat := #[1]
def r24 : Array Nat := #[1]
def r25 : Array Nat := #[1]
def r26 : Array Nat := #[1]
def r27 : Array Nat := #[1]
def r28 : Array Nat := #[1]
def r29 : Array Nat := #[1]
def r30 : Array Nat := #[1]
def r31 : Array Nat := #[1]
def r32 : Array Nat := #[1]
def r33 : Array Nat := #[1]
def r34 : Array Nat := #[1]
def r35 : Array Nat := #[1]
def r36 : Array Nat := #[1]
def r37 : Array Nat := #[1]
def r38 : Array Nat := #[1]
def r39 : Array Nat := #[1]
def r40 : Array Nat := #[1]
def r41 : Array Nat := #[1]
def r42 : Array Nat := #[1]
def r43 : Array Nat := #[1]
def r44 : Array Nat := #[1]
def r45 : Array Nat := #[1]
def r46 : Array Nat := #[1]
def r47 : Array Nat := #[1]
def r48 : Array Nat := #[1]
def r49 : Array Nat := #[1]
def r50 : Array Nat := #[1]
def r51 : Array Nat := #[1]
def r52 : Array Nat := #[1]
def r53 : Array Nat := #[1]
def r54 : Array Nat := #[1]
def r55 : Array Nat := #[1]
def r56 : Array Nat := #[1]
def r57 : Array Nat := #[1]
def r58 : Array Nat := #[1]
def r59 : Array Nat := #[1]
def r60 : Array Nat := #[1]
def r61 : Array Nat := #[1]
def r62 : Array Nat := #[1]
def r63 : Array Nat := #[1]
def r64 : Array Nat := #[1]
def r65 : Array Nat := #[1]
def r66 : Array Nat := #[1]
def r67 : Array Nat := #[1]
def r68 : Array Nat := #[1]
def r69 : Array Nat := #[1]
def r70 : Array Nat := #[1]
def r71 : Array Nat := #[1]
def r72 : Array Nat := #[1]
def r73 : Array Nat := #[1]
def r74 : Array Nat := #[1]
def r75 : Array Nat := #[1]
def r76 : Array Nat := #[1]
def r77 : Array Nat := #[1]
def r78 : Array Nat := #[1]
def r79 : Array Nat := #[1]
def r80 : Array Nat := #[1]
def r81 : Array Nat := #[1]
def r82 : Array Nat := #[1]
def r83 : Array Nat := #[1]
def r84 : Array Nat := #[1]
def r85 : Array Nat := #[1]
def r86 : Array Nat := #[1]
def r87 : Array Nat := #[1]
def r88 : Array Nat := #[1]
def r89 : Array Nat := #[1]
def r90 : Array Nat := #[1]
def r91 : Array Nat := #[1]
def r92 : Array Nat := #[1]
def r93 : Array Nat := #[1]
def r94 : Array Nat := #[1]
def r95 : Array Nat := #[1]
def r96 : Array Nat := #[1]
def r97 : Array Nat := #[1]
def r98 : Array Nat := #[1]
def r99 : Array Nat := #[1]
def r100 : Array Nat := #[1]
def r101 : Array Nat := #[1]
def r102 : Array Nat := #[1]
def r103 : Array Nat := #[1]
def r104 : Array Nat := #[1]
def r105 : Array Nat := #[1]
def r106 : Array Nat := #[1]
def r107 : Array Nat := #[1]
def r108 : Array Nat := #[1]
def r109 : Array Nat := #[1]
def r110 : Array Nat := #[1]
def r111 : Array Nat := #[1]
def r112 : Array Nat := #[1]
def r113 : Array Nat := #[1]
def r114 : Array Nat := #[1]
def r115 : Array Nat := #[1]
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0])
    (start5 : a 5 ∈ [0])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0])
    (start8 : a 8 ∈ [0])
    (start9 : a 9 ∈ [0])
    (start10 : a 10 ∈ [0])
    (start11 : a 11 ∈ [0])
    (start12 : a 12 ∈ [0])
    (start13 : a 13 ∈ [0])
    (start14 : a 14 ∈ [0])
    (start15 : a 15 ∈ [0])
    (start16 : a 16 ∈ [0])
    (start17 : a 17 ∈ [0])
    (start18 : a 18 ∈ [0])
    (start19 : a 19 ∈ [0])
    (start20 : a 20 ∈ [0])
    (start21 : a 21 ∈ [0])
    (start22 : a 22 ∈ [0])
    (start23 : a 23 ∈ [0])
    (start24 : a 24 ∈ [0])
    (start25 : a 25 ∈ [0])
    (start26 : a 26 ∈ [0])
    (start27 : a 27 ∈ [0])
    (start28 : a 28 ∈ [0])
    (start29 : a 29 ∈ [0])
    (start30 : a 30 ∈ [0])
    (start31 : a 31 ∈ [0])
    (start32 : a 32 ∈ [0])
    (start33 : a 33 ∈ [0])
    (start34 : a 34 ∈ [0])
    (start35 : a 35 ∈ [0])
    (start36 : a 36 ∈ [0])
    (start37 : a 37 ∈ [0])
    (start38 : a 38 ∈ [0])
    (start39 : a 39 ∈ [0])
    (start40 : a 40 ∈ [0])
    (start41 : a 41 ∈ [0])
    (start42 : a 42 ∈ [0])
    (start43 : a 43 ∈ [0])
    (start44 : a 44 ∈ [0])
    (start45 : a 45 ∈ [0])
    (start46 : a 46 ∈ [0])
    (start47 : a 47 ∈ [0])
    (start48 : a 48 ∈ [0])
    (start49 : a 49 ∈ [0])
    (start50 : a 50 ∈ [0])
    (start51 : a 51 ∈ [0])
    (start52 : a 52 ∈ [0])
    (start53 : a 53 ∈ [0])
    (start54 : a 54 ∈ [0])
    (start55 : a 55 ∈ [0])
    (start56 : a 56 ∈ [0])
    (start57 : a 57 ∈ [0])
    (start58 : a 58 ∈ [0])
    (start59 : a 59 ∈ [0])
    (start60 : a 60 ∈ [0])
    (start61 : a 61 ∈ [0])
    (start62 : a 62 ∈ [0])
    (start63 : a 63 ∈ [0])
    (start64 : a 64 ∈ [0])
    (start65 : a 65 ∈ [0])
    (start66 : a 66 ∈ [0])
    (start67 : a 67 ∈ [0])
    (start68 : a 68 ∈ [0])
    (start69 : a 69 ∈ [0])
    (start70 : a 70 ∈ [0])
    (start71 : a 71 ∈ [0])
    (start72 : a 72 ∈ [0])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 19)=true)
    (c3 : edge r3 (a 1) (a 3)=true)
    (c4 : edge r4 (a 1) (a 4)=true)
    (c5 : edge r5 (a 1) (a 10)=true)
    (c6 : edge r6 (a 2) (a 3)=true)
    (c7 : edge r7 (a 2) (a 11)=true)
    (c8 : edge r8 (a 2) (a 20)=true)
    (c9 : edge r9 (a 3) (a 5)=true)
    (c10 : edge r10 (a 4) (a 5)=true)
    (c11 : edge r11 (a 4) (a 7)=true)
    (c12 : edge r12 (a 4) (a 22)=true)
    (c13 : edge r13 (a 4) (a 39)=true)
    (c14 : edge r14 (a 5) (a 9)=true)
    (c15 : edge r15 (a 5) (a 14)=true)
    (c16 : edge r16 (a 6) (a 7)=true)
    (c17 : edge r17 (a 6) (a 8)=true)
    (c18 : edge r18 (a 7) (a 9)=true)
    (c19 : edge r19 (a 8) (a 9)=true)
    (c20 : edge r20 (a 8) (a 18)=true)
    (c21 : edge r21 (a 8) (a 27)=true)
    (c22 : edge r22 (a 9) (a 28)=true)
    (c23 : edge r23 (a 10) (a 16)=true)
    (c24 : edge r24 (a 10) (a 30)=true)
    (c25 : edge r25 (a 10) (a 46)=true)
    (c26 : edge r26 (a 11) (a 13)=true)
    (c27 : edge r27 (a 11) (a 31)=true)
    (c28 : edge r28 (a 11) (a 47)=true)
    (c29 : edge r29 (a 12) (a 13)=true)
    (c30 : edge r30 (a 12) (a 32)=true)
    (c31 : edge r31 (a 13) (a 14)=true)
    (c32 : edge r32 (a 13) (a 18)=true)
    (c33 : edge r33 (a 14) (a 33)=true)
    (c34 : edge r34 (a 14) (a 48)=true)
    (c35 : edge r35 (a 15) (a 16)=true)
    (c36 : edge r36 (a 15) (a 49)=true)
    (c37 : edge r37 (a 16) (a 17)=true)
    (c38 : edge r38 (a 17) (a 50)=true)
    (c39 : edge r39 (a 19) (a 20)=true)
    (c40 : edge r40 (a 19) (a 21)=true)
    (c41 : edge r41 (a 19) (a 24)=true)
    (c42 : edge r42 (a 19) (a 29)=true)
    (c43 : edge r43 (a 19) (a 54)=true)
    (c44 : edge r44 (a 20) (a 23)=true)
    (c45 : edge r45 (a 20) (a 31)=true)
    (c46 : edge r46 (a 20) (a 56)=true)
    (c47 : edge r47 (a 21) (a 22)=true)
    (c48 : edge r48 (a 21) (a 23)=true)
    (c49 : edge r49 (a 21) (a 32)=true)
    (c50 : edge r50 (a 21) (a 58)=true)
    (c51 : edge r51 (a 23) (a 27)=true)
    (c52 : edge r52 (a 23) (a 59)=true)
    (c53 : edge r53 (a 24) (a 25)=true)
    (c54 : edge r54 (a 25) (a 26)=true)
    (c55 : edge r55 (a 26) (a 28)=true)
    (c56 : edge r56 (a 27) (a 28)=true)
    (c57 : edge r57 (a 28) (a 37)=true)
    (c58 : edge r58 (a 28) (a 63)=true)
    (c59 : edge r59 (a 29) (a 30)=true)
    (c60 : edge r60 (a 29) (a 31)=true)
    (c61 : edge r61 (a 29) (a 32)=true)
    (c62 : edge r62 (a 31) (a 34)=true)
    (c63 : edge r63 (a 32) (a 35)=true)
    (c64 : edge r64 (a 32) (a 65)=true)
    (c65 : edge r65 (a 33) (a 37)=true)
    (c66 : edge r66 (a 34) (a 69)=true)
    (c67 : edge r67 (a 35) (a 36)=true)
    (c68 : edge r68 (a 36) (a 37)=true)
    (c69 : edge r69 (a 36) (a 71)=true)
    (c70 : edge r70 (a 38) (a 39)=true)
    (c71 : edge r71 (a 38) (a 40)=true)
    (c72 : edge r72 (a 38) (a 58)=true)
    (c73 : edge r73 (a 40) (a 59)=true)
    (c74 : edge r74 (a 41) (a 42)=true)
    (c75 : edge r75 (a 41) (a 43)=true)
    (c76 : edge r76 (a 41) (a 49)=true)
    (c77 : edge r77 (a 42) (a 44)=true)
    (c78 : edge r78 (a 43) (a 44)=true)
    (c79 : edge r79 (a 43) (a 60)=true)
    (c80 : edge r80 (a 44) (a 50)=true)
    (c81 : edge r81 (a 45) (a 46)=true)
    (c82 : edge r82 (a 45) (a 47)=true)
    (c83 : edge r83 (a 45) (a 49)=true)
    (c84 : edge r84 (a 48) (a 53)=true)
    (c85 : edge r85 (a 49) (a 51)=true)
    (c86 : edge r86 (a 50) (a 53)=true)
    (c87 : edge r87 (a 50) (a 70)=true)
    (c88 : edge r88 (a 51) (a 52)=true)
    (c89 : edge r89 (a 52) (a 53)=true)
    (c90 : edge r90 (a 52) (a 71)=true)
    (c91 : edge r91 (a 54) (a 55)=true)
    (c92 : edge r92 (a 54) (a 56)=true)
    (c93 : edge r93 (a 54) (a 58)=true)
    (c94 : edge r94 (a 55) (a 57)=true)
    (c95 : edge r95 (a 56) (a 57)=true)
    (c96 : edge r96 (a 56) (a 59)=true)
    (c97 : edge r97 (a 56) (a 60)=true)
    (c98 : edge r98 (a 57) (a 64)=true)
    (c99 : edge r99 (a 58) (a 59)=true)
    (c100 : edge r100 (a 58) (a 61)=true)
    (c101 : edge r101 (a 58) (a 65)=true)
    (c102 : edge r102 (a 59) (a 67)=true)
    (c103 : edge r103 (a 60) (a 69)=true)
    (c104 : edge r104 (a 61) (a 62)=true)
    (c105 : edge r105 (a 62) (a 63)=true)
    (c106 : edge r106 (a 62) (a 71)=true)
    (c107 : edge r107 (a 64) (a 70)=true)
    (c108 : edge r108 (a 65) (a 66)=true)
    (c109 : edge r109 (a 65) (a 67)=true)
    (c110 : edge r110 (a 66) (a 71)=true)
    (c111 : edge r111 (a 67) (a 72)=true)
    (c112 : edge r112 (a 68) (a 70)=true)
    (c113 : edge r113 (a 68) (a 71)=true)
    (c114 : edge r114 (a 69) (a 70)=true)
    (c115 : edge r115 (a 69) (a 72)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0 ∧ a 32=0 ∧ a 33=0 ∧ a 34=0 ∧ a 35=0 ∧ a 36=0 ∧ a 37=0 ∧ a 38=0 ∧ a 39=0 ∧ a 40=0 ∧ a 41=0 ∧ a 42=0 ∧ a 43=0 ∧ a 44=0 ∧ a 45=0 ∧ a 46=0 ∧ a 47=0 ∧ a 48=0 ∧ a 49=0 ∧ a 50=0 ∧ a 51=0 ∧ a 52=0 ∧ a 53=0 ∧ a 54=0 ∧ a 55=0 ∧ a 56=0 ∧ a 57=0 ∧ a 58=0 ∧ a 59=0 ∧ a 60=0 ∧ a 61=0 ∧ a 62=0 ∧ a 63=0 ∧ a 64=0 ∧ a 65=0 ∧ a 66=0 ∧ a 67=0 ∧ a 68=0 ∧ a 69=0 ∧ a 70=0 ∧ a 71=0 ∧ a 72=0) := by
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 start4) (And.intro (forced (a 5) 0 start5) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 0 start7) (And.intro (forced (a 8) 0 start8) (And.intro (forced (a 9) 0 start9) (And.intro (forced (a 10) 0 start10) (And.intro (forced (a 11) 0 start11) (And.intro (forced (a 12) 0 start12) (And.intro (forced (a 13) 0 start13) (And.intro (forced (a 14) 0 start14) (And.intro (forced (a 15) 0 start15) (And.intro (forced (a 16) 0 start16) (And.intro (forced (a 17) 0 start17) (And.intro (forced (a 18) 0 start18) (And.intro (forced (a 19) 0 start19) (And.intro (forced (a 20) 0 start20) (And.intro (forced (a 21) 0 start21) (And.intro (forced (a 22) 0 start22) (And.intro (forced (a 23) 0 start23) (And.intro (forced (a 24) 0 start24) (And.intro (forced (a 25) 0 start25) (And.intro (forced (a 26) 0 start26) (And.intro (forced (a 27) 0 start27) (And.intro (forced (a 28) 0 start28) (And.intro (forced (a 29) 0 start29) (And.intro (forced (a 30) 0 start30) (And.intro (forced (a 31) 0 start31) (And.intro (forced (a 32) 0 start32) (And.intro (forced (a 33) 0 start33) (And.intro (forced (a 34) 0 start34) (And.intro (forced (a 35) 0 start35) (And.intro (forced (a 36) 0 start36) (And.intro (forced (a 37) 0 start37) (And.intro (forced (a 38) 0 start38) (And.intro (forced (a 39) 0 start39) (And.intro (forced (a 40) 0 start40) (And.intro (forced (a 41) 0 start41) (And.intro (forced (a 42) 0 start42) (And.intro (forced (a 43) 0 start43) (And.intro (forced (a 44) 0 start44) (And.intro (forced (a 45) 0 start45) (And.intro (forced (a 46) 0 start46) (And.intro (forced (a 47) 0 start47) (And.intro (forced (a 48) 0 start48) (And.intro (forced (a 49) 0 start49) (And.intro (forced (a 50) 0 start50) (And.intro (forced (a 51) 0 start51) (And.intro (forced (a 52) 0 start52) (And.intro (forced (a 53) 0 start53) (And.intro (forced (a 54) 0 start54) (And.intro (forced (a 55) 0 start55) (And.intro (forced (a 56) 0 start56) (And.intro (forced (a 57) 0 start57) (And.intro (forced (a 58) 0 start58) (And.intro (forced (a 59) 0 start59) (And.intro (forced (a 60) 0 start60) (And.intro (forced (a 61) 0 start61) (And.intro (forced (a 62) 0 start62) (And.intro (forced (a 63) 0 start63) (And.intro (forced (a 64) 0 start64) (And.intro (forced (a 65) 0 start65) (And.intro (forced (a 66) 0 start66) (And.intro (forced (a 67) 0 start67) (And.intro (forced (a 68) 0 start68) (And.intro (forced (a 69) 0 start69) (And.intro (forced (a 70) 0 start70) (And.intro (forced (a 71) 0 start71) (forced (a 72) 0 start72))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_249
