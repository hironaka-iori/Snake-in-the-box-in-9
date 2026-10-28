import GenericWindow
namespace Snake9.LocalWindow.FamilyShare61
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace G120
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 53, 52]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 1, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 21, 22, 23, 26, 28, 31, 33, 35, 37, 38, 39, 46, 47, 49, 51, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 117, 119, 126, 127, 129, 131, 134, 135, 142, 158, 181, 183, 190, 191, 257, 259, 262, 263, 270, 286, 309, 311, 318, 319]
def C : List Nat := [30, 62, 63, 55, 53]
def mask : Nat := 1607205089164431575807152251254754951434105866235342116812184850652144569011884751200979830611508
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 21 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    21 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=21) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G120


namespace G121
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 51, 50]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 2, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 49, 53, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 94, 115, 119, 126, 127, 129, 131, 134, 135, 142, 158, 179, 183, 190, 191, 257, 259, 262, 263, 270, 286, 307, 311, 318, 319]
def C : List Nat := [30, 62, 63, 55, 51]
def mask : Nat := 1606422867349519133150025168110405750220259803628863098458652910583927156293137123820472229338676
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G121


namespace G122
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 63, 55, 119, 118]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 0, 3, 6, 0]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 22, 23, 26, 28, 31, 33, 35, 38, 39, 46, 47, 51, 53, 54, 58, 59, 60, 61, 65, 67, 70, 71, 78, 87, 94, 103, 115, 117, 126, 127, 129, 131, 134, 135, 142, 158, 183, 190, 191, 247, 257, 259, 262, 263, 270, 286, 311, 318, 319, 375]
def C : List Nat := [30, 62, 63, 55, 119]
def mask : Nat := 76957043352332968817644626940141314644255329249208808533167622061965944579123214396757728538765682452945806466612
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G122


namespace G123
def W : List Nat := [0, 1, 3, 7, 6, 14, 30, 62, 60, 61, 29, 13]
def ds : List Nat := [0, 1, 2, 0, 3, 4, 5, 1, 0, 5, 4]
def D : List Nat := [2, 4, 5, 9, 10, 11, 12, 15, 17, 19, 21, 22, 23, 25, 26, 28, 31, 33, 35, 38, 39, 44, 45, 46, 52, 53, 54, 56, 57, 58, 63, 65, 67, 70, 71, 78, 93, 94, 124, 125, 126, 129, 131, 134, 135, 142, 157, 158, 188, 189, 190, 257, 259, 262, 263, 270, 285, 286, 316, 317, 318]
def C : List Nat := [30, 62, 60, 61, 29]
def mask : Nat := 934494328401896295229084077383864688544844629676126039329051219530012992124973564912849212055092
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G123


namespace G130
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 29, 21, 53, 37]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 0, 3, 5, 4]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 25, 30, 31, 33, 35, 39, 44, 46, 47, 49, 52, 55, 60, 61, 65, 67, 71, 76, 78, 79, 85, 92, 93, 117, 129, 131, 135, 140, 142, 143, 149, 156, 157, 181, 257, 259, 263, 268, 270, 271, 277, 284, 285, 309]
def C : List Nat := [12, 28, 29, 21, 53]
def mask : Nat := 1042962513380378991008679092873588644948938003727938285988498823357925115329645629309162499956
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 7 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    7 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=7) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G130


namespace G131
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62, 63, 59]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 2]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 54, 55, 56, 58, 61, 65, 67, 71, 76, 78, 79, 92, 124, 126, 127, 129, 131, 135, 140, 142, 143, 156, 188, 190, 191, 257, 259, 263, 268, 270, 271, 284, 316, 318, 319]
def C : List Nat := [12, 28, 60, 62, 63]
def mask : Nat := 1735489466716828325898042824759881366389579545893800579817747578785827321202539223162777748778868
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G131


namespace G132
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62, 63, 55]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 3]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 54, 56, 58, 59, 61, 65, 67, 71, 76, 78, 79, 92, 124, 126, 127, 129, 131, 135, 140, 142, 143, 156, 188, 190, 191, 257, 259, 263, 268, 270, 271, 284, 316, 318, 319]
def C : List Nat := [12, 28, 60, 62, 63]
def mask : Nat := 1735489466716828325898042824759881366389579545893800579817747578785827321202539763594733033238388
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G132


namespace G133
def W : List Nat := [0, 1, 3, 7, 15, 14, 12, 28, 60, 62, 63, 127]
def ds : List Nat := [0, 1, 2, 3, 0, 1, 4, 5, 1, 0, 6]
def D : List Nat := [2, 4, 5, 6, 8, 9, 10, 11, 13, 17, 19, 20, 23, 24, 29, 30, 31, 33, 35, 39, 44, 46, 47, 52, 54, 55, 56, 58, 59, 61, 65, 67, 71, 76, 78, 79, 92, 124, 126, 129, 131, 135, 140, 142, 143, 156, 188, 190, 191, 257, 259, 263, 268, 270, 271, 284, 316, 318, 319]
def C : List Nat := [12, 28, 60, 62, 63]
def mask : Nat := 1735489466716828325898042824759881366389579545893800579817577437602366851970808112319814168096628
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2 ≤ (C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2 ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum :=
  share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G133

end Snake9.LocalWindow.FamilyShare61