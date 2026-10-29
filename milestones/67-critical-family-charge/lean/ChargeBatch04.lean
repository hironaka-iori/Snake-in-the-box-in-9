import GenericWindow
namespace Snake9.LocalWindow.FamilyCharge67
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G020
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 60, 44, 46, 110]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 0, 4, 1, 6]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 36, 38, 39, 40, 42, 45, 47, 52, 53, 56, 57, 62, 63, 65, 67, 71, 77, 79, 93, 108, 124, 125, 129, 131, 135, 141, 143, 157, 172, 174, 188, 189, 257, 259, 263, 269, 271, 285, 300, 302, 316, 317]
def C : List Nat := [29, 61, 60, 44, 46]
def mask : Nat := 400507754477222476254004717625655367318683833859155933455587592523019238632934745390365637499492
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G020
namespace G021
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 63, 55, 54, 52]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 1, 3, 0, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 22, 23, 25, 28, 31, 33, 35, 38, 39, 45, 47, 50, 51, 53, 57, 59, 60, 62, 65, 67, 71, 77, 79, 93, 118, 119, 125, 127, 129, 131, 135, 141, 143, 157, 182, 183, 189, 191, 257, 259, 263, 269, 271, 285, 310, 311, 317, 319]
def C : List Nat := [29, 61, 63, 55, 54]
def mask : Nat := 1341249672032038506128412037001185980280076507977733477751855902060930235452346712810247194040932
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 4≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G021
namespace G022
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 63, 55, 51, 49]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 1, 3, 2, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 50, 53, 54, 57, 59, 60, 62, 65, 67, 71, 77, 79, 93, 115, 119, 125, 127, 129, 131, 135, 141, 143, 157, 179, 183, 189, 191, 257, 259, 263, 269, 271, 285, 307, 311, 317, 319]
def C : List Nat := [29, 61, 63, 55, 51]
def mask : Nat := 1339424487797242806595115509664371177447769028562615768260281375235089605775268915589108604754532
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 5≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    5≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=5) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G022
namespace G023
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 63, 55, 119, 117]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 1, 3, 6, 1]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 51, 53, 54, 57, 59, 60, 62, 65, 67, 71, 77, 79, 87, 93, 103, 115, 118, 125, 127, 129, 131, 135, 141, 143, 157, 183, 189, 191, 247, 257, 259, 263, 269, 271, 285, 311, 317, 319, 375]
def C : List Nat := [29, 61, 63, 55, 119]
def mask : Nat := 76957043352332968550646247387864988089345670803174235760676846995718614380751845201419651135381586634514763504228
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 4≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    4≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=4) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G023
namespace G024
def W : List Nat := [0, 1, 3, 7, 15, 13, 29, 61, 125, 109, 111, 110]
def ds : List Nat := [0, 1, 2, 3, 1, 4, 5, 6, 4, 1, 0]
def D : List Nat := [2, 5, 6, 9, 11, 12, 14, 17, 19, 21, 23, 25, 28, 31, 33, 35, 39, 45, 47, 53, 57, 60, 63, 65, 67, 71, 77, 79, 93, 101, 103, 105, 107, 108, 117, 121, 124, 127, 129, 131, 135, 141, 143, 157, 189, 237, 239, 253, 257, 259, 263, 269, 271, 285, 317, 365, 367, 381]
def C : List Nat := [29, 61, 125, 109, 111]
def mask : Nat := 4925626541362553715118340708965721943247707152211702488855819399853065933255044044432432969060624445650481577613924
theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheck W D=true := by decide +kernel
theorem supported : supportCheck W C=true := by decide +kernel
theorem checked_mask : maskCheck mask D=true := by decide +kernel
theorem credit : 2≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    2≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:=2) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP
#print axioms canonical
#print axioms forced
#print axioms supported
#print axioms checked_mask
#print axioms credit
#print axioms in_snake
end G024
end Snake9.LocalWindow.FamilyCharge67
