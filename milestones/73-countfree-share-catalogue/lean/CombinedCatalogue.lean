import Share120.Geometry
import Share12.Geometry
import FiveCentreOverlap
import CountFreeTarget
import SixShapeCoverage
import CanonicalShareAdapter
import ConditionalCatalogueDispatch
import Share7300.Reversal
import Share7304.Reversal
import Share7306.Reversal

namespace Snake9.CatalogueIntegration73
open LocalWindow WindowAutomaton DirectionWindow CountFreeAdapter73
theorem canonical7300 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0, 1, 2, 0, 3, 1] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 0, 3, 1]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  apply share_bound_of_either_canonical_match (K := 15) p r [0, 1, 2, 0, 3, 1] hr hshape
  exact LocalWindow.ShareWindow7300.refuted
end Snake9.CatalogueIntegration73

namespace Snake9.CatalogueIntegration73
open LocalWindow WindowAutomaton DirectionWindow CountFreeAdapter73
theorem canonical7304 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0, 1, 2, 3, 0, 4] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 3, 0, 4]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  apply share_bound_of_either_canonical_match (K := 15) p r [0, 1, 2, 3, 0, 4] hr hshape
  exact LocalWindow.ShareWindow7304.refuted
end Snake9.CatalogueIntegration73

namespace Snake9.CatalogueIntegration73
open LocalWindow WindowAutomaton DirectionWindow CountFreeAdapter73
theorem canonical7306 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0, 1, 2, 3, 1, 4] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 3, 1, 4]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  apply share_bound_of_either_canonical_match (K := 15) p r [0, 1, 2, 3, 1, 4] hr hshape
  exact LocalWindow.ShareWindow7306.refuted
end Snake9.CatalogueIntegration73

namespace Snake9.CatalogueIntegration73
open LocalWindow DirectionWindow CountFreeAdapter73
theorem partial_catalogue_share
    (h7301 : RefutedShare (winOf [0, 1, 2, 0, 3, 2]) broadBounds 12 15)
    (h7302 : RefutedShare (winOf [0, 1, 2, 0, 3, 4]) broadBounds 12 19)
    (h7303 : RefutedShare (winOf [0, 1, 2, 3, 0, 1]) broadBounds 12 15)
    (h7305 : RefutedShare (winOf [0, 1, 2, 3, 1, 0]) broadBounds 12 11)
    (h7307 : RefutedShare (winOf [0, 1, 2, 3, 4, 0]) broadBounds 12 15)
    (h7308 : RefutedShare (winOf [0, 1, 2, 3, 4, 5]) broadBounds 12 15)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m) :
    windowLower p r ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  exact catalogue_share_bound LocalWindow.ShareWindow7300.refuted h7301 h7302 h7303 LocalWindow.ShareWindow7304.refuted h7305 LocalWindow.ShareWindow7306.refuted h7307 h7308 p r hr
#check @partial_catalogue_share
end Snake9.CatalogueIntegration73

#print axioms Snake9.LocalWindow.ShareWindow120.share_bound
#print axioms Snake9.LocalWindow.ShareWindow12.share_bound
#print axioms Snake9.CountFreeBridge.shareN_eq_coreShare
#print axioms Snake9.CountFreeBridge.core_share12_charge_le
#print axioms Snake9.CountFreeBridge.core_share_five_centre_overlap
#print axioms Snake9.CountFreeBridge.core_share12_five_centre_charge_le
#print axioms Snake9.CountFreeTarget.upper234_of_weight_bounds
#print axioms Snake9.CountFreeTarget.strict_margin
#print axioms Snake9.CountFreeCoverage73.restricted_growth_table
#print axioms Snake9.CountFreeCoverage73.canonical_coverage
#print axioms Snake9.CountFreeCoverage73.snake_window_coverage
#print axioms Snake9.CountFreeCoverage73.catalogue_size
#print axioms Snake9.CountFreeAdapter73.blockList_eq_dsOf
#print axioms Snake9.CountFreeAdapter73.canonical_share_bound
#print axioms Snake9.CountFreeAdapter73.reversed_canonical_share_bound
#print axioms Snake9.CountFreeAdapter73.share_bound_of_either_canonical_match
#print axioms Snake9.CountFreeAdapter73.selectedCap_ge11
#print axioms Snake9.CountFreeAdapter73.windowLower_ge12
#print axioms Snake9.CountFreeAdapter73.selectedShape_mem_and_match
#print axioms Snake9.CountFreeAdapter73.representative_refutation
#print axioms Snake9.CountFreeAdapter73.catalogue_share_bound
#print axioms Snake9.CountFreeAdapter73.catalogue_share_ge12
#print axioms Snake9.LocalWindow.ShareWindow7300.share_bound
#print axioms Snake9.LocalWindow.ShareWindow7300.share_bound_rev
#print axioms Snake9.CatalogueIntegration73.canonical7300
#print axioms Snake9.LocalWindow.ShareWindow7304.share_bound
#print axioms Snake9.LocalWindow.ShareWindow7304.share_bound_rev
#print axioms Snake9.CatalogueIntegration73.canonical7304
#print axioms Snake9.LocalWindow.ShareWindow7306.share_bound
#print axioms Snake9.LocalWindow.ShareWindow7306.share_bound_rev
#print axioms Snake9.CatalogueIntegration73.canonical7306
#print axioms Snake9.CatalogueIntegration73.partial_catalogue_share
