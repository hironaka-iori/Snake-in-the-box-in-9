import WitnessTablesData
import WitnessLookup

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Witness90
open Snake9.Balanced89 Snake9.Direction77 Snake9.Reference85 Snake9.Boxes88

theorem directionTable_valid : check directionTable = true := by decide +kernel

theorem directionTable_flat : flatten directionTable = extensions := by decide +kernel

theorem referenceTable_valid : check referenceTable = true := by decide +kernel

theorem referenceTable_flat : flatten referenceTable = referenceKeys := by decide +kernel

theorem referenceCount_eq : 1378 = referenceKeys.length := by decide +kernel

def directionsAt (i : Nat) : List Nat := lookup directionTable i []

def referencesAt (i : Nat) : List Nat × List Nat := lookup referenceTable i ([],[])

theorem directionsAt_eq (i : Nat) : directionsAt i = extensions.getD i [] :=
  lookup_eq_list directionTable extensions directionTable_valid directionTable_flat i []

theorem referencesAt_eq (i : Nat) : referencesAt i = referenceKeys.getD i ([],[]) :=
  lookup_eq_list referenceTable referenceKeys referenceTable_valid referenceTable_flat i ([],[])

theorem balanced_entries_eq :
    entriesValidAt directionsAt referencesAt 1378 = entriesValid :=
  entriesValidAt_eq directionsAt referencesAt 1378 directionsAt_eq referencesAt_eq referenceCount_eq

#print axioms directionTable_valid
#print axioms directionTable_flat
#print axioms referenceTable_valid
#print axioms referenceTable_flat
#print axioms referenceCount_eq
#print axioms directionsAt_eq
#print axioms referencesAt_eq
#print axioms balanced_entries_eq
end Snake9.Witness90
