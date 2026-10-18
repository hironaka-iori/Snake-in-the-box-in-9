import CycleCuts
namespace Snake9.ComponentConstruction.Seed
open Classical CycleExclusion
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def vertices : List Vertex := [0,1,17,36,38,39,40,41,43,44,48,49,50,58,59,67,68,70,71,72,73,76,82,83,89,90,94,95,96,97,98,101,106,110,111,116,117,120,121,124,127,131,132,134,135,136,137,140,146,147,153,154,158,159,160,161,162,165,170,174,175,180,181,184,185,188,191,192,193,194,202,205,206,207,209,212,214,215,220,221,228,230,231,232,233,235,236,240,241,242,247,250,251,259,260,262,263,264,265,268,274,275,281,282,286,287,288,289,290,293,298,302,303,308,309,312,313,316,319,320,321,322,330,333,334,335,337,340,342,343,348,349,356,358,359,360,361,363,364,368,369,370,375,378,379,384,385,386,394,397,398,399,401,404,406,407,412,413,420,422,423,424,425,427,428,432,433,434,439,442,443,451,452,454,455,456,457,460,466,467,473,474,478,479,480,481,482,485,490,494,495,500,501,504,505,508,511]
def endpoints : List Vertex := [0,39]
def cycles : List (List Vertex) := [[67,68,70,71,72,73,76,82,83,89,90,94,95,96,97,98,101,106,110,111,116,117,120,121,124,127],[131,132,134,135,136,137,140,146,147,153,154,158,159,160,161,162,165,170,174,175,180,181,184,185,188,191],[192,193,194,202,205,206,207,209,212,214,215,220,221,228,230,231,232,233,235,236,240,241,242,247,250,251],[259,260,262,263,264,265,268,274,275,281,282,286,287,288,289,290,293,298,302,303,308,309,312,313,316,319],[320,321,322,330,333,334,335,337,340,342,343,348,349,356,358,359,360,361,363,364,368,369,370,375,378,379],[384,385,386,394,397,398,399,401,404,406,407,412,413,420,422,423,424,425,427,428,432,433,434,439,442,443],[451,452,454,455,456,457,460,466,467,473,474,478,479,480,481,482,485,490,494,495,500,501,504,505,508,511]]
def pathVertices : List Vertex := [0,1,17,49,48,50,58,59,43,41,40,44,36,38,39]

def degreeCheck : Bool := vertices.all (fun v =>
  (vertices.filter (fun w => decide (Adj v w))).length ==
    (if endpoints.contains v then 1 else 2))
theorem vertex_count : vertices.length = 197 := by decide
theorem vertices_distinct : vertices.Nodup := by decide
theorem endpoint_count : endpoints.length = 2 := by decide
theorem endpoints_selected : endpoints.all vertices.contains = true := by decide
theorem degrees_checked : degreeCheck = true := by decide
theorem cycles_checked : cycles.all cycleCheck = true := by decide
theorem partition_checked :
    (pathVertices ++ cycles.flatten).toFinset = vertices.toFinset ∧
    (pathVertices ++ cycles.flatten).Nodup := by decide
theorem cuts_valid {m : Nat} (p : Snake m) : ∀ c ∈ cycles,
    (c.toFinset.filter (fun v => InPath p v)).card ≤ c.toFinset.card-1 := by
  intro c hc
  exact checked_cycle_cut p c (List.all_eq_true.mp cycles_checked c hc)
#print axioms vertex_count
#print axioms vertices_distinct
#print axioms degrees_checked
#print axioms partition_checked
#print axioms cuts_valid
end Snake9.ComponentConstruction.Seed
