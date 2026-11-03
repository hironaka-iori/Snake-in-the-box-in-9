# Attempt record

1. The full nine-transition target 012031041 was native UNSAT with no cycle cuts.
   Both six-transition subwindows had negative capped-count tests. Weakening
   the 012032 conditions first removed the middle cap, then both outer caps,
   leaving only the second and fourth counts.
2. The first exported four-outer proof, Lower032, has 4508 deductions and 274137
   hints in 20 modules. Its native proof was independently replayed, but its
   Lean export and ActualOuter121 wrapper were not compiled. They remain saved
   as unselected intermediate work.
3. Three simpler certificates were selected: PairMin032, Pair25032 and Pair34032.
   They use 34 modules in total. All passed. ActualPair121, ReferenceCoverage121,
   all three Boundary modules and EndpointArithmetic121 subsequently passed,
   giving 40 checked modules and 47 printed axiom reports. No Lean source repair
   was needed for the selected proof or witnesses.
4. Twenty-nine initial probes yield fifteen native negative answers, twelve
   checked local configurations and two UNKNOWN cases. Both UNKNOWN cases
   retain their cycle cuts. Local attainments led to three full-Q9 searches;
   each yielded a complete induced path, subsequently checked independently
   and in Lean. These paths establish sharpness for the pair theorem.
5. Three additional full-Q9 tests add one endpoint-outside-intersection clause.
   All are native UNSAT with zero cycle cuts. Their base clauses and added
   condition have been checked, but no negative proof replay or Lean endpoint
   theorem is claimed. This new endpoint hypothesis is the continuation target.
6. The first independent graph audit stopped at a metadata-field lookup before
   producing evidence. Replacing `newly_removed` by the producer's actual field
   `marginal_removed` fixed the adapter. The initial source is preserved. The
   corrected audit verifies all 14,646 additional removals and both saved cycles.
7. The endpoint audit's initial scope wording was clarified to say outside the
   intersection of the two spheres. Its original script and output are retained
   under audit/endpoint-audit-initial.*. The rerun has identical encoding data.
8. An initial endpoint-distance inspection used `window_start` instead of the
   saved field `start`; it stopped without writing a result. The corrected
   observation is saved. Tool calls aborted before dispatch did not execute.

9. A final note wording update occurred while the receipt audit was being saved.
   Its initial additional note hash was stale. The initial review evidence and
   report are retained; the final audit was refreshed against the current note
   before the manifest was frozen. Proof sources and objects were unchanged.

The existing 104 and 115 proof jobs were checked by their live process commands
and left unchanged. The manuscript and editor remain revision 116. No local
negative answer is promoted to a theorem without its complete checked proof.
