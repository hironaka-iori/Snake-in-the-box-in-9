from pathlib import Path
import re
H=Path('work/branch241-lean');R=H/'lrat_replay'
parts=[(H/'PeerLratSmokeStandalone.lean').read_text(encoding='utf-8')]
for name in ['ProofPack.lean','NatPack.lean','PeerLratFast2F_5000W18.lean']:
 parts.append(re.sub(r'^import .*\n','',(R/name).read_text(encoding='utf-8'),flags=re.M))
x=sum(v<<(18*i) for i,v in enumerate([3,0,131073,131074,0]));pack=1+(5+(x<<16))*(1<<16);npack=5+256*(3+65536*(9+32*473))
parts.append(f'''
namespace PeerLratInfrastructure
open Snake9.LocalWindow
open Snake9.LratO5k (Tree TreeTrue andB unsat_of_raw)
open Snake9.PeerLratFast5000W18
open Snake9.PeerLratFast2_5000W18
open Snake9.PeerLratFast2F_5000W18
open PeerLratSmoke (raw cnf start proof)
theorem packedProofExact : Snake9.ProofPack.unpackL 18 [nat_lit {pack}] = proof := by decide +kernel
theorem packedCheckpointExact : Snake9.NatPack.unpackL [nat_lit {npack}] = [0,1,3,0,7] := by decide +kernel
theorem checkedForced : andB (check2f start (perf 2 0) proof) (hasEmpty (replay start proof) 3) = true := by decide +kernel
theorem unsatForced : Unsat cnf := by
  apply unsat_of_raw
  intro t ht
  have hs : TreeTrue t start := start_true (raw := raw) (h := 2) (slots := [1,2]) t ht
  exact final_false2f (s := start) (ps := proof) (h := 2) t checkedForced hs
#print axioms Snake9.PeerLratFast2F_5000W18.check2f_eq
#print axioms Snake9.PeerLratFast2F_5000W18.replay_true2f
#print axioms Snake9.PeerLratFast2F_5000W18.cpz_true2f
#print axioms Snake9.PeerLratFast2F_5000W18.final_false2f
#print axioms packedProofExact
#print axioms packedCheckpointExact
#print axioms checkedForced
#print axioms unsatForced
end PeerLratInfrastructure
''')
(H/'PeerLratInfrastructureStandalone.lean').write_text('\n'.join(parts),encoding='utf-8')

