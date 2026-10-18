import unittest
from common import *
from worker import diagnose
from check_proof import replay


class Controls(unittest.TestCase):
    def test_valid_witness_model_reconstruction(self):
        p=bank()[0];d=encode(p,96,192);assignment,failed=witness_assignment(d,p[95:])
        self.assertEqual(failed,[])
        r=diagnose(d,[i if v else -i for i,v in assignment.items()],0)
        self.assertEqual(r['candidate_edges'],191)
        self.assertFalse(r['full_snake_verified']) # 192-edge target remains unchanged.

    def test_induced_condition_checks_nonconsecutive_pairs(self):
        for path in ([0,1,3,2],[0,1,0],[0,3]):
            with self.assertRaises(ValueError):verify_path(path)

    def test_invalid_unsat_certificate_rejected(self):
        with self.assertRaises(ValueError):replay([[1]],['0'])

    def test_proof_replay(self):
        clauses=[[1,2],[-1,2],[1,-2],[-1,-2]]
        r=replay(clauses,['2 0','0']);self.assertEqual(r['additions'],2)
        self.assertEqual(replay([[1],[-1]],[])['status'],'PASSED_EXECUTABLE_RUP_CHECK')

    def test_selection_balance(self):
        p=json.loads((OUT/'pilot-selection.json').read_text())['entries']
        self.assertEqual(len(p),12);self.assertEqual(sum(i%2 for i in p),6)
        self.assertEqual(len({i//2 for i in p}),12)


if __name__=='__main__':unittest.main()
