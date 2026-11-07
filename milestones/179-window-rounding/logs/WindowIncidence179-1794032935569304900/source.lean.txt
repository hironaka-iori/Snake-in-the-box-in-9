set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace WindowIncidence179
def adjacent (x y : Nat) : Bool :=
  (List.range 9).any (fun i => x ^^^ y == 2^i)

theorem first_pattern : ∀ i : Fin 5, ∀ a : Fin 9,
    ([1,3,7,6,14].countP (adjacent (([1,3,7,6,14][i.val]!) ^^^ 2^a.val)))≤2 := by decide
theorem second_pattern : ∀ i : Fin 5, ∀ a : Fin 9,
    ([1,3,7,15,14].countP (adjacent (([1,3,7,15,14][i.val]!) ^^^ 2^a.val)))≤2 := by decide
theorem last_two_patterns : ∀ i : Fin 5, ∀ a : Fin 9,
    ([1,3,7,15,31].countP (adjacent (([1,3,7,15,31][i.val]!) ^^^ 2^a.val)))≤2 := by decide

theorem bound_attained :
    ([1,3,7,6,14].countP (adjacent 5))=2 ∧
    ([1,3,7,15,14].countP (adjacent 5))=2 ∧
    ([1,3,7,15,31].countP (adjacent 5))=2 := by decide

#print axioms first_pattern
#print axioms second_pattern
#print axioms last_two_patterns
#print axioms bound_attained
end WindowIncidence179
