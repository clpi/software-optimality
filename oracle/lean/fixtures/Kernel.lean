import Lean
universe u v
namespace OracleSlice
theorem identity (α : Sort u) (x : α) : (fun y => y) x = x := rfl
theorem eta (α : Type u) (β : Type v) (f : α → β) : (fun x => f x) = f := rfl
theorem proofs (p : Prop) (h k : p) : h = k := rfl
theorem quotient (α : Sort u) (r : α → α → Prop) (a : α) :
    Quot.lift (fun _ => (0 : Nat)) (by intro x y _; rfl) (Quot.mk r a) = 0 := rfl
theorem dependent (α : Sort u) (a b : α) (h : HEq a b) : a = b := eq_of_heq h
def walk : Nat → Nat
  | 0 => 0
  | n + 1 => walk n + 1
theorem walk_correct (n : Nat) : walk n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walk, ih]
structure Pair where
  left : Nat
  right : Nat
example : (Pair.mk 7 9).left = 7 := rfl
#print axioms identity
#print axioms eta
#print axioms proofs
#print axioms quotient
#print axioms dependent
#print axioms walk_correct
#eval walk 12
end OracleSlice
