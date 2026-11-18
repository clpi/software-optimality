import Std

namespace RangeLedger.AdaptiveReads

-- Any contiguous range inside one bank may be requested in either direction.
structure Page where
  bank : Fin 4
  lo : Fin 1025
  hi : Fin 1025

abbrev World := Nat → Int
def atPos (p : Page) (x : Fin 1025) := p.bank.val * 1024 + x.val
def read (p : World) (q : Page) := p (atPos q q.hi) - p (atPos q q.lo)

inductive Plan where
  | done (result : Int)
  | ask (q : Page) (next : Int → Plan)

def run (p : World) : Plan → Int × List Nat
  | .done v => (v,[])
  | .ask q next =>
    let (answer, reads) := run p (next (read p q))
    (answer,q.bank.val :: reads)

def correct (s : Plan) := ∀ p, (run p s).1 = p 4096 - p 0
def shift (i : Fin 4) (p : World) : World :=
  fun x => p x + (if (i.val+1)*1024 ≤ x then 1 else 0)

theorem other_bank (i : Fin 4) (p : World) (q : Page) (h : q.bank.val ≠ i.val) :
    read (shift i p) q = read p q := by
  have hlo := q.lo.isLt
  have hhi := q.hi.isLt
  unfold read shift atPos
  split <;> split <;> omega

theorem indistinguishable (i : Fin 4) (p : World) (s : Plan)
    (miss : i.val ∉ (run p s).2) : run (shift i p) s = run p s := by
  induction s with
  | done => rfl
  | ask q next ih =>
    simp only [run,List.mem_cons,not_or] at miss
    have same := other_bank i p q (Ne.symm miss.1)
    simp only [run,same,ih _ miss.2]

theorem touches_every_bank (s : Plan) (ok : correct s) (p : World) (i : Fin 4) :
    i.val ∈ (run p s).2 := by
  apply Classical.byContradiction; intro absent
  have eq := congrArg Prod.fst (indistinguishable i p s absent)
  rw [ok,ok] at eq
  have hi := i.isLt
  simp only [shift] at eq
  split at eq <;> split at eq <;> omega

private theorem count (n : Nat) (xs : List Nat) (h : ∀ i < n, i ∈ xs) : n ≤ xs.length := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    have hn := h n (by omega)
    have prev := ih (xs.erase n) (fun i hi => (List.mem_erase_of_ne (Nat.ne_of_lt hi)).mpr (h i (by omega)))
    rw [List.length_erase_of_mem hn] at prev
    have pos := List.length_pos_of_mem hn
    omega

theorem lower_bound (s : Plan) (ok : correct s) (p : World) : 4 ≤ (run p s).2.length :=
  count 4 _ (fun i hi => touches_every_bank s ok p ⟨i,hi⟩)

def whole (b : Fin 4) : Page := ⟨b,0,1024⟩
def four := Plan.ask (whole 0) fun a => .ask (whole 1) fun b =>
  .ask (whole 2) fun c => .ask (whole 3) fun d => .done (a+b+c+d)

theorem attains (p : World) :
    (run p four).1 = p 4096 - p 0 ∧ (run p four).2.length = 4 := by
  change (p 1024 - p 0 + (p 2048 - p 1024) + (p 3072 - p 2048) + (p 4096 - p 3072) =
    p 4096 - p 0) ∧ 4 = 4
  omega
#print axioms lower_bound
#print axioms attains
end RangeLedger.AdaptiveReads
