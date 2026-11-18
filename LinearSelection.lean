import Std
namespace LinearSelection
variable {T : Type}

-- One comparison per tail element. Equal costs keep the earlier candidate.
def bestFrom (cost : T → Int) (best : T) : List T → T
  | [] => best
  | x :: xs => bestFrom cost (if cost x < cost best then x else best) xs

theorem bestFrom_spec (cost : T → Int) (best : T) (xs : List T) :
    bestFrom cost best xs ∈ best :: xs ∧
      ∀ x, x ∈ best :: xs → cost (bestFrom cost best xs) ≤ cost x := by
  induction xs generalizing best with
  | nil => simp [bestFrom]
  | cons x xs ih =>
    unfold bestFrom
    split
    next h =>
      obtain ⟨hm, hb⟩ := ih x
      constructor
      · exact List.mem_cons_of_mem best hm
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Int.le_trans (hb x List.mem_cons_self) (Int.le_of_lt h)
        · exact hb y hy
    next h =>
      obtain ⟨hm, hb⟩ := ih best
      constructor
      · rcases List.mem_cons.mp hm with hm | hm
        · exact List.mem_cons.mpr (Or.inl hm)
        · exact List.mem_cons_of_mem best (List.mem_cons_of_mem x hm)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hb _ List.mem_cons_self
        · rcases List.mem_cons.mp hy with rfl | hy
          · have hle : cost best ≤ cost y := Int.le_of_not_gt h
            exact Int.le_trans (hb best List.mem_cons_self) hle
          · exact hb y (List.mem_cons_of_mem best hy)

def select (cost : T → Int) : List T → Option T
  | [] => none
  | best :: xs => some (bestFrom cost best xs)

theorem selected_minimum (cost : T → Int) (xs : List T) (winner : T)
    (h : select cost xs = some winner) :
    winner ∈ xs ∧ ∀ x, x ∈ xs → cost winner ≤ cost x := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    have hw : bestFrom cost x xs = winner := Option.some.inj h
    exact hw ▸ bestFrom_spec cost x xs

-- Eligibility is filtered before any comparison, never traded against the objective.
theorem selected_eligible_minimum (cost : T → Int) (gate : T → Bool)
    (xs : List T) (winner : T)
    (h : select cost (xs.filter gate) = some winner) :
    (winner ∈ xs ∧ gate winner = true) ∧
      ∀ x, x ∈ xs → gate x = true → cost winner ≤ cost x := by
  obtain ⟨hm, hb⟩ := selected_minimum cost (xs.filter gate) winner h
  exact ⟨List.mem_filter.mp hm, fun x hx hg => hb x (List.mem_filter.mpr ⟨hx,hg⟩)⟩

-- Instrumentation counts the actual scalar comparisons made by this recursion.
def bestFromCounted (cost : T → Int) (best : T) : List T → T × Nat
  | [] => (best,0)
  | x :: xs =>
    let result := bestFromCounted cost (if cost x < cost best then x else best) xs
    (result.1, result.2 + 1)

theorem counted_refines (cost : T → Int) (best : T) (xs : List T) :
    (bestFromCounted cost best xs).1 = bestFrom cost best xs ∧
    (bestFromCounted cost best xs).2 = xs.length := by
  induction xs generalizing best with
  | nil => simp [bestFromCounted,bestFrom]
  | cons x xs ih =>
    obtain ⟨ha,hb⟩ := ih (if cost x < cost best then x else best)
    simp only [bestFromCounted,bestFrom,List.length_cons,ha,hb]
    trivial

-- Public set-valued selection retains ALL exact ties, not an arrival-order winner.
def allMinima (cost : T → Int) (xs : List T) : List T :=
  match select cost xs with
  | none => []
  | some winner => xs.filter (fun x => decide (cost x = cost winner))

theorem allMinima_exact (cost : T → Int) (xs : List T) (x : T) :
    x ∈ allMinima cost xs ↔ x ∈ xs ∧ ∀ y, y ∈ xs → cost x ≤ cost y := by
  cases xs with
  | nil => simp [allMinima,select]
  | cons b bs =>
    obtain ⟨hm,hb⟩ := bestFrom_spec cost b bs
    simp only [allMinima,select,List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨hx,he⟩
      exact ⟨hx, fun y hy => he ▸ hb y hy⟩
    · rintro ⟨hx,hmin⟩
      exact ⟨hx, Int.le_antisymm (hmin _ hm) (hb x hx)⟩

theorem allMinima_order_independent (cost : T → Int) (xs ys : List T)
    (same : ∀ x, x ∈ xs ↔ x ∈ ys) :
    ∀ x, x ∈ allMinima cost xs ↔ x ∈ allMinima cost ys := by
  intro x
  rw [allMinima_exact,allMinima_exact]
  constructor
  · rintro ⟨hx,hmin⟩
    exact ⟨(same x).mp hx, fun y hy => hmin y ((same y).mpr hy)⟩
  · rintro ⟨hx,hmin⟩
    exact ⟨(same x).mpr hx, fun y hy => hmin y ((same y).mp hy)⟩

#print axioms allMinima_exact
#print axioms allMinima_order_independent
#print axioms bestFrom_spec
#print axioms selected_minimum
#print axioms selected_eligible_minimum
#print axioms counted_refines
end LinearSelection
