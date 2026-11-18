import ComparisonContract

namespace ThreeValuedGate

theorem absent_axis_admitted_by_two_valued_dominance :
    let c : ComparisonContract.Contract := ⟨[⟨0, 0, .minimize, 0⟩], 0, 0, 0⟩
    (([] : List Int)[0]? = none) ∧
      ComparisonContract.dominates c [] [1] = true := by
  decide

end ThreeValuedGate
