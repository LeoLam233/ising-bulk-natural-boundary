import IsingBulk.Tail.ExteriorQuantitative

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

/-- Killing the incorrect order-independent inverse-product shortcut. -/
theorem four_half_roots_inverse_product :
    ‖(coordinateProduct (fun _ : Fin 4 => (1/2:ℂ)))⁻¹‖ = 16 := by
  norm_num [coordinateProduct]

theorem four_half_roots_not_single_inverse_bound :
    ¬ ‖(coordinateProduct (fun _ : Fin 4 => (1/2:ℂ)))⁻¹‖ ≤ 2 := by
  rw [four_half_roots_inverse_product]
  norm_num

#print axioms exteriorEvenTerm_analyticAt
#print axioms exteriorEvenSeries_iteratedDeriv
#print axioms compact_exteriorEven_derivative_majorant
#print axioms exteriorNormalizedBulk_analyticOn
#print axioms exteriorNormalizedBulk_eq_quarter_far
#print axioms compact_exteriorEven_sqrt_bound
#print axioms compact_exteriorEven_cauchy_sqrt_bound
#print axioms even_cauchy_sqrt_majorant_summable

end
end IsingBulk.Tail
