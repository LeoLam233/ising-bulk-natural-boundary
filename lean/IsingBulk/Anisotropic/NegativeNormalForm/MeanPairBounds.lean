import IsingBulk.Anisotropic.NegativeNormalForm.MeanPairAlgebra
import IsingBulk.Anisotropic.NegativeNormalForm.MeanEnergyBound
import IsingBulk.Anisotropic.NegativeNormalForm.ReciprocalFieldBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

/-- The factor n in the rank-one coefficient cancels the reciprocal-root sum.
This estimate does not divide by a quadratic energy or a coordinate difference. -/
theorem rankOne_pair_term_bound {n : ℕ} (hn : n≠0) (S : Config n)
    (hS : ∀ i, ‖S i-1‖≤1/4) (mu D : ℂ) (i j : Fin n) :
    ‖rankOneCoefficient (meanCoefficients S)*mu*(D/(S i*S j*(∑ k,(S k)⁻¹)))‖≤8*‖mu‖*‖D‖ := by
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hi := scalar_inverse_norm_of_near_one (S i) ((hS i).trans (by norm_num))
  have hj := scalar_inverse_norm_of_near_one (S j) ((hS j).trans (by norm_num))
  have he (k : Fin n) : ‖1-(S k)⁻¹‖≤1/2 := by
    have h := scalar_reciprocal_error (S k) ((hS k).trans (by norm_num))
    linarith [hS k]
  have hden := reciprocal_sum_norm_lower S (1/2) he
  have hsum : ‖(∑ k,(S k)⁻¹)⁻¹‖≤2/(n:ℝ) := by
    rw [norm_inv]
    have h := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(n:ℝ)*(1-1/2)) hden
    rw [show (n:ℝ)*(1-1/2)=(n:ℝ)/2 by ring] at h
    simpa only [one_div,inv_div] using h
  have hrewrite : rankOneCoefficient (meanCoefficients S)*mu*(D/(S i*S j*(∑ k,(S k)⁻¹)))=
      rankOneCoefficient (meanCoefficients S)*mu*D*(S i)⁻¹*(S j)⁻¹*(∑ k,(S k)⁻¹)⁻¹ := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hrewrite]
  simp only [norm_mul]
  calc
    _ ≤ (n:ℝ)*‖mu‖*‖D‖*2*2*(2/(n:ℝ)) := by
      gcongr
      exact rankOneCoefficient_norm_le _
    _ = _ := by field_simp; ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
