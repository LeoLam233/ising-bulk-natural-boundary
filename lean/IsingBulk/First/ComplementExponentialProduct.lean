import IsingBulk.First.ComplementAuxiliary
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual finite products of positive-half-line exponential integrals.
The auxiliary variables are independent at each fixed angular point. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

/-- The auxiliary integration domain, with its ordinary product Lebesgue measure. -/
def positiveAuxiliaryOrthant (ι : Type*) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun _ => Ioi 0)

theorem positiveAuxiliaryOrthant_measure {ι : Type*} [Fintype ι] :
    volume.restrict (positiveAuxiliaryOrthant ι) =
      Measure.pi (fun _ : ι => volume.restrict (Ioi (0 : ℝ))) := by
  rw [positiveAuxiliaryOrthant, volume_pi, Measure.restrict_pi_pi]

/-- The finite exponential product is absolutely integrable for fixed positive damping. -/
theorem auxiliary_exponential_integrable {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (hd : ∀ i, (d i).re < 0) :
    IntegrableOn (fun ξ : ι → ℝ => Complex.exp (∑ i, d i * (ξ i : ℂ)))
      (positiveAuxiliaryOrthant ι) := by
  unfold IntegrableOn
  rw [positiveAuxiliaryOrthant_measure]
  have h := Integrable.fintype_prod (fun i => integrableOn_exp_mul_complex_Ioi (hd i) 0)
  simpa only [Complex.exp_sum] using h

/-- The exact finite-product half-line representation, including the empty family. -/
theorem integral_auxiliary_exponential {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (hd : ∀ i, (d i).re < 0) :
    (∫ ξ : ι → ℝ in positiveAuxiliaryOrthant ι,
      Complex.exp (∑ i, d i * (ξ i : ℂ))) = ∏ i, (-d i)⁻¹ := by
  rw [positiveAuxiliaryOrthant_measure]
  simp only [Complex.exp_sum]
  calc
    _ = ∏ i, ∫ t : ℝ in Ioi 0, Complex.exp (d i * t) :=
      integral_fintype_prod_eq_prod (fun i (t : ℝ) => Complex.exp (d i * t))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [integral_exp_mul_complex_Ioi (hd i) 0]
      simp [div_eq_mul_inv]

end
end IsingBulk.First
