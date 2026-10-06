import IsingBulk.First.ComplementExponentialProduct
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Fixed-parameter absolute convergence and legitimate angular/auxiliary
Fubini for the exact finite exponential representation. Uniform boundary bounds
are obtained only after angular integration by parts. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι]

/-- Exact absolute auxiliary integral for strictly damped factors. -/
theorem integral_norm_auxiliary_exponential (d : ι → ℂ) (hd : ∀ i, (d i).re < 0) :
    (∫ ξ : ι → ℝ in positiveAuxiliaryOrthant ι,
      ‖Complex.exp (∑ i, d i * (ξ i : ℂ))‖) = ∏ i, (-(d i).re)⁻¹ := by
  rw [positiveAuxiliaryOrthant_measure]
  simp only [Complex.exp_sum, norm_prod]
  calc
    _ = ∏ i, ∫ t : ℝ in Ioi 0, ‖Complex.exp (d i * t)‖ :=
      integral_fintype_prod_eq_prod (fun i (t : ℝ) => ‖Complex.exp (d i * t)‖)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      rw [integral_exp_mul_Ioi (hd i) 0]
      simp [div_eq_mul_inv]

variable {E : Type*} [NormedAddCommGroup E]

/-- The absolute auxiliary-integral density is continuous through every
outside-support zero, without requiring its totalized denominator globally nonzero. -/
theorem supported_norm_quotient_regular (A : E → ℂ) (b : E → ℝ)
    (hA : Continuous A) (hc : HasCompactSupport A) (hb : Continuous b)
    (hne : ∀ x ∈ tsupport A, b x ≠ 0) :
    Continuous (fun x => ‖A x‖ / b x) ∧ HasCompactSupport (fun x => ‖A x‖ / b x) := by
  constructor
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport A
    · exact hA.norm.continuousAt.div hb.continuousAt (hne x hx)
    · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
      have hq : (fun x => ‖A x‖ / b x) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hz] with y hy
        simp [hy]
      exact continuousAt_const.congr_of_eventuallyEq hq
  · apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    contrapose! hx
    simp [Function.mem_support] at hx ⊢
    simp [hx]

variable [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The full joint integrand is absolutely integrable at each fixed damped
parameter. There is no claim of a uniform absolute bound before angular IBP. -/
theorem fixed_parameter_exponential_integrable (A : E → ℂ) (d : ι → E → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (hd : ∀ i, Continuous (d i))
    (hneg : ∀ u ∈ tsupport A, ∀ i, (d i u).re < 0) :
    Integrable (fun p : E × (ι → ℝ) =>
      A p.1 * Complex.exp (∑ i, d i p.1 * (p.2 i : ℂ)))
      (μ.prod (volume.restrict (positiveAuxiliaryOrthant ι))) := by
  classical
  have hm : Continuous (fun p : E × (ι → ℝ) =>
      A p.1 * Complex.exp (∑ i, d i p.1 * (p.2 i : ℂ))) := by
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  have hinner (u : E) :
      IntegrableOn (fun ξ : ι → ℝ => A u * Complex.exp (∑ i, d i u * (ξ i : ℂ)))
        (positiveAuxiliaryOrthant ι) := by
    by_cases hu : A u = 0
    · simp [hu]
    · exact (auxiliary_exponential_integrable (fun i => d i u)
        (hneg u (subset_closure hu))).const_mul (A u)
  refine ⟨Filter.Eventually.of_forall hinner, ?_⟩
  let b : E → ℝ := fun u => ∏ i, -(d i u).re
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hbne (u : E) (hu : u ∈ tsupport A) : b u ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => neg_ne_zero.mpr (ne_of_lt (hneg u hu i)))
  have hreg := supported_norm_quotient_regular A b hA hc hb hbne
  have hint := hreg.1.integrable_of_hasCompactSupport (μ := μ) hreg.2
  apply hint.congr
  apply Filter.Eventually.of_forall
  intro u
  by_cases hu : A u = 0
  · simp [hu]
  · simp only [norm_mul, integral_const_mul]
    rw [integral_norm_auxiliary_exponential (fun i => d i u) (hneg u (subset_closure hu))]
    dsimp [b]
    rw [div_eq_mul_inv, Finset.prod_inv_distrib]

/-- Finite-product representation followed by genuine Fubini on the actual
coupled angular/auxiliary integrand. -/
theorem fixed_parameter_exponential_fubini (A : E → ℂ) (d : ι → E → ℂ)
    (hA : Continuous A) (hc : HasCompactSupport A) (hd : ∀ i, Continuous (d i))
    (hneg : ∀ u ∈ tsupport A, ∀ i, (d i u).re < 0) :
    (∫ u, A u * ∏ i, (-d i u)⁻¹ ∂μ) =
      ∫ ξ : ι → ℝ in positiveAuxiliaryOrthant ι,
        ∫ u, A u * Complex.exp (∑ i, d i u * (ξ i : ℂ)) ∂μ := by
  have heq (u : E) : A u * ∏ i, (-d i u)⁻¹ =
      ∫ ξ : ι → ℝ in positiveAuxiliaryOrthant ι,
        A u * Complex.exp (∑ i, d i u * (ξ i : ℂ)) := by
    by_cases hu : A u = 0
    · simp [hu]
    · rw [integral_const_mul,
        integral_auxiliary_exponential (fun i => d i u) (hneg u (subset_closure hu))]
  simp_rw [heq]
  exact integral_integral_swap (fixed_parameter_exponential_integrable A d hA hc hd hneg)

end
end IsingBulk.First
