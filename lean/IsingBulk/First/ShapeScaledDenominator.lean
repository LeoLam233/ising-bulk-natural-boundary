import IsingBulk.First.ShapeScaledPhase
import IsingBulk.First.AnalyticQuadraticLimit

/-! The actual constrained post-mean denominator along a fixed shape ray. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Set Filter
open scoped Topology BigOperators

def scaledShapeDefect {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) (lam : ℂ) : ℂ :=
  -Complex.I*((∑ j, scaledShapePhase a ((shapeExtend tau j : ℝ) : ℂ) lam)-
    (n+1:ℂ)*(a.beta:ℂ))

def scaledShapeDenominator {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) (lam : ℂ) : ℂ :=
  1-Complex.exp (scaledShapeDefect a tau lam)

theorem scaledShapeDefect_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    scaledShapeDefect a tau 0 = 0 := by
  simp [scaledShapeDefect, scaledShapePhase_zero]

theorem scaledShapeDefect_analytic_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    AnalyticAt ℂ (scaledShapeDefect a tau) 0 := by
  have hs := Finset.analyticAt_fun_sum Finset.univ
    (fun j _ => scaledShapePhase_analytic_zero a ((shapeExtend tau j : ℝ) : ℂ))
  exact analyticAt_const.mul (hs.sub analyticAt_const)

theorem scaledShapeDefect_hasDerivAt_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    HasDerivAt (scaledShapeDefect a tau) 0 0 := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => scaledShapePhase_hasDerivAt_zero a ((shapeExtend tau j : ℝ) : ℂ))
  have h := (hs.sub_const ((n+1:ℂ)*(a.beta:ℂ))).const_mul (-Complex.I)
  convert h using 1
  · rfl
  · simp [← Finset.mul_sum, ← Complex.ofReal_sum]

theorem scaledShapeDefect_deriv_near_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    deriv (scaledShapeDefect a tau) =ᶠ[𝓝 (0:ℂ)]
      (fun lam => -Complex.I*∑ j, deriv (scaledShapePhase a ((shapeExtend tau j : ℝ) : ℂ)) lam) := by
  have he : ∀ᶠ lam : ℂ in 𝓝 0, ∀ j : Fin (n+1),
      AnalyticAt ℂ (scaledShapePhase a ((shapeExtend tau j : ℝ) : ℂ)) lam :=
    Filter.eventually_all.mpr fun j => (scaledShapePhase_analytic_zero a ((shapeExtend tau j : ℝ) : ℂ)).eventually_analyticAt
  filter_upwards [he] with lam hlam
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (hlam j).differentiableAt.hasDerivAt)
  exact ((hs.sub_const ((n+1:ℂ)*(a.beta:ℂ))).const_mul (-Complex.I)).deriv

theorem scaledShapeDefect_second_hasDerivAt_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    HasDerivAt (deriv (scaledShapeDefect a tau))
      (-2*(a.Q (n+1):ℂ)+2*Complex.I*(a.d:ℂ)*∑ j, ((shapeExtend tau j : ℝ) : ℂ)^2) 0 := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => scaledShapePhase_second_hasDerivAt_zero a ((shapeExtend tau j : ℝ) : ℂ))
  have h := hs.const_mul (-Complex.I)
  have hQ : (n+1:ℂ)*(a.A₀ 0 : ℂ) = (a.Q (n+1):ℂ) := by
    exact_mod_cast (by simpa using a.physical_damping_N (n+1) 0)
  have hc : -Complex.I*(∑ j : Fin (n+1),
      (-2*Complex.I*(a.A₀ 0 : ℂ)-2*(a.d:ℂ)*((shapeExtend tau j : ℝ):ℂ)^2)) =
      -2*(a.Q (n+1):ℂ)+2*Complex.I*(a.d:ℂ)*∑ j, ((shapeExtend tau j : ℝ):ℂ)^2 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    have he : -Complex.I*((n+1:ℂ)*(-2*Complex.I*(a.A₀ 0:ℂ))-
        2*(a.d:ℂ)*∑ j, ((shapeExtend tau j:ℝ):ℂ)^2) =
        -2*((n+1:ℂ)*(a.A₀ 0:ℂ))+2*Complex.I*(a.d:ℂ)*∑ j, ((shapeExtend tau j:ℝ):ℂ)^2 := by
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [he, hQ]
  rw [hc] at h
  exact h.congr_of_eventuallyEq (scaledShapeDefect_deriv_near_zero a tau)

theorem scaledShapeDenominator_analytic_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    AnalyticAt ℂ (scaledShapeDenominator a tau) 0 :=
  analyticAt_const.sub ((scaledShapeDefect_analytic_zero a tau).cexp)

theorem scaledShapeDenominator_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    scaledShapeDenominator a tau 0 = 0 := by
  simp [scaledShapeDenominator, scaledShapeDefect_zero]

theorem scaledShapeDenominator_hasDerivAt_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    HasDerivAt (scaledShapeDenominator a tau) 0 0 := by
  simpa [scaledShapeDenominator] using! ((scaledShapeDefect_hasDerivAt_zero a tau).cexp).const_sub 1

theorem scaledShapeDenominator_deriv_near_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    deriv (scaledShapeDenominator a tau) =ᶠ[𝓝 (0:ℂ)]
      (fun lam => -Complex.exp (scaledShapeDefect a tau lam)*deriv (scaledShapeDefect a tau) lam) := by
  filter_upwards [(scaledShapeDefect_analytic_zero a tau).eventually_analyticAt] with lam hlam
  have h : HasDerivAt (scaledShapeDenominator a tau)
      (-Complex.exp (scaledShapeDefect a tau lam)*deriv (scaledShapeDefect a tau) lam) lam := by
    convert! (hlam.differentiableAt.hasDerivAt.cexp).const_sub 1 using 1;
      simp
  exact h.deriv

theorem scaledShapeDenominator_second_hasDerivAt_zero {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    HasDerivAt (deriv (scaledShapeDenominator a tau))
      (2*((a.Q (n+1):ℂ)-Complex.I*(a.d:ℂ)*∑ j, ((shapeExtend tau j:ℝ):ℂ)^2)) 0 := by
  have h := ((scaledShapeDefect_hasDerivAt_zero a tau).cexp.neg).mul
    (scaledShapeDefect_second_hasDerivAt_zero a tau)
  have hh : HasDerivAt (fun lam => -Complex.exp (scaledShapeDefect a tau lam)*
      deriv (scaledShapeDefect a tau) lam)
      (2*((a.Q (n+1):ℂ)-Complex.I*(a.d:ℂ)*∑ j, ((shapeExtend tau j:ℝ):ℂ)^2)) 0 := by
    convert h using 1
    simp [scaledShapeDefect_zero, Pi.neg_apply]
    ring
  exact hh.congr_of_eventuallyEq (scaledShapeDenominator_deriv_near_zero a tau)

/-- The genuine constrained quadratic limit, established for each fixed shape
from actual branch derivatives and an analytic Taylor remainder. -/
theorem scaledShapeDenominator_quotient_limit {n : ℕ} (a : OrderedChartData) (tau : Fin n → ℝ) :
    Tendsto (fun lam : ℝ => scaledShapeDenominator a tau (lam:ℂ)/(lam:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((a.Q (n+1):ℂ)-Complex.I*(a.d:ℂ)*∑ j, ((shapeExtend tau j:ℝ):ℂ)^2)) :=
  analytic_quadratic_quotient_limit_real (scaledShapeDenominator_analytic_zero a tau)
    (scaledShapeDenominator_zero a tau) (scaledShapeDenominator_hasDerivAt_zero a tau).deriv
    (scaledShapeDenominator_second_hasDerivAt_zero a tau).deriv


theorem shapeExtend_real_smul {n : ℕ} (lam : ℝ) (tau : Fin n → ℝ) :
    shapeExtend (lam • tau) = lam • shapeExtend tau := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  · simp [Pi.smul_apply]

theorem scaledShapeDefect_eq_actual {n : ℕ} (a : OrderedChartData)
    (tau : Fin n → ℝ) (lam : ℝ) :
    scaledShapeDefect a tau (lam:ℂ) = shapePhaseDefect a (lam^2) (lam • tau) := by
  unfold scaledShapeDefect shapePhaseDefect
  simp_rw [scaledShapePhase_eq_radialResiduePhase, shapeExtend_real_smul,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]

theorem scaledShapeDenominator_eq_actual {n : ℕ} (a : OrderedChartData)
    (tau : Fin n → ℝ) (lam : ℝ)
    (hbeta : Complex.exp (-(n+1:ℂ)*(a.beta:ℂ)*Complex.I) = 1) :
    scaledShapeDenominator a tau (lam:ℂ) =
      shapePoleDenominator (radialParameter a.theta (lam^2)) a.alpha (lam • tau) := by
  rw [shapePoleDenominator_eq_exp_defect a (lam^2) (lam • tau) hbeta]
  rw [scaledShapeDenominator, scaledShapeDefect_eq_actual]

/-- The source denominator itself, rather than a model polynomial, has the
fixed-shape quadratic scaling required by the shape dominated limit. -/
theorem actual_shape_denominator_scale_limit {n : ℕ} (a : OrderedChartData)
    (tau : Fin n → ℝ)
    (hbeta : Complex.exp (-(n+1:ℂ)*(a.beta:ℂ)*Complex.I) = 1) :
    Tendsto (fun lam : ℝ =>
      shapePoleDenominator (radialParameter a.theta (lam^2)) a.alpha (lam • tau)/(lam:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((a.Q (n+1):ℂ)-Complex.I*(a.d:ℂ)*∑ j, ((shapeExtend tau j:ℝ):ℂ)^2)) := by
  simpa only [scaledShapeDenominator_eq_actual a tau _ hbeta] using
    scaledShapeDenominator_quotient_limit a tau

/-- The same actual denominator limit in the manuscript's positive radial
parameter ε, with the fixed shape rescaled by √ε. -/
theorem actual_shape_denominator_sqrt_limit {n : ℕ} (a : OrderedChartData)
    (tau : Fin n → ℝ)
    (hbeta : Complex.exp (-(n+1:ℂ)*(a.beta:ℂ)*Complex.I) = 1) :
    Tendsto (fun epsilon : ℝ =>
      shapePoleDenominator (radialParameter a.theta epsilon) a.alpha
        (Real.sqrt epsilon • tau)/(epsilon:ℂ))
      (𝓝[>] 0) (𝓝 ((a.Q (n+1):ℂ)-Complex.I*(a.d:ℂ)*∑ j, ((shapeExtend tau j:ℝ):ℂ)^2)) := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with epsilon he
      exact Real.sqrt_pos.mpr he
  have ht := (actual_shape_denominator_scale_limit a tau hbeta).comp hs
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with epsilon he
  simp only [Function.comp_apply, ← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt he)]

end
end IsingBulk.First
