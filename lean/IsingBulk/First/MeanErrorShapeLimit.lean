import IsingBulk.First.MeanErrorShapeIntegral
import IsingBulk.First.ShapeLimitTransfer
import IsingBulk.First.ActualPostMeanInterchange
import IsingBulk.First.MeanPhysicalDecomposition

/-! The literal mean error remains bounded after fixed-cutoff shape
integration and contributes zero to the square-root normalized asymptotic. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Filter Set
open scoped Topology

def localizedMeanErrorIntegral {n : ℕ} (a : OrderedChartData) (chi : ShapeSpace n → ℂ)
    (eta : ℝ → ℂ) (rho delta : ℝ) (s : ℂ) : ℂ :=
  ∫ t : Fin n → ℝ, chi (shapeCoordinateEquiv n (WithLp.toLp 2 t))*
    (meanRegularError eta s rho a.alpha delta t/((n+1).factorial:ℂ))

theorem localizedMeanErrorIntegral_eq_intrinsic {n : ℕ} (a : OrderedChartData)
    (chi : ShapeSpace n → ℂ) (eta : ℝ → ℂ) (rho delta : ℝ) (s : ℂ) :
    localizedMeanErrorIntegral a chi eta rho delta s =
      (Real.sqrt (n+1))⁻¹ • intrinsicMeanErrorIntegral a chi eta rho delta s := by
  simpa only [localizedMeanErrorIntegral,intrinsicMeanErrorIntegral,
    intrinsicShapeCoordinates_shapeCoordinateEquiv] using integral_shapeExtend n (fun x =>
      chi x*(meanRegularError eta s rho a.alpha delta (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ)))

theorem localizedMeanErrorIntegral_iteratedDeriv {n : ℕ} (a : OrderedChartData)
    (chi : ShapeSpace n → ℂ) (eta : ℝ → ℂ) (rho delta : ℝ) (j : ℕ) (s : ℂ) :
    (deriv^[j] (localizedMeanErrorIntegral a chi eta rho delta)) s =
      (Real.sqrt (n+1))⁻¹ • (deriv^[j] (intrinsicMeanErrorIntegral a chi eta rho delta)) s := by
  have he : localizedMeanErrorIntegral a chi eta rho delta =
      fun z => (((Real.sqrt (n+1))⁻¹:ℝ):ℂ)*intrinsicMeanErrorIntegral a chi eta rho delta z := by
    funext z
    rw [localizedMeanErrorIntegral_eq_intrinsic,Complex.real_smul]
  rw [he,iterate_deriv_const_mul]
  rfl

theorem actual_mean_error_shape_sqrt_limit {n : ℕ} (a : OrderedChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ R : ℝ, 0 < R ∧ ∀ eta : ℝ → ℂ, Continuous eta →
        ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, ‖chi x‖ ≤ 1) →
          (∀ x, chi x ≠ 0 → ‖x‖ < R) → ∀ j : ℕ,
          Tendsto (fun epsilon : ℝ => Real.sqrt epsilon •
            (deriv^[j] (localizedMeanErrorIntegral a chi eta
              (-(Real.sin a.theta/4)*epsilon) delta)) (radialParameter a.theta epsilon))
            (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨D,hD,h⟩ := actual_mean_error_shape_integral_bounds (n := n) a ha hb
  refine ⟨D,hD,?_⟩
  intro delta hd hdD
  obtain ⟨R,hR,hBound⟩ := h delta hd hdD
  refine ⟨R,hR,?_⟩
  intro eta heta chi hchi hchib hchis j
  obtain ⟨C,hC,hbnd⟩ := (hBound eta heta chi hchi hchib hchis).2 j
  let c₀ := Real.sin a.theta/4
  have hc₀ : 0 < c₀ := div_pos a.sin_theta_pos (by norm_num)
  let epsilon₀ := R/(c₀+1)
  have he0 : 0 < epsilon₀ := div_pos hR (by positivity)
  have hsmall (epsilon : ℝ) (he : 0 < epsilon) (heR : epsilon < epsilon₀) :
      |(-c₀*epsilon)| ≤ R ∧ ‖radialParameter a.theta epsilon-exp ((a.theta:ℂ)*I)‖ < R := by
    have hm := (lt_div_iff₀ (show 0 < c₀+1 by positivity)).mp heR
    rw [radialParameter_sub_center_norm,abs_of_pos he,abs_of_neg (by nlinarith)]
    constructor <;> nlinarith
  have hε : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hbounded : IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ))
      (norm ∘ fun epsilon : ℝ => (deriv^[j] (localizedMeanErrorIntegral a chi eta
        (-c₀*epsilon) delta)) (radialParameter a.theta epsilon)) := by
    refine ⟨‖(Real.sqrt (n+1))⁻¹‖*C,eventually_map.mpr ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds he0).filter_mono nhdsWithin_le_nhds] with epsilon he heR
    dsimp only [Function.comp_apply]
    rw [localizedMeanErrorIntegral_iteratedDeriv,norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hbnd (-c₀*epsilon) (hsmall epsilon he heR).1 _ (hsmall epsilon he heR).2) (norm_nonneg _)
  simpa only [Pi.smul_apply] using!
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hε hbounded

end
end IsingBulk.First
