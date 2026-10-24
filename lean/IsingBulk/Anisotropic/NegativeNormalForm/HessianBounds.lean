import IsingBulk.Anisotropic.NegativeNormalForm.RemovableEnergy

/-! A proved, n-independent quadratic bound on the actual anisotropic Hessian.
The constant comes from scalar holomorphy, not an assumed uniform estimate. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

theorem centralHessian_zero (B : ℂ → ℂ) (phi : ℝ) : centralHessian B phi 0 = 1 := by
  simp [centralHessian]

theorem centralHessian_even (B : ℂ → ℂ) (phi : ℝ) (d : ℂ) :
    centralHessian B phi (-d) = centralHessian B phi d := by
  simp [centralHessian]

theorem centralHessian_analyticAt_zero (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) : AnalyticAt ℂ (centralHessian B phi) 0 := by
  have hC : AnalyticAt ℂ (fun z : ℂ => B (1 - Complex.cos z)) 0 :=
    hB.comp_of_eq (analyticAt_const.sub Complex.analyticAt_cos) (by simp)
  exact Complex.analyticAt_cos.sub
    (((hC.mul analyticAt_const).div_const).mul (Complex.analyticAt_sin.pow 2))

theorem centralHessian_deriv_zero (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) : deriv (centralHessian B phi) 0 = 0 := by
  have hd := (centralHessian_analyticAt_zero B phi hB).differentiableAt.hasDerivAt
  have hd' : HasDerivAt (centralHessian B phi) (-deriv (centralHessian B phi) 0) 0 := by
    have hd0 : HasDerivAt (centralHessian B phi) (deriv (centralHessian B phi) 0) ((-id) (0 : ℂ)) := by
      simpa using hd
    convert hd0.comp (0 : ℂ) (hasDerivAt_id (0 : ℂ)).neg using 1
    · ext z
      exact (centralHessian_even B phi z).symm
    · simp
  have he := hd.unique hd'
  linear_combination he / 2

/-- Scalar holomorphy supplies an actual uniform quadratic remainder bound. -/
theorem analytic_zero_derivative_quadratic_bound {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hd : deriv f 0 = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ‖f z - f 0‖ ≤ C * ‖z‖^2 := by
  let G := dslope (dslope f 0) 0
  have hG : AnalyticAt ℂ G 0 := analyticAt_dslope_center (analyticAt_dslope_center hf)
  have hb := hG.continuousAt.norm.eventually_lt continuousAt_const
    (show ‖G 0‖ < ‖G 0‖ + 1 by linarith)
  refine ⟨‖G 0‖+1, by positivity, ?_⟩
  filter_upwards [hb] with z hz
  have h1 := sub_smul_dslope f 0 z
  have h2 := sub_smul_dslope (dslope f 0) 0 z
  simp only [sub_zero, smul_eq_mul, dslope_same, hd] at h1 h2
  have he : f z - f 0 = z^2 * G z := by
    dsimp [G]
    linear_combination -h1 - z*h2
  rw [he, norm_mul, norm_pow]
  nlinarith [norm_nonneg z, sq_nonneg ‖z‖]

theorem centralHessian_quadratic_bound (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d in 𝓝 (0 : ℂ),
      ‖centralHessian B phi d - 1‖ ≤ C * ‖d‖^2 := by
  simpa only [centralHessian_zero] using analytic_zero_derivative_quadratic_bound
    (centralHessian_analyticAt_zero B phi hB) (centralHessian_deriv_zero B phi hB)

theorem centralHessian_eventually_nonzero (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) : ∀ᶠ d in 𝓝 (0 : ℂ), centralHessian B phi d ≠ 0 :=
  (centralHessian_analyticAt_zero B phi hB).continuousAt.eventually_ne (by simp [centralHessian_zero])

end
end IsingBulk.Anisotropic.NegativeNormalForm
