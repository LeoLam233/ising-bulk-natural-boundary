import IsingBulk.First.MeanMotion
import IsingBulk.First.GlobalResidueRoot

/-! Full mean-chart geometry with the complex source parameter free and the
chosen logarithmic radius held fixed. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

def meanParameterBase (a : OrderedChartData) : ℂ × ℝ × ℝ × ℝ :=
  (Complex.exp ((a.theta:ℂ)*Complex.I),0,0,0)

def parameterDeformedW (a : OrderedChartData) (x : ℂ × ℝ × ℝ × ℝ) : ℂ :=
  IsingBulk.Branch.dispersion x.1
    (Complex.exp (((x.2.1+x.2.2.2:ℝ):ℂ)+(((-a.alpha+x.2.2.1:ℝ):ℂ))*Complex.I))

theorem parameterDeformedW_base (a : OrderedChartData) :
    parameterDeformedW a (meanParameterBase a) = (Real.cos a.beta:ℂ) := by
  have hS := IsingBulk.PrimeFamily.exp_angle_add_inv a.theta
  have ha : (Real.cos a.alpha:ℂ)+(Real.cos a.beta:ℂ)=2*(Real.cos a.theta:ℂ) := by
    exact_mod_cast a.angle_relation
  unfold parameterDeformedW meanParameterBase
  rw [polar_dispersion]
  simp only [add_zero, Complex.ofReal_zero, Complex.ofReal_neg, zero_add,
    Complex.cosh_mul_I, Complex.cos_neg, ← Complex.ofReal_cos, hS]
  linear_combination -ha

theorem parameterDeformedW_continuous (a : OrderedChartData) :
    ContinuousAt (parameterDeformedW a) (meanParameterBase a) := by
  unfold parameterDeformedW IsingBulk.Branch.dispersion
  fun_prop (disch := simp [meanParameterBase])

/-- Uniform source-parameter chart. Positivity of Im W is derived from the
actual global radius/trace margin and monotonicity under downward motion. -/
theorem parameterDeformedW_uniform_domain (a : OrderedChartData) :
    ∃ r : ℝ, 0 < r ∧ ∀ (s : ℂ) (rho u depth : ℝ),
      ‖s-Complex.exp ((a.theta:ℂ)*Complex.I)‖ < r → |rho| < r → rho < 0 → |u| < r →
      0 ≤ depth → depth < r → (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im →
      0 < (parameterDeformedW a (s,rho,u,depth)).re ∧
      0 < (parameterDeformedW a (s,rho,u,depth)).im ∧
      -(Real.pi/2) < -a.alpha+u ∧ -a.alpha+u < 0 := by
  have he : ∀ᶠ x in 𝓝 (meanParameterBase a), 0 < (parameterDeformedW a x).re :=
    continuousAt_const.eventually_lt
      (Complex.continuous_re.continuousAt.comp (parameterDeformedW_continuous a))
      (by rw [parameterDeformedW_base]; exact a.cos_beta_pos)
  obtain ⟨rR,hrR,hR⟩ := Metric.eventually_nhds_iff.mp he
  let rAngle := min a.alpha (Real.pi/2-a.alpha)/2
  have hrAngle : 0 < rAngle := half_pos (lt_min a.alpha_pos (by linarith [a.alpha_lt]))
  let r := min rR rAngle
  refine ⟨r,lt_min hrR hrAngle,?_⟩
  intro s rho u depth hs hrho hrhoneg hu hd hdr hmargin
  have hang : -(Real.pi/2) < -a.alpha+u ∧ -a.alpha+u < 0 := by
    have hu' := abs_lt.mp (hu.trans_le (min_le_right _ _))
    have h1 := min_le_left a.alpha (Real.pi/2-a.alpha)
    have h2 := min_le_right a.alpha (Real.pi/2-a.alpha)
    dsimp [rAngle] at hu'
    constructor <;> linarith [a.alpha_pos,a.alpha_lt]
  have htop : 0 < (IsingBulk.Branch.dispersion s
      (Complex.exp ((rho:ℂ)+(((-a.alpha+u:ℝ):ℂ))*Complex.I))).im := by
    exact sourceW_upper_of_margin (Real.exp_pos rho) (Real.exp_lt_one_iff.mpr hrhoneg) hmargin
      (by rw [Complex.norm_exp]; simp [Complex.mul_re])
  have hsin := Real.sin_neg_of_neg_of_neg_pi_lt hang.2 (by linarith [hang.1,Real.pi_pos])
  have him := htop.trans_le (polar_dispersion_im_monotone s rho (rho+depth) (-a.alpha+u)
    (le_add_of_nonneg_right hd) hsin.le)
  refine ⟨?_,him,hang.1,hang.2⟩
  apply hR
  have hs' := hs.trans_le (min_le_left rR rAngle)
  have hrho' := hrho.trans_le (min_le_left rR rAngle)
  have hu' := hu.trans_le (min_le_left rR rAngle)
  have hd' := hdr.trans_le (min_le_left rR rAngle)
  simpa [meanParameterBase, Prod.dist_eq, Real.dist_eq, abs_of_nonneg hd, dist_eq_norm] using
    And.intro hs' (And.intro hrho' (And.intro hu' hd'))

end
end IsingBulk.First
