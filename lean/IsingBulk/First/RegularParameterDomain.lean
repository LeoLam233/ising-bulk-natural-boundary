import IsingBulk.First.RegularMeanLocal
import IsingBulk.First.RegularChartData
import IsingBulk.First.MeanParameterDomain

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

def meanParameterBase (a : RegularChartData) : ℂ × ℝ × ℝ × ℝ :=
  (Complex.exp ((a.theta:ℂ)*Complex.I),0,0,0)

def parameterDeformedW (a : RegularChartData) (x : ℂ × ℝ × ℝ × ℝ) : ℂ :=
  IsingBulk.Branch.dispersion x.1
    (Complex.exp (((x.2.1+x.2.2.2:ℝ):ℂ)+(((-a.alpha+x.2.2.1:ℝ):ℂ))*Complex.I))

theorem parameterDeformedW_base (a : RegularChartData) :
    parameterDeformedW a (meanParameterBase a) = (Real.cos a.beta:ℂ) := by
  have hS := IsingBulk.PrimeFamily.exp_angle_add_inv a.theta
  have ha : (Real.cos a.alpha:ℂ)+(Real.cos a.beta:ℂ)=2*(Real.cos a.theta:ℂ) := by
    exact_mod_cast a.angle_relation
  unfold parameterDeformedW meanParameterBase
  rw [polar_dispersion]
  simp only [add_zero, Complex.ofReal_zero, Complex.ofReal_neg, zero_add,
    Complex.cosh_mul_I, Complex.cos_neg, ← Complex.ofReal_cos, hS]
  linear_combination -ha

theorem parameterDeformedW_continuous (a : RegularChartData) :
    ContinuousAt (parameterDeformedW a) (meanParameterBase a) := by
  unfold parameterDeformedW IsingBulk.Branch.dispersion
  fun_prop (disch := simp [meanParameterBase])

/-- Uniform source-parameter chart. Positivity of Im W is derived from the
actual global radius/trace margin and monotonicity under downward motion. -/
theorem parameterDeformedW_uniform_domain (a : RegularChartData) :
    ∃ r : ℝ, 0 < r ∧ ∀ (s : ℂ) (rho u depth : ℝ),
      ‖s-Complex.exp ((a.theta:ℂ)*Complex.I)‖ < r → |rho| < r → rho < 0 → |u| < r →
      0 ≤ depth → depth < r → (Real.exp rho)⁻¹-Real.exp rho < (sourceS s).im →
      0 < (parameterDeformedW a (s,rho,u,depth)).im ∧
      -Real.pi < -a.alpha+u ∧ -a.alpha+u < 0 := by
  let rAngle := min a.alpha (Real.pi-a.alpha)/2
  have hrAngle : 0 < rAngle := half_pos (lt_min a.alpha_pos (by linarith [a.alpha_lt_pi]))
  refine ⟨rAngle,hrAngle,?_⟩
  intro s rho u depth _hs _hrho hrhoneg hu hd _hdr hmargin
  have hang : -Real.pi < -a.alpha+u ∧ -a.alpha+u < 0 := by
    have hu' := abs_lt.mp hu
    have h1 := min_le_left a.alpha (Real.pi-a.alpha)
    have h2 := min_le_right a.alpha (Real.pi-a.alpha)
    dsimp [rAngle] at hu'
    constructor <;> linarith [a.alpha_pos,a.alpha_lt_pi]
  have htop : 0 < (IsingBulk.Branch.dispersion s
      (Complex.exp ((rho:ℂ)+(((-a.alpha+u:ℝ):ℂ))*Complex.I))).im := by
    exact sourceW_upper_of_margin (Real.exp_pos rho) (Real.exp_lt_one_iff.mpr hrhoneg) hmargin
      (by rw [Complex.norm_exp]; simp [Complex.mul_re])
  have hsin := Real.sin_neg_of_neg_of_neg_pi_lt hang.2 (by linarith [hang.1,Real.pi_pos])
  have him := htop.trans_le (polar_dispersion_im_monotone s rho (rho+depth) (-a.alpha+u)
    (le_add_of_nonneg_right hd) hsin.le)
  exact ⟨him,hang.1,hang.2⟩

end
end IsingBulk.First.Regular
