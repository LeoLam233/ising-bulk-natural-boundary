import IsingBulk.First.RegularResidueDomain
import IsingBulk.First.RegularMeanLocal

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

def deformedMeanW (a : RegularChartData) (c₀ : ℝ) (x : ℝ × ℝ × ℝ) : ℂ :=
  IsingBulk.Branch.dispersion (radialParameter a.theta x.1)
    (Complex.exp (((-c₀*x.1+x.2.2:ℝ):ℂ)+(((-a.alpha+x.2.1:ℝ):ℂ))*Complex.I))

theorem deformedMeanW_zero (a : RegularChartData) (c₀ : ℝ) :
    deformedMeanW a c₀ 0 = (Real.cos a.beta:ℂ) := by
  have hS : radialParameter a.theta 0+(radialParameter a.theta 0)⁻¹ = 2*(Real.cos a.theta:ℂ) := by
    simpa [radialParameter, complexRadialTrace] using complexRadialTrace_zero a.theta
  have hangle : (Real.cos a.alpha:ℂ)+(Real.cos a.beta:ℂ)=2*(Real.cos a.theta:ℂ) := by
    exact_mod_cast a.angle_relation
  unfold deformedMeanW
  rw [polar_dispersion]
  simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, Complex.ofReal_zero,
    Complex.ofReal_neg, zero_add, Complex.cosh_mul_I, Complex.cos_neg, ← Complex.ofReal_cos, hS]
  linear_combination -hangle

theorem deformedMeanW_continuous (a : RegularChartData) (c₀ : ℝ) :
    ContinuousAt (deformedMeanW a c₀) 0 := by
  unfold deformedMeanW IsingBulk.Branch.dispersion radialParameter
  fun_prop (disch := simp)

/-- The single source c₀ produced by global radial admissibility also meets
A₀>c₀; no incompatible second radius choice is necessary. -/
theorem global_radius_implies_mean_margin (a : RegularChartData) {c₀ : ℝ}
    (hc : 0 < c₀) (hsmall : c₀ < Real.sin a.theta/2) : c₀ < a.A₀ c₀ := by
  unfold RegularChartData.A₀
  apply (lt_div_iff₀ a.sin_beta_pos).mpr
  have ha := mul_le_mul_of_nonneg_left (Real.sin_le_one a.alpha) hc.le
  have hb := mul_le_mul_of_nonneg_left (Real.sin_le_one a.beta) hc.le
  nlinarith [a.sin_theta_pos]

/-- One fixed neighborhood works for every sufficiently small radial
parameter, angular deviation and downward depth. -/
theorem deformedMeanW_uniform_domain (a : RegularChartData) (c₀ : ℝ)
    (hA : 0 < a.A₀ c₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ epsilon u depth : ℝ,
      0 < epsilon → epsilon < r → |u| < r → 0 ≤ depth → depth < r →
      0 < (deformedMeanW a c₀ (epsilon,u,depth)).im ∧
      -Real.pi < -a.alpha+u ∧ -a.alpha+u < 0 := by
  obtain ⟨rM,hrM,hM⟩ := radial_chart_imaginary_margin a c₀ hA
  let rAngle := min a.alpha (Real.pi-a.alpha)/2
  have hrAngle : 0 < rAngle := half_pos (lt_min a.alpha_pos (by linarith [a.alpha_lt_pi]))
  let r := min rM rAngle
  have hrp : 0 < r := lt_min hrM hrAngle
  refine ⟨r,hrp,?_⟩
  intro epsilon u depth he her hu hd _hdr
  have hrM' : r ≤ rM := min_le_left _ _
  have hrAng' : r ≤ rAngle := min_le_right _ _
  have hangle : -Real.pi < -a.alpha+u ∧ -a.alpha+u < 0 := by
    have hu' := (abs_lt.mp (hu.trans_le hrAng'))
    have h1 := min_le_left a.alpha (Real.pi-a.alpha)
    have h2 := min_le_right a.alpha (Real.pi-a.alpha)
    dsimp [rAngle] at hu'
    constructor <;> linarith [a.alpha_pos, a.alpha_lt_pi]
  have hs := Real.sin_neg_of_neg_of_neg_pi_lt hangle.2 (by linarith [hangle.1, Real.pi_pos])
  have htop := hM epsilon u he (her.trans_le hrM') (hu.trans_le hrM')
  have htoppos : 0 < (IsingBulk.Jets.chartW (radialParameter a.theta epsilon) (-c₀*epsilon) a.alpha (u:ℂ)).im :=
    (mul_pos (div_pos (mul_pos hA a.sin_beta_pos) (by norm_num)) he).trans_le htop
  have htop' : 0 < (IsingBulk.Branch.dispersion (radialParameter a.theta epsilon)
      (Complex.exp (((-c₀*epsilon:ℝ):ℂ)+(((-a.alpha+u:ℝ):ℂ))*Complex.I))).im := by
    convert htoppos using 1
    unfold IsingBulk.Jets.chartW IsingBulk.Jets.angularY
    congr 3
    push_cast
    ring
  have him := htop'.trans_le (polar_dispersion_im_monotone (radialParameter a.theta epsilon)
    (-c₀*epsilon) (-c₀*epsilon+depth) (-a.alpha+u) (le_add_of_nonneg_right hd) hs.le)
  exact ⟨him, hangle.1, hangle.2⟩

end
end IsingBulk.First.Regular
