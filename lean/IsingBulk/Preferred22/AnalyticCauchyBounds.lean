import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-! Dimension-independent Cauchy bounds used for the rescaled actual
collective field. These estimates do not assume any derivative bound. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The Schwarz estimate on a concentric half ball, with an absolute
function bound rather than a bound centered at its unknown value. -/
theorem analytic_fderiv_half_ball_bound (f : E → F) (x : E) (R M : ℝ)
    (hR : 0<R) (hf : AnalyticOnNhd ℂ f (ball x R))
    (hM : ∀ z∈ball x R, ‖f z‖≤M) (y : E) (hy : y∈ball x (R/2)) :
    ‖fderiv ℂ f y‖≤4*M/R := by
  have hsub : ball y (R/2)⊆ball x R := by
    intro z hz
    have hh := dist_triangle z y x
    have hz' : dist z y<R/2 := hz
    have hy' : dist y x<R/2 := hy
    change dist z x<R
    linarith
  have hyR : y∈ball x R := ball_subset_ball (by linarith) hy
  have hmap : MapsTo f (ball y (R/2)) (closedBall (f y) (2*M)) := by
    intro z hz
    change dist (f z) (f y)≤2*M
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hM z (hsub hz),hM y hyR])
  have hh := Complex.norm_fderiv_le_div_of_mapsTo_ball
    (fun z hz => (hf z (hsub hz)).differentiableAt.differentiableWithinAt)
    hmap (half_pos hR)
  convert hh using 1
  field_simp
  ring

/-- Only the derivative order enters this numerical constant. -/
def cauchyJetConstant : ℕ → ℝ
  | 0 => 1
  | n+1 => 4*2^n*cauchyJetConstant n

theorem cauchyJetConstant_pos (n : ℕ) : 0<cauchyJetConstant n := by
  induction n with
  | zero => norm_num [cauchyJetConstant]
  | succ n ih => simp only [cauchyJetConstant]; positivity

/-- All Fréchet derivative norms follow from analyticity and a function
bound on one fixed ball. The constant is independent of both dimensions. -/
theorem analytic_iteratedFDeriv_ball_bound (f : E → F) (x : E) (R M : ℝ)
    (hR : 0<R) (hf : AnalyticOnNhd ℂ f (ball x R))
    (hM : ∀ z∈ball x R, ‖f z‖≤M) (n : ℕ) :
    ∀ y∈ball x (R/2^n),
      ‖iteratedFDeriv ℂ n f y‖≤cauchyJetConstant n*M/R^n := by
  induction n with
  | zero => simpa only [pow_zero,div_one,cauchyJetConstant,one_mul,
      norm_iteratedFDeriv_zero] using hM
  | succ n ih =>
    intro y hy
    have hRn : 0<R/(2:ℝ)^n := div_pos hR (by positivity)
    have hsmall : ball x (R/(2:ℝ)^n)⊆ball x R := by
      apply ball_subset_ball
      exact div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hfn : AnalyticOnNhd ℂ (iteratedFDeriv ℂ n f) (ball x (R/(2:ℝ)^n)) :=
      (hf.iteratedFDeriv n).mono hsmall
    have hy' : y∈ball x ((R/(2:ℝ)^n)/2) := by
      convert hy using 1
      simp only [pow_succ]
      ring
    have hh := analytic_fderiv_half_ball_bound (iteratedFDeriv ℂ n f) x
      (R/(2:ℝ)^n) (cauchyJetConstant n*M/R^n) hRn hfn ih y hy'
    rw [norm_fderiv_iteratedFDeriv] at hh
    convert hh using 1
    simp only [cauchyJetConstant,pow_succ]
    field_simp

theorem analytic_iteratedFDeriv_center_bound (f : E → F) (x : E) (R M : ℝ)
    (hR : 0<R) (hf : AnalyticOnNhd ℂ f (ball x R))
    (hM : ∀ z∈ball x R, ‖f z‖≤M) (n : ℕ) :
    ‖iteratedFDeriv ℂ n f x‖≤cauchyJetConstant n*M/R^n :=
  analytic_iteratedFDeriv_ball_bound f x R M hR hf hM n x
    (mem_ball_self (div_pos hR (by positivity)))

end
end IsingBulk.Preferred22
