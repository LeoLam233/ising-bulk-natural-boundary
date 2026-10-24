import IsingBulk.Anisotropic.NegativeNormalForm.Dispersion
import Mathlib.Analysis.Calculus.Deriv.Inv
import IsingBulk.Anisotropic.NegativeDominance.ExactModel

/-! Actual second derivatives of the local inverse phase. These retain the
complex anisotropy and are derived from the inverse equation, not a Hessian
ansatz. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

theorem edgePhase_deriv_eventually (phi : ℝ) (hphi : Real.sin phi ≠ 0) :
    ∀ᶠ w in 𝓝 (Real.cos phi : ℂ),
      deriv (edgePhase phi hphi) w = (Complex.sinh (edgePhase phi hphi w))⁻¹ := by
  have hs := edgePhase_spec phi hphi
  have he := Filter.EventuallyEq.deriv (show
    (fun w => Complex.cosh (edgePhase phi hphi w)) =ᶠ[𝓝 (Real.cos phi : ℂ)] id
    from hs.2.2.1)
  filter_upwards [hs.1.eventually_analyticAt, he] with w hw hew
  have hc := (Complex.hasDerivAt_cosh (edgePhase phi hphi w)).comp w hw.differentiableAt.hasDerivAt
  have hm : Complex.sinh (edgePhase phi hphi w) * deriv (edgePhase phi hphi) w = 1 := by
    change deriv (Complex.cosh ∘ edgePhase phi hphi) w = deriv id w at hew
    rw [hc.deriv, deriv_id] at hew
    exact hew
  have hn : Complex.sinh (edgePhase phi hphi w) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hm
    exact zero_ne_one hm
  field_simp
  linear_combination hm

theorem edgePhase_second_derivative (phi : ℝ) (hphi : Real.sin phi ≠ 0) :
    HasDerivAt (deriv (edgePhase phi hphi))
      (-(Real.cos phi : ℂ) / ((Real.sin phi : ℂ) * Complex.I)^3)
      (Real.cos phi : ℂ) := by
  have hs := edgePhase_spec phi hphi
  have hn : Complex.sinh (edgePhase phi hphi (Real.cos phi)) ≠ 0 := by
    rw [hs.2.1, Complex.sinh_mul_I, ← Complex.ofReal_sin]
    exact mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero
  have h := ((Complex.hasDerivAt_sinh _).comp _ hs.2.2.2).inv hn
  have he := edgePhase_deriv_eventually phi hphi
  have hh := h.congr_of_eventuallyEq he
  convert hh using 1
  simp only [Function.comp_apply]
  rw [hs.2.1, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  field_simp


theorem negativePhase_deriv_delta_eventually (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    ∀ᶠ delta in 𝓝 d,
      deriv (negativePhase B phi hphi (1 - Complex.cos d)) delta =
        deriv (edgePhase phi hphi)
          (negativeDispersion B (Real.cos phi) (1 - Complex.cos d) delta) *
          (-B (1 - Complex.cos d) * Complex.sin delta) := by
  have hc := (negativeDispersion_hasDerivAt_delta B (Real.cos phi) (1 - Complex.cos d) d).continuousAt
  have ha := (edgePhase_spec phi hphi).1.eventually_analyticAt
  rw [← negativeDispersion_center B (Real.cos phi) d] at ha
  filter_upwards [hc.tendsto.eventually ha] with delta hd
  exact (hd.differentiableAt.hasDerivAt.comp delta
    (negativeDispersion_hasDerivAt_delta B (Real.cos phi) (1 - Complex.cos d) delta)).deriv

/-- Second angular derivative at the central pole, with no frozen-B
approximation. The t-dependence of B is constant only in this angular derivative. -/
theorem negativePhase_second_delta (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    HasDerivAt (deriv (negativePhase B phi hphi (1 - Complex.cos d)))
      ((-(Real.cos phi : ℂ) / ((Real.sin phi : ℂ) * Complex.I)^3) *
          (-B (1 - Complex.cos d) * Complex.sin d)^2 +
        ((Real.sin phi : ℂ) * Complex.I)⁻¹ * (-B (1 - Complex.cos d) * Complex.cos d)) d := by
  have he := edgePhase_second_derivative phi hphi
  rw [← negativeDispersion_center B (Real.cos phi) d] at he
  have hc := he.comp d
    (negativeDispersion_hasDerivAt_delta B (Real.cos phi) (1 - Complex.cos d) d)
  have hd := (Complex.hasDerivAt_sin d).const_mul (-B (1 - Complex.cos d))
  have hp := hc.mul hd
  have hh := hp.congr_of_eventuallyEq (negativePhase_deriv_delta_eventually B phi hphi d)
  convert hh using 1
  simp only [Function.comp_apply]
  rw [negativeDispersion_center, (edgePhase_spec phi hphi).2.2.2.deriv]
  ring


/-- The exact constrained Hessian factor, prior to specializing d=π/n. -/
def centralHessian (B : ℂ → ℂ) (phi : ℝ) (d : ℂ) : ℂ :=
  Complex.cos d - B (1 - Complex.cos d) * (Real.cos phi : ℂ) /
    (Real.sin phi : ℂ)^2 * Complex.sin d ^ 2

theorem centralHessian_at_winding (B : ℂ → ℂ) (phi : ℝ) (n : ℕ) :
    centralHessian B phi (Real.pi / n : ℝ) =
      IsingBulk.Anisotropic.NegativeDominance.hessianFactor
        (B (IsingBulk.Anisotropic.NegativeDominance.tau n))
        (Real.cos phi) (Real.sin phi) n := by
  simp only [centralHessian, IsingBulk.Anisotropic.NegativeDominance.hessianFactor,
    IsingBulk.Anisotropic.NegativeDominance.tau, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_cos, Complex.ofReal_sin]

/-- The actual phase has second derivative -h times its central parameter
slope. This verifies the Hessian used in the exact model. -/
theorem negativePhase_second_delta_hessian (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    HasDerivAt (deriv (negativePhase B phi hphi (1 - Complex.cos d)))
      (-centralHessian B phi d *
        (((Real.sin phi : ℂ) * Complex.I)⁻¹ * B (1 - Complex.cos d))) d := by
  convert negativePhase_second_delta B phi hphi d using 1
  have hs : (Real.sin phi : ℂ) ≠ 0 := by exact_mod_cast hphi
  unfold centralHessian
  field_simp
  simp only [Complex.I_sq]
  ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
