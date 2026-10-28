import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Quantitative protected complex projection for F001's covariance.
The angle secant is close to a positive real number, while the inverse-slope
secant stays in a rotated cone. Neither factor is declared real. -/
namespace IsingBulk.HT22

theorem projected_product_lower {phase a b : ℂ} {d η κ L : ℝ}
    (hphase : ‖phase‖≤1) (hd : 0≤d) (hκ : η≤κ)
    (ha : ‖a-(d:ℂ)‖≤η*d)
    (hb : κ*‖b‖≤(phase*b).re)
    (hsize : L*d≤‖b‖) :
    (κ-η)*L*d^2≤(phase*(a*b)).re := by
  have herr : ‖phase*((a-(d:ℂ))*b)‖≤η*d*‖b‖ := by
    rw [norm_mul,norm_mul]
    calc
      ‖phase‖*(‖a-(d:ℂ)‖*‖b‖) ≤ 1*(‖a-(d:ℂ)‖*‖b‖) :=
        mul_le_mul_of_nonneg_right hphase (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ η*d*‖b‖ := by
        simp only [one_mul]
        exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  have hre : -(η*d*‖b‖)≤(phase*((a-(d:ℂ))*b)).re := by
    have hh := Complex.abs_re_le_norm (phase*((a-(d:ℂ))*b))
    have := (abs_le.mp (hh.trans herr)).1
    exact this
  have he : (phase*(a*b)).re=d*(phase*b).re+(phase*((a-(d:ℂ))*b)).re := by
    have hc : phase*(a*b)=(d:ℂ)*(phase*b)+phase*((a-(d:ℂ))*b) := by ring
    rw [hc,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
    ring
  have hs := mul_le_mul_of_nonneg_left hsize (mul_nonneg (sub_nonneg.mpr hκ) hd)
  have hb' := mul_le_mul_of_nonneg_left hb hd
  rw [he]
  nlinarith

/-- A multiplier close to one retains a protected cone projection. -/
theorem projected_multiplier_stability {phase z factor : ℂ} {κ η : ℝ}
    (hphase : ‖phase‖≤1) (hfactor : ‖factor-1‖≤η)
    (hz : κ*‖z‖≤(phase*z).re) :
    (κ-η)*‖z‖≤(phase*(factor*z)).re := by
  have herr : ‖phase*((factor-1)*z)‖≤η*‖z‖ := by
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 1*(‖factor-1‖*‖z‖) := mul_le_mul_of_nonneg_right hphase (by positivity)
      _ ≤ η*‖z‖ := by simpa using mul_le_mul_of_nonneg_right hfactor (norm_nonneg z)
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (phase*((factor-1)*z))).trans herr)).1
  have he : phase*(factor*z)=phase*z+phase*((factor-1)*z) := by ring
  rw [he,Complex.add_re]
  nlinarith

end IsingBulk.HT22
